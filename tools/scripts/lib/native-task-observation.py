#!/usr/bin/env python3
"""Bounded annotations for existing resource samples, not a scheduler or poller.

Operand association, setup-validated module identity and observation-time source
bytes are separate claims. None identifies compiler-open-time bytes or an OOM
victim. Only the recognized Lake compiler argv is mapped; argv is never emitted.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time

LIMIT = 64
RECORD_LIMIT = 4096 - len("NATIVE_TASK_SAMPLE \n")
UNAVAILABLE = "UNAVAILABLE"


def fingerprint(value):
    return (value.st_dev, value.st_ino, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def read_bounded(path, limit, measurement=None):
    measurement = measurement if measurement is not None else {}
    measurement.update(limit_bytes=limit, status="unavailable")
    with path.open("rb") as stream:
        before = os.fstat(stream.fileno())
        measurement["stat_size_bytes"] = before.st_size
        data = stream.read(limit + 1)
        after = os.fstat(stream.fileno())
    measurement.update(bytes_read=len(data), length_kind="lower-bound" if len(data) > limit else "exact")
    if path.name == "cmdline":
        measurement["nul_complete"] = data.endswith(b"\0") if len(data) <= limit else UNAVAILABLE
    if fingerprint(before) != fingerprint(after) or fingerprint(after) != fingerprint(path.stat()):
        measurement["status"] = "read-changed"
        raise ValueError("read-changed")
    if len(data) > limit:
        measurement["status"] = "limit-exceeded"
        raise ValueError("limit-exceeded")
    measurement["status"] = "read"
    return data


def stat_identity(proc, pid, measurement=None):
    text = read_bounded(proc / str(pid) / "stat", 4096, measurement).decode("utf-8")
    fields = text[text.rindex(")") + 2:].split()
    if int(text.split(" ", 1)[0]) != pid or len(fields) < 20:
        raise ValueError("invalid-stat")
    parent, birth = int(fields[1]), int(fields[19])
    if not 0 <= parent <= 2147483647 or not 0 <= birth <= 18446744073709551615 or fields[0] not in "RSDZTtXxKWPI":
        raise ValueError("invalid-stat")
    return parent, birth, fields[0]


def native_operands(repository, cwd, argv):
    if len(argv) < 7 or argv[-1] != "--json" or argv[-3] != "--setup":
        raise ValueError("unsupported-suffix")
    outputs = {}
    pos = len(argv) - 4
    while pos > 1 and argv[pos - 1] in ("-o", "-i", "-c", "-b"):
        flag = argv[pos - 1]
        if flag in outputs:
            raise ValueError("duplicate-output")
        outputs[flag] = argv[pos]
        pos -= 2
    if "-o" not in outputs or pos < 1:
        raise ValueError("missing-output")
    index = 1
    while index < pos:
        arg = argv[index]
        if arg in ("-R", "--root", "--load-dynlib", "--plugin"):
            index += 2
        elif arg.startswith(("-D", "--root=", "--load-dynlib=", "--plugin=")):
            index += 1
        else:
            raise ValueError("unsupported-prefix")
    if index != pos:
        raise ValueError("missing-prefix-operand")
    paths = []
    for value in (argv[pos], outputs["-o"], argv[-2]):
        path = (cwd / value).resolve()
        try:
            path.relative_to(repository)
        except ValueError:
            raise ValueError("outside-repository") from None
        paths.append(path)
    source, olean, setup = paths
    # Derive an operand tail only, never a public module name, before setup I/O.
    marker = "/.lake/build/lib/lean/"
    if marker not in str(olean) or not str(olean).endswith(".olean"):
        raise ValueError("output-path-shape")
    tail = str(olean).rsplit(marker, 1)[1][:-6]
    if not tail or not all(part.isidentifier() for part in tail.split("/")):
        raise ValueError("unsupported-tail")
    if not str(source).endswith("/" + tail + ".lean"):
        raise ValueError("source-tail-mismatch")
    if not str(setup).endswith("/.lake/build/ir/" + tail + ".setup.json"):
        raise ValueError("setup-tail-mismatch")
    return paths, tail


def setup_module(data, tail):
    value = json.loads(data)
    module = value.get("name") if isinstance(value, dict) else None
    if not isinstance(module, str) or len(module) > 512:
        raise ValueError("invalid-module-name")
    if not all(part.isidentifier() for part in module.split(".")):
        raise ValueError("invalid-module-name")
    if module.replace(".", "/") != tail:
        raise ValueError("module-tail-mismatch")
    return module


# Only these bounded reason tokens can reach the output. Exception text cannot.
REASONS = frozenset(("read-changed", "limit-exceeded", "invalid-stat", "unsupported-suffix",
    "duplicate-output", "missing-output", "unsupported-prefix", "missing-prefix-operand",
    "outside-repository", "output-path-shape", "unsupported-tail", "source-tail-mismatch",
    "setup-tail-mismatch", "invalid-module-name", "module-tail-mismatch", "sampled-parent-mismatch",
    "parent-toolchain-mismatch", "nul-incomplete", "cwd-changed", "cmdline-changed",
    "parent-executable-changed", "process-changed", "parent-changed", "executable-changed",
    "operands-changed", "source-changed", "setup-changed", "not-lean"))
ERRORS = (OSError, ValueError, KeyError, TypeError, RuntimeError, RecursionError)


def failure(stage, error):
    result = {"stage": stage, "reason": "invalid-data"}
    if isinstance(error, OSError):
        result["reason"] = "os-error"
        if error.errno is not None:
            result["errno"] = error.errno
    elif isinstance(error, UnicodeError):
        result["reason"] = "invalid-utf8"
    elif isinstance(error, json.JSONDecodeError):
        result["reason"] = "invalid-json"
    elif str(error) in REASONS:
        result["reason"] = str(error)
    return result


def annotate(proc, repository, pid, sampled_parent):
    record = {"schema": 1, "event": "sample", "pid": pid,
              "birth_ticks": UNAVAILABLE, "ppid": UNAVAILABLE,
              "parent_birth_ticks": UNAVAILABLE, "state": UNAVAILABLE,
              "executable": UNAVAILABLE, "module": UNAVAILABLE,
              "file": UNAVAILABLE, "source_sha256_at_sample": UNAVAILABLE,
              "facet": UNAVAILABLE, "package": UNAVAILABLE,
              "identity_status": "unavailable", "utc_epoch_ns": time.time_ns()}
    diagnostic = {"stability": "unavailable", "operand_status": "unavailable",
                  "setup_name_status": "not-attempted", "source_hash_status": "not-attempted",
                  "reads": {}, "failures": []}
    record["diagnostic"] = diagnostic
    stage = "process-before"

    def read(path, bound):
        return read_bounded(path, bound, diagnostic["reads"].setdefault(stage, {}))

    def stat(pid):
        return stat_identity(proc, pid, diagnostic["reads"].setdefault(stage, {}))

    def require(condition, reason):
        if not condition:
            raise ValueError(reason)

    try:
        before = stat(pid)
        require(before[0] == sampled_parent, "sampled-parent-mismatch")
        directory = proc / str(pid)
        stage = "executable-before"
        executable = os.readlink(directory / "exe")
        stage = "parent-before"
        parent_before = stat(before[0])
        paths = command = cwd = parent_exe = module = source_hash = None
        file_tokens = {}
        try:
            stage = "invocation"
            require(Path(executable).name == "lean", "not-lean")
            stage = "parent-executable-before"
            parent_exe = os.readlink(proc / str(before[0]) / "exe")
            require(Path(parent_exe).name == "lake" and Path(parent_exe).parent == Path(executable).parent,
                    "parent-toolchain-mismatch")
            stage = "cwd-before"
            cwd = os.readlink(directory / "cwd")
            stage = "cmdline-before"
            command = read(directory / "cmdline", 65536)
            require(command.endswith(b"\0"), "nul-incomplete")
            argv = command[:-1].decode("utf-8").split("\0")
            stage = "operands"
            paths, tail = native_operands(repository, Path(cwd), argv)
            diagnostic["argv_shape"] = "native-compiler"
            # Setup and source observations are independent after operand checks.
            for kind, path, bound in (("setup", paths[2], 2097152), ("source", paths[0], 16777216)):
                try:
                    stage = kind + "-read"
                    diagnostic["reads"][stage] = {"limit_bytes": bound, "status": "unavailable"}
                    token = fingerprint(path.stat())
                    diagnostic["reads"][stage]["stat_size_bytes"] = token[2]
                    data = read(path, bound)
                    require(fingerprint(path.stat()) == token, kind + "-changed")
                    file_tokens[kind] = (path, token)
                    if kind == "setup":
                        stage = "setup-name"
                        module = setup_module(data, tail)
                        diagnostic["setup_name_status"] = "validated"
                    else:
                        source_hash = hashlib.sha256(data).hexdigest()
                        diagnostic["source_hash_status"] = "hashed"
                except ERRORS as error:
                    diagnostic["failures"].append(failure(stage, error))
                    diagnostic[kind + ("_name_status" if kind == "setup" else "_hash_status")] = "failed"
        except ERRORS as error:
            diagnostic["failures"].append(failure(stage, error))

        # Always revalidate captured identity, including after a later read failed.
        stage = "process-after"
        after = stat(pid)
        require(before[:2] == after[:2], "process-changed")
        stage = "parent-after"
        require(parent_before[:2] == stat(before[0])[:2], "parent-changed")
        stage = "executable-after"
        require(os.readlink(directory / "exe") == executable, "executable-changed")
        record.update(birth_ticks=before[1], ppid=before[0], parent_birth_ticks=parent_before[1],
                      state=after[2], executable=Path(executable).name if Path(executable).name in ("lean", "lake") else "other")
        if parent_exe is not None:
            stage = "parent-executable-after"
            require(os.readlink(proc / str(before[0]) / "exe") == parent_exe, "parent-executable-changed")
        if cwd is not None:
            stage = "cwd-after"
            require(os.readlink(directory / "cwd") == cwd, "cwd-changed")
        if command is not None:
            stage = "cmdline-after"
            require(read(directory / "cmdline", 65536) == command, "cmdline-changed")
        if paths is not None:
            stage = "operands-after"
            require(native_operands(repository, Path(cwd), argv)[0] == paths, "operands-changed")
            for kind, (path, token) in file_tokens.items():
                stage = kind + "-after"
                require(fingerprint(path.stat()) == token, kind + "-changed")
            diagnostic.update(operand_status="operand-only", operands=dict(zip(
                ("source", "output", "setup"), (str(p.relative_to(repository)) for p in paths))))
            if source_hash is not None:
                diagnostic["source_sha256_at_sample"] = source_hash
            if module is not None and source_hash is not None:
                record.update(module=module, file=str(paths[0].relative_to(repository)),
                              source_sha256_at_sample=source_hash, identity_status="native-file")
        diagnostic["stability"] = "stable"
    except ERRORS as error:
        diagnostic["failures"].append(failure(stage, error))
        diagnostic["stability"] = "unverified"
        if diagnostic["source_hash_status"] == "hashed":
            diagnostic["source_hash_status"] = "discarded-unstable"
        if diagnostic["setup_name_status"] == "validated":
            diagnostic["setup_name_status"] = "discarded-unstable"
    return record


def encode_record(record, sample_id):
    record["sample_id"] = sample_id
    diagnostic = record.get("diagnostic", {})
    # Cap the entire emitted line (hence also the added fields), including prefix,
    # newline, escaping and join identifier. Normal full identities stay raw.
    # Omitted paths are never emitted as deceptively complete truncated operands.
    def size():
        return len(json.dumps(record, separators=(",", ":")).encode())
    if size() > RECORD_LIMIT:
        diagnostic.pop("operands", None)
        diagnostic["operand_status"] = "truncated"
        diagnostic["truncation"] = "operands-omitted"
    if size() > RECORD_LIMIT:
        for key in ("module", "file", "source_sha256_at_sample"):
            record[key] = UNAVAILABLE
        record["identity_status"] = "unavailable"
        diagnostic.pop("source_sha256_at_sample", None)
        diagnostic["source_hash_status"] = "omitted-truncated"
        diagnostic["truncation"] = "identity-omitted"
    if size() > RECORD_LIMIT:
        diagnostic.pop("reads", None)
        diagnostic["truncation"] = "identity-and-read-measurements-omitted"
    return json.dumps(record, separators=(",", ":"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proc-root", type=Path, required=True)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--sample-id", required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{32}", args.sample_id):
        parser.error("sample-id must be 32 lowercase hex characters")
    repository = args.repository.resolve()
    tree = sys.stdin.buffer.read(1048576 + 1)
    entries = tree.decode("ascii", errors="replace").strip().split(";") if len(tree) <= 1048576 else []
    emitted = False
    for entry in entries[:LIMIT]:
        match = re.match(r"^pid:([0-9]{1,10}),ppid:([0-9]{1,10}),", entry)
        if match:
            record = annotate(args.proc_root, repository, int(match[1]), int(match[2]))
            print("NATIVE_TASK_SAMPLE " + encode_record(record, args.sample_id), flush=True)
            emitted = True
    if not emitted:
        record = {"schema": 1, "identity_status": "unavailable", "diagnostic": {
            "failures": [{"stage": "tree", "reason": "limit-exceeded" if len(tree) > 1048576 else "no-process-entry"}],
            "limit_bytes": 1048576, "bytes_read": len(tree),
            "length_kind": "lower-bound" if len(tree) > 1048576 else "exact"}}
        print("NATIVE_TASK_SAMPLE " + encode_record(record, args.sample_id), flush=True)


if __name__ == "__main__":
    main()
