#!/usr/bin/env python3
"""Bounded annotations for existing resource samples, not a scheduler or poller.

Linux stat field 22 identifies a PID lifetime within this boot. Lake 4.33's
compileLeanModule supplies source/output/--setup operands directly to Lean.
Only that recognized invocation is mapped; no argv or environment is emitted.
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
UNAVAILABLE = "UNAVAILABLE"


def read_bounded(path, limit):
    with path.open("rb") as stream:
        data = stream.read(limit + 1)
    if len(data) > limit:
        raise ValueError("bounded read exceeded")
    return data


def stat_identity(proc, pid):
    text = read_bounded(proc / str(pid) / "stat", 4096).decode("utf-8")
    fields = text[text.rindex(")") + 2:].split()
    if int(text.split(" ", 1)[0]) != pid or len(fields) < 20:
        raise ValueError("stat identity")
    parent, birth = int(fields[1]), int(fields[19])
    if parent < 0 or birth < 0 or fields[0] not in "RSDZTtXxKWPI":
        raise ValueError("stat fields")
    return parent, birth, fields[0]


def native_file(repository, cwd, argv):
    # Recognize the native compiler suffix; unknown prefix options fail closed.
    if len(argv) < 7 or argv[-1] != "--json" or argv[-3] != "--setup":
        raise ValueError("not a Lake compiler invocation")
    outputs = {}
    pos = len(argv) - 4
    while pos > 1 and argv[pos - 1] in ("-o", "-i", "-c", "-b"):
        flag = argv[pos - 1]
        if flag in outputs:
            raise ValueError("duplicate output")
        outputs[flag] = argv[pos]
        pos -= 2
    if "-o" not in outputs or pos < 1:
        raise ValueError("no native olean")
    source_arg = argv[pos]
    index = 1
    while index < pos:
        arg = argv[index]
        if arg in ("-R", "--root", "--load-dynlib", "--plugin"):
            index += 2
        elif arg.startswith(("-D", "--root=", "--load-dynlib=", "--plugin=")):
            index += 1
        else:
            raise ValueError("unknown compiler prefix")
    if index != pos:
        raise ValueError("missing prefix operand")

    def local_path(value):
        path = (cwd / value).resolve()
        path.relative_to(repository)
        return path

    source = local_path(source_arg)
    olean = local_path(outputs["-o"])
    setup = local_path(argv[-2])
    # The module name is supplied by Lean's own ModuleSetup, not a timing match.
    data = json.loads(read_bounded(setup, 2 * 1024 * 1024))
    module = data["name"]
    if not isinstance(module, str) or len(module) > 512:
        raise ValueError("module name")
    parts = module.split(".")
    if not all(part.isidentifier() for part in parts):
        raise ValueError("unsupported module name")
    tail = "/".join(parts)
    if not str(source).endswith("/" + tail + ".lean"):
        raise ValueError("source/module mismatch")
    if not str(olean).endswith("/.lake/build/lib/lean/" + tail + ".olean"):
        raise ValueError("olean/module mismatch")
    if not str(setup).endswith("/.lake/build/ir/" + tail + ".setup.json"):
        raise ValueError("setup/module mismatch")
    # Source bytes identify what is present at observation time, not proof that
    # they could not have changed after the compiler opened the input.
    source_hash = hashlib.sha256(read_bounded(source, 16 * 1024 * 1024)).hexdigest()
    return {"module": module, "file": str(source.relative_to(repository)),
            "source_sha256_at_sample": source_hash,
            "facet": UNAVAILABLE, "package": UNAVAILABLE}


def annotate(proc, repository, pid, sampled_parent):
    record = {"schema": 1, "event": "sample", "pid": pid,
              "birth_ticks": UNAVAILABLE, "ppid": UNAVAILABLE,
              "parent_birth_ticks": UNAVAILABLE, "state": UNAVAILABLE,
              "executable": UNAVAILABLE, "module": UNAVAILABLE,
              "file": UNAVAILABLE, "source_sha256_at_sample": UNAVAILABLE,
              "facet": UNAVAILABLE, "package": UNAVAILABLE,
              "identity_status": "unavailable", "utc_epoch_ns": time.time_ns()}
    try:
        before = stat_identity(proc, pid)
        if before[0] != sampled_parent:
            return record
        directory = proc / str(pid)
        executable = os.readlink(directory / "exe")
        parent_before = stat_identity(proc, before[0])
        native = None
        # A real toolchain executable with a Lake parent, not an argv[0] label.
        if Path(executable).name == "lean":
            try:
                parent_exe = os.readlink(proc / str(before[0]) / "exe")
                if Path(parent_exe).name != "lake" or Path(parent_exe).parent != Path(executable).parent:
                    raise ValueError("not the toolchain Lake parent")
                cwd = os.readlink(directory / "cwd")
                command = read_bounded(directory / "cmdline", 65536)
                if not command.endswith(b"\0"):
                    raise ValueError("truncated cmdline")
                argv = command[:-1].decode("utf-8").split("\0")
                native = native_file(repository, Path(cwd), argv)
                if (os.readlink(directory / "cwd") != cwd
                        or read_bounded(directory / "cmdline", 65536) != command
                        or os.readlink(proc / str(before[0]) / "exe") != parent_exe):
                    native = None
            except (OSError, ValueError, KeyError, TypeError):
                native = None
        after = stat_identity(proc, pid)
        parent_after = stat_identity(proc, before[0])
        if (before[:2] != after[:2] or parent_before[:2] != parent_after[:2]
                or os.readlink(directory / "exe") != executable):
            return record
        record.update(birth_ticks=before[1], ppid=before[0],
                      parent_birth_ticks=parent_before[1], state=after[2],
                      executable=Path(executable).name if Path(executable).name in ("lean", "lake") else "other")
        if native is not None:
            record.update(native)
            record["identity_status"] = "native-file"
    except (OSError, ValueError, KeyError, TypeError):
        pass
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proc-root", type=Path, required=True)
    parser.add_argument("--repository", type=Path, required=True)
    args = parser.parse_args()
    repository = args.repository.resolve()
    # Input is the existing resource observer's tree, never process arguments.
    tree = sys.stdin.buffer.read(1024 * 1024 + 1)
    if len(tree) > 1024 * 1024:
        print('NATIVE_TASK_SAMPLE {"schema":1,"identity_status":"unavailable"}', flush=True)
        return
    entries = tree.decode("ascii", errors="replace").strip().split(";")
    emitted = False
    for entry in entries[:LIMIT]:
        match = re.match(r"^pid:([0-9]+),ppid:([0-9]+),", entry)
        if match:
            record = annotate(args.proc_root, repository, int(match[1]), int(match[2]))
            print("NATIVE_TASK_SAMPLE " + json.dumps(record, separators=(",", ":")), flush=True)
            emitted = True
    if not emitted:
        print('NATIVE_TASK_SAMPLE {"schema":1,"identity_status":"unavailable"}', flush=True)


if __name__ == "__main__":
    main()
