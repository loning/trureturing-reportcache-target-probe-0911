#!/usr/bin/env bash
# Source after resource-observation-lib.sh with explicit repository and proc roots.
native_observation_repository="$1"
native_observation_proc_root="$2"
eval "$(declare -f resource_observe_sample | sed '1s/resource_observe_sample/resource_observe_sample_unlabelled/')"
resource_observe_sample() {
  # A fresh UUID per call also separates sampler, signal and final lifetimes.
  local resource_observation_sample_id
  resource_observation_sample_id="$(python3 -c 'import uuid; print(uuid.uuid4().hex)' 2>/dev/null)" || resource_observation_sample_id=""
  resource_observe_sample_unlabelled "$@"
}
eval "$(declare -f resource_observation_process_values | sed '1s/resource_observation_process_values/resource_observation_process_values_unlabelled/')"
resource_observation_process_values() {
  local values status=0 count _cpu tree
  values="$(resource_observation_process_values_unlabelled "$@")" || status=$?
  printf '%s\n' "$values"
  IFS=$'\t' read -r count _cpu tree <<< "$values"
  if [[ ! "${resource_observation_sample_id:-}" =~ ^[0-9a-f]{32}$ ]]; then
    printf '%s\n' 'NATIVE_TASK_SAMPLE {"schema":1,"identity_status":"unavailable","diagnostic":{"failures":[{"stage":"sample-id","reason":"unavailable"}]}}' >&2
    return "$status"
  fi
  printf '%s\n' "$tree" | python3 "$native_observation_repository/tools/scripts/lib/native-task-observation.py" \
    --repository "$native_observation_repository" --proc-root "$native_observation_proc_root" \
    --sample-id "$resource_observation_sample_id" >&2 || \
    printf 'NATIVE_TASK_SAMPLE {"schema":1,"sample_id":"%s","identity_status":"unavailable","diagnostic":{"failures":[{"stage":"observer","reason":"unavailable"}]}}\n' "$resource_observation_sample_id" >&2
  return "$status"
}
