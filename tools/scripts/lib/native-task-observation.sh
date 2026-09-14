#!/usr/bin/env bash
# Source after resource-observation-lib.sh with explicit repository and proc roots.
native_observation_repository="$1"
native_observation_proc_root="$2"
eval "$(declare -f resource_observation_process_values | sed '1s/resource_observation_process_values/resource_observation_process_values_unlabelled/')"
resource_observation_process_values() {
  local values status=0 count _cpu tree
  values="$(resource_observation_process_values_unlabelled "$@")" || status=$?
  printf '%s\n' "$values"
  IFS=$'\t' read -r count _cpu tree <<< "$values"
  printf '%s\n' "$tree" | python3 "$native_observation_repository/tools/scripts/lib/native-task-observation.py" \
    --repository "$native_observation_repository" --proc-root "$native_observation_proc_root" >&2 || \
    printf '%s\n' 'NATIVE_TASK_SAMPLE {"schema":1,"identity_status":"unavailable"}' >&2
  return "$status"
}
