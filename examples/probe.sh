set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
lily=${LILY:-lily}
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
n=0
for schema in "$@"; do
  n=$((n + 1))
  mkdir "$dir/$n"
  echo "+ lily compile $schema -o term.ml"
  "$lily" compile "$schema" -o "$dir/$n/term.ml"
  cp "$root/runtime/bind.ml" "$root/examples/probe.ml" "$dir/$n/"
  (cd "$dir/$n" && ocamlopt -o probe bind.ml term.ml probe.ml)
  printf '  schema  %s\n' "$(grep -o 'PairArm of { body: [^}]*}' "$schema")"
  "$dir/$n/probe" | sed '1s/^/  probe   /; 2,$s/^/    /'
done
