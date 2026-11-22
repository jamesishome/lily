set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
cp "$root/proof/Bind.v" "$root/proof/Extract.v" "$dir"
cd "$dir"
rocq compile -R . Lily Bind.v
rocq compile -w -extraction-default-directory -R . Lily Extract.v
rocqchk -silent -o -R . Lily Lily.Bind > context.txt 2>&1
for fact in 'Axioms: <none>' 'Constants/Inductives relying on type-in-type: <none>' \
  'Constants/Inductives relying on unsafe (co)fixpoints: <none>' \
  'Inductives whose positivity is assumed: <none>'; do
  grep -Fxq "* $fact" context.txt || { echo "proof: missing '$fact'" >&2; exit 1; }
done
if [ "${1:-}" = update ]; then
  cp model.ml model.mli "$root/test/"
fi
cmp model.ml "$root/test/model.ml"
cmp model.mli "$root/test/model.mli"
echo "proof: subst_identity checked without axioms, test/model.ml matches extraction"
