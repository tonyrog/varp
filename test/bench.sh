#!/bin/bash
#
# Raw solver performance on a fixed set of instances.
#
#   test/bench.sh [ebin-dir]
#
# Prints, per instance: conflicts, watch list visits, the time spent in
# the search plugin and the user CPU time of the whole run.  Compare
# conflict counts first: two builds that do not agree on them followed
# different search paths, and their times are not comparable.
#
# With an ebin directory argument the run uses that tree instead of the
# working copy, so two builds can be compared side by side:
#
#   mkdir -p /tmp/A/varp && cp -r ebin priv /tmp/A/varp/
#   test/bench.sh /tmp/A/varp/ebin
#
# Extra global options go in VARP_OPTS, space separated:
#
#   VARP_OPTS="--qtype=lifo" test/bench.sh
#
TOP=$(cd "$(dirname "$0")/.." && pwd)
EBIN=${1:-$TOP/ebin}
cd "$TOP"

INSTANCES=(
  "sat bj formulas/dimacs/p9.cnf"
  "sat bj formulas/dimacs/p10.cnf"
  "sat bj formulas/varp/pigeon.varp n=9"
  "sat bj formulas/varp/pigeon.varp n=10"
  "sat bj formulas/dimacs/sp33.cnf"
)

printf "%-44s %10s %13s %9s %9s\n" instance conflicts visits search cpu
for inst in "${INSTANCES[@]}"; do
  args=""; for a in $VARP_OPTS $inst; do args="$args\"$a\","; done; args="${args%,}"
  out=$( { /usr/bin/time -f "user=%U" env -u ERL_LIBS LC_ALL=C timeout 900 \
           erl -noshell -pa "$EBIN" -eval "varp:main([\"--log=info\",$args])" 2>&1; } 2>&1 )
  echo "$out" | awk -v name="$inst" '
    /clause:n/ { split($0,a,/[:,]/); n=a[3]; d=a[9] }
    /#conflict/ { c=$NF; sub("#conflict:","",c) }
    /time=/     { t=$NF }
    /^user=/    { u=$0; sub("user=","",u) }
    END { printf "%-44s %10s %13d %9s %8ss\n", name, c, n+d, t, u }'
done
