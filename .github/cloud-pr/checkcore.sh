#!/bin/bash
# checkcore.sh <proof.lean> <step id, e.g. L-meta-3420> <checker tree> <log dir> [--quick]
# The checks of one proof file against one checker tree (a checkout of open-goat/pequalnp-proofs main), using CI's
# OWN scripts from that tree. Shared by testrun.sh (local, holds the tree lock and moves the tree to upstream main
# first) and .github/workflows/ready.yml (GitHub Actions). It does NOT lock, fetch or check out the tree.
#   1. guard 'gap'     : step still posted, statement/imports/kind exactly as CI reads them
#   2. guard 'imports' : format/token rules, imports, file name, size
#   2b. CONTRIBUTING rules the guard does not enforce
#   3. guard 'closure' : the listed imports resolve in the base tree
#   4. (unless --quick) the official checker tools/check-lean.mjs, pinned to 2 cores like CI
# Exit 0 only if every step passes (and the checker prints ACCEPTED). Result line in <log dir>/result.
# Environment:
#   NODE          node binary (required)
#   TC            bin dir of the pinned Lean toolchain (required unless --quick)
#   CHECK_WRAP    command prefix for the checker (default: "taskset -c 0,1" if taskset exists)
#   CHECK_TIMEOUT checker time limit in s (default 2700)
#   GAPS_FILE     a local gaps.json to use instead of downloading the live one (testing only)
#   REL_OVERRIDE  path of the file in the tree (default lean/PEqualNP/Outside/<module>.lean; e.g. a reduction R_meta_N_k.lean)
#   GUARD_KIND    check (default), refute or reduce
F=$(readlink -f "$1"); ID=$2; T=$3; LOG=$4; QUICK=$5
: "${NODE:?NODE must name the node binary}"
[ -n "${CHECK_WRAP+x}" ] || { command -v taskset >/dev/null && CHECK_WRAP="taskset -c 0,1" || CHECK_WRAP=; }
mkdir -p $LOG/in
fail(){ echo "FAIL: $*" | tee -a $LOG/result; exit 1; }

G=$T/.github/scripts/outside-guard.mjs
MOD=$(echo "$ID" | tr - _)                      # L-meta-3420 -> L_meta_3420
REL=${REL_OVERRIDE:-lean/PEqualNP/Outside/$MOD.lean}

if [ -n "$PRESTAGE_IMPORTS" ]; then
  # step not listed yet (pnp-toolkit checkcore.sh STAGED lane): the gap guard cannot run; the imports/format,
  # CONTRIBUTING and closure guards run against the file's own imports (a JSON list) instead
  echo "$PRESTAGE_IMPORTS" > $LOG/in/imports.json; echo "${GUARD_KIND:-check}" > $LOG/in/gap.kind
  echo "1 gap skipped (prestage, kind $(cat $LOG/in/gap.kind))"
else
if [ -n "$GAPS_FILE" ]; then cp "$GAPS_FILE" $LOG/in/gaps.json || fail "copy $GAPS_FILE"
else curl -sf https://data.pequalnp.com/data/desk/gaps.json -o $LOG/in/gaps.json || fail "download gaps.json"; fi
$NODE $G gap $LOG/in/gaps.json "$ID" "$REL" $LOG/in ${GUARD_KIND:-check} > $LOG/gap.log 2>&1 || { cat $LOG/gap.log; fail "guard gap"; }
grep -q REFUSED $LOG/gap.log && { cat $LOG/gap.log; fail "guard gap"; }
echo "1 gap ok (kind $(cat $LOG/in/gap.kind))"
fi

$NODE $G imports "$F" $LOG/in/imports.json "$REL" "$(cat $LOG/in/gap.kind)" > $LOG/imports.log 2>&1 || { cat $LOG/imports.log; fail "guard imports/format"; }
grep -q REFUSED $LOG/imports.log && { cat $LOG/imports.log; fail "guard imports/format"; }
echo "2 format/imports ok: $(cat $LOG/imports.log)"


# 2b. CONTRIBUTING rules the guard does not enforce (a break means refusal or a wait for a human reader)
python3 -I - "$F" > $LOG/rules.log 2>&1 <<'PY' || { cat $LOG/rules.log; fail "CONTRIBUTING rules"; }
import re,sys
L=open(sys.argv[1],encoding='utf-8').read().split('\n'); bad=[]; inb=False; depth=[]
for n,l in enumerate(L):
    m=re.match(r'^(\s*)(namespace|section|end)\b\s*(\S*)',l)
    if m and not inb:
        if m.group(1): bad.append((n+1,'namespace/section/end not at column 0'))
        if m.group(2)=='end' and not m.group(3): bad.append((n+1,'end without a name'))
    if not inb and '/-' in l:
        k=l.index('/-')
        if l[:k].strip(): bad.append((n+1,'block comment opens mid-line'))
        inb='-/' not in l[k+2:]
    elif inb:
        if l.strip() and not l.startswith((' ','\t')) and not l.strip().startswith('-/'): bad.append((n+1,'unindented block-comment text'))
        if '-/' in l: inb=False
    if re.match(r'^\s*(instance|@\[instance|@\[simp)',l): bad.append((n+1,'instance or simp helper'))
for b in bad[:20]: print('RULE',*b)
own=[n+1 for n,l in enumerate(L) if re.match(r'^\s*(inductive|structure|class)\b',l)]
if own: print('WARN own types at lines',own[:10],'(rule 5: may wait for a human reader)')
sys.exit(1 if bad else 0)
PY
echo "2b CONTRIBUTING rules ok $(grep WARN $LOG/rules.log)"

cp "$F" $T/$REL
$NODE $G closure $T $LOG/in/imports.json "$REL" $LOG/in "$(cat $LOG/in/gap.kind)" > $LOG/closure.log 2>&1 || { cat $LOG/closure.log; fail "guard closure"; }
grep -q REFUSED $LOG/closure.log && { cat $LOG/closure.log; fail "guard closure"; }
echo "3 closure ok"

[ "$QUICK" = "--quick" ] && { echo "PASS (quick: guards only)" | tee $LOG/result; exit 0; }
: "${TC:?TC must name the Lean toolchain bin dir}"

# clear a stale lock (file or directory): the caller owns this tree (testrun.sh holds its flock; a CI runner is
# alone), so no checker uses this tree and any check.lock here is stale
rm -rf $T/lean/.lake/check.lock
( cd $T && /usr/bin/time -v $CHECK_WRAP env HOME=$HOME LANG=C.UTF-8 PATH=$TC:$(dirname $NODE):/usr/bin:/bin \
    timeout ${CHECK_TIMEOUT:-2700} $NODE tools/check-lean.mjs $REL $LOG/in/statement.txt "$(cat $LOG/in/gap.kind | tr -d '\n')" \
    > $LOG/checker.out 2> $LOG/checker.err )
tail -1 $LOG/checker.out | grep -q '^ACCEPTED' || { tail -3 $LOG/checker.out; grep FAULT $LOG/checker.err; fail "checker"; }
echo "4 checker: $(tail -1 $LOG/checker.out | cut -c1-120)"
echo "   $(grep 'Elapsed' $LOG/checker.err | sed 's/^\s*//')"
echo "PASS" | tee $LOG/result
