#!/bin/bash

# This script runs the coprocessor-for-modelcounting.sh script with a model counter versus
# the model counter without preprocessing, times the executions and checks that the solutions 
# of both runs are equal. Provide the instance to solve as the first and only argument.

SCRIPT_DIR="$(dirname $0)"

TMPDIR="/tmp/solv.tmp"
SHARPSAT_TMPDIR1="$TMPDIR/solv1"
SHARPSAT_TMPDIR2="$TMPDIR/solv2"
mkdir $TMPDIR > /dev/null 2>&1
mkdir $SHARPSAT_TMPDIR1 > /dev/null 2>&1
mkdir $SHARPSAT_TMPDIR2 > /dev/null 2>&1

TMP_CNF="$TMPDIR/out.cnf"
COPROC_LOG="$TMPDIR/coproc.log"
COPROC_SOL="$TMPDIR/coprocsol.log"
COPROC_TIME="$TMPDIR/coproc.time"
EXPECTED_SOL="$TMPDIR/expected.log"
EXPECTED_TIME="$TMPDIR/expected.time"

INPUT=$1
SOLVER="/home/antonr/repos/sharpsat-td/bin/sharpSAT"
SOLVERARGS="-decot 10 -decow 100 -cs 1500"

COPROC="0"
EXPECTED="0"

rm $SHARPSAT_TMPDIR/* > /dev/null 2>&1

coprocessor() {
  echo "Running Coprocessor..."
  CPSTART=`date +%s.%N`
  ./coprocessor-for-modelcounting.sh -o $TMP_CNF $INPUT $SOLVERCALL > $COPROC_LOG 2>&1
  echo "Solving Coprocessor Output..."
  "$SOLVER" "$SOLVERARGS" -tmpdir $SHARPSAT_TMPDIR1 $TMP_CNF > $COPROC_SOL 2>&1
  CPEND=`date +%s.%N`
  CP_TIME=$( echo "$CPEND - $CPSTART" | bc -l )
  echo "$CP_TIME" > $COPROC_TIME
  echo "Coprocessor Done."
}

reference() {
  echo "Running Reference..."
  REFSTART=`date +%s.%N`
  "$SOLVER" "$SOLVERARGS" -tmpdir $SHARPSAT_TMPDIR2 $INPUT > $EXPECTED_SOL 2>&1
  REFEND=`date +%s.%N`
  REF_TIME=$( echo "$REFEND - $REFSTART" | bc -l )
  echo "$REF_TIME" > $EXPECTED_TIME
  echo "Reference Done."
}

coprocessor &
reference &

wait

COPROC=`sed -n '/^c s log10-estimate /p' $COPROC_SOL | grep -Eo '\<[0-9.]+\>'`      # probably not optimal
EXPECTED=`sed -n '/^c s log10-estimate /p' $EXPECTED_SOL | grep -Eo '\<[0-9.]+\>'`      # probably not optimal
CP_TIME=`cat $COPROC_TIME`
REF_TIME=`cat $EXPECTED_TIME`

echo "Expected solution: $EXPECTED, got $COPROC"
echo "Unpreprocessed time: ${REF_TIME}s"
echo "Preprocessed time: ${CP_TIME}s"

rm -r $TMPDIR

if [[ $EXPECTED == $COPROC ]]
then
  echo -e "\033[32;1;4mEQUAL\033[0m"
  exit 0
fi

echo -e "\033[31;1;4mUNEQUAL\033[0m"
exit 1
