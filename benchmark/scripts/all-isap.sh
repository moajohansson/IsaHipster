#!/bin/bash

INPUT=~/Field/thesis/benchmarks/benchmarks/isaplanner/*.smt2
OUTDIR=~/Field/thesis/IsaHipster/benchmark/
EXTENSION=.thy

while [[ $# > 1 ]]
do
key="$1"

case $key in
  -o|--origin)
  INPUT="$2"/*.smt2
  shift
  ;;
  -d|--destination)
  OUTDIR="$2"
  echo $OUTDIR
  shift
  ;;
  --default)
  DEFAULT=YES
  shift
  ;;
  *)
  # unknown option
  ;;
esac
shift
done

for f in $INPUT
do
  f2="${f##*/}"
  f3="${f2%.*}"
  echo "Processing $f file..."
  outfile=${OUTDIR%%/}/$f3$EXTENSION
  echo "Output file: $outfile"
  # take action on each file. $f store current file name
  tip-parser $f --isabelle | sed "1s/A/$f3/" | sed "s/cons/Cons/g" | sed "s/nil/Nil/g" > $outfile

done
