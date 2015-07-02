#!/bin/bash

EXTENSION=.thy

dir="$1"
files=$dir/*.thy


for f in $files
do
  echo "Processing $f file..."
  # take action on each file. $f store current file name
  sed "s/[\.,\/]*.IsaHipster/\$HIPSTER_HOME\/IsaHipster/" $f > "temp.thy"
  cat temp.thy > $f

done

