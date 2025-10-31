#!/bin/bash

DATA_PATH=$1

export DATA_PATH

run() {
  method=$1
  union_count=$(echo "scale=0; 1000000 * (1.9 ^ $2)" | bc | cut -f1 -d.)

  if [ $method = "lean" ]; then
    program=.lake/build/bin/example mem
  else
    program=./example-rs
  fi

  t=$(bash -c "time -p $program $DATA_PATH $union_count queries.tsv >/dev/null" 2>&1 | awk '/real/ {print $2}')

  echo $method,$union_count,$t
}

export -f run

parallel run ::: rs lean ::: $(seq 0 8)
