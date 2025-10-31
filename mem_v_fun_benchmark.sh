#!/bin/bash

DATA_PATH=$1

export DATA_PATH

run() {
  method=$1
  union_count=$(echo "scale=0; 100 * (1.9 ^ $2)" | bc | cut -f1 -d.)

  t=$(bash -c "time -p .lake/build/bin/example $method $DATA_PATH $union_count small_queries.tsv >/dev/null" 2>&1 | awk '/real/ {print $2}')

  echo $method,$union_count,$t
}

export -f run

head -n 1000 queries.tsv > small_queries.tsv
parallel run ::: mem fun ::: $(seq 0 8)
rm small_queries.tsv
