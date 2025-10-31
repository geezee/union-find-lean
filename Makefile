DATA=enwikigraph2018.tsv
MAX_QUERY_COUNT=1000000

all: .lake/build/bin/example example-rs

.lake/build/bin/example: Example.lean UnionFind/UnionFind.lean UnionFind/FLike.lean
	lake build example -KleanArgs="-O3 -DNDEBUG -s"

example-rs: example.rs
	rustc -O example.rs
	mv example example-rs

queries.tsv: make_queries
	./make_queries $(DATA) $(MAX_QUERY_COUNT) > queries.tsv

make_queries: make_queries.rs
	rustc -O make_queries.rs

lean_v_rust_benchmark_data.csv: .lake/build/bin/example example-rs lean_v_rust_benchmark.sh queries.tsv
	./lean_v_rust_benchmark.sh $(DATA) | tee lean_v_rust_benchmark_data.csv

mem_v_fun_benchmark_data.csv: .lake/build/bin/example mem_v_fun_benchmark.sh queries.tsv
	./mem_v_fun_benchmark.sh $(DATA) | tee mem_v_fun_benchmark_data.csv

enwikigraph2018.tsv:
	wget https://zenodo.org/records/2539424/files/enwiki.wikilink_graph.2018-03-01.csv.gz?download=1
	mv enwiki.wikilink_graph.2018-03-01.csv* enwikigraph2018.tsv.gz.gz
	gunzip enwikigraph2018.tsv.gz.gz
	gunzip enwikigraph2018.tsv.gz

.PHONY: all
