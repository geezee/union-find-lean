# Union-Find

This repo contains the code for a verified efficient implementation of a coinductive union-finds.

`UnionFind/FLike.lean` contains the function-like interface that would let you use functions, hashmaps, or even arrays as the internal implementation for the union-find.
`UnionFind/UnionFind.lean` contains the implementation and proofs and theorems about the union-find.

## Efficiency Case Study: WikiLinkGraph

I implemented  a program twice, once in Lean in `Example.lean` and once in rust `example.rs`.
The program consumes a dataset of Wikipedia article connections, a number of connections N, and a list of pairs of articles.
It prints out all the pairs in the latter list which are not mutually reachable in the dataset where only the first N connections are considered.
At its heart is a union-find whose edges are these N connections.
This union-find then encodes the *reachability* equivalence relation.

If you want to see the performance comparison between the best Lean version and the Rust version look no further than `lean_v_rust_benchmark_data.csv`.
To see the performance comparison between the Lean version with hashmaps (the best) and the Lean version with function closures look in `mem_v_fun_benchmark_data.csv`.

To download the dataset run `make enwikigraph2018.tsv`. **BEWARE** this requires at least 10GB of storage and will take some time.

To create a random sample of pairs of articles from the dataset, to use for the case study, you can run `make queries.tsv`. **BEWARE** This only works on Linux (thanks Rust for not providing a RNG in your stdlib).

Finally to recreate or to generate your own benchmark data (if you have GNU parallel installed) you can run
```
make lean_v_rust_benchmark_data.csv
make mem_v_fun_benchmark_data.csv
```

### Manual Trial Test

If you just want to play with it then do the following:
* Create a TSV file `data.tsv` with four headers and each row being a numeric id, an article title, then a numeric id, then an article title.
* Create a TSV file `queries.tsv` without a header and row row is just two titles.
* Run `make` to generate the binaries.
* Run `./example-rs data.tsv 1000 queries.tsv` to check the reachability of the two article in each row of `queries.tsv` using the first 1000 equalities from `data.tsv`.
* Run `./.lake/build/bin/example mem data.tsv 1000 queries.tsv` to do the same using the Lean.

For example `data.tsv` could be
```
id1	title1	id2	title2
9228	Earth	11890785	Summer solstice
12746	Generalization	12157671	Specialisation (biology)
13458	List of historical period drama films and series	1694208	Arturo Perez-Reverte
1216	Athens	915711	East European Time
10037	Euroscepticism	12132619	Danish Single European Act referendum, 1986
7985	Dill	22209033	Western Romance languages
1842	Augustin-Louis Cauchy	978412	Cauchy (crater)
3415	Bulgaria	1024431	Chandrayaan-1
3338	The Bronx	36234270	Robert F. Kennedy Bridge
2224	April 8	36046	1139
6704	Christendom	13692155	Philosophy
6021	C (programming language)	66924	Memory management
1368	Assembly language	29294	IBM System/360
12388	Genome	862843	Short tandem repeats
6852	Caligula	8563998	Fabius Rusticus
8311	Dinosaur	22265741	Ammonotelic
<AND MANY MORE SIMILAR ROWS FOLLOW>
```

And `queries.tsv` could be
```
Tintin on postage stamps	5β-coprostanol
The Rebel Gladiators	Shorttail Catshark
501c(3)	Kabupaten Sukoharjo
That's Right (album)	1931 Chicago Cardinals football
State Road 10 (Washington)	Old Customs House (Montreal)
```
