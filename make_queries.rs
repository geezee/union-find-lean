#![allow(warnings)]

use std::fs::{File};
use std::io::{self, Read, BufRead, BufReader};
use std::{env};

use std::collections::{HashSet};

fn rand() -> usize {
  let mut f = File::open("/dev/urandom").unwrap();
  let mut bytes = [0u8; std::mem::size_of::<usize>()];
  f.read_exact(&mut bytes).unwrap();
  usize::from_ne_bytes(bytes)
}

fn main() {
  let args: Vec<String> = env::args().collect();
  if args.len() != 3 {
    eprintln!("USAGE: make_queries enwikigraph2018.csv max_query_count");
    return
  }

  let filename = args[1].clone();
  let max_query_count : usize = args[2].parse().unwrap();

  let mut names = HashSet::new();

  let file = File::open(filename).unwrap();
  let reader = BufReader::new(file);
  let mut count = 0;
  let mut lines = reader.lines();
  let _ = lines.next();
  for line_result in lines {
    count += 1;
    if count % (1<<20) == 0 { eprint!("{count}\r"); }
    let line = line_result.unwrap();
    let fields: Vec<&str> = line.split('\t').collect();
    names.insert(fields[1].to_string());
    names.insert(fields[3].to_string());
  }

  let mut names = names.into_iter().collect::<Vec<_>>();
  let N = names.len();
  for i in 0..max_query_count {
    println!("{}\t{}", names[rand() % N], names[rand() % N])
  }
}
