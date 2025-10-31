#![allow(warnings)]

use std::collections::{HashMap};


struct UnionFind {
  parent: HashMap<String, String>
}


impl UnionFind {
  fn new() -> UnionFind {
    UnionFind { parent: HashMap::new() }
  }

  fn find(&mut self, x: &String) -> String {
    match self.parent.get(x) {
      None => x.clone(),
      Some(p) => if x == p {
        x.clone()
      } else {
        let root = self.find(&p.clone());
        self.parent.insert(x.clone(), root.clone());
        root
      }
    }
  }

  fn union(&mut self, x: String, y: String) {
    let xr = self.find(&x);
    let yr = self.find(&y);
    self.parent.insert(xr, yr);
  }
}



fn main() {
  use std::fs::{File};
  use std::io::{self, BufRead, BufReader};
  use std::{env};

  let args: Vec<String> = env::args().collect();
  if args.len() != 4 {
    eprintln!("USAGE: example enwikigraph2018.csv line_num query_file.txt");
    return
  }

  let filename = args[1].clone();
  let line_num : usize = args[2].parse().unwrap();
  let query_file = args[3].clone();

  let mut uf = UnionFind::new();

  let file = File::open(filename).unwrap();
  let reader = BufReader::new(file);
  let mut count = 0;
  for line_result in reader.lines() {
    count += 1;
    if count == 1 { continue; }
    if count > line_num { break; }
    let line = line_result.unwrap();
    let fields: Vec<&str> = line.split('\t').collect();
    uf.union(fields[1].to_string(), fields[3].to_string());
  }

  let file = File::open(query_file).unwrap();
  let reader = BufReader::new(file);
  let mut total_not_connected = 0;
  for line_result in reader.lines() {
    let line = line_result.unwrap();
    let fields: Vec<&str> = line.split('\t').collect();
    if uf.find(&fields[0].to_string()) != uf.find(&fields[1].to_string()) {
      total_not_connected += 1;
      println!("{} :: {}", fields[0], fields[1]);
    }
  }

  println!("{total_not_connected}");
}
