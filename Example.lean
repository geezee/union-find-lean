import UnionFind.UnionFind
import UnionFind.FLike

def UnionFindFun : Type := UnionFind.UnionFind FunCtx Fun String
def UnionFindMem : Type := UnionFind.UnionFind MapCtx MapType String


instance : Default String String where
  default := (·)
  default_is_id := by simp only [eq_mp_eq_cast, cast_eq, imp_self, implies_true]


def fun_ctx : FunCtx String String := ()

macro "map_ctx" : term => `(
  ⟨ inferInstanceAs (BEq String)
  , inferInstanceAs (Hashable String)
  , inferInstanceAs (Default String String)
  , inferInstanceAs (LawfulBEq String)
  , inferInstanceAs (LawfulHashable String)
  ⟩)

def uf_trivial_fun : UnionFindFun := UnionFind.UnionFind.trivial ()
def uf_trivial_mem : UnionFindMem := UnionFind.UnionFind.trivial map_ctx

def mk_uf C α (c: C String String) [FLike C α String String c] (trivial: UnionFind.UnionFind C α String) (filename: String) (max_lines: Nat) : IO (UnionFind.UnionFind C α String) := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read

  let rec parse
    (line_num: Nat)
    (uf: UnionFind.UnionFind C α String)
    : IO (UnionFind.UnionFind C α String)
  := do
    let line ← handle.getLine
    if line_num == 0 then -- skip the header
      parse (line_num + 1) uf
    else if line.length == 0 || line_num > max_lines then
      return uf
    else
      match line.trimRight.splitToList (· == '\t') with
      | _ :: title₁ :: _ :: title₂ :: [] => parse (line_num + 1) (uf.union_mut title₂.trim title₁.trim)
      | _ => parse (line_num + 1) uf
    decreasing_by all_goals sorry

  parse 0 trivial

def query_uf (uf: UnionFind.UnionFind C α String) (filename: String) : IO Nat := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read

  let rec counter
    {C α}
    (count: Nat)
    (uf: UnionFind.UnionFind C α String)
    : IO (Nat × UnionFind.UnionFind C α String)
  := do
    let line ← handle.getLine
    if line.length == 0 then
      return (count, uf)
    else
      match line.trimRight.splitToList (· == '\t') with
      | title₁ :: title₂ :: [] =>
        let ⟨c₁, uf₁, _, _, _, _, _⟩ := uf.find_mut title₁
        let ⟨c₂, uf₂, _, _, _, _, _⟩ := uf₁.find_mut title₂
        if c₁ == c₂
        then
          counter count uf₂
        else
          IO.println s!"{title₁} :: {title₂}"
          counter (count+1) uf₂
      | _ =>
        counter count uf
    decreasing_by all_goals sorry

  do
    let ans ← counter 0 uf
    return ans.1


def main (args: List String) : IO Unit :=
  match args with
  | kind :: filename :: max_lines :: query_file :: [] =>
    match kind with
    | "mem" => do
      let uf ← mk_uf MapCtx MapType map_ctx uf_trivial_mem filename max_lines.toNat!
      let ans ← query_uf uf query_file 
      IO.println s!"{ans}"
    | "fun" => do
      let uf ← mk_uf FunCtx Fun fun_ctx uf_trivial_fun filename max_lines.toNat!
      let ans ← query_uf uf query_file 
      IO.println s!"{ans}"
    | _ => IO.eprintln s!"ERROR: Unknown kind {kind}, expecting mem or fun"
  | _ => do
    IO.eprintln s!"USAGE: example (mem|fun) enwikigraph2018.csv line_num query_file.txt"
