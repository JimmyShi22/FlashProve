-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Bytes.lean: writers for a parsed key file or proof file (a "carrier",
OnBytes/Maker/Carrier.lean) and for the small file of seeds beside it; and: the carrier's readers
give back what was written.

Why. The compiled verifier's proof input is laid of a `File`, which `read` decodes from bytes. A
prover in Lean that is to hand over bytes needs the way back: from a `File` to bytes that `read`
takes and decodes to that `File`.

How. The library has the frame for the format's plain readers: `Fmt.Undoes r sp ok`
(Fmt/Rules1Laws.lean): the reader r undoes the spelling sp on the values with ok, at any place in a
longer string; with laws for words, elements, digests, texts, pairs and lists. The writers here are
chains of the format's own spellings (Fmt/Rules1.lean). The carrier's readers say where they refuse
(`RdE`), and have a loop of their own for lists; `UndoesE` is the same frame for them.

Main names.
  `okF`, `okE`, `okItem`, `Round.WF`, `Row.WF`, `TreeRows.WF`, `File.WF magic` (namespace
    `OnBytes.Maker.Carrier`): what the readers take, one field a clause: digests of 32 bytes; words
    of elements and of columns below the prime; numbers and lengths below 2^64; salts of at most 64
    bytes; a chain's number at most 2; trees' numbers and leaves rise; a key file's copy is 0
  `wrItem`, `wrRound`, `wrRow`, `wrTree`, `wrFile magic`, `wrSeed`, `wrSeeds`: the writers, with
    code (namespace `OnBytes.Prover.Print`, as all that follows)
  `fallFrom_eq_none`: the reader's test "the numbers rise" says: each is below all that follow
  `At`, `UndoesE`: the frame; `undoesE_plain`, `undoesE_fld`, `undoesE_nat`, `undoesE_list`: its
    laws; `undoesE_item` ... `undoesE_file`, `undoesE_seed`: struct by struct
  `read_wrFile`: at a magic of 8 bytes, k.WF magic → read magic (wrFile magic k) = .ok k
  `readSeeds_wrSeeds`: the like for the seeds' file
  `size_magicKey`: both magics have 8 bytes

Limits. One direction: nothing says that what `read` takes was written by `wrFile`. Bytes alone: no
protocol, no hash, nothing on what a field means. That a prover's `File` meets `File.WF` is not
shown here. That these bytes are those of the outside parser (tools/parser/parse_files.py) is not
shown: the writers follow the reader's text. The parsed leaf file has no writer here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Carrier
import Fmt.Rules1Laws
import Fmt.ParsedReadFileLaws

set_option autoImplicit false

namespace OnBytes.Maker.Carrier
open _root_.Fmt (ItemValue Ext Fld)

/-! ## What a reader takes: the conditions, struct by struct -/

/-- a word below the prime of the format's second field -/
def okF (x : UInt64) : Prop := x.toNat < Fld.two.p

/-- three such words -/
def okE (e : Ext) : Prop :=
  e.1.toNat < Fld.two.p ∧ e.2.1.toNat < Fld.two.p ∧ e.2.2.toNat < Fld.two.p

/-- an item: a root has 32 bytes; the words of an element are below the prime -/
def okItem : ItemValue → Prop
  | .root d => d.size = 32
  | .f x => okF x
  | .word _ => True
  | .e x => okE x
  | .answer x => okE x

structure Round.WF (r : Round) : Prop where
  count : r.items.length < 2 ^ 64
  items : ∀ x ∈ r.items, okItem x
  nonce : r.nonce < 2 ^ 64

structure Row.WF (r : Row) : Prop where
  leaf : r.leaf < 2 ^ 64
  width : r.column.length < 2 ^ 64
  column : ∀ x ∈ r.column, okF x
  salt : r.salt.size ≤ 64
  depth : r.path.length < 2 ^ 64
  path : ∀ d ∈ r.path, d.size = 32

structure TreeRows.WF (t : TreeRows) : Prop where
  tree : t.tree < 2 ^ 64
  chain : t.chain ≤ 2
  count : t.rows.length < 2 ^ 64
  rows : ∀ r ∈ t.rows, r.WF
  rise : fallFrom 0 (t.rows.map fun r => r.leaf) = none

/-- What `read magic` takes: one field a clause. -/
structure File.WF (magic : String) (k : File) : Prop where
  root : k.root.size = 32
  answersCount : k.answers.length < 2 ^ 64
  answers : ∀ e ∈ k.answers, okE e
  run1 : k.run1.size = 32
  copy : k.copy < 2 ^ 64
  keyCopy : magic = magicKey → k.copy = 0
  rounds1Count : k.rounds1.length < 2 ^ 64
  rounds1 : ∀ r ∈ k.rounds1, r.WF
  run2 : k.run2.size = 32
  rounds2Count : k.rounds2.length < 2 ^ 64
  rounds2 : ∀ r ∈ k.rounds2, r.WF
  run3 : k.run3.size = 32
  rounds3Count : k.rounds3.length < 2 ^ 64
  rounds3 : ∀ r ∈ k.rounds3, r.WF
  treesCount : k.trees.length < 2 ^ 64
  trees : ∀ t ∈ k.trees, t.WF
  treesRise : fallFrom 0 (k.trees.map fun t => t.tree) = none
  storedCount : k.stored.length < 2 ^ 64
  stored : ∀ r ∈ k.stored, r.WF
  storedRise : fallFrom 0 (k.stored.map fun r => r.leaf) = none
  bindRoot : k.bindRoot.size = 32
  place : k.place < 2 ^ 64
  places : k.places < 2 ^ 64
  slotSalt : k.slotSalt.size ≤ 64
  slotDepth : k.slotPath.length < 2 ^ 64
  slotPath : ∀ d ∈ k.slotPath, d.size = 32

end OnBytes.Maker.Carrier

namespace OnBytes.Prover.Print
open OnBytes.Maker.Carrier
open _root_.Fmt (Rd Undoes ItemValue Ext Fld u64 u64n elt ext text list cat)

/-! ## The writers -/

/-- Item: the kind, then the value. -/
def wrItem : ItemValue → ByteArray
  | .root d => u64n 0 ++ d
  | .f x => u64n 1 ++ elt x
  | .word w => u64n 2 ++ u64 w
  | .e x => u64n 3 ++ ext x
  | .answer x => u64n 4 ++ ext x

def wrRound (r : Round) : ByteArray := list wrItem r.items ++ u64n r.nonce

def wrRow (r : Row) : ByteArray :=
  u64n r.leaf ++ (list elt r.column ++ (text r.salt ++ list id r.path))

def wrTree (t : TreeRows) : ByteArray := u64n t.tree ++ (u64n t.chain ++ list wrRow t.rows)

/-- A carrier's bytes: the magic, then the sixteen fields in their order. -/
def wrFile (magic : String) (k : File) : ByteArray :=
  magic.toUTF8 ++ (k.root ++ (list ext k.answers ++ (k.run1 ++ (u64n k.copy ++
    (list wrRound k.rounds1 ++ (k.run2 ++ (list wrRound k.rounds2 ++ (k.run3 ++
    (list wrRound k.rounds3 ++ (list wrTree k.trees ++ (list wrRow k.stored ++ (k.bindRoot ++
    (u64n k.place ++ (u64n k.places ++ (text k.slotSalt ++ list id k.slotPath)))))))))))))))

def wrSeed (s : List Ext × Ext) : ByteArray := list ext s.1 ++ ext s.2

/-- The bytes of the small file beside a carrier. -/
def wrSeeds (l : List (List Ext × Ext)) : ByteArray := list wrSeed l

/-- a seed that the reader takes -/
def okSeed (s : List Ext × Ext) : Prop := s.1.length < 2 ^ 64 ∧ (∀ e ∈ s.1, okE e) ∧ okE s.2

/-! ## The frame -/

/-- the string s stands in b from byte i on -/
def At (b : ByteArray) (i : Nat) (s : ByteArray) : Prop :=
  ∃ pre post : ByteArray, b = pre ++ s ++ post ∧ i = pre.size

/-- The reader r, which says where it refuses, undoes the spelling sp on the values with ok, at any
place in a longer string: `Fmt.Undoes` (Fmt/Rules1Laws.lean) for the carrier's readers. -/
def UndoesE {α : Type} (r : RdE α) (sp : α → ByteArray) (ok : α → Prop) : Prop :=
  ∀ x, ok x → ∀ b i, At b i (sp x) → r b i = .ok (x, i + (sp x).size)

/-! ## Rising numbers -/

/-- The reader's test "the numbers rise" says: each is below all that follow. -/
theorem fallFrom_eq_none :
  ∀ (l : List Nat) (k : Nat), fallFrom k l = none ↔ l.Pairwise (· < ·)
  | [], _ => ⟨fun _ => List.Pairwise.nil, fun _ => rfl⟩
  | [_], _ => ⟨fun _ => List.pairwise_singleton _ _, fun _ => rfl⟩
  | a :: b :: l, k => by
    have ih := fallFrom_eq_none (b :: l) (k + 1)
    show (if a < b then fallFrom (k + 1) (b :: l) else some (k + 1, b, a)) = none ↔ _
    by_cases h : a < b
    · rw [if_pos h, ih, List.pairwise_cons (a := a)]
      refine ⟨fun hp => ⟨fun x hx => ?_, hp⟩, fun hp => hp.2⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact Nat.lt_trans h ((List.pairwise_cons.1 hp).1 x hx)
    · rw [if_neg h]
      refine ⟨fun e => (by cases e), fun hp => ?_⟩
      exact absurd ((List.pairwise_cons.1 hp).1 b List.mem_cons_self) h

/-! ## A string in a longer one -/

theorem At.head {b : ByteArray} {i : Nat} {s t : ByteArray} (h : At b i (s ++ t)) : At b i s := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre, t ++ post, by simp only [ByteArray.append_assoc], rfl⟩

theorem At.tail {b : ByteArray} {i : Nat} {s t : ByteArray} (h : At b i (s ++ t)) :
    At b (i + s.size) t := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  exact ⟨pre ++ s, post, by simp only [ByteArray.append_assoc], by rw [ByteArray.size_append]⟩

theorem At.le {b : ByteArray} {i : Nat} {s : ByteArray} (h : At b i s) : i + s.size ≤ b.size := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  rw [ByteArray.size_append, ByteArray.size_append]
  omega

theorem at_whole (s : ByteArray) : At s 0 s :=
  ⟨ByteArray.empty, ByteArray.empty, by rw [ByteArray.empty_append, ByteArray.append_empty], rfl⟩

/-- `Fmt.Undoes`, said with `At`. -/
theorem Undoes.at {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop} (h : Undoes r sp ok)
    {x : α} (hx : ok x) {b : ByteArray} {i : Nat} (hb : At b i (sp x)) :
    r b i = some (x, i + (sp x).size) := by
  obtain ⟨pre, post, rfl, rfl⟩ := hb
  exact h x hx pre post

theorem size_u64n (n : Nat) : (u64n n).size = 8 := rfl

/-! ## The grammar's readers -/

theorem undoesE_plain :
  ∀ (α : Type) (r : Rd α) (sp : α → ByteArray) (ok : α → Prop) (n : Nat),
  Undoes r sp ok → UndoesE (plain n r) sp ok := by
  intro α r sp ok n h x hx b i hb
  simp only [plain, Undoes.at h hx hb]

theorem undoesE_fld :
  ∀ (α : Type) (r : RdE α) (sp : α → ByteArray) (ok : α → Prop) (name : String),
  UndoesE r sp ok → UndoesE (fld name r) sp ok := by
  intro α r sp ok name h x hx b i hb
  simp only [fld, h x hx b i hb, Except.mapError]

theorem undoesE_nat : UndoesE rdNat u64n fun n => n < 2 ^ 64 := by
  intro n hn b i hb
  have h : plain 8 Fmt.rdWord b i = .ok (UInt64.ofNat n, i + (u64n n).size) :=
    undoesE_plain _ _ _ _ 8 Fmt.undoes_word (UInt64.ofNat n) trivial b i hb
  have hn' : (UInt64.ofNat n).toNat = n := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt hn
  simp only [rdNat, h, Except.map, hn']

theorem undoesE_F : UndoesE rdF elt okF := undoesE_plain _ _ _ _ 8 (Fmt.undoes_elt .two)

theorem undoesE_E : UndoesE rdE ext okE := undoesE_plain _ _ _ _ 24 (Fmt.undoes_ext .two)

theorem undoesE_dig : UndoesE rdDig id fun d => d.size = 32 :=
  undoesE_plain _ _ _ _ 32 Fmt.undoes_digest

/-- the same, with the spelling written out: for a digest that is a field -/
theorem undoesE_dig' : UndoesE rdDig (fun d => d) fun d => d.size = 32 := undoesE_dig

theorem undoesE_bytes (n : Nat) :
    UndoesE (plain n (Fmt.rdBytes n)) (fun s => s) fun s => s.size = n :=
  undoesE_plain _ _ _ _ n (Fmt.undoes_bytes n)

/-- The loop: the items of l, one after the other, behind those that were read. -/
theorem rdLoop_cat {α : Type} {r : RdE α} {sp : α → ByteArray} {ok : α → Prop}
    (h : UndoesE r sp ok) : ∀ (l : List α), (∀ x ∈ l, ok x) → ∀ (k : Nat) (acc : Array α)
      (b : ByteArray) (i : Nat), At b i (cat (l.map sp)) →
      rdLoop r l.length k acc b i = .ok (acc.toList ++ l, i + (cat (l.map sp)).size)
  | [], _, k, acc, b, i, _ => by
    simp [rdLoop, Fmt.cat_nil]
  | x :: l, hl, k, acc, b, i, hb => by
    rw [List.map_cons, Fmt.cat_cons] at hb ⊢
    have h1 := h x (hl x List.mem_cons_self) b i hb.head
    have h2 := rdLoop_cat h l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (k + 1) (acc.push x)
      b _ hb.tail
    simp only [List.length_cons, rdLoop, h1, h2, Array.toList_push, List.append_assoc,
      List.cons_append, List.nil_append, ByteArray.size_append, Nat.add_assoc]

theorem undoesE_list :
  ∀ (α : Type) (r : RdE α) (sp : α → ByteArray) (ok : α → Prop),
  UndoesE r sp ok → (∀ x, ok x → 1 ≤ (sp x).size) →
  UndoesE (OnBytes.Maker.Carrier.rdList r) (list sp)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, ok x := by
  intro α r sp ok h hp l hl b i hb
  have hb' : At b i (u64n l.length ++ cat (l.map sp)) := hb
  have h1 := undoesE_fld _ _ _ _ "count" undoesE_nat l.length hl.1 b i hb'.head
  have h2 := rdLoop_cat h l hl.2 0 #[] b _ hb'.tail
  have hc := Fmt.length_le_cat (sp := sp) l fun x hx => hp x (hl.2 x hx)
  have hle := hb'.tail.le
  have hn : ¬ l.length > b.size - (i + (u64n l.length).size) := by omega
  have hs : (list sp l).size = (u64n l.length).size + (cat (l.map sp)).size :=
    ByteArray.size_append
  simp only [OnBytes.Maker.Carrier.rdList, h1, if_neg hn, h2, hs, Nat.add_assoc,
    List.nil_append]

/-! ## The small structs -/

theorem one_le_wrItem (x : ItemValue) : 1 ≤ (wrItem x).size := by
  cases x <;> simp only [wrItem, ByteArray.size_append, size_u64n] <;> omega

theorem undoesE_item : UndoesE rdItem wrItem okItem := by
  intro x hx b i hb
  cases x with
  | root d =>
    have hb' : At b i (u64n 0 ++ d) := hb
    have h1 := undoesE_fld _ _ _ _ "kind" undoesE_nat 0 (by omega) b i hb'.head
    have h2 := undoesE_fld _ _ _ _ "root" undoesE_dig' d hx b _ hb'.tail
    simp only [rdItem, bind, Except.bind, h1, h2, Except.map, wrItem, ByteArray.size_append,
      Nat.add_assoc]
  | f y =>
    have hb' : At b i (u64n 1 ++ elt y) := hb
    have h1 := undoesE_fld _ _ _ _ "kind" undoesE_nat 1 (by omega) b i hb'.head
    have h2 := undoesE_fld _ _ _ _ "f" undoesE_F y hx b _ hb'.tail
    simp only [rdItem, bind, Except.bind, h1, h2, Except.map, wrItem, ByteArray.size_append,
      Nat.add_assoc]
  | word w =>
    have hb' : At b i (u64n 2 ++ u64 w) := hb
    have h1 := undoesE_fld _ _ _ _ "kind" undoesE_nat 2 (by omega) b i hb'.head
    have h2 := undoesE_fld _ _ _ _ "word" (undoesE_plain _ _ _ _ 8 Fmt.undoes_word) w trivial b _
      hb'.tail
    simp only [rdItem, bind, Except.bind, h1, h2, Except.map, wrItem, ByteArray.size_append,
      Nat.add_assoc]
  | e y =>
    have hb' : At b i (u64n 3 ++ ext y) := hb
    have h1 := undoesE_fld _ _ _ _ "kind" undoesE_nat 3 (by omega) b i hb'.head
    have h2 := undoesE_fld _ _ _ _ "e" undoesE_E y hx b _ hb'.tail
    simp only [rdItem, bind, Except.bind, h1, h2, Except.map, wrItem, ByteArray.size_append,
      Nat.add_assoc]
  | answer y =>
    have hb' : At b i (u64n 4 ++ ext y) := hb
    have h1 := undoesE_fld _ _ _ _ "kind" undoesE_nat 4 (by omega) b i hb'.head
    have h2 := undoesE_fld _ _ _ _ "answer" undoesE_E y hx b _ hb'.tail
    simp only [rdItem, bind, Except.bind, h1, h2, Except.map, wrItem, ByteArray.size_append,
      Nat.add_assoc]

theorem undoesE_items : UndoesE (OnBytes.Maker.Carrier.rdList rdItem) (list wrItem)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, okItem x :=
  undoesE_list _ _ _ _ undoesE_item fun x _ => one_le_wrItem x

theorem undoesE_round : UndoesE rdRound wrRound Round.WF := by
  intro x hx b i hb
  have hb' : At b i (list wrItem x.items ++ u64n x.nonce) := hb
  have h1 := undoesE_fld _ _ _ _ "items" undoesE_items x.items ⟨hx.count, hx.items⟩ b i hb'.head
  have h2 := undoesE_fld _ _ _ _ "nonce" undoesE_nat x.nonce hx.nonce b _ hb'.tail
  simp only [rdRound, bind, Except.bind, pure, Except.pure, h1, h2, wrRound,
    ByteArray.size_append, Nat.add_assoc]

theorem undoesE_salt : UndoesE rdSalt text fun s => s.size ≤ 64 := by
  intro s hs b i hb
  have hb' : At b i (u64n s.size ++ s) := hb
  have h1 := undoesE_fld _ _ _ _ "length" undoesE_nat s.size (by omega) b i hb'.head
  have h2 := undoesE_bytes s.size s rfl b _ hb'.tail
  have hn : ¬ s.size > 64 := by omega
  simp only [rdSalt, bind, Except.bind, pure, Except.pure, h1, if_neg hn, h2, text,
    ByteArray.size_append, Nat.add_assoc]

theorem undoesE_column : UndoesE (OnBytes.Maker.Carrier.rdList rdF) (list elt)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, okF x :=
  undoesE_list _ _ _ _ undoesE_F fun _ _ => by
    show 1 ≤ 8
    omega

theorem undoesE_path : UndoesE (OnBytes.Maker.Carrier.rdList rdDig) (list id)
    fun l => l.length < 2 ^ 64 ∧ ∀ d ∈ l, d.size = 32 :=
  undoesE_list _ _ _ _ undoesE_dig fun d hd => by
    show 1 ≤ d.size
    omega

theorem undoesE_row : UndoesE rdRow wrRow Row.WF := by
  intro x hx b i hb
  have t0 : At b i (u64n x.leaf ++ (list elt x.column ++ (text x.salt ++ list id x.path))) := hb
  have t1 := t0.tail
  have t2 := t1.tail
  have h1 := undoesE_fld _ _ _ _ "leaf" undoesE_nat x.leaf hx.leaf b i t0.head
  have h2 := undoesE_fld _ _ _ _ "column" undoesE_column x.column ⟨hx.width, hx.column⟩ b _ t1.head
  have h3 := undoesE_fld _ _ _ _ "salt" undoesE_salt x.salt hx.salt b _ t2.head
  have h4 := undoesE_fld _ _ _ _ "path" undoesE_path x.path ⟨hx.depth, hx.path⟩ b _ t2.tail
  simp only [rdRow, bind, Except.bind, pure, Except.pure, h1, h2, h3, h4]
  simp only [wrRow, ByteArray.size_append, Nat.add_assoc]

theorem one_le_wrRow (x : Row) : 1 ≤ (wrRow x).size := by
  simp only [wrRow, ByteArray.size_append, size_u64n]
  omega

theorem undoesE_rows : UndoesE (OnBytes.Maker.Carrier.rdList rdRow) (list wrRow)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, x.WF :=
  undoesE_list _ _ _ _ undoesE_row fun x _ => one_le_wrRow x

theorem undoesE_tree : UndoesE rdTree wrTree TreeRows.WF := by
  intro x hx b i hb
  have t0 : At b i (u64n x.tree ++ (u64n x.chain ++ list wrRow x.rows)) := hb
  have t1 := t0.tail
  have h1 := undoesE_fld _ _ _ _ "tree" undoesE_nat x.tree hx.tree b i t0.head
  have h2 := undoesE_fld _ _ _ _ "chain" undoesE_nat x.chain
    (Nat.lt_of_le_of_lt hx.chain (by omega)) b _ t1.head
  have h3 := undoesE_fld _ _ _ _ "rows" undoesE_rows x.rows ⟨hx.count, hx.rows⟩ b _ t1.tail
  have hn : ¬ x.chain > 2 := Nat.not_lt.2 hx.chain
  simp only [rdTree, bind, Except.bind, pure, Except.pure, h1, h2, h3, if_neg hn, hx.rise]
  simp only [wrTree, ByteArray.size_append, Nat.add_assoc]

/-! ## The carrier -/

theorem one_le_wrRound (x : Round) : 1 ≤ (wrRound x).size := by
  simp only [wrRound, ByteArray.size_append, size_u64n]
  omega

theorem one_le_wrTree (x : TreeRows) : 1 ≤ (wrTree x).size := by
  simp only [wrTree, ByteArray.size_append, size_u64n]
  omega

theorem one_le_ext (x : Ext) : 1 ≤ (ext x).size := by
  show 1 ≤ (u64 x.1 ++ u64 x.2.1 ++ u64 x.2.2).size
  simp only [ByteArray.size_append, Fmt.size_u64]
  omega

theorem undoesE_rounds : UndoesE (OnBytes.Maker.Carrier.rdList rdRound) (list wrRound)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, x.WF :=
  undoesE_list _ _ _ _ undoesE_round fun x _ => one_le_wrRound x

theorem undoesE_trees : UndoesE (OnBytes.Maker.Carrier.rdList rdTree) (list wrTree)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, x.WF :=
  undoesE_list _ _ _ _ undoesE_tree fun x _ => one_le_wrTree x

theorem undoesE_exts : UndoesE (OnBytes.Maker.Carrier.rdList rdE) (list ext)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, okE x :=
  undoesE_list _ _ _ _ undoesE_E fun x _ => one_le_ext x

theorem undoesE_file :
  ∀ magic : String, magic.toUTF8.size = 8 →
  UndoesE (rdFile magic) (wrFile magic) (File.WF magic) := by
  intro magic hm k hk b i hb
  have t0 : At b i (magic.toUTF8 ++ (k.root ++ (list ext k.answers ++ (k.run1 ++ (u64n k.copy ++
    (list wrRound k.rounds1 ++ (k.run2 ++ (list wrRound k.rounds2 ++ (k.run3 ++
    (list wrRound k.rounds3 ++ (list wrTree k.trees ++ (list wrRow k.stored ++ (k.bindRoot ++
    (u64n k.place ++ (u64n k.places ++ (text k.slotSalt ++ list id k.slotPath))))))))))))))))
    := hb
  have t1 := t0.tail
  have t2 := t1.tail
  have t3 := t2.tail
  have t4 := t3.tail
  have t5 := t4.tail
  have t6 := t5.tail
  have t7 := t6.tail
  have t8 := t7.tail
  have t9 := t8.tail
  have t10 := t9.tail
  have t11 := t10.tail
  have t12 := t11.tail
  have t13 := t12.tail
  have t14 := t13.tail
  have t15 := t14.tail
  have h0 := undoesE_fld _ _ _ _ "magic" (undoesE_bytes 8) magic.toUTF8 hm b i t0.head
  have h1 := undoesE_fld _ _ _ _ "root" undoesE_dig' k.root hk.root b _ t1.head
  have h2 := undoesE_fld _ _ _ _ "answers" undoesE_exts k.answers ⟨hk.answersCount, hk.answers⟩
    b _ t2.head
  have h3 := undoesE_fld _ _ _ _ "run1" undoesE_dig' k.run1 hk.run1 b _ t3.head
  have h4 := undoesE_fld _ _ _ _ "copy" undoesE_nat k.copy hk.copy b _ t4.head
  have h5 := undoesE_fld _ _ _ _ "rounds1" undoesE_rounds k.rounds1 ⟨hk.rounds1Count, hk.rounds1⟩
    b _ t5.head
  have h6 := undoesE_fld _ _ _ _ "run2" undoesE_dig' k.run2 hk.run2 b _ t6.head
  have h7 := undoesE_fld _ _ _ _ "rounds2" undoesE_rounds k.rounds2 ⟨hk.rounds2Count, hk.rounds2⟩
    b _ t7.head
  have h8 := undoesE_fld _ _ _ _ "run3" undoesE_dig' k.run3 hk.run3 b _ t8.head
  have h9 := undoesE_fld _ _ _ _ "rounds3" undoesE_rounds k.rounds3 ⟨hk.rounds3Count, hk.rounds3⟩
    b _ t9.head
  have h10 := undoesE_fld _ _ _ _ "trees" undoesE_trees k.trees ⟨hk.treesCount, hk.trees⟩
    b _ t10.head
  have h11 := undoesE_fld _ _ _ _ "stored" undoesE_rows k.stored ⟨hk.storedCount, hk.stored⟩
    b _ t11.head
  have h12 := undoesE_fld _ _ _ _ "bindRoot" undoesE_dig' k.bindRoot hk.bindRoot b _ t12.head
  have h13 := undoesE_fld _ _ _ _ "place" undoesE_nat k.place hk.place b _ t13.head
  have h14 := undoesE_fld _ _ _ _ "places" undoesE_nat k.places hk.places b _ t14.head
  have h15 := undoesE_fld _ _ _ _ "slotSalt" undoesE_salt k.slotSalt hk.slotSalt b _ t15.head
  have h16 := undoesE_fld _ _ _ _ "slotPath" undoesE_path k.slotPath ⟨hk.slotDepth, hk.slotPath⟩
    b _ t15.tail
  have hm' : (magic.toUTF8 != magic.toUTF8) = false := by
    simp only [bne, Fmt.bytes_beq_self, Bool.not_true]
  have hc : (magic == magicKey && k.copy != 0) = false := by
    by_cases e : magic = magicKey
    · rw [hk.keyCopy e]
      simp
    · simp [e]
  simp only [rdFile, bind, Except.bind, pure, Except.pure, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, hm', hc, hk.treesRise, hk.storedRise, Bool.false_eq_true,
    if_false]
  simp only [wrFile, ByteArray.size_append, Nat.add_assoc]

/-- **The reader of a whole carrier gives back what was written.** -/
theorem read_wrFile :
  ∀ (magic : String) (k : File), magic.toUTF8.size = 8 → k.WF magic →
  OnBytes.Maker.Carrier.read magic (wrFile magic k) = .ok k := by
  intro magic k hm hk
  have h := undoesE_file magic hm k hk (wrFile magic k) 0 (at_whole _)
  simp [OnBytes.Maker.Carrier.read, h, whole]

theorem size_magicKey : magicKey.toUTF8.size = 8 ∧ magicProof.toUTF8.size = 8 :=
  ⟨by decide, by decide⟩

/-! ## The file beside: the record's seeds -/

theorem undoesE_seed : UndoesE rdSeed wrSeed okSeed := by
  intro x hx b i hb
  have hb' : At b i (list ext x.1 ++ ext x.2) := hb
  have h1 := undoesE_fld _ _ _ _ "z" undoesE_exts x.1 ⟨hx.1, hx.2.1⟩ b i hb'.head
  have h2 := undoesE_fld _ _ _ _ "beta" undoesE_E x.2 hx.2.2 b _ hb'.tail
  simp only [rdSeed, bind, Except.bind, pure, Except.pure, h1, h2, wrSeed,
    ByteArray.size_append, Nat.add_assoc]

theorem one_le_wrSeed (x : List Ext × Ext) : 1 ≤ (wrSeed x).size := by
  have h := one_le_ext x.2
  simp only [wrSeed, ByteArray.size_append]
  omega

/-- **The reader of the seeds' file gives back what was written.** -/
theorem readSeeds_wrSeeds :
  ∀ l : List (List Ext × Ext), l.length < 2 ^ 64 → (∀ s ∈ l, okSeed s) →
  readSeeds (wrSeeds l) = .ok l := by
  intro l hl hs
  have h : OnBytes.Maker.Carrier.rdList rdSeed (wrSeeds l) 0 = .ok (l, 0 + (wrSeeds l).size) :=
    undoesE_list _ _ _ _ undoesE_seed (fun x _ => one_le_wrSeed x) l ⟨hl, hs⟩ (wrSeeds l) 0
      (at_whole _)
  simp [readSeeds, h, whole]

end OnBytes.Prover.Print
