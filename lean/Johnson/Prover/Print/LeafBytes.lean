-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/LeafBytes.lean: a writer for a parsed leaf file (leaf-k.parsed.bin, magic
FPENTC01); and: its reader `rdLeaf` (Johnson/PV/EntryInOf.lean) gives back what was written.

Why. What the verifier is handed for the entry file is laid of a `LeafP`, which `rdLeaf` decodes
from bytes. A prover in Lean that is to hand over bytes needs the way back.

How. `rdLeaf` is made of the format's plain readers. For these the library has the frame
`Fmt.Undoes r sp ok` with its laws (Fmt/Rules1Laws.lean; `undoes_map`, Fmt/ParsedReadLaws.lean); the
writers here are chains of the format's own spellings (Fmt/Rules1.lean). Almost all is calls.

Main names.
  `okItemL`, `RowP.WF`, `okRoundL`, `okTreeL`, `LeafP.WF` (namespace `PV.EntryInOf`): what the
    reader takes, one field a clause: digests of 32 bytes; numbers and lengths below 2^64; no item
    of the kinds that this reader does not know (an element of the base field, a bare word)
  `wrT3`, `wrItemL`, `wrRoundL`, `wrRowL`, `wrTreeL`, `wrLeaf`: the writers, with code (namespace
    `Johnson.Prover.Print`, as all that follows)
  `undoes_natL` ... `undoes_treeL`: reader by reader
  `rdLeaf_wrLeaf`: L.WF → rdLeaf (wrLeaf L) = some L

Limits. One direction: nothing says that what `rdLeaf` takes was written by `wrLeaf`. It is not so:
a tree's second field (the chain's number) is dropped by the reader, and the writer lays 0 there.
Bytes alone: no protocol, no hash, nothing on what a field means. This reader does not test that a
word is below the prime, nor a salt's length, nor that leaves rise; so `LeafP.WF` does not ask it.
That a prover's `LeafP` meets `LeafP.WF` is not shown here, nor that these bytes are those of the
outside parser.

Terms: lean/GLOSSARY.md.

-/
import Johnson.PV.EntryInOf
import OnBytes.Prover.Print.Bytes

set_option autoImplicit false

namespace PV.EntryInOf
open _root_.Fmt (ItemValue)

/-! ## What the reader of a parsed leaf file takes -/

/-- an item: a root of 32 bytes, an element or an answer; the reader knows no other kind -/
def okItemL : ItemValue → Prop
  | .root d => d.size = 32
  | .e _ => True
  | .answer _ => True
  | .f _ => False
  | .word _ => False

structure RowP.WF (r : RowP) : Prop where
  leaf : r.leaf < 2 ^ 64
  width : r.col.length < 2 ^ 64
  salt : r.salt.size < 2 ^ 64
  depth : r.path.length < 2 ^ 64
  path : ∀ d ∈ r.path, d.size = 32

/-- a round: its items and its nonce -/
def okRoundL (r : List ItemValue × Nat) : Prop :=
  (r.1.length < 2 ^ 64 ∧ ∀ x ∈ r.1, okItemL x) ∧ r.2 < 2 ^ 64

/-- a tree's number with its rows -/
def okTreeL (t : Nat × List RowP) : Prop :=
  t.1 < 2 ^ 64 ∧ t.2.length < 2 ^ 64 ∧ ∀ r ∈ t.2, r.WF

/-- What `rdLeaf` takes: one field a clause. -/
structure LeafP.WF (L : LeafP) : Prop where
  root0 : L.root0.size = 32
  answers0Count : L.answers0.length < 2 ^ 64
  root : L.root.size = 32
  answersCount : L.answers.length < 2 ^ 64
  run : L.run.size = 32
  roundsCount : L.rounds.length < 2 ^ 64
  rounds : ∀ r ∈ L.rounds, okRoundL r
  treesCount : L.trees.length < 2 ^ 64
  trees : ∀ t ∈ L.trees, okTreeL t
  stored0Count : L.stored0.length < 2 ^ 64
  stored0 : ∀ r ∈ L.stored0, r.WF
  stored1Count : L.stored1.length < 2 ^ 64
  stored1 : ∀ r ∈ L.stored1, r.WF

end PV.EntryInOf

namespace Johnson.Prover.Print
open PV.EntryInOf OnBytes.Prover.Print
open _root_.Fmt (Rd Undoes ItemValue u64 u64n text list pair cat)

/-! ## The writers -/

/-- three words -/
def wrT3 : UInt64 × UInt64 × UInt64 → ByteArray := pair u64 (pair u64 u64)

/-- Item: the kind, then the value. (The reader refuses the kinds 1 and 2.) -/
def wrItemL : ItemValue → ByteArray
  | .root d => u64 0 ++ d
  | .f x => u64 1 ++ u64 x
  | .word w => u64 2 ++ u64 w
  | .e x => u64 3 ++ wrT3 x
  | .answer x => u64 4 ++ wrT3 x

def wrRoundL : List ItemValue × Nat → ByteArray := pair (list wrItemL) u64n

def wrRowL (r : RowP) : ByteArray :=
  pair u64n (pair (list u64) (pair text (list id))) (r.leaf, r.col, r.salt, r.path)

/-- TreeRows: the tree, the chain, the rows. The reader drops the second: 0 is written. -/
def wrTreeL (t : Nat × List RowP) : ByteArray :=
  pair u64n (pair u64n (list wrRowL)) (t.1, 0, t.2)

/-- A parsed leaf file's bytes: the magic, then the nine fields in their order. -/
def wrLeaf (L : LeafP) : ByteArray :=
  magicLeaf ++ (L.root0 ++ (list wrT3 L.answers0 ++ (L.root ++ (list wrT3 L.answers ++ (L.run ++
    (list wrRoundL L.rounds ++ (list wrTreeL L.trees ++ (list wrRowL L.stored0 ++
    list wrRowL L.stored1))))))))

/-! ## The small readers -/

/-- From the form with `At` (OnBytes/Prover/Print/Bytes.lean) back to `Fmt.Undoes`. -/
theorem undoes_of_at {α : Type} {r : Rd α} {sp : α → ByteArray} {ok : α → Prop}
    (h : ∀ x, ok x → ∀ b i, At b i (sp x) → r b i = some (x, i + (sp x).size)) : Undoes r sp ok :=
  fun x hx pre post => h x hx _ _ ⟨pre, post, rfl, rfl⟩

/-- The reader's own "turned reader" is the format's. -/
theorem rdMap_eq {α β : Type} (f : α → β) (r : Rd α) : PV.EntryInOf.rdMap f r = Fmt.rdMap f r := rfl

theorem undoes_natL :
  Undoes PV.EntryInOf.rdNat u64n fun n => n < 2 ^ 64 :=
  Fmt.undoes_map Fmt.undoes_word (·.toNat) UInt64.ofNat
    (fun n hn => by
      show (UInt64.ofNat n).toNat = n
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt hn)
    (fun _ _ => rfl) fun _ _ => trivial

theorem undoes_t3 :
  Undoes rdT3 wrT3 fun _ => True :=
  fun x _ => Fmt.undoes_pair Fmt.undoes_word (Fmt.undoes_pair Fmt.undoes_word Fmt.undoes_word) x
    ⟨trivial, trivial, trivial⟩

theorem undoes_itemL :
  Undoes PV.EntryInOf.rdItem wrItemL okItemL := by
  refine undoes_of_at fun x hx b i hb => ?_
  cases x with
  | f _ => exact hx.elim
  | word _ => exact hx.elim
  | root d =>
    have hb' : At b i (u64 0 ++ d) := hb
    have h1 := Undoes.at Fmt.undoes_word (x := (0 : UInt64)) trivial hb'.head
    have h2 : Fmt.rdDigest b (i + (u64 0).size) = some (d, i + (u64 0).size + d.size) :=
      Undoes.at Fmt.undoes_digest (x := d) hx hb'.tail
    have k0 : ((0 : UInt64) == 0) = true := by decide
    simp only [PV.EntryInOf.rdItem, h1, k0, if_true, PV.EntryInOf.rdMap, h2, Option.map_some]
    simp only [wrItemL, ByteArray.size_append, Nat.add_assoc]
  | e y =>
    have hb' : At b i (u64 3 ++ wrT3 y) := hb
    have h1 := Undoes.at Fmt.undoes_word (x := (3 : UInt64)) trivial hb'.head
    have h2 := Undoes.at undoes_t3 (x := y) trivial hb'.tail
    have k0 : ((3 : UInt64) == 0) = false := by decide
    have k3 : ((3 : UInt64) == 3) = true := by decide
    simp only [PV.EntryInOf.rdItem, h1, k0, k3, Bool.false_eq_true, if_false, if_true,
      PV.EntryInOf.rdMap, h2, Option.map_some]
    simp only [wrItemL, ByteArray.size_append, Nat.add_assoc]
  | answer y =>
    have hb' : At b i (u64 4 ++ wrT3 y) := hb
    have h1 := Undoes.at Fmt.undoes_word (x := (4 : UInt64)) trivial hb'.head
    have h2 := Undoes.at undoes_t3 (x := y) trivial hb'.tail
    have k0 : ((4 : UInt64) == 0) = false := by decide
    have k3 : ((4 : UInt64) == 3) = false := by decide
    have k4 : ((4 : UInt64) == 4) = true := by decide
    simp only [PV.EntryInOf.rdItem, h1, k0, k3, k4, Bool.false_eq_true, if_false, if_true,
      PV.EntryInOf.rdMap, h2, Option.map_some]
    simp only [wrItemL, ByteArray.size_append, Nat.add_assoc]

theorem one_le_wrItemL (x : ItemValue) : 1 ≤ (wrItemL x).size := by
  cases x <;> simp only [wrItemL, ByteArray.size_append, Fmt.size_u64] <;> omega

theorem undoes_roundL :
  Undoes (Fmt.rdPair (Fmt.rdList PV.EntryInOf.rdItem) PV.EntryInOf.rdNat) wrRoundL okRoundL :=
  Fmt.undoes_pair (Fmt.undoes_list undoes_itemL fun x _ => one_le_wrItemL x) undoes_natL

theorem undoes_rowL :
  Undoes PV.EntryInOf.rdRow wrRowL RowP.WF := by
  have hw : Undoes (Fmt.rdList Fmt.rdWord) (list u64)
      fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, True :=
    Fmt.undoes_list Fmt.undoes_word fun x _ => by
      rw [Fmt.size_u64]
      omega
  have hp : Undoes (Fmt.rdList Fmt.rdDigest) (list id)
      fun l => l.length < 2 ^ 64 ∧ ∀ d ∈ l, d.size = 32 :=
    Fmt.undoes_list Fmt.undoes_digest fun d hd => by
      show 1 ≤ d.size
      omega
  have h := Fmt.undoes_pair undoes_natL (Fmt.undoes_pair hw (Fmt.undoes_pair Fmt.undoes_text hp))
  unfold PV.EntryInOf.rdRow
  rw [rdMap_eq]
  refine Fmt.undoes_map h _ (fun r => (r.leaf, r.col, r.salt, r.path)) (fun _ _ => rfl)
    (fun _ _ => rfl) fun r hr => ?_
  exact ⟨hr.leaf, ⟨hr.width, fun _ _ => trivial⟩, hr.salt, hr.depth, hr.path⟩

theorem one_le_wrRowL (r : RowP) : 1 ≤ (wrRowL r).size := by
  show 1 ≤ (u64n r.leaf ++ _).size
  rw [ByteArray.size_append, size_u64n]
  omega

theorem undoes_rowsL : Undoes (Fmt.rdList PV.EntryInOf.rdRow) (list wrRowL)
    fun l => l.length < 2 ^ 64 ∧ ∀ r ∈ l, r.WF :=
  Fmt.undoes_list undoes_rowL fun r _ => one_le_wrRowL r

theorem undoes_treeL :
  Undoes PV.EntryInOf.rdTree wrTreeL okTreeL := by
  have h := Fmt.undoes_pair undoes_natL (Fmt.undoes_pair undoes_natL undoes_rowsL)
  have h0 : (0 : Nat) < 2 ^ 64 := by omega
  unfold PV.EntryInOf.rdTree
  rw [rdMap_eq]
  refine Fmt.undoes_map h _ (fun t => (t.1, 0, t.2)) (fun _ _ => rfl) (fun _ _ => rfl)
    fun t ht => ?_
  exact ⟨ht.1, h0, ht.2⟩

theorem one_le_wrT3 (x : UInt64 × UInt64 × UInt64) : 1 ≤ (wrT3 x).size := by
  show 1 ≤ (u64 x.1 ++ _).size
  rw [ByteArray.size_append, Fmt.size_u64]
  omega

theorem one_le_wrRoundL (r : List ItemValue × Nat) : 1 ≤ (wrRoundL r).size := by
  show 1 ≤ (_ ++ u64n r.2).size
  rw [ByteArray.size_append, size_u64n]
  omega

theorem one_le_wrTreeL (t : Nat × List RowP) : 1 ≤ (wrTreeL t).size := by
  show 1 ≤ (u64n t.1 ++ _).size
  rw [ByteArray.size_append, size_u64n]
  omega

theorem undoes_t3s : Undoes (Fmt.rdList rdT3) (list wrT3)
    fun l => l.length < 2 ^ 64 ∧ ∀ x ∈ l, True :=
  Fmt.undoes_list undoes_t3 fun x _ => one_le_wrT3 x

/-! ## The whole file -/

/-- **The reader of a parsed leaf file gives back what was written.** -/
theorem rdLeaf_wrLeaf :
  ∀ L : LeafP, L.WF → rdLeaf (wrLeaf L) = some L := by
  intro L hL
  have t0 : At (wrLeaf L) 0 (magicLeaf ++ (L.root0 ++ (list wrT3 L.answers0 ++ (L.root ++
    (list wrT3 L.answers ++ (L.run ++ (list wrRoundL L.rounds ++ (list wrTreeL L.trees ++
    (list wrRowL L.stored0 ++ list wrRowL L.stored1))))))))) := at_whole _
  have hx : (wrLeaf L).extract 0 8 = magicLeaf := by
    have h := Fmt.extract_mid ByteArray.empty magicLeaf (L.root0 ++ (list wrT3 L.answers0 ++
      (L.root ++ (list wrT3 L.answers ++ (L.run ++ (list wrRoundL L.rounds ++
      (list wrTreeL L.trees ++ (list wrRowL L.stored0 ++ list wrRowL L.stored1))))))))
    rw [ByteArray.empty_append] at h
    exact h
  have hs : (wrLeaf L).size = 8 + (L.root0.size + ((list wrT3 L.answers0).size + (L.root.size +
      ((list wrT3 L.answers).size + (L.run.size + ((list wrRoundL L.rounds).size +
      ((list wrTreeL L.trees).size + ((list wrRowL L.stored0).size +
      (list wrRowL L.stored1).size)))))))) := by
    simp only [wrLeaf, ByteArray.size_append]
    rfl
  generalize wrLeaf L = b at t0 hx hs ⊢
  have t1 : At b 8 _ := t0.tail
  have t2 := t1.tail
  have t3 := t2.tail
  have t4 := t3.tail
  have t5 := t4.tail
  have t6 := t5.tail
  have t7 := t6.tail
  have t8 := t7.tail
  have h1 : Fmt.rdDigest b 8 = some (L.root0, 8 + L.root0.size) :=
    Undoes.at Fmt.undoes_digest (x := L.root0) hL.root0 t1.head
  have h2 := Undoes.at undoes_t3s (x := L.answers0) ⟨hL.answers0Count, fun _ _ => trivial⟩ t2.head
  have h3 : Fmt.rdDigest b _ = some (L.root, _ + L.root.size) :=
    Undoes.at Fmt.undoes_digest (x := L.root) hL.root t3.head
  have h4 := Undoes.at undoes_t3s (x := L.answers) ⟨hL.answersCount, fun _ _ => trivial⟩ t4.head
  have h5 : Fmt.rdDigest b _ = some (L.run, _ + L.run.size) :=
    Undoes.at Fmt.undoes_digest (x := L.run) hL.run t5.head
  have h6 := Undoes.at (Fmt.undoes_list undoes_roundL fun r _ => one_le_wrRoundL r)
    (x := L.rounds) ⟨hL.roundsCount, hL.rounds⟩ t6.head
  have h7 := Undoes.at (Fmt.undoes_list undoes_treeL fun t _ => one_le_wrTreeL t)
    (x := L.trees) ⟨hL.treesCount, hL.trees⟩ t7.head
  have h8 := Undoes.at undoes_rowsL (x := L.stored0) ⟨hL.stored0Count, hL.stored0⟩ t8.head
  have h9 := Undoes.at undoes_rowsL (x := L.stored1) ⟨hL.stored1Count, hL.stored1⟩ t8.tail
  simp only [rdLeaf, hx, Fmt.bytes_beq_self, if_true, bind, Option.bind, h1, h2, h3, h4, h5, h6, h7,
    h8, h9]
  simp only [hs, Nat.add_assoc, beq_self_eq_true, if_true]

end Johnson.Prover.Print
