-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TiePlanes.lean: the bits of
a lookup's planes, read as the library reads them, in machine elements: a text proposed for the
table of the key file's joints (Johnson/Desc/Key/KeyK3W.lean: bitVec): the
sum, over the lookup's blocks that hold the plane, of the entry of B's main table at the library's
index; written with no sum of Mathlib's. And the reading lemma: read, it is the library's
Planes.bitsOf (OnBytes/Slice/BlkPlanesAt.lean).

Main names:
  blockPlace rb logEll b e: the index of entry e of the block b in a table with rb row bits and
    logEll bits of a place in a row: plain arithmetic. blockPlace_eq: it is the library's blockIdx.
  bitVecL x codes l valB i: the bit number i = plane + 2 ^ mu · row of lookup l, off B's main table.
  read_bitVecL: readE (bitVecL x codes l valB i) =
    Planes.bitsOf x codes l (the table read) (i / 2 ^ mu) (i % 2 ^ mu). No premise.
  sum_pick_find, blockPlace_plain: among blocks of which no two hold the plane the sum is the first
    one's term; at a block that lies as the layout's docstring says the index is
    row + 2 ^ rb · (firstPlace + e).
  bitPlaceOld, bitVecOld: another text of the table's bit, under these names.
  read_bitVecL_old: bitVecL reads as bitVecOld at every
    index at which no two of the lookup's blocks hold the plane and the block that holds it lies so.
  bitVecS: the same bit by the table's own sum sumE, over the numbers of the lookup's blocks.
  read_bitVecS: read, it is Planes.bitsOf too: no premise. read_bitVecS_L: the two texts read alike.

Object: definitions of the library; a text proposed for the table of the key file's joints.
User: FieldR14X.lean calls read_bitVecL.
Letters: x, the ranges' public record · codes · l, a lookup's number · valB, B's main table.

Limits. The layout's facts are premises of read_bitVecL_old; no lemma on Wf.layout gives them.
Nothing on soundness.

-/
import Johnson.Desc.Key.KeyK3Items
import OnBytes.Slice.BlkPlanesAt
import Johnson.Desc.Key.KeySumRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TiePlanes
open OnBytes OnBytes.Slice
open OnBytes.Params (WfPublic)

/-- The index, in a table with rb row bits and logEll bits of a place in a row, of entry e of the
block b: the row's number in the low bits; above them the entry's low bits, the block's number among
the blocks of its size in the row, and the entry's higher bits. -/
def blockPlace (rb logEll : Nat) (b : Wf.Block) (e : Nat) : Nat :=
  b.row % 2 ^ rb +
    (e % 2 ^ b.bits + b.firstPlace / 2 ^ b.bits % 2 ^ (logEll - b.bits) * 2 ^ b.bits +
      e / 2 ^ b.bits * 2 ^ (b.bits + (logEll - b.bits))) * 2 ^ rb

/-- It is the library's index. -/
theorem blockPlace_eq (rb logEll : ℕ) (b : Wf.Block) (e : ℕ) :
    blockPlace rb logEll b e = Planes.blockIdx rb logEll b e := by
  unfold blockPlace Planes.blockIdx shiftIn
  simp only [pow_zero, Nat.mod_one, Nat.div_one, Nat.mul_one, Nat.zero_add]

/-- **Bit number i = plane + 2 ^ mu · row of lookup l**: the sum, over the lookup's blocks that hold
the plane, of the entry of B's main table at the block's index. valB: B's main table. -/
def bitVecL (x : WfPublic) (codes : Codes) (l : Nat) (valB : Nat → E) (i : Nat) : E :=
  let mu := (x.lookups.getD l default).mu
  let j := i % 2 ^ mu
  let t := i / 2 ^ mu
  let code := codes.base.getD x.message.shape.code default
  ((Wf.layout x.lookups code.ell).filter (·.lookup == l)).foldl (fun s b =>
    if b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes then
      addE s (valB (blockPlace (ceilLog2 x.message.shape.mainRows) code.logEll b
        (j - b.first + 2 ^ b.logPlanes * t)))
    else s) zeroE

theorem read_pickFold {α : Type} (c : α → Prop) [DecidablePred c] (f : α → E) :
    ∀ (bs : List α) (a : E),
      readE (bs.foldl (fun s b => if c b then addE s (f b) else s) a) =
        readE a + (bs.map fun b => if c b then readE (f b) else 0).sum
  | [], a => by simp
  | b :: bs, a => by
    rw [List.foldl_cons, read_pickFold c f bs, List.map_cons, List.sum_cons]
    by_cases h : c b
    · rw [if_pos h, if_pos h, readE_add]
      ring
    · rw [if_neg h, if_neg h]
      ring

/-- **Read, it is the library's reading of the bit.** -/
theorem read_bitVecL (x : WfPublic) (codes : Codes) (l : ℕ) (valB : ℕ → E) (i : ℕ) :
    readE (bitVecL x codes l valB i) =
      Planes.bitsOf x codes l (fun k => readE (valB k)) (i / 2 ^ (x.lookups.getD l default).mu)
        (i % 2 ^ (x.lookups.getD l default).mu) := by
  unfold bitVecL Planes.bitsOf Planes.bitAt Planes.blocksOf Planes.codeOf
  simp only
  rw [read_pickFold, readE_zero, zero_add]
  simp only [blockPlace_eq]

/-! ## Another text of the table, where the layout is as its docstring says -/

/-- **Another text of the table** (bitPlace, which is not in KeyK3W.lean as it stands),
carried here under this file's own name: where entry number i of lookup l's multiplicities lies in
B's main table: at the FIRST of the lookup's blocks that holds the plane, by the plain index. -/
def bitPlaceOld (x : WfPublic) (codes : Codes) (l i : Nat) : Option Nat :=
  let mu := (x.lookups.getD l default).mu
  let j := i % 2 ^ mu
  let t := i / 2 ^ mu
  let code := codes.base.getD x.message.shape.code default
  (((Wf.layout x.lookups code.ell).filter (·.lookup == l)).find? fun b =>
    decide (b.first ≤ j) && decide (j < b.first + 2 ^ b.logPlanes)).map fun b =>
      b.row + 2 ^ ceilLog2 x.message.shape.mainRows *
        (b.firstPlace + (j - b.first) + 2 ^ b.logPlanes * t)

/-- The table's elder bitVec: the entry there. -/
def bitVecOld (x : WfPublic) (codes : Codes) (l : Nat) (valB : Nat → E) (i : Nat) : E :=
  match bitPlaceOld x codes l i with
  | some k => valB k
  | none => zeroE

/-- Among members of which no two meet the test, the sum over those that meet it is the first one's
term. -/
theorem sum_pick_find {α : Type} (c : α → Prop) [DecidablePred c] (g : α → GE) :
    ∀ bs : List α, bs.Pairwise (fun a b => ¬ (c a ∧ c b)) →
      (bs.map fun b => if c b then g b else 0).sum =
        ((bs.find? fun b => decide (c b)).map g).getD 0
  | [], _ => rfl
  | b :: bs, h => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    rw [List.map_cons, List.sum_cons, List.find?_cons]
    by_cases hb : c b
    · have z : (bs.map fun b => if c b then g b else 0).sum = 0 :=
        List.sum_eq_zero fun y hy => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
          exact if_neg fun hc => h1 a ha ⟨hb, hc⟩
      rw [if_pos hb, z, add_zero, decide_eq_true hb]
      rfl
    · rw [if_neg hb, zero_add, decide_eq_false hb]
      exact sum_pick_find c g bs h2

/-- The library's index in plain words, at a block that lies as the layout's docstring says. -/
theorem blockPlace_plain (rb logEll : ℕ) (b : Wf.Block) (e : ℕ) (hrow : b.row < 2 ^ rb)
    (hal : b.firstPlace % 2 ^ b.bits = 0) (hin : b.firstPlace + 2 ^ b.bits ≤ 2 ^ logEll)
    (he : e < 2 ^ b.bits) :
    blockPlace rb logEll b e = b.row + 2 ^ rb * (b.firstPlace + e) := by
  have hp : 0 < 2 ^ b.bits := Nat.pow_pos (by omega)
  have hbl : b.bits ≤ logEll := by
    by_contra hc
    have : 2 ^ logEll < 2 ^ b.bits := Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  have hq : b.firstPlace / 2 ^ b.bits < 2 ^ (logEll - b.bits) := by
    rw [Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add, Nat.sub_add_cancel hbl]
    omega
  unfold blockPlace
  rw [Nat.mod_eq_of_lt hrow, Nat.mod_eq_of_lt he, Nat.div_eq_of_lt he, Nat.mod_eq_of_lt hq,
    Nat.zero_mul, Nat.add_zero, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hal), Nat.mul_comm,
    Nat.add_comm e]

/-- **THE NEW TEXT READS AS THE ELDER ONE**, at an index i at which: no two of the lookup's blocks
hold the plane; and the block that holds it lies as the layout's docstring says: its row below
2 ^ rowBits, its first place a multiple of its size, inside the row, the entry inside the block. -/
theorem read_bitVecL_old (x : WfPublic) (codes : Codes) (l : ℕ) (valB : ℕ → E) (i : ℕ)
    (hone : ((Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter
      (·.lookup == l)).Pairwise fun a b =>
        ¬ ((a.first ≤ i % 2 ^ (x.lookups.getD l default).mu ∧
            i % 2 ^ (x.lookups.getD l default).mu < a.first + 2 ^ a.logPlanes) ∧
          (b.first ≤ i % 2 ^ (x.lookups.getD l default).mu ∧
            i % 2 ^ (x.lookups.getD l default).mu < b.first + 2 ^ b.logPlanes)))
    (hlay : ∀ b ∈ (Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter
      (·.lookup == l), b.first ≤ i % 2 ^ (x.lookups.getD l default).mu →
        i % 2 ^ (x.lookups.getD l default).mu < b.first + 2 ^ b.logPlanes →
        b.row < 2 ^ ceilLog2 x.message.shape.mainRows ∧ b.firstPlace % 2 ^ b.bits = 0 ∧
        b.firstPlace + 2 ^ b.bits ≤ 2 ^ (codes.base.getD x.message.shape.code default).logEll ∧
        i % 2 ^ (x.lookups.getD l default).mu - b.first +
          2 ^ b.logPlanes * (i / 2 ^ (x.lookups.getD l default).mu) < 2 ^ b.bits) :
    readE (bitVecL x codes l valB i) = readE (bitVecOld x codes l valB i) := by
  unfold bitVecL bitVecOld bitPlaceOld
  simp only
  rw [read_pickFold, readE_zero, zero_add, sum_pick_find _ _ _ hone]
  have ed : (fun b : Wf.Block => decide (b.first ≤ i % 2 ^ (x.lookups.getD l default).mu ∧
      i % 2 ^ (x.lookups.getD l default).mu < b.first + 2 ^ b.logPlanes)) =
      fun b => decide (b.first ≤ i % 2 ^ (x.lookups.getD l default).mu) &&
        decide (i % 2 ^ (x.lookups.getD l default).mu < b.first + 2 ^ b.logPlanes) :=
    funext fun b => Bool.decide_and _ _
  rw [ed]
  cases hf : ((Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter
      (·.lookup == l)).find? fun b =>
        decide (b.first ≤ i % 2 ^ (x.lookups.getD l default).mu) &&
          decide (i % 2 ^ (x.lookups.getD l default).mu < b.first + 2 ^ b.logPlanes) with
  | none => exact readE_zero.symm
  | some b =>
    have hm := List.mem_of_find?_eq_some hf
    have hc := List.find?_some hf
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc
    obtain ⟨a1, a2, a3, a4⟩ := hlay b hm hc.1 hc.2
    show readE (valB (blockPlace _ _ b _)) = readE (valB _)
    rw [blockPlace_plain _ _ b _ a1 a2 a3 a4, ← Nat.add_assoc b.firstPlace]

/-! ## The same by the table's own sum -/

/-- **Bit number i of lookup l, by the table's own sum sumE**: over the numbers n of the lookup's
blocks: the entry of B's main table at the block's index if block n holds the plane; else zero. -/
def bitVecS (x : WfPublic) (codes : Codes) (l : Nat) (valB : Nat → E) (i : Nat) : E :=
  let mu := (x.lookups.getD l default).mu
  let j := i % 2 ^ mu
  let t := i / 2 ^ mu
  let code := codes.base.getD x.message.shape.code default
  let bs := (Wf.layout x.lookups code.ell).filter (·.lookup == l)
  VerifiableInference.Desc.Key.sumE bs.length fun n =>
    match bs[n]? with
    | some b =>
      if b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes then
        valB (blockPlace (ceilLog2 x.message.shape.mainRows) code.logEll b
          (j - b.first + 2 ^ b.logPlanes * t))
      else zeroE
    | none => zeroE

/-- A sum over a list's members, by their numbers. -/
theorem sum_by_number {α : Type} (g : α → GE) : ∀ bs : List α,
    ∑ n ∈ Finset.range bs.length, ((bs[n]?).map g).getD 0 = (bs.map g).sum
  | [] => rfl
  | b :: bs => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    congr 1
    exact sum_by_number g bs

/-- **Read, it is the library's reading of the bit too.** -/
theorem read_bitVecS (x : WfPublic) (codes : Codes) (l : ℕ) (valB : ℕ → E) (i : ℕ) :
    readE (bitVecS x codes l valB i) =
      Planes.bitsOf x codes l (fun k => readE (valB k)) (i / 2 ^ (x.lookups.getD l default).mu)
        (i % 2 ^ (x.lookups.getD l default).mu) := by
  unfold bitVecS Planes.bitsOf Planes.bitAt Planes.blocksOf Planes.codeOf
  simp only
  rw [VerifiableInference.Desc.Key.sumE_read readE readE_zero readE_add, ← sum_by_number]
  refine Finset.sum_congr rfl fun n _ => ?_
  cases ((Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell).filter
      (·.lookup == l))[n]? with
  | none => exact readE_zero
  | some b =>
    show readE (if _ then _ else _) = if _ then _ else _
    split
    · rw [blockPlace_eq]
    · exact readE_zero

/-- So the two texts read alike. -/
theorem read_bitVecS_L (x : WfPublic) (codes : Codes) (l : ℕ) (valB : ℕ → E) (i : ℕ) :
    readE (bitVecS x codes l valB i) = readE (bitVecL x codes l valB i) := by
  rw [read_bitVecS, read_bitVecL]

end Johnson.RunOne.Law.TiePlanes

#print axioms Johnson.RunOne.Law.TiePlanes.blockPlace_eq
#print axioms Johnson.RunOne.Law.TiePlanes.read_bitVecL
#print axioms Johnson.RunOne.Law.TiePlanes.blockPlace_plain
#print axioms Johnson.RunOne.Law.TiePlanes.read_bitVecL_old
#print axioms Johnson.RunOne.Law.TiePlanes.read_bitVecS
#print axioms Johnson.RunOne.Law.TiePlanes.read_bitVecS_L
