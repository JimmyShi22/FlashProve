-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Reads.lean

The vector of reads of an honest prover, for any list of tables: its entries meet the law of the
reads.

A sub-proof's prover sends, behind challenges, one more vector: the reads (U3 in
docs/format/11-1-machinery.md, "The cells, the arrays of the matrices, U3 and ZZ"). The vector is
made of tables. A table belongs to a matrix of cells and to a public vector of weights; it has one
entry for each column and each stretch of the matrix's rows: the sum of the stretch's cells in that
column under the weights. Johnson/Desc/K8/Honest/Arrays.lean has an entry as a function with code,
"readAt p parts cell n", given the list of tables in the type in which the verifier of
OnBytes/Model/ holds it ("HFun"). The library states what the entries are meant to be as a condition
on a table of entries, the law of the reads ("Fo.ReadsAll", OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean),
and shows that some entries meet it, made by choice ("madeRead", "reads_meet",
Johnson/Meaning/PlanesLaw.lean). This file shows, for a list in which no entry lies in two tables
and a reading that takes integers to integers, that the function with code meets it, and that, read
in a ring, it is the vector made by choice.

Letters. ρ: a reading of the program's field elements in a commutative ring K. hZ: ρ takes the
program's image of an integer to the integer's image in K; at the reading "Reading.gl" that is
"Numerals.ofInt" at "gl_numerals" (Johnson/Road/FormsKeysQK.lean, Johnson/Road/FormsKeysKit.lean).
mats: the sub-proof's list of matrices; funs: its list of tables, one member for each matrix of a
table that is cut into several matrices; cell: integers by the matrix's number in the list, the row
of cells and the column.

Main definitions:
* "ParFits p mats": the numbers of a place p have the rows and columns of mats. "parOfMats mats":
  such numbers.
* "TablesLie mats funs n": every table of funs ends at or below entry n, and no entry lies in two
  tables.
* "SameSizes mats mats'": two lists of matrices with the same rows and columns, number by number.
* "castM cell": the integers' images in K.
* "SentReads ρ p parts cell entry iU3 K3 n": in the table of entries "entry", the first n entries of
  array iU3, read by the rule "Fo.u3Val" at K3 columns, are "readAt p parts cell", read by ρ.
  "entriesOfReads": a table of entries of which that holds.
Main theorems:
* "ParFits.same", "TablesLie.same", "readAt_same": the two conditions, and the vector, hang on the
  matrices' rows and columns alone. (Of "Fo.ReadsAll": "readsAll_sizes",
  Johnson/Meaning/ReadsLaw.lean.)
* "val_readOf": one entry, read by ρ, is the format's sum.
* "readAt_in", "readAt_beyond": the vector inside a table, and from entry n on.
* "val_readAt_eq_madeRead": read by ρ, the vector with code is "madeRead", at every number.
* "readsAll_sent": under "ParFits", "TablesLie", hZ and "SentReads", "Fo.ReadsAll" holds at the
  integers' images.
* "holds_sent": under the same premises, K a field, every table holds what it says of the integers'
  images, in the words of Johnson/Road/FormsKeysMat.lean ("Holds").

Limits. The list of tables, with its weights, is a letter: which tables a sub-proof has, and their
weights as functions of challenges, is not said here. "TablesLie" is a premise; without it "readAt"
serves, at an entry that lies in two tables, the first of them alone. "SentReads" is a premise on a
table of entries: nothing here sends a vector, and nothing is said of what an oracle message holds
beside it. At a list without a table that has an entry, "readsAll_sent" and "holds_sent" say
nothing. "Fo.ReadsAll" asks nothing of a table whose field tree is not 2; "readAt" does not look at
that field. "holds_sent" reads entry i in virtual row i / K3, the tie's third clause ("TieThird",
Johnson/Desc/Kinds/Law/TieReads.lean) in row 0: where n is at most K3, or K3 is 0, the two
name the same places; elsewhere, from entry K3 on, they name different places, and that one array's
table of entries holds the vector at both is not shown here. Whether a value of "readAt" is reduced
(every word below the prime) is not said. "val_readAt_eq_madeRead" uses the second clause of
"TablesLie" alone. Johnson/Meaning/ReadsMember.lean lays "madeRead" at integers that go by the
matrix's number, the column and the row; here they go by the number, the row and the column.

Ground. "readAt", "readOf" and "partLength" are those of Johnson/Desc/K8/Honest/Arrays.lean, which
this file imports; "CellsAt" is that of Johnson/Desc/K8/Honest/Window.lean beneath it.

Not claimed: that a verifier accepts a proof made of these entries (completeness of the protocol);
anything on soundness or on what a proof shows of the cells.
-/
import Johnson.Desc.K8.Honest.Arrays
import Johnson.Meaning.PlanesLaw
import Johnson.Road.FormsKeysMat
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt partLength)
open Meaning.Planes (entriesOf stretches madeRead madeRead_at)

local notation "readAtP" => VerifiableInference.Desc.First.K8.Honest.readAt
local notation "readOfP" => VerifiableInference.Desc.First.K8.Honest.readOf

/-! ## The numbers of a place, and how the tables lie -/

/-- The numbers of a place p have, matrix by matrix, the columns and rows of the list mats; beyond
the list both count as 0. -/
structure ParFits (p : Par) (mats : Array TMat) : Prop where
  ks : ∀ a, p.ks.getD a 0 = (mats.getD a {}).k
  ms : ∀ a, p.ms.getD a 0 = (mats.getD a {}).m

/-- Numbers of a place with the columns and rows of mats. The other fields, which "readAt" does not
read, are 0 or empty. -/
def parOfMats (mats : Array TMat) : Par :=
  { link := 0, piece := 0, ks := mats.toList.map (·.k), ms := mats.toList.map (·.m), tau := 0,
    asks := [], matsIn := [], readsIn := [] }

/-- "parOfMats mats" has the sizes of mats. -/
theorem parFits_parOfMats (mats : Array TMat) : ParFits (parOfMats mats) mats where
  ks := fun a => by
    show (mats.toList.map (·.k)).getD a 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
      Array.getElem?_toList]
    cases mats[a]? <;> rfl
  ms := fun a => by
    show (mats.toList.map (·.m)).getD a 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getD_eq_getD_getElem?,
      Array.getElem?_toList]
    cases mats[a]? <;> rfl

/-- Every table of funs ends at or below entry n, and no entry lies in two tables. The second clause
is the premise of "reads_meet" (Johnson/Meaning/PlanesLaw.lean), word for word. -/
structure TablesLie (mats : Array TMat) (funs : Array HFun) (n : ℕ) : Prop where
  ends : ∀ f ∈ funs.toList, f.start + entriesOf mats f ≤ n
  apart : ∀ f ∈ funs.toList, ∀ f' ∈ funs.toList, ∀ col < entriesOf mats f,
    ∀ col' < entriesOf mats f', f.start + col = f'.start + col' → f = f'

/-- Two lists of matrices have, number by number, the same rows and the same columns; beyond a list
both count as 0. It is the premise of "readsAll_sizes" (Johnson/Meaning/ReadsLaw.lean), by which
"Fo.ReadsAll" passes from one such list to the other. -/
def SameSizes (mats mats' : Array TMat) : Prop :=
  ∀ a, (mats.getD a {}).m = (mats'.getD a {}).m ∧ (mats.getD a {}).k = (mats'.getD a {}).k

/-- A list has its own sizes. -/
theorem SameSizes.refl (mats : Array TMat) : SameSizes mats mats := fun _ => ⟨rfl, rfl⟩

/-- The condition can be turned round. -/
theorem SameSizes.symm {mats mats' : Array TMat} (h : SameSizes mats mats') :
    SameSizes mats' mats := fun a => ⟨(h a).1.symm, (h a).2.symm⟩

/-- A table has the same number of entries at two lists with the same sizes. -/
theorem entriesOf_same {mats mats' : Array TMat} (h : SameSizes mats mats') (f : HFun) :
    entriesOf mats f = entriesOf mats' f := by
  unfold entriesOf stretches
  rw [(h f.mat).1, (h f.mat).2]

/-- "ParFits" hangs on the rows and columns alone. -/
theorem ParFits.same {p : Par} {mats mats' : Array TMat} (h : SameSizes mats mats')
    (P : ParFits p mats) : ParFits p mats' :=
  ⟨fun a => (P.ks a).trans (h a).2, fun a => (P.ms a).trans (h a).1⟩

/-- "TablesLie" hangs on the rows and columns alone. -/
theorem TablesLie.same {mats mats' : Array TMat} (h : SameSizes mats mats') {funs : Array HFun}
    {n : ℕ} (L : TablesLie mats funs n) : TablesLie mats' funs n := by
  refine ⟨fun f hf => ?_, fun f hf f' hf' col hc col' hc' e => ?_⟩
  · rw [← entriesOf_same h]
    exact L.ends f hf
  · rw [← entriesOf_same h] at hc hc'
    exact L.apart f hf f' hf' col hc col' hc' e

/-- Under "ParFits" the two counts of a table's entries agree. -/
theorem partLength_eq {p : Par} {mats : Array TMat} (P : ParFits p mats) (f : HFun) :
    partLength p f = entriesOf mats f := by
  unfold partLength entriesOf stretches
  rw [P.ks, P.ms]

/-! ## The function with code, case by case -/

/-- Where a table is found. -/
theorem readAt_some {p : Par} {parts : List HFun} (cell : CellsAt) {n : ℕ} {f : HFun}
    (h : (parts.find? fun f =>
      decide (f.start ≤ n) && decide (n < f.start + partLength p f)) = some f) :
    readAtP p parts cell n =
      readOfP f cell ((n - f.start) / (p.ms.getD f.mat 0 / f.len))
        ((n - f.start) % (p.ms.getD f.mat 0 / f.len)) := by
  unfold VerifiableInference.Desc.First.K8.Honest.readAt
  rw [h]

/-- Where none is found. -/
theorem readAt_none {p : Par} {parts : List HFun} (cell : CellsAt) {n : ℕ}
    (h : (parts.find? fun f =>
      decide (f.start ≤ n) && decide (n < f.start + partLength p f)) = none) :
    readAtP p parts cell n = zeroE := by
  unfold VerifiableInference.Desc.First.K8.Honest.readAt
  rw [h]

/-- **Two places' numbers that fit one list of matrices give one vector**, at every list of tables,
all cells and every number. -/
theorem readAt_same {p q : Par} {mats : Array TMat} (P : ParFits p mats) (Q : ParFits q mats)
    (parts : List HFun) (cell : CellsAt) (n : ℕ) :
    readAtP p parts cell n = readAtP q parts cell n := by
  have e1 : ∀ a, p.ks.getD a 0 = q.ks.getD a 0 := fun a => (P.ks a).trans (Q.ks a).symm
  have e2 : ∀ a, p.ms.getD a 0 = q.ms.getD a 0 := fun a => (P.ms a).trans (Q.ms a).symm
  unfold VerifiableInference.Desc.First.K8.Honest.readAt partLength
  simp only [e1, e2]

/-- **Under "ParFits" and "TablesLie", inside a table the vector's entry is that table's**: entry
col of the table f is the entry for column col / s and stretch col % s, where s is the number of
stretches of a column. -/
theorem readAt_in {p : Par} {mats : Array TMat} {funs : Array HFun} {n : ℕ} (P : ParFits p mats)
    (L : TablesLie mats funs n) (cell : CellsAt) {f : HFun} (hf : f ∈ funs.toList) {col : ℕ}
    (hc : col < entriesOf mats f) :
    readAtP p funs.toList cell (f.start + col) =
      readOfP f cell (col / stretches mats f) (col % stretches mats f) := by
  cases h : funs.toList.find? fun f' =>
      decide (f'.start ≤ f.start + col) && decide (f.start + col < f'.start + partLength p f') with
  | none =>
    have h0 := List.find?_eq_none.1 h f hf
    rw [partLength_eq P] at h0
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt] at h0
    have := h0 (Nat.le_add_right _ _)
    omega
  | some f' =>
    have hm := List.mem_of_find?_eq_some h
    have hq := List.find?_some h
    rw [partLength_eq P] at hq
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    have e : f = f' := L.apart f hf f' hm col hc (f.start + col - f'.start) (by omega) (by omega)
    subst e
    rw [readAt_some cell h, Nat.add_sub_cancel_left, P.ms]
    rfl

/-- **Under "ParFits" and "TablesLie" at n, the vector is 0 from entry n on.** -/
theorem readAt_beyond {p : Par} {mats : Array TMat} {funs : Array HFun} {n : ℕ}
    (P : ParFits p mats) (L : TablesLie mats funs n) (cell : CellsAt) {i : ℕ} (hi : n ≤ i) :
    readAtP p funs.toList cell i = zeroE := by
  refine readAt_none cell (List.find?_eq_none.2 fun f hf => ?_)
  rw [partLength_eq P]
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, not_lt]
  intro _
  have := L.ends f hf
  omega

/-! ## Read in a ring -/

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The integers' images in K. -/
def castM (cell : CellsAt) : ℕ → ℕ → ℕ → K := fun m r c => ((cell m r c : ℤ) : K)

/-- A sum that the program forms term by term, read by ρ. -/
theorem val_fold (g : ℕ → E) : ∀ n : ℕ,
    ρ.val ((List.range n).foldl (fun s r => addE s (g r)) zeroE) = ∑ r ∈ range n, ρ.val (g r)
  | 0 => by
    show ρ.val zeroE = _
    rw [ρ.zero, Finset.range_zero, Finset.sum_empty]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
    show ρ.val (addE _ (g n)) = _
    rw [ρ.add, val_fold g n]

/-- **Where ρ reads integers as integers, one entry, read by ρ, is the format's sum**: over the rows
r of stretch b, the weight of r times the cell in row b * len + r of column c. -/
theorem val_readOf (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K)) (f : HFun) (cell : CellsAt)
    (c b : ℕ) :
    ρ.val (readOfP f cell c b) =
      ∑ r ∈ range f.len, ρ.val (f.phi.getD r zeroE) * ((cell f.mat (b * f.len + r) c : ℤ) : K) :=
  (val_fold ρ (fun r => mulE (f.phi.getD r zeroE) (ofInt (cell f.mat (b * f.len + r) c)))
    f.len).trans (Finset.sum_congr rfl fun r _ => by rw [ρ.mul, hZ])

/-- **Under "ParFits" and "TablesLie", where ρ reads integers as integers: read by ρ, the vector
with code is the library's vector made by choice**, at every number i, inside the tables and
outside. -/
theorem val_readAt_eq_madeRead (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K)) {p : Par}
    {mats : Array TMat} {funs : Array HFun} {n : ℕ} (P : ParFits p mats)
    (L : TablesLie mats funs n) (cell : CellsAt) (i : ℕ) :
    ρ.val (readAtP p funs.toList cell i) = madeRead ρ mats funs (castM cell) i := by
  by_cases hex : ∃ x : HFun × ℕ, x.1 ∈ funs.toList ∧ x.2 < entriesOf mats x.1 ∧ i = x.1.start + x.2
  · obtain ⟨⟨f, col⟩, hf, hc, rfl⟩ := hex
    rw [readAt_in P L cell hf hc, madeRead_at L.apart _ hf hc, val_readOf ρ hZ]
    rfl
  · have h0 : readAtP p funs.toList cell i = zeroE := by
      refine readAt_none cell (List.find?_eq_none.2 fun f hf hq => hex ?_)
      rw [partLength_eq P] at hq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
      exact ⟨(f, i - f.start), hf, (by omega : i - f.start < entriesOf mats f),
        (by omega : i = f.start + (i - f.start))⟩
    unfold madeRead
    rw [h0, ρ.zero, dif_neg hex]

/-- In the table of entries "entry", the first n entries of the array iU3 of K3 columns, read by the
rule "Fo.u3Val" (entry i stands in virtual row i / K3 at index i % K3), are the entries
of "readAt" at the list parts and the cells, read by ρ. -/
def SentReads (p : Par) (parts : List HFun) (cell : CellsAt) (entry : ℕ → ℕ → ℕ → K)
    (iU3 K3 n : ℕ) : Prop :=
  ∀ i < n, _root_.Fo.u3Val entry iU3 K3 i = ρ.val (readAtP p parts cell i)

/-- A table of entries that holds the vector in array iU3, and 0 in every other array. -/
def entriesOfReads (p : Par) (parts : List HFun) (cell : CellsAt) (iU3 K3 : ℕ) : ℕ → ℕ → ℕ → K :=
  fun a r x => if a = iU3 then ρ.val (readAtP p parts cell (r * K3 + x)) else 0

/-- "SentReads" holds of "entriesOfReads", at every K3 (0 too) and every n. -/
theorem sentReads_entriesOfReads (p : Par) (parts : List HFun) (cell : CellsAt) (iU3 K3 n : ℕ) :
    SentReads ρ p parts cell (entriesOfReads ρ p parts cell iU3 K3) iU3 K3 n := by
  intro i _
  show (if iU3 = iU3 then ρ.val (readAtP p parts cell (i / K3 * K3 + i % K3)) else 0) = _
  rw [if_pos rfl, Nat.div_add_mod']

/-- One entry of a table, under the premises of "readsAll_sent". -/
theorem sent_at (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K)) {p : Par} {mats : Array TMat}
    {funs : Array HFun} {n : ℕ} (P : ParFits p mats) (L : TablesLie mats funs n) {cell : CellsAt}
    {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ} (S : SentReads ρ p funs.toList cell entry iU3 K3 n)
    {f : HFun} (hf : f ∈ funs.toList) {col : ℕ} (hc : col < entriesOf mats f) :
    _root_.Fo.u3Val entry iU3 K3 (f.start + col) =
      ∑ r ∈ range f.len, ρ.val (f.phi.getD r zeroE) *
        ((cell f.mat (col % stretches mats f * f.len + r) (col / stretches mats f) : ℤ) : K) := by
  have := L.ends f hf
  rw [S _ (by omega), readAt_in P L cell hf hc, val_readOf ρ hZ]

/-- **The law of the reads at the honest vector.** "Honest" says how the vector is made of the
integers; these are any. If p has the sizes of mats, every table of funs ends at or below n and no
entry lies in two of them, ρ reads integers as integers, and the first n entries of array iU3 are
those of "readAt" at funs and the cells, then "Fo.ReadsAll" holds of these entries at the cells'
images in K. -/
theorem readsAll_sent (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K)) {p : Par} {mats : Array TMat}
    {funs : Array HFun} {n : ℕ} (P : ParFits p mats) (L : TablesLie mats funs n) {cell : CellsAt}
    {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ} (S : SentReads ρ p funs.toList cell entry iU3 K3 n) :
    _root_.Fo.ReadsAll ρ mats funs entry iU3 K3 (castM cell) := by
  intro f hf _ col hcol
  have hc : col < entriesOf mats f := hcol
  exact sent_at ρ hZ P L S hf hc

end

/-- **Every table holds what it says of the cells' images**, in the words of
Johnson/Road/FormsKeysMat.lean, under the premises of "readsAll_sent" at the matrices in the
smallness test's numbers tl and the entries of a world W. -/
theorem holds_sent {K : Type} [Field K] (ρ : Reading K) (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    {p : Par} {tl : HTailF2} {funs : Array HFun} {n : ℕ} (P : ParFits p tl.mats)
    (L : TablesLie tl.mats funs n) {cell : CellsAt} {W : World K} {iU3 K3 : ℕ}
    (S : SentReads ρ p funs.toList cell W.entry iU3 K3 n) :
    ∀ Fn ∈ funs, Road.Holds ρ W tl iU3 K3 (castM cell) Fn := by
  intro Fn hFn c sg pos hp
  obtain ⟨_, g2, g3, rfl⟩ := OnBytes.Tie.Pv.Tail.tabAt_some tl hp
  have hs : stretches tl.mats Fn = (tl.mats.getD Fn.mat {}).m / Fn.len := rfl
  rw [← hs] at g3 ⊢
  have hc : c * stretches tl.mats Fn + sg < entriesOf tl.mats Fn := by
    show _ < (tl.mats.getD Fn.mat {}).k * stretches tl.mats Fn
    calc c * stretches tl.mats Fn + sg < (c + 1) * stretches tl.mats Fn := by
          rw [Nat.succ_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ g2
  have e := sent_at ρ hZ P L S (Array.mem_toList_iff.2 hFn) hc
  have d1 : (c * stretches tl.mats Fn + sg) / stretches tl.mats Fn = c := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt g3, Nat.add_zero]
  have d2 : (c * stretches tl.mats Fn + sg) % stretches tl.mats Fn = sg := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt g3]
  rw [d1, d2, ← Nat.add_assoc] at e
  exact e

#print axioms parFits_parOfMats
#print axioms SameSizes.refl
#print axioms SameSizes.symm
#print axioms entriesOf_same
#print axioms ParFits.same
#print axioms TablesLie.same
#print axioms partLength_eq
#print axioms readAt_same
#print axioms readAt_some
#print axioms readAt_none
#print axioms readAt_in
#print axioms readAt_beyond
#print axioms val_fold
#print axioms val_readOf
#print axioms val_readAt_eq_madeRead
#print axioms sentReads_entriesOfReads
#print axioms sent_at
#print axioms readsAll_sent
#print axioms holds_sent

end OnBytes.HonestTrace
