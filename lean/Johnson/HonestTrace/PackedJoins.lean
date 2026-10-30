-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PackedJoins.lean

Joins around the first two clauses of the smallness test's "tie" (K8.TieOf,
Johnson/Desc/First/K8/LawItems.lean) as typed in Johnson/HonestTrace/PackedTie.lean and
Johnson/HonestTrace/PackedTable.lean.

Main definitions: "ReadsBy tl A a" (the third clause of K8.TieOf, with the integers a as a letter) ·
"SameLists s t" (t has s's NM, mats and gtTree) · "ShapesFit tl S l" (for every μ < tl.NM, S.shapeNo
l μ is the rows and columns of entry μ of tl.mats) · "ReadsPackedAt tl A a μ" (ReadsPacked at the
one matrix μ).

Main theorems:
* "tieOf_iff": K8.TieOf tl A ↔ ∃ a, SmallBy tl a ∧ PackedBy tl A a ∧ ReadsBy tl A a. By Iff.rfl.
* "readsPacked_iff_tableOf": under GtOne tl: ReadsPacked tl A a holds exactly if A has tableOf tl
  a's values at the array numbers tl.gtTree μ, μ < tl.NM, inside the packed shapes.
* "smallBy_congr", "packedBy_congr", "gtOne_congr", "tableOf_congr", "shapesFit_congr": under
  SameLists s t, SmallBy, PackedBy, GtOne, tableOf and ShapesFit at t are those at s.
* "readsPacked_of_packedOf": under ShapesFit tl S l: if A has, at tl.gtTree μ and inside
  S.packedShape l μ, the image of packedOf S T l μ, for every μ < tl.NM, then ReadsPacked tl A (T
  l).
* "tableOf_meets": under GtOne tl and ShapesFit tl S l: tableOf tl (T l) has, at tl.gtTree μ and
  inside S.packedShape l μ, the image of packedOf S T l μ, for every μ < tl.NM.
* "packedOf_eq_cellOf": under PartsFit X: packedOf Sz.ref T = packedCells Sz.ref (cellOf X T).
* "packedBy_of_packedCells": under NamesFit, MeetsAll, k < 25 and ShapesFit tl Sz.ref k: if A has,
  at tl.gtTree μ and inside Sz.ref.packedShape k μ, the image of packedCells Sz.ref (cellOf X T) k
  μ, for every μ < tl.NM, then PackedBy tl A (cellsAtOf (cellsC X T) (matsOf X k)).
* "tieOf_of_reads": under the premises of packedBy_of_packedCells and ReadsBy tl A (cellsAtOf
  (cellsC X T) (matsOf X k)): K8.TieOf tl A.
* "packedPlan_owner": under NamesFit and MeetsAll, for member number mu of the list of a segment σ
  of the proof, a the owner's number of that matrix, and two states tl, tl' that give entry mu and
  entry a the same rows: packedPlan tl (T σ's number) mu = packedPlan tl' (T the owner's number) a.
* "readsPackedAt_of_owner": under the same, if rows and columns agree, ReadsPackedAt tl' A' holds at
  the owner's list and a, and A has at tl.gtTree mu, inside the packed shape, what A' has at
  tl'.gtTree a: ReadsPackedAt tl A (T σ's number) mu.

Limits. No theorem but tieOf_iff and tieOf_of_reads ends in more than the first or the second clause
of K8.TieOf. Where one ends in the second, it is at a state tl that is handed in and for a table A
of which a premise already says what it holds.
What is assumed and shown here of no plan, no state of a run and no table of a run: GtOne;
ShapesFit; SameLists; the premise on A; ReadsBy, which is typed here and is the conclusion of
no theorem of this file (ReadsBy tl A a is TieThird tl (u3Of tl) A a of
Johnson/Desc/Kinds/Law/TieReads.lean: readsBy_iff_tieThird,
Johnson/HonestTrace/PackedTieThird.lean); and in readsPackedAt_of_owner the premise that the one
table holds at its array number what the other holds at its own. For that last premise no theorem of
this library is cited; of the library's table of cells (Johnson/Desc/Sound/CellsAt.lean) that file's
own limits say that it is not shown that the numbers which the tie reads off the state's plan are
places of the list by which the table is read.
What the clauses read. The first two clauses, GtOne, tableOf and ShapesFit read NM, mats and gtTree
alone. The third clause reads funs and ix.U too and has no congruence here.
On ReadsBy at a plan's state. At a state whose list funs is empty ReadsBy holds of every table and
all integers. By a reading of HTailF2.shapeF and HTailF2.closeFuns (OnBytes/Model/Tail.lean) the
state in a plan is such: shapeF lays no funs, and the run fills it by closeFuns. So K8.TieOf at
Meaning.tlAt X k would say nothing on the tables of reads: it has content only at a state whose funs
a run has filled. tieOf_of_reads is meant for such a state. No theorem of this file shows ShapesFit;
shapesFit_congr carries it between two states with the same NM, mats and gtTree. Since a run's funs
is not the plan's, the third clause cannot be carried from the one state to the other. ReadsBy may
also be one that no table meets, where two tables of tl.funs reach one entry of U3.
On U3. That the array number of U3 (u3Of tl) is no matrix's array number is shown nowhere here, so
this file does not show that one table can meet the second and the third clause together. Under that
premise and GtOne, tieBy_sent_some (Johnson/HonestTrace/PackedTieThird.lean) has such a table.
On the reader. packedBy_of_packedCells stands at the reader cellOf X T alone. At a borrowed matrix
packedCells asks the reader at the borrower's segment number and label (qa, xbI, xbL); the
conclusion's cellsAtOf reads through matsOf at the owner's number and label. The two meet at this
reader, which answers a borrowed name from the borrower's list, by owner_entries
(Johnson/HonestTrace/DigitsAtTrace.lean); at another reader they need not.
Where GtOne fails the premise on A may be one that no table meets. readsPacked_of_packedOf and
ShapesFit are at any sizes S. No theorem joins readsPackedAt_of_owner with packedBy_of_packedCells
(the packed cells at a sub-proof's own matrices, the owner's table at the borrowed ones). Like
Johnson/HonestTrace/PackedTie.lean this file can be built only where the files under
Johnson/Desc/K8/Honest/ and Johnson/Desc/ProofFile/Honest/ lie.

Not claimed: K8.TieOf at any table; that a prover's arrays are these; that a verifier accepts.

-/
import Johnson.HonestTrace.PackedTable

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (HTailF2 HFun)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf)
open VerifiableInference.Desc.First (K8.TieOf)

/-! ## The three clauses are K8.TieOf -/

/-- The third clause of K8.TieOf, at the integers a: every entry of every table of reads, in the
array U3 of the table A, is the weighted sum of its stretch of a. -/
def ReadsBy (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) : Prop :=
  ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos, tl.tabAt Fn c sg = some pos →
    A (u3Of tl) 0 pos =
      ∑ j ∈ Finset.range Fn.len,
        Model.Reading.gl.val (Fn.phi.getD j zeroE) * ((a Fn.mat (sg * Fn.len + j) c : ℤ) : Cb.Gl.E)

/-- K8.TieOf tl A says that there are integers a with SmallBy, PackedBy and ReadsBy. -/
theorem tieOf_iff (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    K8.TieOf tl A ↔ ∃ a, SmallBy tl a ∧ PackedBy tl A a ∧ ReadsBy tl A a := Iff.rfl

/-! ## Tables that agree with tableOf at the matrices' arrays -/

/-- Under GtOne tl: ReadsPacked tl A a holds exactly if A has tableOf tl a's values at the array
numbers tl.gtTree μ, μ < tl.NM, at the columns below the matrix's columns and the rows below its
packed rows. -/
theorem readsPacked_iff_tableOf {tl : HTailF2} (h : GtOne tl) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (a : ℕ → ℕ → ℕ → ℤ) :
    ReadsPacked tl A a ↔ ∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
      ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
        A (tl.gtTree.getD μ 0) i' c = tableOf tl a (tl.gtTree.getD μ 0) i' c := by
  have e := readsPacked_tableOf h a
  exact ⟨fun H μ hμ c hc i' hi => (H μ hμ c hc i' hi).trans (e μ hμ c hc i' hi).symm,
    fun H μ hμ c hc i' hi => (H μ hμ c hc i' hi).trans (e μ hμ c hc i' hi)⟩

/-! ## What the first two clauses, GtOne, tableOf and ShapesFit read of the state -/

/-- t has s's number of matrices, list of matrices and list of symbol arrays. -/
structure SameLists (s t : HTailF2) : Prop where
  /-- the number of matrices -/
  NM : t.NM = s.NM
  /-- the list of matrices -/
  mats : t.mats = s.mats
  /-- the list of symbol arrays -/
  gtTree : t.gtTree = s.gtTree

/-- Under SameLists s t: SmallBy at t is SmallBy at s. -/
theorem smallBy_congr {s t : HTailF2} (h : SameLists s t) (a : ℕ → ℕ → ℕ → ℤ) :
    SmallBy t a ↔ SmallBy s a := by
  unfold SmallBy
  rw [h.NM, h.mats]

/-- Under SameLists s t: PackedBy at t is PackedBy at s. -/
theorem packedBy_congr {s t : HTailF2} (h : SameLists s t) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (a : ℕ → ℕ → ℕ → ℤ) : PackedBy t A a ↔ PackedBy s A a := by
  unfold PackedBy
  rw [h.NM, h.mats, h.gtTree]

/-- Under SameLists s t: GtOne t is GtOne s. -/
theorem gtOne_congr {s t : HTailF2} (h : SameLists s t) : GtOne t ↔ GtOne s := by
  unfold GtOne
  rw [h.NM, h.gtTree]

/-- Under SameLists s t: tableOf t a is tableOf s a. -/
theorem tableOf_congr {s t : HTailF2} (h : SameLists s t) (a : ℕ → ℕ → ℕ → ℤ) :
    tableOf t a = tableOf s a := by
  funext u i' c
  unfold tableOf packedPlan
  rw [h.NM, h.mats, h.gtTree]

/-! ## From packedOf and packedCells -/

/-- For every μ < tl.NM, S's rows and columns of matrix number μ of segment number l are those of
entry μ of tl's list. -/
def ShapesFit (tl : HTailF2) (S : Sz) (l : ℕ) : Prop :=
  ∀ μ, μ < tl.NM → S.shapeNo l μ = ((tl.mats.getD μ {}).m, (tl.mats.getD μ {}).k)

/-- Under ShapesFit tl S l: if for every μ < tl.NM the table A has at tl.gtTree μ, inside
S.packedShape l μ, the image in E of packedOf S T l μ, then ReadsPacked tl A (T l). -/
theorem readsPacked_of_packedOf {tl : HTailF2} {S : Sz} {l : ℕ} (hS : ShapesFit tl S l)
    (T : ℕ → ℕ → ℕ → ℕ → ℤ) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (S.packedShape l μ).2 → ∀ i', i' < (S.packedShape l μ).1 →
      A (tl.gtTree.getD μ 0) i' c = algebraMap Cb.Gl.F Cb.Gl.E (packedOf S T l μ i' c)) :
    ReadsPacked tl A (T l) := by
  intro μ hμ c hc i' hi
  have e := hS μ hμ
  have e1 : (S.shapeNo l μ).1 = (tl.mats.getD μ {}).m := by rw [e]
  have e2 : (S.shapeNo l μ).2 = (tl.mats.getD μ {}).k := by rw [e]
  have hc' : c < (S.shapeNo l μ).2 := by rw [e2]; exact hc
  rw [packedPlan_eq_packedOf tl S T l μ e1 hc' i']
  refine hA μ hμ c hc' i' ?_
  show i' < Alg.symRows (S.shapeNo l μ).1
  rw [e1]
  exact hi

/-- Under SameLists s t: ShapesFit at t is ShapesFit at s. -/
theorem shapesFit_congr {s t : HTailF2} (h : SameLists s t) (S : Sz) (l : ℕ) :
    ShapesFit t S l ↔ ShapesFit s S l := by
  unfold ShapesFit
  rw [h.NM, h.mats]

/-- Under GtOne tl and ShapesFit tl S l: for every μ < tl.NM the table tableOf tl (T l) has at
tl.gtTree μ, inside S.packedShape l μ, the image in E of packedOf S T l μ: the premise on A of
readsPacked_of_packedOf holds of it. -/
theorem tableOf_meets {tl : HTailF2} {S : Sz} {l : ℕ} (hG : GtOne tl) (hS : ShapesFit tl S l)
    (T : ℕ → ℕ → ℕ → ℕ → ℤ) : ∀ μ, μ < tl.NM → ∀ c, c < (S.packedShape l μ).2 →
      ∀ i', i' < (S.packedShape l μ).1 → tableOf tl (T l) (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedOf S T l μ i' c) := by
  intro μ hμ c hc i' _
  have e1 : (S.shapeNo l μ).1 = (tl.mats.getD μ {}).m := by rw [hS μ hμ]
  unfold tableOf
  rw [find_gt hG hμ]
  show algebraMap Cb.Gl.F Cb.Gl.E (packedPlan tl (T l) μ i' c) = _
  rw [packedPlan_eq_packedOf tl S T l μ e1 hc i']

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under PartsFit X: packedOf Sz.ref T is packedCells Sz.ref of the reader cellOf X T, at all
numbers, rows and columns. -/
theorem packedOf_eq_cellOf (P : PartsFit X) (T : Tr) (l mu i' c : ℕ) :
    packedOf Sz.ref T l mu i' c = packedCells Sz.ref (cellOf X T) l mu i' c := by
  refine packedOf_eq_cells Sz.ref T (cellOf X T) (fun σ μ a hσ hμ r c => ?_) l mu i' c
  have hσ' : σ.Below 12 := hσ
  have hμ' : MatName.no? 3 1 1 4 σ μ = some a := by
    have : (if σ.Below 12 then MatName.no? 3 1 1 4 σ μ else none) = some a := hμ
    rwa [if_pos hσ'] at this
  exact cellOf_label P T hσ' hμ' r c

/-- Under NamesFit, MeetsAll, k < 25 and ShapesFit tl Sz.ref k: if for every μ < tl.NM the table A
has at tl.gtTree μ, inside Sz.ref.packedShape k μ, the image in E of packedCells Sz.ref (cellOf X T)
k μ, then PackedBy tl A (cellsAtOf (cellsC X T) (matsOf X k)): the second clause of K8.TieOf alone.
At a borrowed matrix packedCells asks the reader at the number k and the borrower's label, the
conclusion's cellsAtOf at the owner's number and label. -/
theorem packedBy_of_packedCells (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref k) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape k μ).2 →
      ∀ i', i' < (Sz.ref.packedShape k μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c)) :
    PackedBy tl A (cellsAtOf (cellsC X T) (matsOf X k)) :=
  packedBy_trace N M hk tl A (readsPacked_of_packedOf hS T A fun μ hμ c hc i' hi => by
    rw [packedOf_eq_cellOf N.parts T]
    exact hA μ hμ c hc i' hi)

/-- Under the premises of packedBy_of_packedCells: if besides ReadsBy tl A holds at the cells read
through matsOf X k, then K8.TieOf tl A. ReadsBy is a premise; at a state whose funs is empty, as by
a reading of shapeF the state in a plan is, it holds of every table, and the conclusion then says
nothing on the tables of reads. If u3Of tl is tl.gtTree μ for some μ < tl.NM, both premises on A
speak of row 0 of that array, at the columns below the matrix's that a table of tl.funs names; if
they ask two values there, no table meets both. u3Of tl is 0 where the state names no third vector
of reads. -/
theorem tieOf_of_reads (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref k) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape k μ).2 →
      ∀ i', i' < (Sz.ref.packedShape k μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c))
    (hR : ReadsBy tl A (cellsAtOf (cellsC X T) (matsOf X k))) : K8.TieOf tl A :=
  (tieOf_iff tl A).2 ⟨_, smallBy_trace N M hk tl, packedBy_of_packedCells N M hk hS A hA, hR⟩

/-! ## A borrowed matrix -/

/-- ReadsPacked at one matrix. -/
def ReadsPackedAt (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) (μ : ℕ) : Prop :=
  ∀ c, c < (tl.mats.getD μ {}).k → ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
    A (tl.gtTree.getD μ 0) i' c = algebraMap Cb.Gl.F Cb.Gl.E (packedPlan tl a μ i' c)

/-- ReadsPacked is ReadsPackedAt at every μ < tl.NM. -/
theorem readsPacked_iff_at (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) :
    ReadsPacked tl A a ↔ ∀ μ, μ < tl.NM → ReadsPackedAt tl A a μ := Iff.rfl

/-- Under NamesFit and MeetsAll, for a segment σ of the proof, member number mu of its list, and a
the owner's number of that matrix: if tl gives entry mu the rows that tl' gives entry a, packedPlan
tl at σ's list and mu is packedPlan tl' at the owner's list and a, at every row and column. Both are
terms of T; nothing is said on committed arrays. -/
theorem packedPlan_owner (N : NamesFit X T) (M : MeetsAll X i x T) {σ : Seg} (hσ : σ.Below 12)
    {mu : ℕ} {μ : MatName} (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) {a : ℕ}
    (ha : MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a)
    (tl tl' : HTailF2) (hm : (tl.mats.getD mu {}).m = (tl'.mats.getD a {}).m) (i' c : ℕ) :
    packedPlan tl (T (σ.no 12)) mu i' c =
      packedPlan tl' (T ((Sz.ref.owner σ μ).1.no 12)) a i' c := by
  have ent : ∀ r, T ((Sz.ref.owner σ μ).1.no 12) a r c = T (σ.no 12) mu r c := fun r => by
    obtain ⟨a', -, on', oe⟩ := owner_entries N M hσ hμ r c
    obtain rfl : a = a' := Option.some.inj (ha.symm.trans on')
    exact oe
  unfold packedPlan
  rw [hm]
  simp only [ent]

/-- Under the premises of packedPlan_owner, if the columns agree too: if ReadsPackedAt tl' A' holds
at the owner's list and a, and the table A has at tl.gtTree mu, inside the packed shape, what A' has
at tl'.gtTree a, then ReadsPackedAt tl A holds at σ's list and mu. That the one table holds what the
other holds is a premise: no theorem of this library is cited for it. -/
theorem readsPackedAt_of_owner (N : NamesFit X T) (M : MeetsAll X i x T) {σ : Seg}
    (hσ : σ.Below 12) {mu : ℕ} {μ : MatName} (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) {a : ℕ}
    (ha : MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a)
    (tl tl' : HTailF2) (hm : (tl.mats.getD mu {}).m = (tl'.mats.getD a {}).m)
    (hk : (tl.mats.getD mu {}).k = (tl'.mats.getD a {}).k) (A A' : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hO : ReadsPackedAt tl' A' (T ((Sz.ref.owner σ μ).1.no 12)) a)
    (hB : ∀ c, c < (tl.mats.getD mu {}).k → ∀ i', i' < Alg.symRows (tl.mats.getD mu {}).m →
      A (tl.gtTree.getD mu 0) i' c = A' (tl'.gtTree.getD a 0) i' c) :
    ReadsPackedAt tl A (T (σ.no 12)) mu := by
  intro c hc i' hi
  rw [hB c hc i' hi, packedPlan_owner N M hσ hμ ha tl tl' hm i' c]
  exact hO c (by rw [← hk]; exact hc) i' (by rw [← hm]; exact hi)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.tieOf_iff
#print axioms OnBytes.HonestTrace.readsPacked_iff_tableOf
#print axioms OnBytes.HonestTrace.smallBy_congr
#print axioms OnBytes.HonestTrace.packedBy_congr
#print axioms OnBytes.HonestTrace.gtOne_congr
#print axioms OnBytes.HonestTrace.tableOf_congr
#print axioms OnBytes.HonestTrace.readsPacked_of_packedOf
#print axioms OnBytes.HonestTrace.shapesFit_congr
#print axioms OnBytes.HonestTrace.tableOf_meets
#print axioms OnBytes.HonestTrace.tieOf_of_reads
#print axioms OnBytes.HonestTrace.packedOf_eq_cellOf
#print axioms OnBytes.HonestTrace.packedBy_of_packedCells
#print axioms OnBytes.HonestTrace.readsPacked_iff_at
#print axioms OnBytes.HonestTrace.packedPlan_owner
#print axioms OnBytes.HonestTrace.readsPackedAt_of_owner
