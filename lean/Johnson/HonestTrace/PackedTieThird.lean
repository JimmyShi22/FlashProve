-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PackedTieThird.lean

Both clauses of TieBy (Johnson/Desc/ProofFile/Honest/K8/SmallLaw.lean), each from a premise that
says what a table A holds: the packed arrays at the matrices' array numbers, and the vector of reads
in row 0 of the array u3Of tl.

Below, "the five premises" are those of packedBy_of_packedCells
(Johnson/HonestTrace/PackedJoins.lean): NamesFit X T, MeetsAll X i x T, k < 25, ShapesFit tl Sz.ref
k, and the premise on A of packedBy_of_packedCells (for every μ < tl.NM the table A has at tl.gtTree
μ, inside Sz.ref.packedShape k μ, the image in E of packedCells Sz.ref (cellOf X T) k μ). a_k stands
for cellsAtOf (cellsC X T) (matsOf X k). "read" is: by Reading.gl.

Main theorems:
* "readsBy_iff_tieThird": ReadsBy tl A a ↔ TieThird tl (u3Of tl) A a (TieThird:
  Johnson/Desc/Kinds/Law/TieReads.lean), for every state, every table and all integers. By Iff.rfl.
* "tieBy_of_tieThird": under the five premises and TieThird tl (u3Of tl) A a_k: TieBy tl A a_k.
* "tieBy_sent": under the five premises and those of tieThird_sent
  (Johnson/HonestTrace/ReadsTie.lean) at u3Of tl and a_k: ParFits p tl.mats; TablesLie tl.mats
  tl.funs n; for every j < n, A (u3Of tl) 0 j is readAt p tl.funs.toList a_k j, read: TieBy tl A
  a_k.
* "tieBy_head": the same at k = 24 with the premises of tieThird_head
  (Johnson/HonestTrace/ReadsHead.lean): the description's tables returns t; tl has the plan's list
  of matrices and t's tables; row 0 of the array holds u3Head, read, below the plan's number of
  reads.
* "tieBy_hear": the same at k = 2 g, g < 12, with the premises of tieThird_hear
  (Johnson/HonestTrace/ReadsLayers.lean): hearFl returns o; tl's list has the sizes of the group's
  own and tl's tables are o's; ParFits p tl.mats; row 0 of the array holds readAt p o.funs.toList
  a_k, read, below the plan's number of reads.
* "table_of_both": under GtOne tl, and if no tl.gtTree μ, μ < tl.NM, is u3Of tl: for all values p
  and v there is a table A with A (tl.gtTree μ) i' c = p μ i' c for every μ < tl.NM, and A (u3Of tl)
  0 j = v j.
* "tieBy_sent_some": under NamesFit, MeetsAll, k < 25, ShapesFit tl Sz.ref k, GtOne tl, no tl.gtTree
  μ being u3Of tl, ParFits p tl.mats and TablesLie tl.mats tl.funs n: there is a table A that holds
  the packed cells at the matrices' arrays and the vector of reads in row 0 of the array u3Of tl,
  and TieBy tl A a_k holds of it.

Limits. The proofs of the first five are one line each: they add nothing to tieBy_of_reads
(Johnson/HonestTrace/PackedTieBy.lean) and to tieThird_sent, tieThird_head, tieThird_hear. What A
holds is a premise, shown here of no table of a run. tieBy_sent_some shows that the two premises on
A can be met together under its two premises on array numbers; that no tl.gtTree μ is u3Of tl is
shown in this file of no state (u3Of tl is 0 where the state names no third vector of reads). It is
a part of the first clause of the library's test layTest (OnBytes/Tie/Pv/Tail/LayAt.lean), letter
for letter; by that file's own limits the test's result at a sub-proof is a run, no proof term.
Without it: if u3Of tl is tl.gtTree μ for some μ < tl.NM, both premises on A speak of row 0 of that
array, and if they ask two values there, no table meets both. No theorem of this file shows
ShapesFit, GtOne, ParFits or TablesLie; shapesFit_congr and gtOne_congr
(Johnson/HonestTrace/PackedJoins.lean) carry the first two between states with the same NM, mats and
gtTree. parFits_parOfMats (Johnson/HonestTrace/Reads.lean) has ParFits at p := parOfMats tl.mats; at
parOfTail tl (Johnson/Desc/ProofFile/Honest/K8/Digits.lean), which has the same two lists of columns
and rows, no theorem of this file or of the files named has it. At a state whose funs is empty the
second clause holds of every table. At a state with NM = 0 both clauses hold of every table. At an
odd k (an attention sub-proof) tieBy_of_tieThird, tieBy_sent and tieBy_sent_some hold as at every k
< 25, with TablesLie as a premise; no theorem of this file or of the files named shows TablesLie of
an attention sub-proof's tables, as tablesLie_head and tablesLie_hear do of the head's and a
group's. The limits of the files named hold here. This file can be built only where the files under
Johnson/Desc/K8/Honest/ and Johnson/Desc/ProofFile/Honest/ lie, SmallLaw.lean among them.

Not claimed: the other premises of Spec.small_of_honest (SmallLaw.lean), which takes TieBy as a
premise, ZzBy at the same table among them; that a prover's arrays are these; that a verifier
accepts.

-/
import Johnson.HonestTrace.PackedTieBy
import Johnson.HonestTrace.ReadsLayers
import Johnson.HonestTrace.ReadsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (HTailF2 Reading Fork)
open OnBytes.K.Kc (Tape)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf TieBy)
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.Kinds.Head.Law (TieThird)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open OnBytes.Desc.First.K4 (hearFl)

local notation "readAtP" => VerifiableInference.Desc.First.K8.Honest.readAt

/-- ReadsBy tl A a is TieThird tl (u3Of tl) A a, for every state, every table and all integers. It
holds by definition. -/
theorem readsBy_iff_tieThird (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) :
    ReadsBy tl A a ↔ TieThird tl (u3Of tl) A a := Iff.rfl

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- Under the premises of packedBy_of_packedCells (NamesFit, MeetsAll, k < 25, ShapesFit tl Sz.ref
k, and the premise on A): if besides TieThird tl (u3Of tl) A holds at the cells read through matsOf
X k, then TieBy tl A holds at these cells. -/
theorem tieBy_of_tieThird (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref k) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape k μ).2 →
      ∀ i', i' < (Sz.ref.packedShape k μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c))
    (hT : TieThird tl (u3Of tl) A (cellsAtOf (cellsC X T) (matsOf X k))) :
    TieBy tl A (cellsAtOf (cellsC X T) (matsOf X k)) :=
  tieBy_of_reads N M hk hS A hA hT

/-- Under the premises of packedBy_of_packedCells, ParFits p tl.mats and TablesLie tl.mats tl.funs
n: if for every j < n the table A has in row 0 of the array u3Of tl, at j, entry j of readAt p
tl.funs.toList at the cells read through matsOf X k, read, then TieBy tl A holds at these cells. If
u3Of tl is tl.gtTree μ for some μ < tl.NM the two premises on A may be met by no table. -/
theorem tieBy_sent (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref k) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape k μ).2 →
      ∀ i', i' < (Sz.ref.packedShape k μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c))
    {p : Par} {n : ℕ} (P : ParFits p tl.mats) (L : TablesLie tl.mats tl.funs n)
    (S : ∀ j < n, A (u3Of tl) 0 j =
      Reading.gl.val (readAtP p tl.funs.toList (cellsAtOf (cellsC X T) (matsOf X k)) j)) :
    TieBy tl A (cellsAtOf (cellsC X T) (matsOf X k)) :=
  tieBy_of_tieThird N M hk hS A hA (tieThird_sent P L S)

/-- The head. Under the premises of packedBy_of_packedCells at k = 24: if the description's tables
returns t, tl has the plan's list of matrices and t's tables, and for every j below the plan's
number of reads A has in row 0 of the array u3Of tl, at j, entry j of u3Head at the cells read
through matsOf X 24, read: TieBy tl A holds at these cells. If u3Of tl is tl.gtTree μ for some μ <
tl.NM the two premises on A may be met by no table. -/
theorem tieBy_head (N : NamesFit X T) (M : MeetsAll X i x T)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref 24) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape 24 μ).2 →
      ∀ i', i' < (Sz.ref.packedShape 24 μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) 24 μ i' c))
    {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2} {cov : Model.Head.Covered}
    {y : Model.Head.Heard} {t : Model.Head.Tables} (e : ReadsQuiet.tables h L hp cov y = .ok t)
    (hm : tl.mats = hp.tl.mats) (hfuns : tl.funs = t.funs)
    (S : ∀ j < hp.nU.getD 2 0, A (u3Of tl) 0 j =
      Reading.gl.val (u3Head h L hp cov y (cellsAtOf (cellsC X T) (matsOf X 24)) j)) :
    TieBy tl A (cellsAtOf (cellsC X T) (matsOf X 24)) :=
  tieBy_of_tieThird N M (by decide) hS A hA (tieThird_head e hm hfuns S)

/-- A group of layers, g < 12. Under the premises of packedBy_of_packedCells at k = 2 g: if hearFl
returns o, tl's list of matrices has the sizes of the group's own, tl's tables are o's, ParFits p
tl.mats holds, and for every j below the plan's number of reads A has in row 0 of the array u3Of tl,
at j, entry j of readAt p o.funs.toList at the cells read through matsOf X (2 g), read: TieBy tl A
holds at these cells. If u3Of tl is tl.gtTree μ for some μ < tl.NM the two premises on A may be met
by no table. -/
theorem tieBy_hear (N : NamesFit X T) (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref (2 * g)) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape (2 * g) μ).2 →
      ∀ i', i' < (Sz.ref.packedShape (2 * g) μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) (2 * g) μ i' c))
    {P : Model.Layer.Pub} {hp : Model.Layer.HPlan2} {fo : Model.Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Model.Layer.Own} (hh : hearFl P hp g fo F t = some (o, F', t'))
    (hm : SameSizes (P.tails.getD g {}).mats tl.mats) (hfuns : tl.funs = o.funs) {p : Par}
    (Pf : ParFits p tl.mats)
    (S : ∀ j < hp.nU.getD 2 0, A (u3Of tl) 0 j =
      Reading.gl.val (readAtP p o.funs.toList (cellsAtOf (cellsC X T) (matsOf X (2 * g))) j)) :
    TieBy tl A (cellsAtOf (cellsC X T) (matsOf X (2 * g))) :=
  tieBy_of_tieThird N M (by omega) hS A hA (tieThird_hear hh hm hfuns Pf S)

/-- Under GtOne tl, and if no tl.gtTree μ, μ < tl.NM, is u3Of tl: for all values p and v there is a
table that has p μ at the array tl.gtTree μ, for every μ < tl.NM, and v in row 0 of the array u3Of
tl. -/
theorem table_of_both {tl : HTailF2} (hG : GtOne tl)
    (hU : ∀ μ, μ < tl.NM → tl.gtTree.getD μ 0 ≠ u3Of tl) (p : ℕ → ℕ → ℕ → Cb.Gl.E)
    (v : ℕ → Cb.Gl.E) :
    ∃ A : ℕ → ℕ → ℕ → Cb.Gl.E,
      (∀ μ, μ < tl.NM → ∀ i' c, A (tl.gtTree.getD μ 0) i' c = p μ i' c) ∧
        ∀ j, A (u3Of tl) 0 j = v j := by
  refine ⟨fun t i' c => if t = u3Of tl then v c else
    match (List.range tl.NM).find? fun ν => tl.gtTree.getD ν 0 == t with
    | some ν => p ν i' c
    | none => 0, fun μ hμ i' c => ?_, fun j => if_pos rfl⟩
  show (if tl.gtTree.getD μ 0 = u3Of tl then v c else
    match (List.range tl.NM).find? fun ν => tl.gtTree.getD ν 0 == tl.gtTree.getD μ 0 with
    | some ν => p ν i' c
    | none => 0) = p μ i' c
  rw [if_neg (hU μ hμ), find_gt hG hμ]

/-- Under NamesFit, MeetsAll, k < 25, ShapesFit tl Sz.ref k, GtOne tl, no tl.gtTree μ (μ < tl.NM)
being u3Of tl, ParFits p tl.mats and TablesLie tl.mats tl.funs n: there is a table that holds the
packed cells at the matrices' arrays and the vector of reads in row 0 of the array u3Of tl; TieBy
holds of it at the cells read through matsOf X k. -/
theorem tieBy_sent_some (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref k) (hG : GtOne tl)
    (hU : ∀ μ, μ < tl.NM → tl.gtTree.getD μ 0 ≠ u3Of tl)
    {p : Par} {n : ℕ} (P : ParFits p tl.mats) (L : TablesLie tl.mats tl.funs n) :
    ∃ A : ℕ → ℕ → ℕ → Cb.Gl.E,
      (∀ μ, μ < tl.NM → ∀ i' c, A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c)) ∧
      (∀ j, A (u3Of tl) 0 j =
        Reading.gl.val (readAtP p tl.funs.toList (cellsAtOf (cellsC X T) (matsOf X k)) j)) ∧
      TieBy tl A (cellsAtOf (cellsC X T) (matsOf X k)) := by
  obtain ⟨A, h1, h2⟩ := table_of_both hG hU
    (fun μ i' c => algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c))
    fun j => Reading.gl.val (readAtP p tl.funs.toList (cellsAtOf (cellsC X T) (matsOf X k)) j)
  exact ⟨A, h1, h2, tieBy_sent N M hk hS A (fun μ hμ c _ i' _ => h1 μ hμ i' c) P L
    fun j _ => h2 j⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.readsBy_iff_tieThird
#print axioms OnBytes.HonestTrace.tieBy_of_tieThird
#print axioms OnBytes.HonestTrace.tieBy_sent
#print axioms OnBytes.HonestTrace.tieBy_head
#print axioms OnBytes.HonestTrace.tieBy_hear
#print axioms OnBytes.HonestTrace.table_of_both
#print axioms OnBytes.HonestTrace.tieBy_sent_some
