-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PackedTieBy.lean

TieBy (Johnson/Desc/ProofFile/Honest/K8/SmallLaw.lean) against PackedBy
(Johnson/HonestTrace/PackedTie.lean) and ReadsBy (Johnson/HonestTrace/PackedJoins.lean).

Main theorems:
* "tieBy_iff": TieBy tl A a ↔ PackedBy tl A a ∧ ReadsBy tl A a, for every state tl, every table A
  and all integers a. By Iff.rfl.
* "tieBy_of_reads": under NamesFit X T, MeetsAll X i x T, k < 25, ShapesFit tl Sz.ref k, the premise
  on A of packedBy_of_packedCells (for every μ < tl.NM the table A has at tl.gtTree μ, inside
  Sz.ref.packedShape k μ, the image in E of packedCells Sz.ref (cellOf X T) k μ), and ReadsBy tl A
  (cellsAtOf (cellsC X T) (matsOf X k)): TieBy tl A (cellsAtOf (cellsC X T) (matsOf X k)).

Limits. tieBy_of_reads is packedBy_of_packedCells and its own last premise, laid side by side: it
adds nothing to them. ReadsBy, the second clause of TieBy, is a premise here; no theorem of this
file, of PackedTie.lean or of PackedJoins.lean concludes it. By a reading, ReadsBy tl A a is
TieThird tl (u3Of tl) A a (Johnson/Desc/Kinds/Law/TieReads.lean) letter for letter, and
tieThird_sent (Johnson/HonestTrace/ReadsTie.lean) concludes TieThird from premises on tl's tables
and on row 0 of the array; that join is not made here. Johnson/HonestTrace/PackedTieThird.lean makes
it.
On ReadsBy at a plan's state. At a state whose list funs is empty ReadsBy holds of every table and
all integers. By a reading of HTailF2.shapeF and HTailF2.closeFuns (OnBytes/Model/Tail.lean) the
state in a plan is such: shapeF lays no funs, and the run fills it by closeFuns. So TieBy at
Meaning.tlAt X k would say nothing on the tables of reads: its second clause has content only at a
state whose funs a run has filled. tieBy_of_reads is meant for such a state. No theorem of this file
shows ShapesFit; shapesFit_congr (Johnson/HonestTrace/PackedJoins.lean) carries it between two
states with the same NM, mats and gtTree. If u3Of tl is tl.gtTree μ for some μ < tl.NM, both
premises on A speak of row 0 of that array, at the columns below the matrix's that a table of
tl.funs names; if they ask two values there, no table meets both. u3Of tl is 0 where the state names
no third vector of reads. The limits of Johnson/HonestTrace/PackedJoins.lean hold here. This file
can be built only where the files under Johnson/Desc/K8/Honest/ and Johnson/Desc/ProofFile/Honest/
lie, SmallLaw.lean among them.

Not claimed: TieBy at any table; that a prover's arrays are these; that a verifier accepts.

-/
import Johnson.HonestTrace.PackedJoins
import Johnson.Desc.ProofFile.Honest.K8.SmallLaw

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (HTailF2)
open ProofFile.Honest.K8 (cellsAtOf TieBy)

/-- TieBy tl A a is PackedBy tl A a together with ReadsBy tl A a, for every state, every table and
all integers. It holds by definition. -/
theorem tieBy_iff (tl : HTailF2) (A : ℕ → ℕ → ℕ → Cb.Gl.E) (a : ℕ → ℕ → ℕ → ℤ) :
    TieBy tl A a ↔ PackedBy tl A a ∧ ReadsBy tl A a := Iff.rfl

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **At a state whose funs is empty ReadsBy holds of every table, and the conclusion then says
nothing on the tables of reads**; by a reading of shapeF the state in a plan is such a state. Under
the premises of packedBy_of_packedCells (NamesFit, MeetsAll, k < 25, ShapesFit tl Sz.ref k, and the
premise on A): if besides ReadsBy tl A holds at the cells read through matsOf X k, then TieBy tl A
holds at these cells. ReadsBy is a premise. If u3Of tl is tl.gtTree μ for some μ < tl.NM, both
premises on A speak of row 0 of that array, at the columns below the matrix's that a table of
tl.funs names; if they ask two values there, no table meets both. u3Of tl is 0 where the state names
no third vector of reads. -/
theorem tieBy_of_reads (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    {tl : HTailF2} (hS : ShapesFit tl Sz.ref k) (A : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hA : ∀ μ, μ < tl.NM → ∀ c, c < (Sz.ref.packedShape k μ).2 →
      ∀ i', i' < (Sz.ref.packedShape k μ).1 → A (tl.gtTree.getD μ 0) i' c =
        algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X T) k μ i' c))
    (hR : ReadsBy tl A (cellsAtOf (cellsC X T) (matsOf X k))) :
    TieBy tl A (cellsAtOf (cellsC X T) (matsOf X k)) :=
  (tieBy_iff tl A _).2 ⟨packedBy_of_packedCells N M hk hS A hA, hR⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.tieBy_iff
#print axioms OnBytes.HonestTrace.tieBy_of_reads
