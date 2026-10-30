-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/CellsOfIndexStatement.lean: WHAT THE KIND K11 ASKS OF THE
SCRIPT's CELLS (`K11CellsQ`, TiesAtHeadStatement.lean of this folder) FROM ONE CLAUSE UNDER Vd: AT
EVERY VALID INPUT THE SCRIPT's CELLS AND THE HONEST SIDE's READER OF THE INDEX ARE ONE INDEX's
MATRIX. A STATEMENT ALONE: one definition of a proposition; no definition of another kind. NOTHING
IS PROVED IN THIS FILE, and it is none of the library's goals: a lemma's statement.

THE PREMISE IS THE BODY OF `K4IndexIs` (Johnson/Desc/ProofFile/Honest/K4/Law/IndexIs.lean, another
group of authors', in no sealed library), WRITTEN OUT, under "Vd v →": there is an index i that the
cells at v hold (`Holds`, Johnson/Flat/LedgerClaim.lean), and the reader's entry at every row and
column has the image of i's matrix's entry. It is written out so that none of that group's files
comes to lie beneath this one. THAT THE TWO TEXTS ARE ONE IS HELD BY READING; no file puts it to
Lean.

WHAT IT IS NOT. THE PREMISE IS SHOWN OF NO SCRIPT. General in the Script, the layout, the reader and
Vd; no thread, no state, no head.

NEAR. `wm_of_entries` (IndexIs.lean, the same authors'): the two rewrites by which the reading of
the reader's entry is its image in the extension field stand there too, to another end.

Limits. An implication between two premises' forms. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.TiesAtHeadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsLay)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (CellsM)
open ProofFile.Honest.FirstThread

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def CellsOfIndex : Prop :=
  ∀ (Bk : ProverCoinCounts) (W₀ Rc Tr : Type)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (lay : WsLay) (weights : W₀ → Weights) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop),
    (∀ v, Vd v → ∃ i : Cm.Idx, Holds (Q.cells v) i ∧
      ∀ a b, algebraMap Cb.Gl.F Cb.Gl.E ((weights v.w₀).entry a b) =
        ((i.mat a b : ℤ) : Cb.Gl.E)) →
    K11CellsQ Q lay weights Vd

end ProofFile.Honest.K11
