-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4MeansFields.lean: THE SEVEN EQUATIONS OF `K4Fields` (K4AtMg.lean) AND THE TWO IFFS
ON left | leftOn THAT `k4Front_at` TAKES ARE AMONG THE EQUATIONS OF `K4Means` (K4Means.lean).
Statements and proofs: projections. A file of its own, so that K4Means.lean stays free of K4's road.

Limits. Nothing new is said. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.
-/
import Johnson.Road.K4.K4Means
import Johnson.Road.K4.K4AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt)
open VerifiableInference.Desc.Sound (MsgT)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X}

theorem K4Means.fields (E : K4Means Mg D) : K4Fields Mg D.cs D.G D.smp D.ms D.nsOf D.links :=
  ⟨E.held, E.shown, E.noColl, E.ledger, E.freeAbove, E.unheard, E.look⟩

theorem K4Means.eL (E : K4Means Mg D) (Z : P) (m : ℕ) (s : S) :
    Mg.pubP (.left m) (Z, s) ↔ k3LeftItemAt X m s := by rw [E.left]

theorem K4Means.eO (E : K4Means Mg D) (Z : P) (m : ℕ) (s : S) :
    Mg.pubP (.leftOn m) (Z, s) ↔ k3LeftOnItemAt X m s := by rw [E.leftOn]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.K4Means.fields
