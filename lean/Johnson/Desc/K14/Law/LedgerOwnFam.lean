-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerOwnFam.lean: THE LEDGER's TWO LETTERS r9 | r10 (its own error bounds at
the two
proximity tests, the sub-protocols at places 9 and 10 of the shared chain) LAID AS ONE FAMILY OF THE
PROXIMITY TEST's FILES' OWN PAIR: then herrA | herrB are no premises, and eA | εtA | eB | εtB keep
the
values at which these files pay hleA | hleB, hAA | hAB and b9 | b10.
  ownFam π r      at no round: the cap (of nothing) · at d :: dt: (batV0 π r * ‹the first round's
  weight›,
                  errJ π r dt)
  ownFam_cons     its value at d :: dt, by rfl
  herr_ownFam     ds = d :: dt ⊢ HEq (ownFam π r ds) ((batV0 π r * (bsRound .two d.entry d.kind).w,
                  errJ π r dt) : Err …): herrA at r9 := ownFam πA rA, herrB at r10 := ownFam πB rB
  heads_ownFam    errHead | errTail (Johnson/Desc/K14/Law/LedgerErrByMake.lean) of it ARE that pair:
  rfl
WHY THIS FAMILY AND NOT THE CAP. r9 | r10 stand in no conclusion of the ledger: its end speaks of
the
pieces, whose own error bounds are the cut's cap (hcap); r9 | r10 are asked only to be below 2⁻¹ ^
128.

What is not claimed. That the piece's written rounds are d :: dt (NineFacts.ds |
TenFacts.ds). That the pair is below 2⁻¹ ^ 128. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerErrByMake
import Johnson.Desc.K12.Coin.GameJ
import Johnson.Desc.K12.Law.BatPriceOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.K12.Coin
open H2K.Pub (batV0)

/-- The proximity test's own error bounds, round by round, as a family over the written rounds. -/
def ownFam (π : P12) (r : Fmt.M1.Stage → ℕ) : (ds : List RDT) → Err (uLT (ckP .two) ds)
  | [] => Err.cap 128 (uLT (ckP .two) [])
  | d :: dt => (batV0 π r * (bsRound .two d.entry d.kind).w, errJ π r dt)

theorem ownFam_cons (π : P12) (r : Fmt.M1.Stage → ℕ) (d : RDT) (dt : List RDT) :
    ownFam π r (d :: dt) = ((batV0 π r * (bsRound .two d.entry d.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (d :: dt))) := rfl

/-- **herrA | herrB at this family.** -/
theorem herr_ownFam (π : P12) (r : Fmt.M1.Stage → ℕ) {ds : List RDT} {d : RDT} {dt : List RDT}
    (h : ds = d :: dt) :
    HEq (ownFam π r ds) ((batV0 π r * (bsRound .two d.entry d.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (d :: dt))) := by
  subst h
  rfl

theorem heads_ownFam (π : P12) (r : Fmt.M1.Stage → ℕ) (d : RDT) (dt : List RDT) :
    errHead (ownFam π r (d :: dt)) = batV0 π r * (bsRound .two d.entry d.kind).w ∧
      errTail (ownFam π r (d :: dt)) = errJ π r dt := ⟨rfl, rfl⟩

end Desc.K14.Law
