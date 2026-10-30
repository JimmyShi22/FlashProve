-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/Kind24AtMg.lean: IN THE GOALS' SCOPE, AT THE SECOND HASH FUNCTION: THE BUILT SEGMENT
NUMBER 24 OF THE PROOF FILE's PUBLIC PART HAS KIND 2 (the output head's). Two theorems. A joining:
asked as the premise hK of `headSpots_of_fit`
(Johnson/LPFE1R/HeadSpotsAt.lean).
  `kind24_of_ground`: from `IM.ground_named` (Johnson/IMR/PureJoin.lean: the
  blank letters' segment 24 has kind 2) and `blank_built` (Johnson/IMR/OwnSeat.lean: the blank
  letters' segments are the public part's, each with its routine exchanged): ∀ X,
  `Z.p.built.links[24]? = some X → X.kind = 2`.
  `AtMg.kind24`: the same at the head, with no premise beside it.
Limits. At the second hash function alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5T.FenceAtMg
import Johnson.IMR.PureJoin
import Johnson.IMR.OwnSeat
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

/-- The public part's segment 24 has the blank letters' segment's kind. -/
theorem kind24_of_ground {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G₀ : ProofFile.Ground} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ X, Z.p.built.links[24]? = some X → X.kind = 2 := by
  intro X hX
  obtain ⟨-, l, hl, hk, -⟩ := IM.ground_named hS hR hZ hG
  obtain ⟨ls, e⟩ := _root_.Meaning.K2.blank_built hG
  rw [e, Array.getElem?_zipWith, hX] at hl
  cases hx : ls[24]? with
  | none =>
    rw [hx] at hl
    cases hl
  | some y =>
    rw [hx] at hl
    obtain rfl := Option.some.inj hl
    exact hk

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **At the head.** -/
theorem AtMg.kind24 (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∀ X, Zp.p.built.links[24]? = some X → X.kind = 2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact kind24_of_ground h.scope h.reads O.pub O.blank

end P5J

#print axioms P5J.kind24_of_ground
#print axioms P5J.AtMg.kind24
