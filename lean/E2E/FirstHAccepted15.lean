-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHAccepted15.lean: member 15 of `T₁` is accepted: `acceptedS_ties` (E2E/KeyRangesWholeS.lean)
at the two ties, where the first chain's test half is the job's.

  `find_rng`: the search at the test's place.
  `accepted_15`: `AcceptedS` at 15, at every letter `Said` and every fall.

Limits. `hrng`: the letter K.rng is `proverSideOfProximityTest` of the job: a premise, by rfl at the sheet if the sheet
lays it so; not tried. Nothing on the other four at 15, nothing on any property.
-/
import E2E.FirstHRangeClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.FirstH
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces Xi)
open AtPublicFiles.KeyThread (rangesTestJob acceptedS_ties)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12 (proverSideOfProximityTest)

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill (keyBook K₀) W₀ Rc} {w₀ : W₀}
  {rc : Rc} {x : Xi} {Z : PublicFiles}

/-- The search at the test's place. -/
theorem find_rng (h : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == (⟨1, none, 5, .K12⟩ : Place)) = some K.rng := by
  have e1 : ((ProofFile.Honest.K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X').place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.idx.P.place == _) = false
    rw [h.idx]
    decide
  have e2 : ((ProofFile.Honest.K1.proverSideOfSending K.msg : Placed (In1 W₀ Rc) (In1 W₀ Rc) X').place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.msg.P.place == _) = false
    rw [h.msg]
    decide
  have e3 : ((ProofFile.Honest.K3.proverSideOfLookupInChain (V₁ := In1 W₀ Rc) (X₁ := X')
      (ProofFile.Honest.K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0).place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.look0.place == _) = false
    rw [h.look0]
    decide
  have e4 : ((ProofFile.Honest.K3.proverSideOfLookupInChain (V₁ := In1 W₀ Rc) (X₁ := X')
      (ProofFile.Honest.K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1).place ==
      (⟨1, none, 5, .K12⟩ : Place)) = false := by
    show (K.look1.place == _) = false
    rw [h.look1]
    decide
  have e5 : (K.rng.place == (⟨1, none, 5, .K12⟩ : Place)) = true := by
    rw [h.rng]
    decide
  show List.find? _ (_ :: _ :: _ :: _ :: K.rng :: _) = _
  simp only [List.find?, e1, e2, e3, e4, e5]

/-- **Member 15 is accepted.** -/
theorem accepted_15 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hrng : K.rng = proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0))
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall 15 := by
  have hhalf : ((keyProver K).first.find? fun g =>
      g.place == (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0)) := by
    have e : (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0).p.place =
        (⟨1, none, 5, .K12⟩ : Place) := p12_place _ _
    rw [e, ← hrng]
    exact find_rng hp.places
  exact acceptedS_ties Xs N Pl (matrixEntryOf f) (multiplicitiesGroups Xs) 0 (Fl Xs N Pl K f Q x) w₀ rc x
    (keyProver K).first (tbH Xs N Pl K f Q) hK hs scope Said hhalf
    (fun _ _ _ _ c hT hc => wit_is_job hs scope hK hp (msg_zero hs scope hp) (msg_shape hs scope hp)
      (carry_fits hs scope hK hp) hT.1 c hc)
    (fun k _ m _ _ => tb_is_sent hp k m) fall

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.find_rng
#print axioms AtPublicFiles.FirstH.accepted_15
