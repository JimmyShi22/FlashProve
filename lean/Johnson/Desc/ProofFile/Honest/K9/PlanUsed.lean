-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/PlanUsed.lean: A FEED-FORWARD PLAN's NUMBER OF USED SLOTS IS ITS NUMBER OF SLOTS: A
PUBLIC FACT, BY THE PLAN's MAKE: for the premise hused of `filled_le_digits_end` (Honest/K9/LayNumbers.lean). Statements
and proofs; no definition; no state stands in them; no goal is stated. Over the sealed library alone.
  `planG_used`   what `Layer.planG` returns has used = ns: the maker lays both from one number
      (OnBytes/Model/LayerPlan.lean): the skeleton of the sealed `planG_slots`
      (Johnson/Road/K4/Riders/LookInByMake.lean), each arm closed by unfolding · `plansG_used`: the same of each member
      of the list of all groups' plans: the sealed `OnBytes.Road.plansFrom_at` · **`ground_used`**: the same of the plan
      that an opening's ground holds at a group g < 12: the last clause of the sealed `IM.k4_of`
WHAT IS NOT CLAIMED. Nothing on what the number is. `ground_used` is called by Honest/K9/BatFrontHandedFilled.lean
alone. In scope alone. Nothing on any property.
GROUND: beneath this file lies no file but itself that is no row of the sealed library's list (laws.11).
-/
import Johnson.Road.K4.Riders.LookInByMake
import Johnson.Road.FormsKeysPlan
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open Fo.BatRows (bindE_ok)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

/-- **A feed-forward plan's number of used slots is its number of slots, by its make.** -/
theorem planG_used (P : Layer.Pub) (g : ℕ) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.used = hp.ns := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, _, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, _, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, _, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    rfl
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      rfl
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

/-- The same of each member of the list of all groups' plans. -/
theorem plansG_used {P : Layer.Pub} {G : Array Layer.HPlan2} (hG : Layer.plansG P = .ok G) {g : ℕ}
    {hp : Layer.HPlan2} (hg : G[g]? = some hp) : hp.used = hp.ns := by
  unfold Layer.plansG at hG
  obtain ⟨l, hl, hG⟩ := bindE_ok hG
  have e := (Except.ok.inj hG).symm
  subst e
  have hg' : l[g]? = some hp := by simpa using hg
  obtain ⟨O', hO⟩ := OnBytes.Road.plansFrom_at _ _ 0 none l hl g hp hg'
  exact planG_used _ _ _ _ hO

/-- **The same of the plan that the opening's ground holds at a group.** -/
theorem ground_used {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {hp : Layer.HPlan2}
    (hh : Bs.G₀.W.G[g]? = some hp) : hp.used = hp.ns := by
  obtain ⟨-, -, x, -, -, -, -, -, -, -, -, -, hG⟩ := IM.k4_of hS hR O g hg
  exact plansG_used hG hh

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.planG_used
#print axioms ProofFile.Honest.K9.plansG_used
#print axioms ProofFile.Honest.K9.ground_used
