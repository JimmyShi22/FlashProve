-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FunsThirdReached.lean: AT EVERY STATE OF THE VERIFIER THAT IS REACHED BEHIND K4's
SUB-PROTOCOL OF A FEED-FORWARD SEGMENT, THE TEST OF THE NAME "K8.funsThird" ACCEPTS: in the goals'
scope, at an opening of the IOP as written in Lean, at border 28 g + 5 of the first chain. No
premise on a mark: the seated sub-protocol accepts only with no mark behind it.

  `funsThird_step`: an accept of the seated sub-protocol at K4's place gives funsThirdB behind it.
  `reach_pred`: what is reached at k + 1 comes of what is reached at k by an accepting step of
    entry k: the relation Reach (Johnson/Top/H0/Walk/Reach.lean) is inductive: by cases.
  **`funsThird_reached`**: Reach 0 c.blocksInOrder start (28 * g + 5) (z, s') gives funsThirdB s' = true.
    PREMISES: the scope (hS, hR) · an opening O · g < 12 · that the state is reached.
  **`funsThird_rchAt`**: the same at RchAt (descAt Z A B c) (28 * g + 5) a.
No new argument: k4_of, k4_yes (Johnson/IMR/K4Seat.lean: which sub-protocol stands at K4's place,
and what its accept is) · hear_at_flat, flatIx_scope (Johnson/IMR/FlatIx.lean, FlatScope.lean: its
number in the flat list) · kept_atS (Johnson/Road/K4/KeptAtS.lean) · funsThirdB_made
(Johnson/Road/K4/Riders/DoorFuns.lean) · stepYes_decide (Johnson/Top/H0/Walk/ReachInv.lean).
Limits. That there is an opening is shown by no theorem. One of three clauses on three names, at one
border a group. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.DoorFuns
import Johnson.Road.K4.K04Sits
import Johnson.Top.H0.Walk.ReachAt
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.Riders (funsThirdB_made)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready (funsThirdB)
open Johnson.Desc.First.Walk.Tied (Reach StepYes RchAt rchAt_raw stepYes_decide)

/-- An accept of the seated sub-protocol at K4's place gives the test behind it. -/
theorem funsThird_step {b : Block S ProofFile.Cl} {x : Bool × Par} {name : String} {g : ℕ}
    (h : IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) name (k4PlaceAt g)) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    funsThirdB s' = true :=
  funsThirdB_made (kept_atS ((IM.k4_yes h s s' rs gs).1 hd).1)

/-- What is reached at k + 1 comes of what is reached at k by an accepting step of entry k. -/
theorem reach_pred {σ Cl Q : Type} {ft : ℕ} {bs : List (Block σ Cl)} {start : Q → σ} {k : ℕ}
    {a : Q × σ} (h : Reach ft bs start (k + 1) a) :
    ∃ z s s' b, a = (z, s') ∧ Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧
      StepYes ft b s s' := by
  cases h with
  | succ hr hb hy => exact ⟨_, _, _, _, rfl, hr, hb, hy⟩

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ}

/-- **Behind K4's sub-protocol, at every reached state: the test of "K8.funsThird" accepts.** -/
theorem funsThird_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Q : Type}
    {start : Q → S} {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 5) (z, s')) :
    funsThirdB s' = true := by
  obtain ⟨z', s, s'', b, e, _, hb, hy⟩ := reach_pred (k := 28 * g + 4) h
  obtain ⟨_, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b₀, x, e1, e2, _, e4, _⟩ := IM.k4_of hS hR O g hg
  have hi : IM.flatIx c (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope hS hR O (by omega) 2]
    omega
  have hf : c.blocksInOrder[28 * g + 4]? = some b₀ := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  exact funsThird_step e4 hd

/-- **The same at the relation "reached" of the IOP as written in Lean.** -/
theorem funsThird_rchAt (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Str : Type}
    {a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str}
    (h : RchAt (descAt Z A B c) (28 * g + 5) a) : funsThirdB a.1.2 = true :=
  funsThird_reached hS hR O hg (z := a.1.1) (s' := a.1.2) (rchAt_raw h)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.funsThird_step
#print axioms OnBytes.Road.K4.reach_pred
#print axioms OnBytes.Road.K4.funsThird_reached
#print axioms OnBytes.Road.K4.funsThird_rchAt
