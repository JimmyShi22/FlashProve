-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/GrownFence.lean: x_reachedR's PREMISE hF IS ASKED AT j < 358 ALONE, with Johnson/IMR/HandsFence.lean: a weaker premise; no conclusion turns. OVER THE BASE (N) v5 WITH L25's RIDER 5: e₁ AT THE PROOF FILE, THE HALF THAT READS THE VERIFIER's STATE ALONE: THE JOIN AND THE WHOLE ROAD AT HandsR (Hands with a fence Fk): ADDITIVE: Shares · SharesS · s1_of_shares · s1_of_seated · x_reached STAND; WHOEVER HAS
SharesS HAS THIS FORM AT EVERY Fk (fenced_of_seated): NOBODY's TERM TURNS.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.

  SharesR Fk N E ft Z G₀ c   ∀ k b, FlatCase Z G₀ c k b → HandsR Fk N linksW placesW E ft k b: HandsR at each of the ten forms of `FlatCase`, with all that its seat says in hand.
  fenced_of_seated  SharesS → SharesR Fk.
  x_reachedR        IN SCOPE, THE WHOLE ROAD: SharesR Fk · Fk at the state behind each cut j < 358 of this very fold · the plan's two counts at the front · E 0 at the first state ⟹ X k at the state that the fold over the first k sub-protocols reaches from ProofFile.startS Z p, if it bears no mark.

MEANT AT (the sheet's keeper's proposal; «so» by part 5's keeper): Fk k s := s.failed = none → ‹FoldFacts' fields at s› · E k s := part 5's First.ePubAt at border k, the public part fixed.
What is not claimed. NO SHARE IS PAID HERE. Fk at any state. No soundness.
-/
import Johnson.IMR.GrownStart
import Johnson.IMR.HandsFence

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain FileDescription Place KindName foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers frontPlace)
open ProofFile (Cl)

/-- **The shares, at the seated sub-protocols, under a fence.** -/
def SharesR (Fk : ℕ → S → Prop) (N : Numbers) (E : ℕ → S → Bool) (ft : ℕ) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground) (c : Chain S Cl) : Prop :=
  ∀ k b, FlatCase Z G₀ c k b → HandsR Fk N linksW placesW E ft k b

theorem fenced_of_seated {Fk : ℕ → S → Prop} {N : Numbers} {E : ℕ → S → Bool} {ft : ℕ}
    {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {c : Chain S Cl} (h : SharesS N E ft Z G₀ c) :
    SharesR Fk N E ft Z G₀ c := fun k b hc => (h k b hc).fenced

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **IN SCOPE, THE WHOLE ROAD, UNDER A FENCE.** -/
theorem x_reachedR (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Fk : ℕ → S → Prop} {N : Numbers}
    {E : ℕ → S → Bool} {ft : ℕ} (Sh : SharesR Fk N E ft Z Bs.G₀ c) (p : ProofFile.InstPub)
    (hT : N.treesAt (some frontPlace) = 0) (hM : N.msgsAt (some frontPlace) = 0)
    (hE : (ProofFile.startS Z p).failed = none → E 0 (ProofFile.startS Z p) = true) {rs : List Fmt.RoundView}
    {cols : List OpenedColumn}
    (hF : ∀ j, j < 358 → ∀ r, foldBlocks ft (c.blocksInOrder.take j) (ProofFile.startS Z p) rs cols = .ok r →
      Fk j r.1)
    {k : ℕ} (hk : k ≤ 358) {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out)
    (hu : out.1.failed = none) : XK N linksW placesW E k out.1 = true := by
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  have h0 := s0_of_open (links := linksW) O p hT hM hE
  rw [places_scope hS hR O] at h0
  exact x_at_cutR (fun k b hb => Sh k b (flat_cases hS hR O k b hb)) (hlen ▸ hF) h0 k (hlen ▸ hk) out
    hf hu

end

end IM

#print axioms IM.fenced_of_seated
#print axioms IM.x_reachedR
