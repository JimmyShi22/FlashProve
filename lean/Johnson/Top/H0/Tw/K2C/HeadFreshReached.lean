-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadFreshReached.lean: code switching: AT EVERY STATE THAT IS REACHED IN FRONT
OF THE SWITCH AT THE OUTPUT HEAD's SEGMENT (sub-protocol number 339 of the first chain's flat list)
THE GROUP THAT THE HEAD's OWN PART OF THE STATE NAMES IS FRESH (HeadFresh, K2C/HandsEnds.lean), in
the goals' scope. NO SUB-PROTOCOL IMPORTS THIS FILE.
  reach_back       free of the kind: what is reached at number k + 1 is the state behind an
                   accepting step of sub-protocol number k from a state reached at k
  fresh_of_reach   if every accept of the decision of sub-protocol number 338 leaves the group
                   fresh, it is fresh at every state reached at 339
  fresh_k7Block    the term for the lot's sub-protocol at the head's
                   segment's first place (IM.k7Block, Johnson/IMR/K7Seat.lean) is the term of
                   fresh_behind (K2C/HeadFreshAt.lean)
  fresh_reached    in scope, at an opening of the description's value: at every state reached at
                   339 over the chain's flat list
CALLED: Reach · StepYes (Johnson/Top/H0/Walk/Reach.lean) · step_ok_iff
(Johnson/Desc/Sound/RunIsDecide.lean) · IM.k7_sits · IM.k7_sits_yes (Johnson/IMR/FirstSeats.lean) ·
IM.hear_at_flat (IMR/FlatIx.lean) · IM.flatIx_scope (IMR/FlatScope.lean).
LIMITS. Over the chain's own flat list: for the list of the wrapped sub-protocols see reach_raw
(Walk/Reach.lean). At whatever first tree, start and public part. The promise in front is not
spent. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HeadFreshAt
import Johnson.Top.H0.Walk.Reach
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile (Cl)

/-- **What is reached at k + 1 stands behind an accepting step from what is reached at k.** -/
theorem reach_back {σ C Pz : Type} {ft : ℕ} {bs : List (Block σ C)} {start : Pz → σ} {k : ℕ}
    {z : Pz} {s' : σ} (h : Reach ft bs start (k + 1) (z, s')) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s s' := by
  cases h with
  | succ h1 hb hy => exact ⟨_, _, h1, hb, hy⟩

theorem fresh_of_reach {C Pz : Type} {ft : ℕ} {bs : List (Block S C)} {start : Pz → S} {z : Pz}
    (h : ∀ b, bs[338]? = some b → ∀ s s' rs gs, b.decide s rs gs = .ok s' → HeadFresh s') :
    ∀ s, Reach ft bs start 339 (z, s) → HeadFresh s := by
  intro s hr
  obtain ⟨s₀, b, -, hb, R, c, -, hy⟩ := reach_back (k := 338) hr
  exact h b hb _ _ _ _ ((step_ok_iff ft b s₀ s R c c.length).1 hy).2.2.2

theorem fresh_k7Block {X : OnBytes.Model.Verify.Public} {l : ℕ} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (IM.k7Block X l).decide s rs gs = .ok t) :
    HeadFresh t :=
  fresh_behind (W := X) (tl := X.H.tl) (l := l) (l' := l)
    (pl := (VerifiableInference.Desc.Kinds.Reply.blockOf X l).place) (nm := "H:1") h

/-- **In scope: at every state reached in front of the head's segment's switch.** -/
theorem fresh_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pz : Type} {ft : ℕ}
    {start : Pz → S} {z : Pz} : ∀ s, Reach ft c.blocksInOrder start 339 (z, s) → HeadFresh s := by
  obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hf' : c.blocksInOrder[338]? = some b := hf
  refine fresh_of_reach fun b' hb' s s' rs gs hy => ?_
  obtain rfl : b = b' := Option.some.inj (hf'.symm.trans hb')
  exact fresh_k7Block (IM.k7_sits_yes hS hR O hj hy).1

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.reach_back
#print axioms VerifiableInference.Desc.First.K2.fresh_of_reach
#print axioms VerifiableInference.Desc.First.K2.fresh_k7Block
#print axioms VerifiableInference.Desc.First.K2.fresh_reached
