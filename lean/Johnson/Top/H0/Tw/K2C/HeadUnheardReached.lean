-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadUnheardReached.lean: THE PREMISE hU OF made_head
(K2C/MadeLook.lean) AT EVERY STATE THAT IS REACHED IN FRONT OF THE SWITCH AT THE HEAD's LINK
(sub-protocol number 339 of the first chain's flat list), in the goals' scope. NO BLOCK IMPORTS
THIS FILE.

  unheard_behind    an accept of: headFrontQ tl as a sub-protocol without a round, under whatever
                    place, guarded on the reply; then the next token's block: HeadUnheard tl behind
  unheard_k7Block   the same at the term for the lot's sub-protocol at the
                    head's link's first place (IM.k7Block, Johnson/IMR/K7Seat.lean)
  unheard_reached   in scope, at an opening of the description's value: HeadUnheard at the plan's
                    state of the smallness test, at every state reached at 339 over the chain's flat
                    list
  hU_reached        **hU's body there**, where that state of the plan's has nothing heard

IT FOLLOWS, STEP FOR STEP, fresh_behind · fresh_k7Block · fresh_reached
(K2C/HeadFreshAt.lean · HeadFreshReached.lean),
and calls the former's guarded_front and reach_back, out of those two files.
Limits. Over the chain's own flat list; at whatever first tree, start and public part. That the
share's fence is this «reached» is the join's. The one premise left is on the plan: evaluated in no
theorem. No state is exhibited. No soundness statement.

-/
import Johnson.Top.H0.Tw.K2C.HeadFreshReached
import Johnson.Top.H0.Tw.K2C.HeadUnheard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription roundlessBlock Place)
open VerifiableInference.Desc.Sound (step_ok_iff)
open VerifiableInference.Desc.Kinds (Reply.blockOf)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile (Cl)

/-- **Behind the two steps in a row.** pl: whatever place the first is stamped with. -/
theorem unheard_behind {W : Verify.Public} {tl : HTailF2} {l l' : Nat} {pl : Place} {nm : String}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (Block.andThen nm (Block.guarded ProofFile.sameReply (fun _ => false)
      ({ (roundlessBlock nm 1 (some l') 1 (headFrontQ tl) : Block S Unit) with place := pl }))
      (Reply.blockOf W l)).decide s rs gs = .ok s') : HeadUnheard tl s' :=
  joined_unheard W l nm tl _ (fun _ _ _ _ e => front_unheard (guarded_front e)) s rs gs s' h

theorem unheard_k7Block {X : Verify.Public} {l : ℕ} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (IM.k7Block X l).decide s rs gs = .ok t) :
    HeadUnheard X.H.tl t :=
  unheard_behind (W := X) (tl := X.H.tl) (l := l) (l' := l)
    (pl := (Reply.blockOf X l).place) (nm := "H:1") h

/-- **In scope: at every state reached in front of the head's link's switch.** -/
theorem unheard_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pz : Type} {ft : ℕ}
    {start : Pz → S} {z : Pz} :
    ∀ s, Reach ft c.blocksInOrder start 339 (z, s) → HeadUnheard Bs.G₀.W.H.tl s := by
  obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hf' : c.blocksInOrder[338]? = some b := hf
  intro s hr
  obtain ⟨s₀, b', -, hb', R, cc, -, hy⟩ := reach_back (k := 338) hr
  obtain rfl : b = b' := Option.some.inj (hf'.symm.trans hb')
  exact unheard_k7Block
    (IM.k7_sits_yes hS hR O hj ((step_ok_iff ft b s₀ s R cc cc.length).1 hy).2.2.2).1

/-- **hU's body at every such state.** -/
theorem hU_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pz : Type} {ft : ℕ}
    {start : Pz → S} {z : Pz} (hh : Bs.G₀.W.H.tl.heard = none) :
    ∀ s, Reach ft c.blocksInOrder start 339 (z, s) →
      ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none :=
  fun s hr => hU_of_unheard (unheard_reached hS hR O s hr) hh

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.unheard_behind
#print axioms VerifiableInference.Desc.First.K2.unheard_k7Block
#print axioms VerifiableInference.Desc.First.K2.unheard_reached
#print axioms VerifiableInference.Desc.First.K2.hU_reached
