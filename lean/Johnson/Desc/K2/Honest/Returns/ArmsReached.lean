-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ArmsReached.lean: AT EVERY STATE THAT IS REACHED IN FRONT OF THE
SWITCH AT THE OUTPUT HEAD's SEGMENT (sub-protocol number 339 of the first chain's flat list), IN THE
GOALS' SCOPE, THE GROUP THAT THE HEAD's OWN PART OF THE STATE NAMES HAS THE SHAPE's MAIN CODE
(`HeadCode`, Returns/ArmsBehind.lean). With the library's `fresh_reached`
(Johnson/Top/H0/Tw/K2C/HeadFreshReached.lean): BOTH CLAUSES ON THE NEW GROUP THAT `HeadBehind` ASKS
HOLD THERE. Statements with their proofs.

  `of_reach`     the library's `fresh_of_reach`, general in the property: what every accept of the
                 decision of sub-protocol number 338 leaves holds at every state reached at 339
  `behind_k7_reached`   the library's `fresh_reached`, general in the property: what every accept
                 of the lot's sub-protocol at the head's segment's first place (`IM.k7Block`,
                 Johnson/IMR/K7Seat.lean) leaves holds there, in scope, at an opening
  `code_k7Block`   that sub-protocol's term is the term of `headCode_behind`
  `code_reached`, `group_reached`   THE ENDS

By: THE PROOFS ARE THE LIBRARY's, WITH A LETTER FOR ITS PROPERTY: `reach_back`, `fresh_of_reach`,
`fresh_k7Block`, `fresh_reached` (K2C/HeadFreshReached.lean) and what these call. A NEAR RELATIVE,
NOT THE SAME: `prop_of_reach` (Johnson/Top/H0/K2Hands/SampleReach.lean), general in the property
too, goes by an invariant: the property at the start, kept by every sub-protocol in front; here the
one sub-protocol in front is asked alone.

Limits. Those of K2C/HeadFreshReached.lean: OVER THE CHAIN's OWN FLAT LIST, NOT THE LIST OF THE
WRAPPED SUB-PROTOCOLS (for that list the library points to `reach_raw`,
Johnson/Top/H0/Walk/Reach.lean: not called here): a frame that walks the wrapped list has the two
fields only behind that step; at whatever first tree, start and public part; the promise in front is
not spent. TWO OF `HeadBehind`'s ELEVEN FIELDS ARE PAID HERE; NOTHING ON THE NINE OTHERS. Nothing on
any property.

-/
import Johnson.Desc.K2.Honest.Returns.ArmsBehind
import Johnson.Top.H0.Tw.K2C.HeadFreshReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (step_ok_iff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (reach_back fresh_reached)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- What every accept of sub-protocol number 338 leaves holds at every state reached at 339. -/
theorem of_reach (Pr : S → Prop) {C Pz : Type} {ft : Nat} {bs : List (Block S C)}
    {start : Pz → S} {z : Pz}
    (h : ∀ b, bs[338]? = some b → ∀ s s' rs gs, b.decide s rs gs = .ok s' → Pr s') :
    ∀ s, Reach ft bs start 339 (z, s) → Pr s := by
  intro s hr
  obtain ⟨s₀, b, -, hb, R, c, -, hy⟩ := reach_back (k := 338) hr
  exact h b hb _ _ _ _ ((step_ok_iff ft b s₀ s R c c.length).1 hy).2.2.2

/-- **In scope**: what every accept of the lot's sub-protocol at the head's segment's first place
leaves holds at every state reached in front of the head's segment's switch. -/
theorem behind_k7_reached (Pr : S → Prop)
    (hPr : ∀ (X : OnBytes.Model.Verify.Public) (l : Nat) (s t : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))), (IM.k7Block X l).decide s rs gs = .ok t → Pr t)
    {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pz : Type} {ft : Nat}
    {start : Pz → S} {z : Pz} : ∀ s, Reach ft c.blocksInOrder start 339 (z, s) → Pr s := by
  obtain ⟨Lk, b, e1, e2, hj, -⟩ := IM.k7_sits hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hf' : c.blocksInOrder[338]? = some b := hf
  refine of_reach Pr fun b' hb' s s' rs gs hy => ?_
  obtain rfl : b = b' := Option.some.inj (hf'.symm.trans hb')
  exact hPr _ _ _ _ _ _ (IM.k7_sits_yes hS hR O hj hy).1

theorem code_k7Block {X : OnBytes.Model.Verify.Public} {l : Nat} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block X l).decide s rs gs = .ok t) :
    HeadCode t :=
  headCode_behind (W := X) (tl := X.H.tl) (l := l) (l' := l)
    (pl := (VerifiableInference.Desc.Kinds.Reply.blockOf X l).place) (nm := "H:1") h

/-- **In scope: at every state reached in front of the head's segment's switch the group has the
shape's main code.** -/
theorem code_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pz : Type} {ft : Nat}
    {start : Pz → S} {z : Pz} : ∀ s, Reach ft c.blocksInOrder start 339 (z, s) → HeadCode s :=
  behind_k7_reached HeadCode (fun _ _ _ _ _ _ h => code_k7Block h) hS hR O

/-- **Both clauses on the new group that `HeadBehind` asks**, at every such state. -/
theorem group_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pz : Type} {ft : Nat}
    {start : Pz → S} {z : Pz} :
    ∀ s, Reach ft c.blocksInOrder start 339 (z, s) → First.K2.HeadFresh s ∧ HeadCode s :=
  fun s h => ⟨fresh_reached hS hR O s h, code_reached hS hR O s h⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.of_reach
#print axioms VerifiableInference.Desc.K2.Honest.Returns.behind_k7_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.code_k7Block
#print axioms VerifiableInference.Desc.K2.Honest.Returns.code_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.group_reached
