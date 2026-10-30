-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/CallsBetween.lean: how the state of the calls stands
between two links, at every reached state.

The members that stand at the front of a link ask three things of the walk's state of the calls: no
link is under way, the chain stands at this link, and a link's first message is due. ("Link l: laid"
asks the first two: its guards B, W0 and W2. The first hearing member asks the third: guard F1 of
the code switch's `firstFront`, and the like at the head's link.) The library learns these facts
from the members' own accepts. To show that the honest prover's run is accepted one needs them in
front of those accepts. Here they are drawn from the accepts of the three members that stand in
front: the closing of the link before (kind K10) lays "the link's number plus one" and "a first
message is due" into the live copy of the state of the calls; the marking behind it (kind K9's
`shut`) lays "no link is under way"; "cleared" lays the live copy into the walk's own. That is three
steps back along the library's `Reach`. Lemmas only; no definition.

  `closing_live`, `shut_live`   what the two members' own texts lay into the live copy
  `shut_link`, `closing_link`   a link is open in the record in front of each of the two
  `calls_behind_cleared`   at a state reached behind "link l: cleared", l < 25: the record stands
      between two links; no link is under way; a first message is due; the link's number is one
      more than the live copy's in front of the closing; the shape is that copy's; and the state
      in front of the closing has a link open and bears no mark
  `calls_at_laid`   the same in front of "link l + 1: laid", l < 24
  `calls_behind_laid`   behind "link l: laid", l < 25: the state is as it was, and that member's
      own three guards hold of it
  `first_due_at`   in front of the first hearing member of link l + 1, l < 24: these three guards,
      and a first message is due

Where the members stand (Johnson/IMR/FlatCases.lean): link l has "laid" at number 14 l + 1, its
first hearing member at 14 l + 2, the one equation, the closing and the marking at 14 l + n + 4,
+ 5 and + 6, and "cleared" at 14 l + n + 7, where n is `IM.nAt l`.

Called: `Close.atLive_lays` (Johnson/Desc/First/Close/Law/LaysLive.lean), `Meaning.K2.bindE`
(Johnson/Goal/Meaning/RecRel.lean), `Meaning.K2.link_putLink` (Johnson/IMR/GroupRest.lean),
`IM.frame_of`, `IM.close_of`, `IM.close_numbers`, `IM.alone_underR`, `IM.yes_alone` (Johnson/IMR/),
`clearedGives`, `framesOf_row`, `layFront_iff` (Johnson/Top/H0/Walk/), `K2.reach_back`
(Johnson/Top/H0/Tw/K2C/HeadFreshReached.lean).

Limits. In the goals' scope, at the format's second hash function. Which number the live copy's link has in
front of the closing is not said here (the field `frameIs` of the library's `FoldFacts` says it at
an unmarked reached state). The front of link 0 (the start) is not treated. These are laws from a
reach: where no state is reached they say nothing. None is one of the library's goals. Nothing is
said on any property.

-/
import Johnson.IMR.FlatCases
import Johnson.IMR.GroupRest
import Johnson.Desc.BlockKeeps
import Johnson.Desc.First.Close.Law.LaysLive
import Johnson.Top.H0.Walk.FrameTiedRec
import Johnson.Top.H0.Walk.FrameRows
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Top.H0.Tw.K2C.HeadFreshReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (reach_back)
open Johnson.Desc.First.Walk.Props (LayFront layFront_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide clearedGives)
open ProofFile (Cl)

/-! ## 1 The two members' own texts -/

/-- **The closing**: of the live copy it turns the frame alone: the link's number goes up by one; a
first message is due; the shape stays. -/
theorem closing_live {C : Type} (Q : VerifiableInference.Desc.First.Close.Par) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.closing (Cl := C) Q).decide s rs gs = .ok t) :
    t.live.frame.link = s.live.frame.link + 1 ∧ t.live.frame.next = .first ∧
      t.live.frame.shape = s.live.frame.shape := by
  have e := (VerifiableInference.Desc.First.Close.atLive_lays (Cl := C)
    VerifiableInference.Desc.K9.owedOf Q s t rs gs h).1
  exact ⟨congrArg (·.frame.link) e, congrArg (·.frame.next) e, congrArg (·.frame.shape) e⟩

/-- **The marking behind the closing**: the live copy behind is the live copy in front with "no link
is under way". -/
theorem shut_live {C : Type} (p : VerifiableInference.Desc.K9.Where) (piece : Nat) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.shut (Cl := C) p piece).decide s rs gs = .ok t) :
    t.live = { s.live with inLink := false } := by
  obtain ⟨L, hL, h⟩ := Meaning.K2.bindE h
  cases h
  have hl : s.link? = some L := by
    cases e : s.link? with
    | none =>
      rw [e] at hL
      cases hL
    | some L' =>
      rw [e] at hL
      exact congrArg some (Except.ok.inj hL)
  have e1 : (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)).live =
      (VerifiableInference.Desc.K9.closed L L.check.frame).check := by
    unfold VerifiableInference.Desc.First.S.live
    rw [Meaning.K2.link_putLink hl]
  have e2 : s.live = L.check := by
    unfold VerifiableInference.Desc.First.S.live
    rw [hl]
  rw [e2]
  exact e1

/-- The marking asks that a link is open in the record. -/
theorem shut_link {C : Type} (p : VerifiableInference.Desc.K9.Where) (piece : Nat) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.shut (Cl := C) p piece).decide s rs gs = .ok t) :
    s.link?.isSome = true := by
  obtain ⟨L, hL, -⟩ := Meaning.K2.bindE h
  cases e : s.link? with
  | none =>
    rw [e] at hL
    cases hL
  | some L' => rfl

/-- The closing opens no link: where one is open behind it, one was open in front. -/
theorem closing_link {C : Type} (Q : VerifiableInference.Desc.First.Close.Par) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K9.closing (Cl := C) Q).decide s rs gs = .ok t)
    (ht : t.link?.isSome = true) : s.link?.isSome = true := by
  obtain ⟨r, -, rfl⟩ := VerifiableInference.Desc.Keeps.emap_ok h
  cases hs : s.link? with
  | some L => rfl
  | none =>
    exfalso
    have e : (VerifiableInference.Desc.K9.putRec s r).link? = none := by
      show (s.putLive { s.live with frame := r.frame }).link? = none
      unfold VerifiableInference.Desc.First.S.putLive
      rw [hs]
      exact hs
    rw [e] at ht
    cases ht

/-! ## 2 Along the reach -/

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Behind "link l: cleared".** -/
theorem calls_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 7 + 1) (z, s)) :
    ∃ s₁, Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 5) (z, s₁) ∧
      s.atBetween = true ∧ s.check.inLink = false ∧ s.check.frame.next = .first ∧
      s.check.frame.link = s₁.live.frame.link + 1 ∧
      s.check.frame.shape = s₁.live.frame.shape ∧ s₁.link?.isSome = true ∧ s₁.failed = none := by
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, e1, hn, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ := hall l hl
  have hn' : Lk.hear.length = IM.nAt l := hn
  obtain ⟨LkC, p, Q, eC, -, -, hcl⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk = LkC := Option.some.inj (e1.symm.trans eC)
  obtain ⟨b0, x0, c0, -, la0⟩ := hcl 0 KindName.K9 rfl
  obtain ⟨b1, x1, c1, ex1, la1⟩ := hcl 1 KindName.K10 rfl
  obtain ⟨b2, x2, c2, ex2, la2⟩ := hcl 2 KindName.K9 rfl
  have i0 := IM.close_numbers hS hR O hl e1 c0
  have i1 := IM.close_numbers hS hR O hl e1 c1
  have i2 := IM.close_numbers hS hR O hl e1 c2
  rw [hn'] at i0 i1 i2 iC
  obtain rfl : VerifiableInference.Desc.K9.closing Q = x1 := Option.some.inj ex1
  obtain rfl : VerifiableInference.Desc.K9.shut p (Q.piece + 1) = x2 := Option.some.inj ex2
  -- "cleared"
  obtain ⟨s₃, b, R₃, hb, hy⟩ := reach_back R
  obtain rfl : bC = b := Option.some.inj (iC.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  rw [dC, hClear] at d
  obtain ⟨-, Xl, counts, left, hcw, -⟩ :=
    Johnson.Desc.First.Walk.Seat.framesOf_row hfs (List.mem_of_getElem? hf)
  have g := d.1
  rw [hcw] at g
  have G := clearedGives Xl counts left _ _ s₃ s g
  -- the marking
  have R₃' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 4 + 2 + 1) (z, s₃) := R₃
  obtain ⟨s₂, b, R₂, hb, hy⟩ := reach_back R₃'
  obtain rfl : b2 = b := Option.some.inj (i2.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  have e3 := shut_live (C := Unit) (rs := rs) (gs := gs) p (Q.piece + 1)
    ((IM.alone_underR la2).2 _ _ _ _ d)
  have k2 := shut_link (C := Unit) (rs := rs) (gs := gs) p (Q.piece + 1)
    ((IM.alone_underR la2).2 _ _ _ _ d)
  -- the closing
  have R₂' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 4 + 1 + 1) (z, s₂) := R₂
  obtain ⟨s₁, b, R₁, hb, hy⟩ := reach_back R₂'
  obtain rfl : b1 = b := Option.some.inj (i1.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  obtain ⟨a1, a2, a3⟩ := closing_live (C := Unit) (rs := rs) (gs := gs) Q
    ((IM.alone_underR la1).2 _ _ _ _ d)
  have k1 := closing_link (C := Unit) (rs := rs) (gs := gs) Q
    ((IM.alone_underR la1).2 _ _ _ _ d) k2
  -- the one equation: its seat's guard says that the state behind it bears no mark
  have R₁' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 4 + 0 + 1) (z, s₁) := R₁
  obtain ⟨s₀, b, -, hb, hy⟩ := reach_back R₁'
  obtain rfl : b0 = b := Option.some.inj (i0.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  have m1 : s₁.failed = none :=
    ((IM.yes_alone la0 (by show KindName.K9 ≠ KindName.K7; decide) s₀ s₁ rs gs).1 d).2.1
  have ec : s.check = { s₂.live with inLink := false } := G.2.1.trans e3
  refine ⟨s₁, R₁, G.1, ?_, ?_, ?_, ?_, k1, m1⟩
  · rw [ec]
  · rw [ec]
    exact a2
  · rw [ec]
    exact a1
  · rw [ec]
    exact a3

/-- **In front of "link l + 1: laid".** -/
theorem calls_at_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {z : ProofFile.InstPub} {s : S} (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (l + 1) + 1) (z, s)) :
    ∃ s₁, Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 12) (z, s₁) ∧
      s.atBetween = true ∧ s.check.inLink = false ∧ s.check.frame.next = .first ∧
      s.check.frame.link = s₁.live.frame.link + 1 ∧
      s.check.frame.shape = s₁.live.frame.shape ∧ s₁.link?.isSome = true ∧ s₁.failed = none := by
  have hn : IM.nAt l = 7 := by
    unfold IM.nAt
    rw [if_neg (by omega)]
  have e : 14 * (l + 1) + 1 = 14 * l + IM.nAt l + 7 + 1 := by omega
  rw [e] at R
  obtain ⟨s₁, R₁, h⟩ := calls_behind_cleared hS hR O (by omega) R
  rw [show 14 * l + IM.nAt l + 5 = 14 * l + 12 by omega] at R₁
  exact ⟨s₁, R₁, h⟩

/-- **Behind "link l: laid"**: the state is as it was, and that member's own three guards hold of
it. -/
theorem calls_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S} (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 1 + 1) (z, s)) :
    Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 1) (z, s) ∧ LayFront l s := by
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, -, -, -, -, hlayf, hLay, -, iL, -, dL, -⟩ := hall l hl
  obtain ⟨s₀, b, R₀, hb, hy⟩ := reach_back R
  obtain rfl : bL = b := Option.some.inj (iL.symm.trans hb)
  obtain ⟨rs, gs, d⟩ := stepYes_decide hy
  rw [dL, hLay, hlayf] at d
  obtain ⟨rfl, hF⟩ := layFront_iff.1 d.1
  exact ⟨R₀, hF⟩

/-- **In front of the first hearing member of link l + 1**: no link is open in the record; a first
call is due; the chain stands at the link; a first message is due. -/
theorem first_due_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 24)
    {z : ProofFile.InstPub} {s : S} (R : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (l + 1) + 2) (z, s)) :
    LayFront (l + 1) s ∧ s.check.frame.next = .first := by
  obtain ⟨R₀, hF⟩ := calls_behind_laid hS hR O (l := l + 1) (by omega) R
  obtain ⟨s₁, -, -, -, hn, -⟩ := calls_at_laid hS hR O hl R₀
  exact ⟨hF, hn⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.closing_live
#print axioms ProofFile.Honest.shut_live
#print axioms ProofFile.Honest.shut_link
#print axioms ProofFile.Honest.closing_link
#print axioms ProofFile.Honest.calls_behind_cleared
#print axioms ProofFile.Honest.calls_at_laid
#print axioms ProofFile.Honest.calls_behind_laid
#print axioms ProofFile.Honest.first_due_at
