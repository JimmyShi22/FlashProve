-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchEndsBoth.lean: THE CODE SWITCH's TWO LAST PLACES IN THE PROOF FILE's OWN
FIRST CHAIN (kind K2): THE SECOND PLACE OF THE HEAD's LINK (14 · 24 + 1 + 2) AND THE FIRST PLACE
BEHIND THE LINKS (353 + 0), IN THE FRAME's OWN FORM: TWO OF THE PREMISES THAT THE RULE FOR
ACCEPTANCE ASKS: Carries AND Returns (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the
reader shA, at SwitchFrames.lean's steps WITH A GUARD ON THE SHAPE IN FRONT, under named tests on
values. A joining of laws; nothing is evaluated.

  `headGd p HP x`: THE GUARD AT THE HEAD's PLACE: headB · headP
    (Johnson/Desc/First/Shape/SwitchArmsB.lean, SwitchArmsFits.lean) at x; headQuietB HP
    (SwitchEndsReturns.lean) AT WHAT THE SWITCH's UPDATE headU RETURNS.
  `headW HP s`: THE TESTS ON VALUES THERE: headOnesV (the ones, at the rows that the head's own
    frame carries) · headQuietV HP (the reply is an entry of the vocabulary; the covered positions
    can be made, and their four arrays have the due length: by headQuietV_eq, SwitchEndsVals.lean,
    these are one test: S.covered returns).
  `finGd p x`: THE GUARD BEHIND THE LINKS: finFrontB at x; finB · finP AT WHAT THE QUIET FRONT's
    UPDATE finFrontU RETURNS.
  THE TEST ON VALUES THERE: switchW (SwitchReturns.lean): the ones, at the rows that the frame
  carries.
  **`switch_head_both`** · **`switch_finish_both`**: under the head P5J.AtMgA: for every table of
    steps G and of tests vals with G ‹number› = the guarded step and vals ‹number› = the tests, at
    the plan's numbers: Carries and Returns.

What pays what in Returns. The guards pay all that hangs on the shape and the plan, at the state in
front and, through the updates, at the states between. The member's own test on rounds and columns
(Block.Fits) pays headR | finR (headR_of_Fits | finR_of_Fits). The tests on values stand at the
state in front: that the switch leaves what headQuietV reads, and that the quiet front leaves what
the ones read, are laws (Johnson/Desc/First/Shape/SwitchEndsVals.lean). The dress and the seats:
SwitchSeatEnds.lean.

Limits. That a guard or a test accepts at any state is not shown. G and vals are letters. NEITHER
STATEMENT SAYS THAT A MEMBER STANDS AT ITS NUMBER (the proofs have it; SwitchSeatEnds.lean's
switch_head_seat | switch_finish_seat state it): where none stood, Carries and Returns would say
nothing: both begin "for every member at that number". With the guard in front "Carries" is the weak
form: no law here says that a yes of the member passes the guard. The guards' and the steps' numbers
are taken at the empty name (k2P … "" …): the three updates read no name (SwitchAtHead.lean's
nameless). The step at the head's place is still switchU (SwitchAtHead.lean), which holds two
updates, a link's at "here" = 0 and the head's at "here" = 4, and chooses by the shape. That the
head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SwitchSeatEnds
import Johnson.Desc.First.Shape.SwitchEndsVals
import Johnson.Desc.First.Shape.SwitchArmsFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith HeadPar)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (k2P k2PlaceF)
open P5J (AtMgA)
open ProofFile.Honest (Carries Returns returns_seat)

/-- **THE GUARD AT THE HEAD's PLACE.** -/
def headGd (p : P2) (HP : HeadPar) (x : ChainF) : Bool :=
  headB p x && headP p x &&
    match headU p x with
    | some y => headQuietB HP y
    | none => false

/-- **THE TESTS ON VALUES AT THE HEAD's PLACE.** -/
def headW (HP : HeadPar) (s : S) : Bool := headOnesV s && headQuietV HP s

/-- **THE GUARD BEHIND THE LINKS.** -/
def finGd (p : P2) (x : ChainF) : Bool :=
  finFrontB x &&
    match finFrontU x with
    | some y => finB p y && finP p y
    | none => false

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SECOND PLACE OF THE HEAD's LINK: BOTH PREMISES.** -/
theorem switch_head_both (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * 24 + 1 + 2) = optE (fun y =>
          if headGd (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n) HP
            y
          then switchU Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } n HP y
          else none) →
        (∀ s rs gs, vals (14 * 24 + 1 + 2) s rs gs = headW HP s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * 24 + 1 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * 24 + 1 + 2) := by
  obtain ⟨Bs, P, n, HP, Lk, b, a1, a2, a3, a4, -, -, a7, hc⟩ := switch_head_at h
  obtain ⟨Bs', P', n', HP', b', c1, c2, c3, c4, c5, hro, hr⟩ := switch_head_seat h
  obtain rfl : Bs = Bs' := Except.ok.inj (a1.symm.trans c1)
  obtain rfl : P = P' := Option.some.inj (a2.symm.trans c2)
  obtain rfl : n = n' := Option.some.inj (a3.symm.trans c3)
  obtain rfl : HP = HP' := Option.some.inj (a4.symm.trans c4)
  obtain rfl : b = b' := Option.some.inj (a7.symm.trans c5)
  refine ⟨Bs, P, n, HP, a1, a2, a3, a4, fun ft G vals hG hV => ⟨?_, ?_⟩⟩
  · refine carries_of_seat a7 fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    obtain ⟨-, hu'⟩ := optE_guard hu
    exact Option.some.inj ((optE_ok.1 hu').symm.trans (hc s _ gs t hd))
  · refine returns_seat a7 fun rs cols hF s u hg hv => ?_
    have hg1 : G (14 * 24 + 1 + 2) (shA s) = .ok u := hg
    rw [hG] at hg1
    obtain ⟨hgd, hg0⟩ := optE_guard hg1
    have hg' := optE_ok.1 hg0
    have hv1 : vals (14 * 24 + 1 + 2) s (rs.map noDigest) (b.shown ft rs cols) = true := hv
    rw [hV] at hv1
    unfold headW at hv1
    rw [Bool.and_eq_true] at hv1
    unfold headGd at hgd
    simp only [Bool.and_eq_true] at hgd
    obtain ⟨⟨g1, g2⟩, g3⟩ := hgd
    obtain ⟨R₁, R₂, rfl, hR⟩ := headR_of_Fits hro hF g1 g2
    obtain ⟨m, hm⟩ := head_returns_B g1 hv1.1 hR
    have hU := head_carries rfl hm
    have g3' : headQuietB HP (chainF m) = true := by
      have e : headU (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n)
          (shA s) = some (chainF m) := hU
      rw [e] at g3
      exact g3
    obtain ⟨r₁, r₂, a0, G0, w, roots, -, R⟩ :=
      VerifiableInference.Desc.First.K2.head_inv
        (rfl : (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n).stands =
          .head) hm
    have hh : (shA s).1.here = if a0.opened then 3 else 4 := by
      show hereNo s.here = _
      rw [R.hHere]
      rfl
    unfold switchU at hg'
    rw [hh] at hg'
    cases ho : a0.opened with
    | true =>
      rw [ho] at hg'
      cases hg'
    | false =>
      rw [ho] at hg'
      have hg2 : (headU (k2P Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } "" .head n)
          (chainF s)).bind (headOpenU HP) = some u := hg'
      rw [hU] at hg2
      obtain ⟨t, ht⟩ := headOpen_returns g3' (by rw [headQuietV_behind rfl hm]; exact hv1.2)
        (y := u) hg2
      exact ⟨t, hr s m t _ _ _ hm ht⟩

/-- **THE FIRST PLACE BEHIND THE LINKS: BOTH PREMISES.** -/
theorem switch_finish_both (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P none = some n ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (353 + 0) = optE (fun y =>
          if finGd (k2P Zp k2PlaceF "" .finish n) y
          then ((finFrontU y).bind (finU (k2P Zp k2PlaceF "" .finish n))).bind finBehindU
          else none) →
        (∀ s rs gs, vals (353 + 0) s rs gs = switchW s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (353 + 0) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (353 + 0) := by
  obtain ⟨Bs, P, n, b, a1, a2, a3, a4, hc⟩ := switch_finish_at h
  obtain ⟨Bs', P', n', b', c1, c2, c3, c5, hro, hr⟩ := switch_finish_seat h
  obtain ⟨Bs'', base, O⟩ := h.laid.opened
  have hf := (IM.back_numbers h.scope h.reads O).1 0 b a4
  obtain rfl : Bs = Bs' := Except.ok.inj (a1.symm.trans c1)
  obtain rfl : P = P' := Option.some.inj (a2.symm.trans c2)
  obtain rfl : n = n' := Option.some.inj (a3.symm.trans c3)
  obtain rfl := Option.some.inj (hf.symm.trans c5)
  refine ⟨Bs, P, n, a1, a2, a3, fun ft G vals hG hV => ⟨?_, ?_⟩⟩
  · refine carries_of_seat hf fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    obtain ⟨-, hu'⟩ := optE_guard hu
    exact Option.some.inj ((optE_ok.1 hu').symm.trans (hc s _ gs t hd))
  · refine returns_seat hf fun rs cols hF s u hg hv => ?_
    have hg1 : G (353 + 0) (shA s) = .ok u := hg
    rw [hG] at hg1
    obtain ⟨hgd, hg0⟩ := optE_guard hg1
    have hg' := optE_ok.1 hg0
    have hv1 : vals (353 + 0) s (rs.map noDigest) _ = true := hv
    rw [hV] at hv1
    unfold finGd at hgd
    rw [Bool.and_eq_true] at hgd
    obtain ⟨g0, g1⟩ := hgd
    obtain ⟨y₂, hy₂, hu₃⟩ := Option.bind_eq_some_iff.1 hg'
    obtain ⟨y₁, hy₁, hu₂⟩ := Option.bind_eq_some_iff.1 hy₂
    obtain ⟨m₁, hm₁⟩ := finFront_returns g0 hy₁
    obtain rfl : y₁ = chainF m₁ := Option.some.inj (hy₁.symm.trans (finFront_carries hm₁))
    have e1 : finFrontU (shA s) = some (chainF m₁) := hy₁
    rw [e1] at g1
    have g1' : (finB (k2P Zp k2PlaceF "" .finish n) (chainF m₁) &&
        finP (k2P Zp k2PlaceF "" .finish n) (chainF m₁)) = true := g1
    rw [Bool.and_eq_true] at g1'
    obtain ⟨R₁, R₂, rfl, hR⟩ := finR_of_Fits hro hF g1'.1 g1'.2
    obtain ⟨m₂, hm₂⟩ := finish_returns_B g1'.1 (by rw [finOnesV_behind hm₁]; exact hv1) hR
    obtain rfl : y₂ = chainF m₂ := Option.some.inj (hu₂.symm.trans (fin_carries rfl hm₂))
    obtain ⟨t, ht⟩ := finBehind_returns hu₃
    exact ⟨t, hr s m₁ m₂ t _ _ _ hm₁ hm₂ ht⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.switch_head_both
#print axioms Johnson.AtFull.Shape.switch_finish_both
#print axioms Johnson.AtFull.Shape.headGd
#print axioms Johnson.AtFull.Shape.headW
#print axioms Johnson.AtFull.Shape.finGd
