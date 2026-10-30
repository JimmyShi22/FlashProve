-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file stands over Block.lean and State.lean, and over the seats that go with
them (Stored/HeadSeatAt.lean, Stored/ReplySeatAt.lean). k06HonestWhole: K6On has six
clauses (Law/RowPins.lean).
Johnson/Desc/Kinds/Law/K06HonestWhole.lean: A RIDER TO Law/K06Honest.lean, ON THREE FINDS ON IT (its fences (11) (13)):
  (11) "whatever is drawn" was brighter than k06HonestExists's conclusion: ShapedAs says that each drawn element is AMONG the given draws: membership, not order. HERE: HeardAre: THE CHALLENGES THAT THE HEARING HEARD ARE THE GIVEN ONES, IN THEIR ORDER: pV = pts · gam · om · the four
       sumchecks' challenges are the given lists without their last member (the last is the further variable's).
  (7)  the two tops were joined at general W by nobody. HERE: k06HonestWhole: K6On ∧ K6MoreB ∧ K6RoomB ∧ honest cells ∧ DrawsOk ⇒ there are rs, s', gs with ALL NINE PREMISES: in it "honest run" cancels: premises 1, 7, 8, 9 are earned; 2 to 6 stay K6On's own.
  (13) in k06Honest_closes the record s' stood under a bare "there is", tied to no decision. HERE: ClosedWhole stands AT THE VERY s' THAT THE DECISION RETURNS, and what the seat reads back as heard at s' is the H whose challenges are the given ones.
EVERY LETTER UNDER "THERE IS" IN k06HonestWhole, AND WHAT PINS IT: s': THE DECISION's OWN RETURN (b.decide s rs gs = .ok s': an equation) · H: WHAT THE SEAT READS BACK AT s' (heard s' = some H: an equation) · gs: PINNED BY NOTHING: the decision never reads it (in the proof it is []) · rs: NO EQUATION: it
is tied by HeardAre (through H: pts, gam, om and the four lists but for their last members: in order), by ShapedAs (every drawn element is AMONG the given draws; the rounds' counts are the table's) and by the nine: THE SENDER IS A "THERE IS". LETTERS UNDER "FOR ALL" THAT ARE TIED TO rs BY MEMBERSHIP ALONE: epsS · down ·
epsP · epsN · epsL and the last member of each of rsS | rsP | rsN | rsL: head_sendsC hands no equation for them. l is read by blockOf alone; b is pinned by blockOf W l = some b.
WHAT IT IS NOT. ALL SEVEN FENCES OF Law/K06Honest.lean's HEAD, AND ITS SIX MORE, of which these stay: (8) A MEMBER OF rowRides ALONE: not of rowFrontRides | rowStep | k6Own: nothing on JoinOpened, Block.step or the pin · (9) of the nine, 2 to 6 are K6On's own; 8 is met by empty
lists (at the truth the rule's lists are empty at every front) · (10) ALL PREMISES ARE PAID TOGETHER AT THE TOY ALONE; the four Bools bring no cells · (12) "no drawn element is (0,0,0)" asks more than the tape does (it refuses a 0 at a round's last draw alone); rs stands behind all draws at
once: that a message hangs on earlier draws alone is not said. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06Honest
import Johnson.Desc.Kinds.Law.RowAtDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)

/-- The challenges heard are the given draws, in their order. -/
def HeardAre [Sizes] (pts : List E) (gam om : E) (rsS rsP rsN rsL : List E) (H : HeardAll) : Prop :=
  H.1.pV = pts.toArray ∧ H.1.gam = gam ∧ H.1.om = om ∧
    H.1.squares.r = (rsS.take (lPd + lt)).toArray ∧ H.1.products.r = (rsP.take lt).toArray ∧
    H.2.1.normed.r = (rsN.take lt).toArray ∧ H.2.2.logits.r = (rsL.take (lt + lPd)).toArray

section Letters

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- honestRun_exists, with the challenges heard. -/
theorem honestRun_exists_eq (c : NCells) (mask : Nat → E) {F : Fork} (hW : WellLaid F)
    (hH : (dataOf c).Holds) (hzt : (FinalNorm.zt).size = lt)
    (pts : List E) (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E)
    (hD : DrawsOk pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL)
    (hroom : Fresh F (41 + 8 * lt + 4 * lPd)) :
    ∃ (rs : List Fmt.RoundView) (H : HeardAll) (G : Fork),
      HonestRun c mask F (drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) rs H G ∧
      HeardAre pts gam om rsS rsP rsN rsL H := by
  have szP : zP.size = lt + lPd := by
    unfold zP
    rw [Array.size_append, hzt]
    simp [halves]
  have sPt : pts.toArray.size = lt := by simpa using hD.lpts
  have mem : ∀ x, x ∈ drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL →
      okE x = true := fun x hx => (hD.ok x hx).1
  have inD : ∀ x, (x ∈ pts ∨ (x = gam ∨ x = down ∨ x = epsS ∨ x ∈ rsS) ∨
      (x = om ∨ x = epsP ∨ x ∈ rsP) ∨ (x = epsN ∨ x ∈ rsN) ∨ (x = epsL ∨ x ∈ rsL)) →
      x ∈ drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL := by
    intro x hx
    unfold drawsOf
    simp only [List.mem_append, List.mem_cons]
    rcases hx with a | a | a | a | a
    · exact Or.inl (Or.inl (Or.inl (Or.inl a)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr a)))
    · exact Or.inl (Or.inl (Or.inr a))
    · exact Or.inl (Or.inr a)
    · exact Or.inr a
  have lS : rsS.length = (zS pts.toArray).size + 1 := by rw [zS_size _ sPt]; exact hD.lS
  have lP : rsP.length = pts.toArray.size + 1 := by rw [sPt]; exact hD.lP
  have lN : rsN.length = (FinalNorm.zt).size + 1 := by rw [hzt]; exact hD.lN
  have lL : rsL.length = zP.size + 1 := by rw [szP]; exact hD.lL
  have hF := hroom.less (m := 9 + (Part.MaskedSum.ownSlots
      (callOf 0 (zS pts.toArray) 2).all + 2 +
      (7 + (1 + (Part.MaskedSum.ownSlots (callOf 1 pts.toArray 4).all + 4 +
        (1 + (Part.MaskedSum.ownSlots (callOf 1 FinalNorm.zt 2).all + 2 +
          (1 + (Part.MaskedSum.ownSlots (callOf 1 zP 2).all + 2 + 0))))))))) (by
    rw [own_callOf, own_callOf, own_callOf, own_callOf, zS_size _ sPt, sPt, hzt, szP]
    omega)
  obtain ⟨rs, H, G, hShape, hcan, hhear, hNT, hST, _, hWG, ePV, eg, eo, eS, eP, eN, eL, hval⟩ :=
    head_sendsC c mask hW hH pts hD.lpts gam epsS down om epsP epsN epsL rsS rsP rsN rsL lS lP lN
      lL (fun x hx => mem x (inD x (Or.inl hx)))
      (mem _ (inD _ (Or.inr (Or.inl (Or.inl rfl)))))
      (mem _ (inD _ (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))))
      (mem _ (inD _ (Or.inr (Or.inl (Or.inr (Or.inl rfl))))))
      (mem _ (inD _ (Or.inr (Or.inr (Or.inl (Or.inl rfl))))))
      (mem _ (inD _ (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl rfl)))))))
      (mem _ (inD _ (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl rfl)))))))
      (mem _ (inD _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
      (fun x hx => mem x (inD x (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr hx)))))))
      (fun x hx => mem x (inD x (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hx)))))))
      (fun x hx => mem x (inD x (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hx)))))))
      (fun x hx => mem x (inD x (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hx))))))) hF
  have hRT : RowTruth c mask F rs :=
    ⟨hNT, fun pre tN tL Hn Fa Fb F1 SN SL a b c' d' =>
      ⟨(hST pre tN tL Hn Fa Fb F1 SN SL a b c' d').1,
        logits_form _ _ _ _ (hST pre tN tL Hn Fa Fb F1 SN SL a b c' d').2⟩⟩
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7⟩, ⟨n0, n1, n2, n3⟩, ⟨l0, l1, l2, l3⟩⟩ :=
    hval G (worldE G mask noEnt) (OnBytes.PscRun.Later.refl _) (fun _ _ _ => rfl)
  have sL : H.2.2.logits.r.size = lt + lPd := by
    rw [eL, List.size_toArray, List.length_take, lL, szP]
    omega
  obtain ⟨Fa, Fb, lr, hNorm, _, _, _, hsL, _⟩ := Came.hear_parts hW hhear
  have ok1 : okE (H.2.2.logits.end_ 1).var.const = true := sumcheck_okEnds hsL 1
  refine ⟨rs, H, G, ⟨hcan, hhear, hShape hzt, fun x hx => (hD.ok x hx).2, hRT, by rw [ePV]; exact sPt,
    by rw [eS, List.size_toArray, List.length_take, lS, zS_size _ sPt]; omega,
    by rw [eP, List.size_toArray, List.length_take, lP, sPt]; omega,
    by rw [eN, List.size_toArray, List.length_take, lN, hzt]; omega, ?_, ?_⟩,
    ⟨ePV, eg, eo, by rw [eS, zS_size _ sPt], by rw [eP, sPt], by rw [eN, hzt], by rw [eL, szP]⟩⟩
  · letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : FinalNorm.Reads := normReadsAtCells c
    exact { sums := w1, prods := w2, sqRow := w3, sq0 := w4 0 (by omega), sq1 := w4 1 (by omega)
            prClaimed := w5, prRow := w6, prEnd := w7, nmRow := n1
            nm0 := by rw [Came.vsG_length, hzt] at n2; exact n2
            nm1 := by rw [Came.vsG_length, hzt] at n3; exact n3 }
  · letI : Heard := H.2.2
    letI : Reads := readsAt c.toCells
    exact headTruth_of_values c.toCells G mask noEnt hzt sL l0 l1
      (by rw [Came.vsG_length, szP] at l2; exact l2) (by rw [Came.vsG_length, szP] at l3; exact l3)
      ok1

end Letters

/-- Where the seated block's decision goes on (decide_hears, at the seat). -/
theorem decide_hears_at (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (F : Fork) (w : SumOnMatrix) (s1 s2 : S),
      given (parOf h work) (seatAt h iU3) s = .ok g ∧
      hear ((seatAt h iU3).ledger s) rs = some (H, F, []) ∧
      (seatAt h iU3).setLedger s F = .ok s1 ∧ (seatAt h iU3).setHeard s1 H = .ok s2 ∧
      s' = (seatAt h iU3).setWeightClaim s2 w := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  exact Came.decide_hears hd'

/-- **THE TWO TOPS JOINED, AT EVERY PUBLIC RECORD.** -/
def K06HonestWholeStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (s : S) (c : NCells) (mask : Nat → E), K6On W s → K6MoreB s = true → K6RoomB W s = true →
    (∀ g : Given, given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g →
      (dataOf c).Holds ∧ HonestHead c.toCells) →
    ∀ (pts : List E) (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E),
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     DrawsOk pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) →
    ∃ (rs : List Fmt.RoundView) (s' : S) (gs : List (List (Nat × List UInt64))) (H : HeardAll),
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     HeardAre pts gam om rsS rsP rsN rsL H) ∧
    ShapedAs (drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) rs
      (@rounds (parOf W.hS (workOf W)).sizes) ∧
    ClosedWhole (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask ∧
    b.decide s rs gs = .ok s' ∧ WellLaid ((seatAt W.hS (readsOf W)).ledger s) ∧
    (parOf W.hS (workOf W)).ok = true ∧ hasFeatures (parOf W.hS (workOf W)) ∧
    (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true ∧
    (∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V) ∧
    Canonical rs ∧
    Sound.NoBad (ruleK6T (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask) rs ∧
    Opened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask

theorem k06HonestWhole : K06HonestWholeStatement := by
  intro W l b hb s c mask hOn hMore hRoom hc pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL hD
  have hOn' := hOn
  obtain ⟨a1, a2, a3, a4, a5, _⟩ := hOn'
  have hRoom' := hRoom
  unfold K6RoomB at hRoom'
  rw [Bool.and_eq_true] at hRoom'
  have hgiven := hRoom'.1
  cases hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s with
  | error e => rw [hg] at hgiven; cases hgiven
  | ok g =>
    obtain ⟨hH, hC⟩ := hc g hg
    obtain ⟨z, y, hz, hty, hP, rfl⟩ :=
      Came.given_ok (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s g hg
    letI : Sizes := (parOf W.hS (workOf W)).sizes
    letI : Policy := (parOf W.hS (workOf W)).policy
    letI : Request := (seatAt W.hS (readsOf W)).request s
    letI : Token := ⟨y⟩
    obtain ⟨_, hzt, _⟩ := letters_of_lookup (parOf W.hS (workOf W)).sT
      (parOf W.hS (workOf W)).floor z.1 z.2 a2 hP
    letI : FinalNorm.In := (fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
    letI : In := (fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
    obtain ⟨rs, H, G, R, hE⟩ := honestRun_exists_eq c mask a1 hH hzt pts gam epsS down om epsP epsN
      epsL rsS rsP rsN rsL hD ((roomB_iff _ _).mp hRoom'.2)
    have RK : HonestRunK6 W.hS (readsOf W) (workOf W) s c mask rs := ⟨_, _, H, G, hg, hH, hC, R⟩
    obtain ⟨s', gs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := k06Honest W l b hb s c mask rs hOn hMore RK
    -- what the seat reads back at s' is H
    have hat : (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s' := by
      obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
      have hr : readsOf W = iU3 := by
        unfold readsOf
        rw [hu]
        rfl
      rw [hr]
      rw [← hbb] at h1
      exact h1
    obtain ⟨g2, H2, F2, w2, s1, s2, hg2, hhear2, e1, e2, hs'⟩ :=
      decide_hears_at W.hS (readsOf W) (workOf W) l s s' rs gs hat
    rw [hg] at hg2
    have hgg := (Except.ok.inj hg2).symm
    subst hgg
    have hsame : some (H2, F2, ([] : List Fmt.RoundView)) = some (H, G, []) := hhear2.symm.trans R.hears
    have hH2 : H2 = H := congrArg Prod.fst (Option.some.inj hsame)
    obtain ⟨_, bH, _, _⟩ := seatBack_at W.hS (readsOf W) (workOf W) s _ rs [] F2 H2 w2 s1 s2 hg a1
      R.can hhear2 e1 e2
    refine ⟨rs, s', gs, H, by rw [hs', ← hH2]; exact bH, hE, R.shaped,
      Came.rowRides W l _ hb s c mask s' rs gs h1 h2 h3 h4 h5 h6 h7 h8 h9,
      h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.honestRun_exists_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06HonestWhole
