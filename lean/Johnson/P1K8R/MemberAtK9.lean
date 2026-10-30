-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MemberAtK9.lean: THE HONEST SIDE's FRAME: THE MEMBER OF `FirstAsks` AT ONE RUN WITH
THE BOUND ON THE BATCHING's FALL OF THE FREE SLOTS ASKED AT NO SEGMENT: AT ALL 25 IT IS EXCHANGED
FOR INEQUALITIES ON THE LETTER qF: EXCHANGED, NOT PAID. A lemma; NONE OF THE LIBRARY's GOALS. A
joining. Nothing on completeness, soundness or hiding.

  **`firstAsks_k9`**   `firstAsks_more` (Johnson/P1K8R/MemberMore.lean); `attE_handed`
      (FieldAtAtt.lean); `layE_handed` (FieldAtLay.lean); `headE_handed` (FieldAtHead.lean); the
      batching's authors' k9_fallDebt_form_att_with, k9_fallDebt_form_lay_with,
      k9_fallDebt_form_head_with (Johnson/Desc/ProofFile/Honest/K9/FallFormAttWith.lean,
      FallFormLayWith.lean, FallFormHeadWith.lean)
How. `firstAsks_more` at E := the three sentences at the batching of an attention segment AND the
batching's authors' BatFrontLay at the batching of a feed-forward segment AND their goodW at the
batching of the output head's segment. Its hF9: the batching's authors' three lemmas, which spend E.
Its hE: `attE_handed`, `layE_handed` and `headE_handed`.
Against `firstAsks_lay` (Johnson/P1K8R/MemberAtLay.lean). Gone: hF9h. Come: hq9h, the batching's
authors' inequality on qF at l = 24. The condition in the end has a fourth part.
Limits. A MEMBER UNDER ELEVEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING: h, hB, hG, cut, hK3,
hq9, hq9l, hq9h, hq4, hqF, hPr. AT ALL 25 SEGMENTS THE BOUND IS NOT PAID: IT IS EXCHANGED (the
batching's authors' own word): qF is an open letter: whoever calls this lays qF, at these 25 falls,
at or above their bound, and the sum grows with it; hq9, hq9l and hq9h are not hqF. THEIR OWN LIMITS
HOLD: true for nothing where the condition holds of no state or the fall is counted at no member;
the letter notGood has no payer. THE BATCHING's AUTHORS' HEAVIEST LIMIT HOLDS: NO MEMBER: no walk,
state or list of marks is given at which the premises hold together; that any walk returns is proved
nowhere; at the output head's segment the premises stand at member number 347. THE FEED-FORWARD
LAYERS' AUTHORS' CAUTION HOLDS: the event that the layers' fall names is not saved: it has moved
into the layers' own yes: whoever sums shares may not drop that fall's: hq4 stays. THE CONDITION IN
THE END ASKS MORE OF THE STATE THAN THE CALLER's Pr (it holds of fewer states): it stands there as
an unnamed text of Z, c and Bs: it names no run. hK3 is asked at every front; what the marks'
silence costs is told in Johnson/P1K8R/MarksAtHead.lean and MarksAtHeadBlocks.lean. THE PROVER IS A
LETTER: no filling is named; what the field hands is the state of a walk that returns. At strings of
hash blocks alone. The head h is a hypothesis; the full size alone. No number is evaluated. One
option is raised (maxHeartbeats). Tactics that search: omega four times.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.MemberMore
import Johnson.P1K8R.FieldAtLay
import Johnson.P1K8R.FieldAtHead
import Johnson.Desc.ProofFile.Honest.K9.FallFormAttWith
import Johnson.Desc.ProofFile.Honest.K9.FallFormLayWith
import Johnson.Desc.ProofFile.Honest.K9.FallFormHeadWith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT WholeD chainsOf)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.K3.Good (markK3 markOut)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first repsAt
  priceAt hin_reps hp₁_sum hp₂_sum places_nodup ChainProgress Mid marksQuiet Prover Ready at₁
  letter_starts letter_tree file_head hz_head Sides ProverCoinCounts Coins ready fallAt drawsAt gates₁ gates₂
  gates₃ kit_two falls_five fallsFull fallsFull_seats marksHead qMHead hq0_head part1_sub k3_sub
  k5_sub k6_sub fallsHead linkFalls)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open H2K5.Honest (HeldLive)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 4000000 in
/-- **THE MEMBER OF THE FRAME's `FirstAsks` AT ONE RUN, WITH hF9 ASKED NOWHERE**: at the lists and
letters of `firstAsks_lay`; the condition is `PWith` at the caller's Pr AND the three sentences at
an attention segment's batching AND the batching's authors' BatFrontLay at a feed-forward segment's
AND their goodW at the output head's. hq9, hq9l, hq9h: their inequalities on qF at the twelve odd l,
at the twelve even l below 24, and at l = 24. -/
theorem firstAsks_k9 {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (kapL : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (w₀ : W₀) (rc : Rc) (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hK3 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks Z Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (fun _ => True) ((mk.share.num : ℝ≥0∞) * kapL))
    (hq9 : ∀ g, g < 12 → ∀ b p u, IM.k9At Z (2 * g + 1) = some p →
      Desc.K9.testsWhere Z.p.X (2 * g + 1) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) /
          ((ProofFile.Honest.K9.sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1))))
    (hq9l : ∀ g, g < 12 → ∀ b p u, IM.k9At Z (2 * g) = some p →
      Desc.K9.testsWhere Z.p.X (2 * g) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) /
          ((ProofFile.Honest.K9.sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g))))
    (hq9h : ∀ b p u, IM.k9At Z 24 = some p → Desc.K9.testsWhere Z.p.X 24 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) /
          ((ProofFile.Honest.K9.sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood 24)))
    (hq4 : ∀ b gk hp, ProofFile.Honest.K4.k4ZeroBound ≤
      qF b (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R) (0 +
                             (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R).start = some a →
      walk (at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R).lay
        ((at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R).steps.take (0 + (A.flatMap
                      (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s') :
    FirstAsks (F := P5J.F0T OnBytes.secondHashFunction Z Np c) (_root_.Run.ckP .two) G.falls₁
      (marksHead Z Bs.G₀)
      (priceAt pre₁ (marksHead Z Bs.G₀)
        (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
        (repsAt c.blocksInOrder G.falls₁) qF) pre₁ e₁ x
      (fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R)
      (fallSeat P5J.At.links) markSeat (fun _ _ => True)
      (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
      (PWith Z c Bs
        (fun b fr s' => Pr b fr s' ∧
          ((∀ g, g < 12 → c.blocksInOrder[14 * (2 * g + 1) + 9]? = some b →
           ∀ a pC pD, (P5J.At.X Z).A[g]? = some a →
           Look.placeAt (P5J.At.X Z) (2 * g + 1) false = some pC →
           Look.placeAt (P5J.At.X Z) (2 * g + 1) true = some pD →
           HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧
             Clause pD (s'.tl?.bind (·.heard))) ∧
            (∀ g, g < 12 → c.blocksInOrder[14 * (2 * g) + 9]? = some b →
             ∀ p4 u, LPFK9.k4ParAt Z Bs.G₀ (2 * g) = some p4 →
             Desc.K9.testsWhere Z.p.X (2 * g) 0 = some u →
             ProofFile.Honest.K9.BatFrontLay p4 u.2.2.filled s') ∧
            (c.blocksInOrder[14 * 24 + 11]? = some b →
             ∀ Lk p w, ProofFile.Honest.K9.SeatedFree c Z 24 9 Lk p w →
             ProofFile.Honest.K9.goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled))))
      qF (repsAt c.blocksInOrder G.falls₁) :=
  firstAsks_more h hB G H kapL notGood r0 x Pr _ qF w₀ rc R hG cut hK3
    (fun A b b' B e hs hr l p u hl hp hu hg dsb hk => by
      by_cases hev : l % 2 = 0
      · by_cases h24 : l = 24
        · subst h24
          exact ProofFile.Honest.K9.k9_fallDebt_form_head_with h Bs G.falls₁ notGood cut _ qF
            (fun b hb Lk p w Sd _ _ hP => hP.2.2.2 hb Lk p w Sd) hq9h
            A b b' B e hs hr p u hp hu hg dsb hk
        · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
          exact ProofFile.Honest.K9.k9_fallDebt_form_lay_with h hB G.falls₁ notGood cut _ qF
            (fun g hg b hb p4 u e4 eu _ _ hP => hP.2.2.1 g hg hb p4 u e4 eu) hq9l
            A b b' B e hs hr g p u (by omega) hp hu hg dsb hk
      · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
        exact ProofFile.Honest.K9.k9_fallDebt_form_att_with h {} G.falls₁ notGood cut Bs _ qF
          (fun g hg b hb a pC pD ha hC hD _ _ hP => hP.2.1 g hg hb a pC pD ha hC hD) hq9
          A b b' B e hs hr g p u (by omega) hp hu hg dsb hk)
    hq4 hqF hPr
    (fun A b b' B e hs hr fr a z s' h1 h2 h3 h4 y1 y2 hv hw =>
      ⟨attE_handed h hB G.falls₁ (G.prover H) x w₀ rc R cut A b b' B e hs hr fr a z s' h1 h2 h3 h4
          y1 y2 hv hw,
        layE_handed h hB G.falls₁ (G.prover H) x w₀ rc R cut A b b' B e hs hr fr a z s' h1 h2 h3 h4
          y1 y2 hv hw,
        headE_handed h hB G.falls₁ (G.prover H) x w₀ rc R cut A b b' B e hs hr fr a z s' h1 h2 h3
          h4 y1 y2 hv hw⟩)

end

end P1K8

#print axioms P1K8.firstAsks_k9
