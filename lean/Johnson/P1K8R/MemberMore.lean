-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MemberMore.lean: THE HONEST SIDE's FRAME: THE MEMBER OF `FirstAsks` AT ONE RUN, AT THE
FRAME's AUTHORS' OWN LISTS, WITH A SECOND LETTER E BESIDE THE CALLER's CONDITION Pr: WHAT THE
MEMBERS `firstAsks_att` (Johnson/P1K8R/MemberAtAtt.lean) AND `firstAsks_lay` (MemberAtLay.lean)
SHARE. A lemma; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or
hiding.

  **`firstAsks_more`**   `firstAsks_own` (Johnson/P1K8R/CountedAtOwn.lean); `full_cases`
      (FallsAtLists.lean); `marksHead_seated` (MarksAtHead.lean), `marksHead_hM_owners`
      (MarksAtHeadBlocks.lean); the feed-forward layers' authors' k4_fallDebt_form
      (Johnson/Desc/ProofFile/Honest/K4/Law/FallForm.lean); LPFK9.places_nodup
      (Johnson/LPFK9R/ToldInScope.lean); fallsFull_seats, hq0_head, part1_sub, k3_sub, k5_sub,
      k6_sub (the frame's authors')
How. hFr of `firstAsks_own` by the list's cases: the smallness test's fifty are that member's own;
the fall of the free slots is hF9, asked at the condition Pr AND E; the feed-forward layers' twelve
by their authors' lemma, which binds the condition as a free letter. hPr of `firstAsks_own`: hPr and
hE.
Limits. A MEMBER UNDER TEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING: h, hB, hG, cut, hK3, hF9,
hq4, hqF, hPr, hE. E IS A LETTER: whoever lays it pays hE at the states that the field hands at this
run; hF9 is asked under Pr AND E: so E may be used to prove it. hK3 is asked at every front; every
author's law keeps its own limits. THE PROVER IS A LETTER: no filling is named; what the field hands
is the state of a walk that returns. At strings of hash blocks alone. The head h is a hypothesis;
the full size alone. No number is evaluated. One option is raised (maxHeartbeats). No tactic that
searches.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FallsAtMarks

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
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

set_option maxHeartbeats 4000000 in
/-- **THE MEMBER OF THE FRAME's `FirstAsks` AT ONE RUN, AT THE CONDITION `PWith` OF "Pr AND E"**:
the falls G.falls₁ (= fallsFull, hG), the marks marksHead, the marks' letter PM := fun _ _ => True.
hF9: the bound on the fall of the free slots at all 25 segments, under that condition. hPr, hE: Pr
and E at the states that the field hands at this run. -/
theorem firstAsks_more {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (kapL : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Pr E : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (w₀ : W₀) (rc : Rc) (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hK3 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks Z Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (fun _ => True) ((mk.share.num : ℝ≥0∞) * kapL))
    (hF9 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ l p u, l < 25 → IM.k9At Z l = some p → Desc.K9.testsWhere Z.p.X l 0 = some u →
      ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l) ∈
        repsAt c.blocksInOrder G.falls₁ b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two)
        (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) 0 b
        (b' :: B ++ [e₁]) dsb [] (PWith Z c Bs (fun b fr s' => Pr b fr s' ∧ E b fr s') b)
        (qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))))
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
      Pr b fr s')
    (hE : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
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
      E b fr s') :
    FirstAsks (F := P5J.F0T OnBytes.secondHashFunction Z Np c) (_root_.Run.ckP .two) G.falls₁
      (marksHead Z Bs.G₀)
      (priceAt pre₁ (marksHead Z Bs.G₀)
        (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
        (repsAt c.blocksInOrder G.falls₁) qF) pre₁ e₁ x
      (fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R)
      (fallSeat P5J.At.links) markSeat (fun _ _ => True)
      (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
      (PWith Z c Bs
        (fun b fr s' => Pr b fr s' ∧ E b fr s'))
      qF (repsAt c.blocksInOrder G.falls₁) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  have eB : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  rw [eB] at O
  have hnd : (c.blocksInOrder.map (·.place)).Nodup := LPFK9.places_nodup h.scope h.reads O
  have hfs : ∀ f ∈ G.falls₁, (fallSeat P5J.At.links) f.place = true := by
    rw [hG]
    exact fallsFull_seats h Bs.G₀
  refine firstAsks_own h hB G.falls₁ (marksHead Z Bs.G₀) x _ (fun _ _ => True) _ _ qF
    (G.prover H) w₀ rc R rfl (part1_sub Z Bs.G₀) (k3_sub Z Bs.G₀) (k6_sub Z Bs.G₀)
    (k5_sub Z Bs.G₀) cut hfs (marksHead_seated _ _) (hq0_head kapL _ pre₁)
    (marksHead_hM_owners (PM := fun _ _ => True) h hB kapL cut hK3)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ hqF
    (fun A b b' B e hs hr fr a z s' h1 h2 h3 h4 y1 y2 hv hw =>
      ⟨hPr A b b' B e hs hr fr a z s' h1 h2 h3 h4 y1 y2 hv hw,
        hE A b b' B e hs hr fr a z s' h1 h2 h3 h4 y1 y2 hv hw⟩)
  intro A b b' B e hs hr g hg hnk dsb hk
  have hmem : g ∈ fallsFull Z Bs.G₀ notGood r0 := by
    rw [← hG]
    exact (List.mem_filter.1 hg).1
  rcases full_cases hmem with h8 | ⟨l, p, u, hl, hp, hu, rfl⟩ | ⟨gk, hp, hgk, hhp, rfl⟩
  · exact absurd h8 hnk
  · exact hF9 A b b' B e hs hr l p u hl hp hu hg dsb hk
  · exact ProofFile.Honest.K4.k4_fallDebt_form h.scope h.reads O hnd cut G.falls₁ r0
      (PWith Z c _ _) qF hq4 A b b' B e hs hr gk hp hgk hhp hg dsb hk

end

end P1K8

#print axioms P1K8.firstAsks_more
