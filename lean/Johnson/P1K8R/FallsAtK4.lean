-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallsAtK4.lean: THE HONEST SIDE's FRAME: THE BOUND ON THE FIRST CHAIN's FALLS AT THE
FRAME's AUTHORS' OWN LISTS (`falls_five_by_owner`, Johnson/P1K8R/FallsAtLists.lean), WITH THE
HYPOTHESIS ON THE FEED-FORWARD LAYERS' OWN ROUNDS' FIRST FALL (hF4) EXCHANGED FOR AN INEQUALITY
BETWEEN TWO TERMS (hq4). A lemma; NONE OF THE LIBRARY's GOALS. A joining: one call. Nothing on
completeness, soundness or hiding.

  **`falls_five_k4`**   `falls_five_by_owner`; that kind's authors' k4_fallDebt_form
      (Johnson/Desc/ProofFile/Honest/K4/Law/FallForm.lean); file_head, places_nodup (the frame's
      authors')
Why. A check, by Lean, that their law has the form that hF4 asks: they held it by a program on the
two texts.
Limits. hF4 IS NOT PAID: IT IS EXCHANGED: qF is an open letter: whoever calls this picks qF at or
above k4ZeroBound at these falls, and the right side grows with it. k4ZeroBound is their term: a
factor for the sampler's bias times the fall's stated share, not the share. Their files' own limits
hold here too. All that Johnson/P1K8R/FallsAtLists.lean says under "Limits" stands: A BOUND UNDER
SIXTEEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING; A SUM OF LETTERS: no number follows, and
nothing says that the right side is below 1. hF9 stays. At strings of hash blocks alone. The head h
is a hypothesis; the full size alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FallsAtLists
import Johnson.Desc.ProofFile.Honest.K4.Law.FallForm

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
/-- **`falls_five_by_owner` (Johnson/P1K8R/FallsAtLists.lean) WITH hF4 EXCHANGED FOR AN INEQUALITY
ON THE LETTER qF**: hq4: at every member, group and plan the feed-forward layers' own kind's
authors' term k4ZeroBound (Johnson/Desc/ProofFile/Honest/K4/Law/FallCount.lean) is at most qF at
that kind's first fall. ONE CALL of their k4_fallDebt_form (Law/FallForm.lean), whose end is hF4's
text. SIXTEEN NAMED HYPOTHESES STAY SIXTEEN. -/
theorem falls_five_k4 {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs)
    {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (k : Coins Bk) (p₂ p₃ : Nat → ℝ≥0∞)
    (kapL kapH : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0)
    (hXc : Xc = fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R)
    (hRd : ready (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk (G.prover H) w₀ rc x k = .ok R)
    (hn : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = []) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hseat : ∀ mk ∈ marksHead Z Bs.G₀, markSeat mk.place = true)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Z Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qMHead kapL kapH b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hF9 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ l p u, l < 25 → IM.k9At Z l = some p → Desc.K9.testsWhere Z.p.X l 0 = some u →
      ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l) ∈
        repsAt c.blocksInOrder G.falls₁ b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two)
        (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) 0 b
        (b' :: B ++ [e₁]) dsb [] (PWith Z c Bs Pr b)
        (qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))))
    (hq4 : ∀ b gk hp, ProofFile.Honest.K4.k4ZeroBound ≤
      qF b (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s') :
    Iop.prRho {ρ : Iop.Rho (chainsOf (_root_.Run.ckP .two) D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt (_root_.Run.ckP .two) D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (marksHead Z Bs.G₀ ++ fitMarks pre₁)
        (priceAt pre₁ (marksHead Z Bs.G₀) (qMHead kapL kapH) (repsAt c.blocksInOrder G.falls₁) qF)
        pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).shared.blocksInOrder) p₂).map
            (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).second.blocksInOrder) p₃).map
            (·.p)).sum) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨-, hpl, -⟩ := file_head h.toAtMg
  exact falls_five_by_owner h hB tF tJ t3 G H k p₂ p₃ kapL kapH notGood r0 x Xc PM Pr qF w₀ rc R
    hG hXc hRd hn hf₂ hf₃ cut hseat hM hPM hF9
    (ProofFile.Honest.K4.k4_fallDebt_form h.scope h.reads O (places_nodup hpl).1 cut G.falls₁ r0
      (PWith Z c _ Pr) qF hq4) hqF hPr

end

end P1K8

#print axioms P1K8.falls_five_k4
