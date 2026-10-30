-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallsAtMarks.lean: THE HONEST SIDE's FRAME: THE BOUND ON THE FIRST CHAIN's FALLS AT
THE FRAME's AUTHORS' OWN LISTS (`falls_five_k4`, Johnson/P1K8R/FallsAtK4.lean), WITH ITS THREE
HYPOTHESES ON MARKS (hseat, hM, hPM) EXCHANGED FOR ONE: THE LOOKUPS' MARKS' BOUND (hK3). A lemma;
NONE OF THE LIBRARY's GOALS. A joining: one call. Nothing on completeness, soundness or hiding.

  **`falls_five_marks`**   `falls_five_k4`; `marksHead_seated` (Johnson/P1K8R/MarksAtHead.lean);
      `marksHead_hM_owners` (MarksAtHeadBlocks.lean)
Why hPM goes. PM is a free letter of the bound: what an author is handed of the challenges in front
of its mark. MarkDebt asks its number at every front at which PM holds; every author's law that is
called holds at every such letter: so PM is set to what holds always, and hPM, which asks PM of the
fronts met, is trivial. WHAT IS GIVEN UP: PM is the door by which "no fall so far" and the silence
of the marks in front reach a later mark's bound. None of the five laws goes through it. WHOEVER HAS
A MARK WHOSE BOUND HOLDS AT SUCH FRONTS ALONE CALLS `falls_five_k4`, WHICH KEEPS PM: this lemma is a
corner of that one, not its heir.
Limits. hK3 IS A HYPOTHESIS, AND AT PM := fun _ _ => True IT IS ASKED AT EVERY FRONT: the heaviest
form of that binder (the lookups' authors' k3Marks_debt,
Johnson/Desc/ProofFile/Honest/K3/Good/MarksHead.lean, ends at that letter, under hypotheses of its
own). THE MARKS' BOUNDS THAT ARE SPENT COME WITH THEIR AUTHORS' OWN LIMITS: all that
Johnson/P1K8R/MarksAtHead.lean and MarksAtHeadBlocks.lean say under "Limits" stands. qMHead's SECOND
LETTER IS SET: the right side is that of `falls_five_k4` at kapH := Iop.kapSl 128 ^ 3 / p ^ 3. All
that Johnson/P1K8R/FallsAtK4.lean and FallsAtLists.lean say under "Limits" stands: A BOUND UNDER
FOURTEEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING; A SUM OF LETTERS: no number follows, and
nothing says that the right side is below 1. hF9, hq4, hqF and hPr stay. THE FRAME's AUTHORS' BOUND
THAT ALL THIS CALLS MAY TURN IN ITS STATEMENT: this lemma turns with it. At strings of hash blocks
alone. The head h is a hypothesis; the full size alone. No option is raised; no tactic.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.FallsAtK4
import Johnson.P1K8R.MarksAtHeadBlocks

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

/-- **`falls_five_k4` (Johnson/P1K8R/FallsAtK4.lean) WITH THE THREE HYPOTHESES ON MARKS SPENT**:
hseat := `marksHead_seated`; hM := `marksHead_hM_owners`, at the letter PM := fun _ _ => True; hPM
is then trivial. IN THEIR STEAD hK3: the lookups' marks' bound, at every front. qMHead's second
letter is set. FOURTEEN NAMED HYPOTHESES FOR SIXTEEN. -/
theorem falls_five_marks {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs)
    {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (k : Coins Bk) (p₂ p₃ : Nat → ℝ≥0∞)
    (kapL : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0)
    (hXc : Xc = fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R)
    (hRd : ready (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk (G.prover H) w₀ rc x k = .ok R)
    (hn : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = []) (cut : c.blocksInOrder = pre₁ ++ [e₁])
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
        (priceAt pre₁ (marksHead Z Bs.G₀)
          (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
          (repsAt c.blocksInOrder G.falls₁) qF)
        pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).shared.blocksInOrder) p₂).map
            (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).second.blocksInOrder) p₃).map
            (·.p)).sum) :=
  falls_five_k4 h hB tF tJ t3 G H k p₂ p₃ kapL _ notGood r0 x Xc (fun _ _ => True) Pr qF w₀ rc R
    hG hXc hRd hn hf₂ hf₃ cut (marksHead_seated _ _)
    (marksHead_hM_owners (PM := fun _ _ => True) h hB kapL cut hK3)
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) hF9 hq4 hqF hPr

end

end P1K8

#print axioms P1K8.falls_five_marks
