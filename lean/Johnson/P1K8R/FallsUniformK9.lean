-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FallsUniformK9.lean: THE HONEST SIDE's FRAME: THE BOUND ON THE FIRST CHAIN's FALLS IN
THE FRAME's AUTHORS' FORM WITH CONDITIONS AND NUMBERS LAID ONCE, IN FRONT OF THE RUN's LETTERS
(falls_uniform_listed), WITH THE BOUND ON THE BATCHING's FALL OF THE FREE SLOTS ASKED AT NO SEGMENT:
EXCHANGED AT ALL 25, NOT PAID: `falls_uniform_lay` (Johnson/P1K8R/FallsUniformLay.lean) WITH hF9h
GONE. A lemma; NONE OF THE LIBRARY's GOALS. A joining: one call. Nothing on completeness, soundness
or hiding.

  **`falls_uniform_k9`**   the frame's authors' falls_uniform_listed
      (Johnson/Desc/ProofFile/Honest/Law/FallsUniformListed.lean), kit_two (KitTwo.lean);
      `firstAsks_k9` (Johnson/P1K8R/MemberAtK9.lean); `marksHead_seated` (MarksAtHead.lean);
      `marksHead_hM_owners` (MarksAtHeadBlocks.lean)
Against `falls_uniform_lay`. Gone: hF9h. Come: hq9h (the batching's authors' inequality on qF at l =
24). The other thirteen hypotheses and the end are that lemma's to the sign.
Limits. NOT A NUMBER: qF, kapL, notGood and r0 are open letters; nothing says that the sum is below
1. FOURTEEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING: h, hB, hG, hn, hf₂, hf₃, cut, hK3, hq9,
hq9l, hq9h, hq4, hqF, hPr. All that Johnson/P1K8R/MemberAtK9.lean and FallsUniformAtt.lean say under
"Limits" stands: at all 25 segments the bound is exchanged, not paid; no member: no walk, state or
list of marks is given at which the premises hold together; the feed-forward layers' fall's share is
not saved; hK3 is asked at every front; every author's law keeps its own limits; Tied is a letter;
the bound stands at each fixed k. THE FORM THAT IS CALLED IS falls_uniform_listed AS IT STANDS: this
lemma says no more than that statement bears. THE PROVER IS A LETTER: no filling is named; where no
walk returns the fields say nothing. At strings of hash blocks alone. The head h is a hypothesis;
the full size alone. No option is raised; no tactic.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.MemberAtK9
import Johnson.Desc.ProofFile.Honest.Law.FallsUniformListed

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
open ProofFile.Honest (falls_uniform_listed)
open H2K5.Honest (HeldLive)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

/-- **THE BOUND ON THE FIRST CHAIN's FALLS, ONE SUM, LAID IN FRONT OF THE RUN's LETTERS: THE SAME
FOR ALL TIED INPUTS AND ALL OF THE RUN's OWN DRAWS; hF9 IS ASKED NOWHERE**: the frame's authors'
falls_uniform_listed, as in `falls_uniform_lay`, with fallsBounded and fallsConditionMet the fields
hF and hP' of `firstAsks_k9` at each tied run that can be made ready. FOURTEEN NAMED HYPOTHESES. -/
theorem falls_uniform_k9 {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs)
    {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (kapL : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (Tied : W₀ → Rc → ProofFile.Inst → Prop)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0)
    (hn : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = []) (cut : c.blocksInOrder = pre₁ ++ [e₁])
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
    (hPr : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
      (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁), Tied w₀ rc x →
      ready (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
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
    ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk), Tied w₀ rc x →
      Iop.prRho {ρ : Iop.Rho (chainsOf (_root_.Run.ckP .two) D tF tJ t3).sh |
          (fallAt G H w₀ rc x k (drawsAt (_root_.Run.ckP .two) D tF tJ t3 ρ)).isSome = true} ≤
        ((List.range pre₁.length).map
          (priceAt pre₁ (marksHead Z Bs.G₀)
            (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)))
            (repsAt c.blocksInOrder G.falls₁) qF)).sum :=
  falls_uniform_listed (_root_.Run.ckP .two) kit_two tF tJ t3 h Bs.G₀ kapL _ notGood r0 G H pre₁ e₁
    cut hG hn hf₂ hf₃ Tied (fun _ _ => True) _ qF (marksHead_seated _ _)
    (marksHead_hM_owners (PM := fun _ _ => True) h hB kapL cut hK3)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun w₀ rc x k R ht hr =>
      (firstAsks_k9 h hB G H kapL notGood r0 x Pr qF w₀ rc R hG cut hK3 hq9 hq9l hq9h hq4 hqF
        (hPr w₀ rc x k R ht hr)).hF)
    (fun w₀ rc x k R ht hr =>
      (firstAsks_k9 h hB G H kapL notGood r0 x Pr qF w₀ rc R hG cut hK3 hq9 hq9l hq9h hq4 hqF
        (hPr w₀ rc x k R ht hr)).hP')

end

end P1K8

#print axioms P1K8.falls_uniform_k9
