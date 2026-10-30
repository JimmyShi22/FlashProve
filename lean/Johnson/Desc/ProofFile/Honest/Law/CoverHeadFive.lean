-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/CoverHeadFive.lean: the bound of `falls_six`
(Honest/Law/CoverHeadSix.lean) on the chance that a run meets a fall, at the three lists and numbers
that are laid: the falls `fallsFull` (Honest/Law/FallsFull.lean), the owners' marks `marksHead` and
the marks' numbers `qMHead` (Honest/Law/MarksHead.lean). At `qMHead` the field `hq0` of `FirstAsks`
is proved (`hq0_head`). So five of the sixteen fields are left as hypotheses. `StopsFit`, a
hypothesis of `falls_six`, is paid here by `stopsFit_head` (Honest/Law/StopsHead.lean) from `hR` and
`hn`: no half of the first chain is of the kind `frame`.

  1  `falls_five`   the bound

Limits.
  * The five fields are hypotheses: `hseat`, `hM`, `hPM` (the owners' marks, their bounds, and what
    their silence gives) and `hF`, `hP'` (the owners' bounds for the falls, and the conditions of
    these bounds). None is proved here. For `hseat` and `hM` each owner's own lemmas serve through
    `marksHead_seat` and `marksHead_hM`, as far as the owners have them.
  * Open arguments: `kap₃` and `kap₆` (the lookups' authors' letter and K6's authors'), `notGood`
    and `r0` (see `fallsHead`), and the numbers `qF` for the falls.
  * Further hypotheses: `hC`, `hR`, `hn`, `hf₂`, `hf₃`, and `hG` (the rows' list of falls of the
    first chain is `fallsFull`). All that is assumed of the other two chains sits in `hf₂` and
    `hf₃`. `hn` has the form of the end of `wider_no_frame` (Honest/Thread/FirstFill.lean, another
    thread's file); the call is not made here.
  * No number follows from the theorem. The full size alone, at the hash function `secondHashFunction`.
  * The theorem proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadSix
import Johnson.Desc.ProofFile.Honest.Law.FallsFull
import Johnson.Desc.ProofFile.Honest.Law.MarksHead
import Johnson.Desc.ProofFile.Honest.Law.StopsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)
open P5J (TS)

variable {W₀ Rc Ky Tr X₀ X TF TJ T3 : Type} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {xh : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- The bound at `fallsFull`, `marksHead` and `qMHead`, under `P5J.AtMgA`, from five fields of
`FirstAsks`. `F₀` is the proof file's description. The hypotheses after it, in their order: `cut`,
`hG`, `hR`, `hn`, `hf₂`, `hf₃`, `hXc`, and the five fields `hseat`, `hM`, `hPM`, `hF`, `hP'`. -/
theorem falls_five (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (G₀ : ProofFile.Ground) (kap₃ kap₆ : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat) :
    let F₀ := P5J.F0T OnBytes.secondHashFunction Zp Np cF
    ∀ (G : Sides F₀ Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : ProofFile.Inst) (k : Coins Bk) (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (p₂ p₃ : Nat → ℝ≥0∞) (pre₁ : List (Block F₀.S₁ F₀.Cl)) (e₁ : Block F₀.S₁ F₀.Cl)
    (_ : F₀.first.blocksInOrder = pre₁ ++ [e₁])
    (_ : G.falls₁ = fallsFull Zp G₀ notGood r0)
    (_ : ready F₀ Bk (G.prover H) w₀ rc x k = .ok R)
    (_ : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (_ : G.falls₂ = []) (_ : G.falls₃ = [])
    (Xc : List Fmt.Drawn → ChainAt F₀.S₁ F₀.Cl (Local W₀ Rc ProofFile.Inst Tr) X)
    (_ : Xc = fun _ => at₁ F₀ (G.prover H) w₀ rc x R)
    (PM : Block F₀.S₁ F₀.Cl → List Fmt.Drawn → Prop)
    (P : Block F₀.S₁ F₀.Cl → List Fmt.Drawn → F₀.S₁ → Prop)
    (qF : Block F₀.S₁ F₀.Cl → Fall F₀.S₁ → ℝ≥0∞)
    (_ : ∀ mk ∈ (marksHead Zp G₀), markSeat mk.place = true)
    (_ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qMHead kap₃ kap₆ b mk))
    (_ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F₀.first.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ ((marksHead Zp G₀) ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (_ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ repsAt F₀.first.blocksInOrder G.falls₁ b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g 0 b (b' :: B ++ [e₁]) dsb [] (P b) (qF b g))
    (_ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F₀.first.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ ((marksHead Zp G₀) ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (F₀.first.blocksInOrder.map below) F₀.start₁ A.length (F₀.pub x, s')) →
      P b fr s'),
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (marksHead Zp G₀ ++ fitMarks pre₁)
          (priceAt pre₁ (marksHead Zp G₀) (qMHead kap₃ kap₆) (repsAt F₀.first.blocksInOrder G.falls₁) qF)
          pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks F₀.shared.blocksInOrder) p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks F₀.second.blocksInOrder) p₃).map (·.p)).sum) := by
  intro F₀ G H w₀ rc x k R p₂ p₃ pre₁ e₁ cut hG hR hn hf₂ hf₃ Xc hXc PM P qF hseat hM hPM hF hP'
  obtain ⟨ρ₀⟩ : Nonempty (Iop.Rho (chainsOf C D tF tJ t3).sh) := inferInstance
  have Sf : StopsFit F₀ (G.prover H) D pre₁ e₁ :=
    stopsFit_head C tF tJ t3 h.toAtMg cut hR ρ₀
      (due_at_data C hC tF tJ t3 h.laid.data (draws_decl h.scope h.laid) ρ₀) hn
  exact falls_six C hC tF tJ t3 h G H w₀ rc x k R (marksHead Zp G₀) p₂ p₃ pre₁ e₁ cut G₀
    (K8.k8ColsAt G₀) (K8.k8TauAt G₀) (P1K8.k8ShareAt Zp G₀) notGood r0 hG hR Sf hf₂ hf₃ Xc hXc PM
    (qMHead kap₃ kap₆) P qF hseat (hq0_head kap₃ kap₆ pre₁) hM hPM hF hP'

end ProofFile.Honest

#print axioms ProofFile.Honest.falls_five
