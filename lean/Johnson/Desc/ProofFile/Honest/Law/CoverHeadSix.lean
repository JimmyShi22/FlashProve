-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/CoverHeadSix.lean: the bound on the chance that a run meets a
fall, at the proof file's description, at the list of falls `fallsHead` (Honest/Law/FallsHead.lean),
from the six fields of `FirstAsks` (Honest/Law/CoverAsks.lean) that wait on the owners of the
sub-protocols. It joins `falls_head` (Honest/Law/CoverHeadAll.lean), `firstAsks_reps`
(Honest/Law/CoverAsksReps.lean), `hz_head` (Honest/Law/CoverDraws.lean) and `fallsHead_seats_full`
(Honest/Law/FallsHeadFull.lean) under one hypothesis of the library, `P5J.AtMgA`. So that ten of the
sixteen fields are proved under that hypothesis is checked by Lean in one term.

  1  `falls_six`   the bound

Limits.
  * The six fields are hypotheses: `hseat`, `hq0`, `hM`, `hPM` (the owners' marks and their bounds)
    and `hF`, `hP'` (the owners' bounds for the falls, and the conditions of these bounds). None is
    proved here.
  * Further hypotheses: `hC` (on the kit of challenges), `hR` and `Sf` (on the prover's rows),
    `hf₂` and `hf₃` (the other two chains have no falls), `hG` (the rows' list of falls of the
    first chain is `fallsHead`).
  * All that is assumed of the other two chains sits in `hf₂` and `hf₃` (see
    Honest/Law/CoverHeadAll.lean). None of the three groups of authors that were asked answered
    that these chains have no fall.
  * The counted falls are `repsAt` and the numbers `priceAt`: choices (Honest/Law/CoverReps.lean,
    Honest/Law/CoverSum.lean). With them the first chain's part of the bound is the sum of the
    stated numbers `qM` and `qF`.
  * The list of the owners' marks `hm` is an argument. It is laid nowhere yet.
  * No number follows from the theorem. The full size alone, at the hash function `secondHashFunction`.
  * The theorem proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadAll
import Johnson.Desc.ProofFile.Honest.Law.CoverAsksReps
import Johnson.Desc.ProofFile.Honest.Law.FallsHeadFull

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
/-- The bound at the list `fallsHead`, under `P5J.AtMgA`, from the six fields of `FirstAsks` that
wait on the owners of the sub-protocols. `F₀` is the proof file's description. The hypotheses after
it, in their order: `cut`, `hG`, `hR`, `Sf`, `hf₂`, `hf₃`, `hXc`, and the six fields `hseat`, `hq0`,
`hM`, `hPM`, `hF`, `hP'`. -/
theorem falls_six (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    let F₀ := P5J.F0T OnBytes.secondHashFunction Zp Np cF
    ∀ (G : Sides F₀ Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : ProofFile.Inst) (k : Coins Bk) (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X) (hm : List Mark)
    (p₂ p₃ : Nat → ℝ≥0∞) (pre₁ : List (Block F₀.S₁ F₀.Cl)) (e₁ : Block F₀.S₁ F₀.Cl)
    (_ : F₀.first.blocksInOrder = pre₁ ++ [e₁])
    (G₀ : ProofFile.Ground) (cols tau : Nat → Nat) (share notGood : Nat → Odds) (r0 : Nat → Nat)
    (_ : G.falls₁ = fallsHead Zp G₀ cols tau share notGood r0)
    (_ : ready F₀ Bk (G.prover H) w₀ rc x k = .ok R) (_ : StopsFit F₀ (G.prover H) D pre₁ e₁)
    (_ : G.falls₂ = []) (_ : G.falls₃ = [])
    (Xc : List Fmt.Drawn → ChainAt F₀.S₁ F₀.Cl (Local W₀ Rc ProofFile.Inst Tr) X)
    (_ : Xc = fun _ => at₁ F₀ (G.prover H) w₀ rc x R)
    (PM : Block F₀.S₁ F₀.Cl → List Fmt.Drawn → Prop) (qM : Block F₀.S₁ F₀.Cl → Mark → ℝ≥0∞)
    (P : Block F₀.S₁ F₀.Cl → List Fmt.Drawn → F₀.S₁ → Prop)
    (qF : Block F₀.S₁ F₀.Cl → Fall F₀.S₁ → ℝ≥0∞)
    (_ : ∀ mk ∈ hm, markSeat mk.place = true)
    (_ : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (_ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ hm.filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (_ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy F₀.first.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
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
      silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (F₀.first.blocksInOrder.map below) F₀.start₁ A.length (F₀.pub x, s')) →
      P b fr s'),
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (hm ++ fitMarks pre₁)
          (priceAt pre₁ hm qM (repsAt F₀.first.blocksInOrder G.falls₁) qF) pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks F₀.shared.blocksInOrder) p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks F₀.second.blocksInOrder) p₃).map (·.p)).sum) := by
  intro F₀ G H w₀ rc x k R hm p₂ p₃ pre₁ e₁ cut G₀ cols tau share notGood r0 hG hR Sf hf₂ hf₃ Xc hXc
    PM qM P qF hseat hq0 hM hPM hF hP'
  subst hXc
  have hfs : ∀ f ∈ G.falls₁, fallSeat P5J.At.links f.place = true := by
    rw [hG]
    exact fallsHead_seats_full h G₀
  exact falls_head C hC tF tJ t3 G H w₀ rc x k R hm _ p₂ p₃ h.toAtMg cut hR Sf hf₂ hf₃
    (firstAsks_reps C G.falls₁ hm x _ PM qM P qF (file_head h.toAtMg).2.2 cut
      (file_head h.toAtMg).2.1 (hz_head h.toAtMg cut) hfs hseat hq0 hM hPM hF hP')

end ProofFile.Honest

#print axioms ProofFile.Honest.falls_six
