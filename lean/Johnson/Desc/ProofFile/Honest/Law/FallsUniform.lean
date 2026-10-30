-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallsUniform.lean: the bound of `falls_six`
(Honest/Law/CoverHeadSix.lean) with its conditions and numbers laid once, in front of input and
prover randomness. At every input of a letter `Tied` and all coins, the chance that an honest run
meets a listed bad event is at most one closed sum.

  1  `falls_uniform`   the bound

What parts from `falls_six`. The hypotheses are named binders in front of the colon, and there is no
`let`: the description `P5J.F0T OnBytes.secondHashFunction Zp Np cF` is written out. For five of its fields the
text has what they are by definition: `TS`, `ProofFile.Cl`, `cF.blocksInOrder`, `ProofFile.startS Zp` and `x.pub` for
`S₁`, `Cl`, `first.blocksInOrder`, `start₁` and `pub x`, as other authors' theorems over `falls_five` have
them. The input, the coins and the readied run go from the front into the hypotheses that read the
run, and into the conclusion. The list of helper events becomes a function `marks` of input and
coins. The conditions `PM` and `P`, the numbers `qM` and `qF` and a new letter `price` stand in
front of both. One hypothesis is new: at every run the sums at a sub-protocol are at most `price`
there. `StopsFit` gives way to the hypothesis from which `falls_five` makes it.

Limits.
  * Twelve named hypotheses. None is proved here of anything.
  * `Tied` is a letter: at `Tied := fun _ _ _ => False` the theorem says nothing.
  * No number follows, and nothing says that the right side is below 1.
  * The bound stands at each fixed list of coins. It does not bound the set of verifier's messages
    at which some list of coins meets a bad event.
  * The full size, under `P5J.AtMgA`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadSix
import Johnson.Desc.ProofFile.Honest.Law.StopsHead
import Johnson.Desc.ProofFile.Honest.Law.CoverNumbers

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
/-- The chance that an honest run meets a listed bad event is at most ONE closed sum, at every input
of `Tied` and all coins. The helper events (`marks`) may be made of the run: they are a function of
input and coins. Their conditions and numbers, those of the bad events, and `price` stand in front
of both. `Tied` is a letter: at `Tied := fun _ _ _ => False` the theorem says nothing. -/
theorem falls_uniform (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (pre₁ : List (Block TS ProofFile.Cl)) (e₁ : Block TS ProofFile.Cl)
    (cutAtLast : cF.blocksInOrder = pre₁ ++ [e₁])
    (G₀ : ProofFile.Ground) (cols tau : Nat → Nat) (share notGood : Nat → Odds) (r0 : Nat → Nat)
    (catalogue : G.falls₁ = fallsHead Zp G₀ cols tau share notGood r0)
    (noFirstHalfAtFrames : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (noneOnShared : G.falls₂ = []) (noneOnSecond : G.falls₃ = [])
    (Tied : W₀ → Rc → ProofFile.Inst → Prop)
    (marks : W₀ → Rc → ProofFile.Inst → Coins Bk → List Mark)
    (PM : Block TS ProofFile.Cl → List Fmt.Drawn → Prop) (qM : Block TS ProofFile.Cl → Mark → ℝ≥0∞)
    (P : Block TS ProofFile.Cl → List Fmt.Drawn → TS → Prop)
    (qF : Block TS ProofFile.Cl → Fall TS → ℝ≥0∞)
    (price : Nat → ℝ≥0∞)
    (marksWellPlaced : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk), Tied w₀ rc x →
      ∀ mk ∈ marks w₀ rc x k, markSeat mk.place = true)
    (fitMarksCostNothing : ∀ b ∈ pre₁, qM b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0)
    (marksBounded : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk), Tied w₀ rc x →
      ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marks w₀ rc x k).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qM b mk))
    (marksConditionMet : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
      (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X), Tied w₀ rc x →
      ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy cF.blocksInOrder G.falls₁ (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R)
        (0 + (A.flatMap (·.rounds)).length) (fr.drop 0) = false →
      silentQ (marks w₀ rc x k ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (fallsBounded : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
      (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X), Tied w₀ rc x →
      ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ repsAt cF.blocksInOrder G.falls₁ b, ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt C g 0 b (b' :: B ++ [e₁]) dsb [] (P b) (qF b g))
    (fallsConditionMet : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
      (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X), Tied w₀ rc x →
      ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy cF.blocksInOrder G.falls₁ (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R)
        (0 + (A.flatMap (·.rounds)).length) (fr.drop 0) = false →
      silentQ (marks w₀ rc x k ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R).start = some a →
      walk (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R).lay
        ((at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R).steps.take
          (0 + (A.flatMap (·.rounds)).length))
        (fr.drop 0) a = .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) A.length (x.pub, s')) →
      P b fr s')
    (pricesBelow : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk), Tied w₀ rc x →
      ∀ j, j < pre₁.length →
      priceAt pre₁ (marks w₀ rc x k) qM (repsAt cF.blocksInOrder G.falls₁) qF j ≤ price j) :
    ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk), Tied w₀ rc x →
      Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
          (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
        ((List.range pre₁.length).map price).sum := by
  intro w₀ rc x k hT
  cases hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k with
  | error _ =>
    refine le_trans (Iop.prRho_empty _ fun ρ hρ => ?_) (zero_le _)
    have hf : (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true := hρ
    unfold fallAt at hf
    cases hr : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k
        (drawsAt C D tF tJ t3 ρ) with
    | error _ =>
      rw [hr] at hf
      cases hf
    | ok r' =>
      obtain ⟨R, -, -, -, -, -, -, hR', -⟩ := runC_parts hr
      rw [hR] at hR'
      cases hR'
  | ok R =>
    obtain ⟨ρ₀⟩ : Nonempty (Iop.Rho (chainsOf C D tF tJ t3).sh) := inferInstance
    have Sf : StopsFit (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) D pre₁ e₁ :=
      stopsFit_head C tF tJ t3 h.toAtMg cutAtLast hR ρ₀
        (due_at_data C hC tF tJ t3 h.laid.data (draws_decl h.scope h.laid) ρ₀) noFirstHalfAtFrames
    have key := falls_six C hC tF tJ t3 h G H w₀ rc x k R (marks w₀ rc x k) (fun _ => 0)
      (fun _ => 0) pre₁ e₁ cutAtLast G₀ cols tau share notGood r0 catalogue hR Sf noneOnShared
      noneOnSecond _ rfl PM qM P qF (marksWellPlaced w₀ rc x k hT) fitMarksCostNothing
      (marksBounded w₀ rc x k hT) (marksConditionMet w₀ rc x k R hT hR)
      (fallsBounded w₀ rc x k R hT hR) (fallsConditionMet w₀ rc x k R hT hR)
    have e₁' : ((gates₁ D G H w₀ rc x R (marks w₀ rc x k ++ fitMarks pre₁)
        (priceAt pre₁ (marks w₀ rc x k) qM (repsAt cF.blocksInOrder G.falls₁) qF) pre₁).map
          (·.p)).sum ≤ ((List.range pre₁.length).map price).sum := by
      unfold gates₁
      rw [coverGates_p]
      refine List.sum_le_sum fun i hi => ?_
      show priceAt pre₁ (marks w₀ rc x k) qM (repsAt cF.blocksInOrder G.falls₁) qF (0 + i) ≤ price i
      rw [Nat.zero_add]
      exact pricesBelow w₀ rc x k hT i (List.mem_range.1 hi)
    have e₂ : ((gates₂ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
        (fun _ => 0)).map (·.p)).sum = 0 := by
      unfold gates₂
      rw [coverGates_p]
      exact List.sum_eq_zero fun a ha => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
        rfl
    have e₃ : ((gates₃ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder)
        (fun _ => 0)).map (·.p)).sum = 0 := by
      unfold gates₃
      rw [coverGates_p]
      exact List.sum_eq_zero fun a ha => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
        rfl
    refine le_trans key ?_
    rw [e₂, e₃, add_zero, add_zero]
    exact e₁'

end ProofFile.Honest

#print axioms ProofFile.Honest.falls_uniform
