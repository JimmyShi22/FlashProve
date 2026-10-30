-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallsUniformListed.lean: `falls_uniform`
(Honest/Law/FallsUniform.lean) at the written lists of `falls_five` (Honest/Law/CoverHeadFive.lean):
the catalogue `fallsFull`, the helper events `marksHead`, their numbers `qMHead`. And, beside it,
that under the head the catalogue has its 87 entries at the ground that the head fixes.

  1  `falls_uniform_listed`   the bound at the written lists
  2  `catalogue_87`   the catalogue's length

Limits.
  * `falls_uniform_listed` has ten named hypotheses. None is proved here of anything. Five of them
    are the five fields of `FirstAsks` that `falls_five` leaves open, three of these now asked at
    every input of `Tied` and every list of coins at which `ready` is `.ok R`.
  * `G₀` is a letter in it, tied to nothing: the bound holds at any ground. Where a look-up at `G₀`
    returns nothing the catalogue has fewer entries. `catalogue_87` names the ground at which it has
    all 87.
  * The helper events are a closed list here. A helper event that is made of the run has no place
    in it: `falls_uniform` has.
  * All limits of Honest/Law/FallsUniform.lean hold here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FallsUniform
import Johnson.Desc.ProofFile.Honest.Law.FallsFull
import Johnson.Desc.ProofFile.Honest.Law.MarksHead

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
/-- `falls_uniform` at the written lists: the helper events are `marksHead Zp G₀` at every run, the
catalogue is `fallsFull`, and `price` is `priceAt` at these. `G₀` is a letter, as in `falls_five`:
that the catalogue has its 87 entries at the ground that the head fixes is `catalogue_87`; a caller
may use it, or `fallsFull_87` with its premise. -/
theorem falls_uniform_listed (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (G₀ : ProofFile.Ground) (kap₃ kap₆ : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (pre₁ : List (Block TS ProofFile.Cl)) (e₁ : Block TS ProofFile.Cl)
    (cutAtLast : cF.blocksInOrder = pre₁ ++ [e₁])
    (catalogue : G.falls₁ = fallsFull Zp G₀ notGood r0)
    (noFirstHalfAtFrames : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (noneOnShared : G.falls₂ = []) (noneOnSecond : G.falls₃ = [])
    (Tied : W₀ → Rc → ProofFile.Inst → Prop)
    (PM : Block TS ProofFile.Cl → List Fmt.Drawn → Prop)
    (P : Block TS ProofFile.Cl → List Fmt.Drawn → TS → Prop)
    (qF : Block TS ProofFile.Cl → Fall TS → ℝ≥0∞)
    (marksWellPlaced : ∀ mk ∈ (marksHead Zp G₀), markSeat mk.place = true)
    (marksBounded : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (qMHead kap₃ kap₆ b mk))
    (marksConditionMet : ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk)
      (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X), Tied w₀ rc x →
      ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk (G.prover H) w₀ rc x k = .ok R →
      ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy cF.blocksInOrder G.falls₁ (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R)
        (0 + (A.flatMap (·.rounds)).length) (fr.drop 0) = false →
      silentQ ((marksHead Zp G₀) ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
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
      silentQ ((marksHead Zp G₀) ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R).start = some a →
      walk (at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R).lay
        ((at₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (G.prover H) w₀ rc x R).steps.take
          (0 + (A.flatMap (·.rounds)).length))
        (fr.drop 0) a = .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) A.length (x.pub, s')) →
      P b fr s') :
    ∀ (w₀ : W₀) (rc : Rc) (x : ProofFile.Inst) (k : Coins Bk), Tied w₀ rc x →
      Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
          (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
        ((List.range pre₁.length).map
          (priceAt pre₁ (marksHead Zp G₀) (qMHead kap₃ kap₆) (repsAt cF.blocksInOrder G.falls₁)
            qF)).sum := by
  exact falls_uniform C hC tF tJ t3 h G H pre₁ e₁ cutAtLast G₀ (K8.k8ColsAt G₀) (K8.k8TauAt G₀)
    (P1K8.k8ShareAt Zp G₀) notGood r0 catalogue noFirstHalfAtFrames noneOnShared noneOnSecond Tied
    (fun _ _ _ _ => marksHead Zp G₀) PM (qMHead kap₃ kap₆) P qF _
    (fun _ _ _ _ _ => marksWellPlaced) (hq0_head kap₃ kap₆ pre₁) (fun _ _ _ _ _ => marksBounded)
    marksConditionMet fallsBounded fallsConditionMet (fun _ _ _ _ _ _ _ => le_rfl)

/-- Under the head the public data have one ground, and at it the catalogue has its 87 entries. -/
theorem catalogue_87 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (notGood : Nat → Odds)
    (r0 : Nat → Nat) :
    ∃ Bs, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      (fallsFull Zp Bs.G₀ notGood r0).length = 87 := by
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  exact ⟨Bs, O.made, fallsFull_87 h O.made⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.falls_uniform_listed
#print axioms ProofFile.Honest.catalogue_87
