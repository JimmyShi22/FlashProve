-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverEnd.lean: the bound of `falls_local`
(Honest/Law/CoverAll.lean) on the chance that a run meets a fall, for a file in which only the first
chain has falls, with the first chain's bounds as one hypothesis, where the marks of the other two
chains never speak at a typed message (`hmk₂`, `hmk₃`), `ready` returns (`hR`), `StopsFit` holds
(`Sf`) and there are gated sub-protocols (`hne`). It is general in the file's description. No
sub-protocol of the protocol is named here.

The hypothesis `d₁` of `falls_first` is written in the form of the conclusion of `localDebts_sorts`
(Honest/Law/CoverSorts.lean), taken at the first chain. The way from statements about single falls
and marks to the bound is one application of each. `falls_asks` (Honest/Law/CoverAsks.lean) makes
both applications, with the statements bundled in one structure. The two small lemmas of section 1
prove two hypotheses of `localDebts_sorts` for the first chain; a third, that the chain's data fit
its rounds, is `kindFits_first` (Honest/Law/CoverData.lean). At the shared and the second chain,
whose lists of falls are empty, the bounds are `localDebts_noFall`'s (Honest/Law/CoverNoFall.lean).

  1  `at₁_from`, `at₁_tree`   what the first chain's walk starts from; its first tree's number
  2  `falls_first`   the bound for a file

Limits.
  * A lemma that wrote all hypotheses of `localDebts_sorts` and the bound into one statement did
    not finish within twelve minutes, in three forms, and was withdrawn each time. `falls_asks` has
    the hypotheses as the fields of a structure.
  * Every hypothesis is an argument. None is proved here of any description.
  * No number follows from them.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverAll
import Johnson.Desc.ProofFile.Honest.Law.CoverNoFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type}

/-! ## 1 The first chain's start -/

/-- Every start of the first chain's walk comes from `ChainProgress.start` with a verifier's state, at some
columns handed (they are `[]`: `letter_starts`, Honest/Law/CoverLetter.lean, keeps that): the form
in which `localDebts_sorts` takes it. -/
theorem at₁_from (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) (a : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hs : (at₁ F P w₀ rc x R).start = some a) :
    ∃ (m₀ : Option (Mid (Local W₀ Rc Xi Tr) X)) (s₀ : F.S₁) (front : List OpenedColumn), m₀.isSome = true ∧
      ChainProgress.start (at₁ F P w₀ rc x R).lay F.first.blocksInOrder m₀ (some s₀) front = .ok a := by
  obtain ⟨m₀, _, h1, h2⟩ := at₁_starts F P w₀ rc x R a (F.start₁ (F.pub x)) hs rfl
  exact ⟨m₀, _, _, h1, h2⟩

/-- The first chain's first tree has the number 0. -/
theorem at₁_tree (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : (at₁ F P w₀ rc x R).lay.firstTree = 0 := rfl

/-! ## 2 The bound -/

/-- The bound of `falls_local` for a file in which the shared and the second chain have empty lists
of falls. `s₁`: the run has met no fall before the first chain's first round (`fellBy_start`,
Honest/Law/CoverStart.lean). `d₁`: the first chain's bounds. `hmk₂`, `hmk₃`: the marks of the other
two chains never speak at a typed message. -/
theorem falls_first (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi}
    {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀)
    (rc : Rc) (x : Xi) (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (ms₁ ms₂ ms₃ : List Mark)
    (p₁ p₂ p₃ : Nat → ℝ≥0∞) {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl}
    (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit F (G.prover H) D pre₁ e₁) (hne : pre₁ ≠ [])
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = [])
    (s₁ : fellBy F.first.blocksInOrder G.falls₁ (at₁ F (G.prover H) w₀ rc x R) 0 [] = false)
    (d₁ : LocalDebts C F.first.blocksInOrder G.falls₁ ms₁ 0 (fun _ => at₁ F (G.prover H) w₀ rc x R) p₁
      [noDraw] (silentQ ms₁ 0 pre₁) pre₁ 0 0 D.ds₁)
    (hmk₂ : ∀ A b B, F.shared.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₂.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms₂ b.place fr (drawnT C _ ρ) = none)
    (hmk₃ : ∀ A b B, F.second.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₃.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms₃ b.place fr (drawnT C _ ρ) = none) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R ms₁ p₁ pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R ms₂ p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R ms₃ p₃).map (·.p)).sum) := by
  refine falls_local C D tF tJ t3 G H w₀ rc x k R ms₁ ms₂ ms₃ p₁ p₂ p₃ (silentQ ms₁ 0 pre₁)
    (silentQ ms₂ 0 F.shared.blocksInOrder) (silentQ ms₃ (D.ds₁.length + D.ds₂.length) F.second.blocksInOrder) hR Sf
    hne s₁ (silentQ_zero _ _ _ _) d₁ ?_ (silentQ_zero _ _ _ _) ?_ ?_ ?_
  · rw [hf₂]
    exact fellBy_noFall _ _ _ _
  · rw [hf₂]
    exact localDebts_noFall C F.shared.blocksInOrder F.shared.blocksInOrder ms₂ 0 _ p₂ [] D.ds₂ Sf.l₂ hmk₂
  · intro a b _ _
    refine ⟨?_, silentQ_zero _ _ _ _⟩
    rw [hf₃]
    exact fellBy_noFall _ _ _ _
  · rw [hf₃]
    exact localDebts_noFall C F.second.blocksInOrder F.second.blocksInOrder ms₃ _ _ p₃ [] D.ds₃ Sf.l₃ hmk₃

end ProofFile.Honest

#print axioms ProofFile.Honest.at₁_from
#print axioms ProofFile.Honest.at₁_tree
#print axioms ProofFile.Honest.falls_first
