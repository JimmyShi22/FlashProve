-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageRep.lean: n stages in a row: a family of stages on the same statement types, run in the
order of its indices, as one stage, with the conditions for `Stage.Props` and all data. (Words of
this library: lean/GLOSSARY.md.)

A protocol may run the same kind of step for f = k, k + 1, .., k + n - 1 (the calls of a lookup
plan, one after the other). If all steps act on the same statement types (`Sorts`,
Blocks/Stage.lean), the sequence of steps is defined by recursion on n:
 * `Core.rep C n k`: the protocols C k, .., C (k + n - 1) in a row; `Core.repSim`.
 * `Stage.rep S n k`: the stages in a row. Its protocol is `Core.rep` of the protocols by definition
   (the other fields are defined one by one beside the protocol); `Stage.rep_zero`, `Stage.rep_succ`
   hold by rfl.
 * `Stage.props_rep`: `Stage.Props` between c k and c (k + n) of a family of relations (`Cut`), if
   each step has `Stage.Props` between c j and c (j + 1), no two steps mask with the same pad, and
   the plain parts of no step depend on a pad with which a later step masks.
 * `Stage.rep_pBad`, `rep_pWin`, `rounds_rep`, `Core.length_rep`: the bounds `pBad`, `pWin` and the
   numbers of rounds are sums.
   `Stage.below_rep`, `Stage.small_rep`: common bounds for the errors, asked of the steps k, ..,
   k + n - 1 only.
 * `Core.imp_rep`: if no C f, for any number f, changes the implicit part, the sequence does not.
 * `Core.Track.rep` with `OK.rep`, `All.rep`, `sum_rep`; `Core.Data.rep`; `CS.rep` with
   `Stage.toCS_rep` (by rfl); `Core.Tame.rep`. (These ask their premise of every number f, not only
   of k, .., k + n - 1: tracks, data and tameness of a step do not depend on sizes.)
Limits: nothing on any particular step. No difference from the implementation is taken here.

After the recursion of Blocks/LookupStage.lean (`coKey`, `stKey`).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Blocks.StageLib
import Blocks.StageSide
import Blocks.StageNums
import Blocks.StageCount
import Blocks.StageData
import Blocks.StageSim
import Blocks.Small
import Blocks.Tame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob
open scoped ENNReal

variable {P E : Type} {a : Sorts}

/-! ## The protocol -/

/-- The protocols C k, C (k + 1), .., C (k + n - 1) in a row. -/
def Core.rep (C : ℕ → Core P E a a) : (n k : ℕ) → Core P E a a
  | 0, _ => Core.id a
  | n + 1, k => (C k).seq (Core.rep C n (k + 1))

/-- Their simulators in a row. -/
def Core.repSim
    (C : ℕ → Core P E a a) (s : ∀ f, Rho (C f).B.shape → PMF (Plains (C f).B.shape)) :
    (n k : ℕ) → Rho (Core.rep C n k).B.shape → PMF (Plains (Core.rep C n k).B.shape)
  | 0, _ => fun _ => PMF.pure ()
  | n + 1, k => Hon.simSeq (s := (C k).B.shape) (s k) (Core.repSim C s n (k + 1))

/-- Their errors in a row. -/
def Core.repErr (C : ℕ → Core P E a a) (ε : ∀ f, Err (C f).B.shape) :
    (n k : ℕ) → Err (Core.rep C n k).B.shape
  | 0, _ => ()
  | n + 1, k => Err.app (s := (C k).B.shape) (ε k) (Core.repErr C ε n (k + 1))

/-- The union of the sets U k, .., U (k + n - 1). -/
def repSet (U : ℕ → Set P) : (n k : ℕ) → Set P
  | 0, _ => ∅
  | n + 1, k => U k ∪ repSet U n (k + 1)

/-- The sum of the numbers p k, .., p (k + n - 1), bracketed to the right, as in
`Stage.rep_succ`. -/
def repSum (p : ℕ → ℝ≥0∞) : (n k : ℕ) → ℝ≥0∞
  | 0, _ => 0
  | n + 1, k => p k + repSum p n (k + 1)

theorem mem_repSet {U : ℕ → Set P} {p : P} :
    ∀ {n k : ℕ}, p ∈ repSet U n k ↔ ∃ j, k ≤ j ∧ j < k + n ∧ p ∈ U j
  | 0, k => ⟨fun h => absurd h (Set.notMem_empty p), fun ⟨j, h1, h2, _⟩ => by omega⟩
  | n + 1, k => by
      show p ∈ U k ∪ repSet U n (k + 1) ↔ _
      rw [Set.mem_union, mem_repSet]
      constructor
      · rintro (h | ⟨j, h1, h2, h3⟩)
        · exact ⟨k, le_rfl, by omega, h⟩
        · exact ⟨j, by omega, by omega, h3⟩
      · rintro ⟨j, h1, h2, h3⟩
        by_cases h : j = k
        · subst h
          exact Or.inl h3
        · exact Or.inr ⟨j, by omega, by omega, h3⟩

theorem repSum_eq (p : ℕ → ℝ≥0∞) : ∀ n k : ℕ, repSum p n k = ∑ j ∈ Finset.range n, p (k + j)
  | 0, _ => rfl
  | n + 1, k => by
      show p k + repSum p n (k + 1) = _
      rw [repSum_eq p n (k + 1), Finset.sum_range_succ']
      rw [add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [show k + 1 + j = k + (j + 1) by omega]

/-- The number of rounds is a sum. -/
theorem Core.length_rep (C : ℕ → Core P E a a) :
    ∀ n k : ℕ, (Core.rep C n k).B.shape.length = ∑ j ∈ Finset.range n, (C (k + j)).B.shape.length
  | 0, _ => rfl
  | n + 1, k => by
      show ((C k).B.shape ++ (Core.rep C n (k + 1)).B.shape).length = _
      rw [List.length_append, Core.length_rep C n (k + 1), Finset.sum_range_succ', add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [show k + 1 + j = k + (j + 1) by omega]

/-- If no C f, for any number f, changes the implicit part, the sequence does not. -/
theorem Core.imp_rep {C : ℕ → Core P E a a} (h : ∀ f y τ, (C f).B.imp y τ = y) :
    ∀ (n k : ℕ) (y : a.Y) (τ : Tr (Core.rep C n k).B.shape), (Core.rep C n k).B.imp y τ = y
  | 0, _, _, _ => rfl
  | n + 1, k, y, τ => by
      show (Core.rep C n (k + 1)).B.imp ((C k).B.imp y _) _ = y
      rw [Core.imp_rep h n (k + 1), h]

/-! ## The stage -/

/-- The stages S k, S (k + 1), .., S (k + n - 1) in a row. -/
def Stage.rep (S : ℕ → Stage P E a a) (n k : ℕ) : Stage P E a a :=
  ⟨Core.rep (fun f => (S f).toCore) n k,
    Core.repErr (fun f => (S f).toCore) (fun f => (S f).ε) n k,
    repSet (fun f => (S f).U) n k,
    repSet (fun f => (S f).D) n k,
    Core.repSim (fun f => (S f).toCore) (fun f => (S f).Sim) n k,
    repSum (fun f => (S f).pBad) n k,
    repSum (fun f => (S f).pWin) n k⟩

theorem Stage.rep_zero (S : ℕ → Stage P E a a) (k : ℕ) : Stage.rep S 0 k = Stage.id a := rfl
theorem Stage.rep_succ (S : ℕ → Stage P E a a) (n k : ℕ) :
    Stage.rep S (n + 1) k = (S k).seq (Stage.rep S n (k + 1)) := rfl
theorem Stage.toCore_rep (S : ℕ → Stage P E a a) (n k : ℕ) :
    (Stage.rep S n k).toCore = Core.rep (fun f => (S f).toCore) n k := rfl

theorem Stage.mem_rep_U {S : ℕ → Stage P E a a} {p : P} {n k : ℕ} :
    p ∈ (Stage.rep S n k).U ↔ ∃ j, k ≤ j ∧ j < k + n ∧ p ∈ (S j).U := mem_repSet
theorem Stage.mem_rep_D {S : ℕ → Stage P E a a} {p : P} {n k : ℕ} :
    p ∈ (Stage.rep S n k).D ↔ ∃ j, k ≤ j ∧ j < k + n ∧ p ∈ (S j).D := mem_repSet
theorem Stage.rep_pBad (S : ℕ → Stage P E a a) (n k : ℕ) :
    (Stage.rep S n k).pBad = ∑ j ∈ Finset.range n, (S (k + j)).pBad := repSum_eq _ n k
theorem Stage.rep_pWin (S : ℕ → Stage P E a a) (n k : ℕ) :
    (Stage.rep S n k).pWin = ∑ j ∈ Finset.range n, (S (k + j)).pWin := repSum_eq _ n k
theorem Stage.rounds_rep (S : ℕ → Stage P E a a) (n k : ℕ) :
    (Stage.rep S n k).rounds = ∑ j ∈ Finset.range n, (S (k + j)).rounds :=
  Core.length_rep _ n k

theorem Stage.below_rep {S : ℕ → Stage P E a a} {κ : ℝ≥0∞} :
    ∀ n k : ℕ, (∀ j, k ≤ j → j < k + n → (S j).Below κ) → (Stage.rep S n k).Below κ
  | 0, _, _ => trivial
  | n + 1, k, h =>
    Stage.Below.seq (h k le_rfl (by omega))
      (Stage.below_rep n (k + 1) fun j h1 h2 => h j (by omega) (by omega))

theorem Stage.small_rep {S : ℕ → Stage P E a a} {D : ℕ} :
    ∀ n k : ℕ, (∀ j, k ≤ j → j < k + n → Small D (S j).ε) → Small D (Stage.rep S n k).ε
  | 0, _, _ => trivial
  | n + 1, k, h =>
    small_app D (S k).ε (Stage.rep S n (k + 1)).ε (h k le_rfl (by omega))
      (Stage.small_rep n (k + 1) fun j h1 h2 => h j (by omega) (by omega))

/-- If the errors of a concatenated list satisfy `Small D`, so do those of its two parts. -/
theorem small_of_app (D : ℕ) :
    ∀ {s t : Shape} (a : Err s) (b : Err t), Small D (Err.app a b) → Small D a ∧ Small D b
  | [], _, _, _, h => ⟨trivial, h⟩
  | _ :: _, _, (_, a), b, h => ⟨⟨h.1, (small_of_app D a b h.2).1⟩, (small_of_app D a b h.2).2⟩

/-- `Stage.Props` of the sequence, between c k and c (k + n), under the two hypotheses below. -/
theorem Stage.props_rep [Fintype P] [DecidableEq P] [AddCommGroup E] [Fintype E]
    {S : ℕ → Stage P E a a} {c : ℕ → Cut P E a} :
    ∀ n k : ℕ, (∀ j, k ≤ j → j < k + n → (S j).Props (c j) (c (j + 1))) →
      (∀ i j, k ≤ i → i < j → j < k + n → Disjoint (S i).U (S j).U ∧ Disjoint (S i).D (S j).U) →
      (Stage.rep S n k).Props (c k) (c (k + n))
  | 0, k, _, _ => Stage.props_id _
  | n + 1, k, h, hd => by
      have h2 := Stage.props_rep n (k + 1) (fun j h1 h2 => h j (by omega) (by omega))
        fun i j h1 h2 h3 => hd i j (by omega) h2 (by omega)
      rw [show k + 1 + n = k + (n + 1) by omega] at h2
      refine (h k le_rfl (by omega)).seq h2 ?_ ?_
      · exact Set.disjoint_left.mpr fun p hp hp' => by
          obtain ⟨j, h1, h2, h3⟩ := Stage.mem_rep_U.mp hp'
          exact Set.disjoint_left.mp (hd k j le_rfl (by omega) (by omega)).1 hp h3
      · exact Set.disjoint_left.mpr fun p hp hp' => by
          obtain ⟨j, h1, h2, h3⟩ := Stage.mem_rep_U.mp hp'
          exact Set.disjoint_left.mp (hd k j le_rfl (by omega) (by omega)).2 hp h3

/-! ## Protocols with their simulators -/

/-- The sequence of protocols with their simulators. -/
def CS.rep (K : ℕ → CS P E a a) (n k : ℕ) : CS P E a a :=
  ⟨Core.rep (fun f => (K f).toCore) n k,
    Core.repSim (fun f => (K f).toCore) (fun f => (K f).Sim) n k⟩

theorem CS.toCore_rep (K : ℕ → CS P E a a) (n k : ℕ) :
    (CS.rep K n k).toCore = Core.rep (fun f => (K f).toCore) n k := rfl
theorem Stage.toCS_rep (S : ℕ → Stage P E a a) (n k : ℕ) :
    (Stage.rep S n k).toCS = CS.rep (fun f => (S f).toCS) n k := rfl

/-! ## Rejection on the verifier's randomness alone -/

theorem Core.Tame.rep {C : ℕ → Core P E a a} {I : ℕ → a.X → Prop}
    (h : ∀ f, (C f).Tame (I f) (I (f + 1))) :
    ∀ n k : ℕ, (Core.rep C n k).Tame (I k) (I (k + n))
  | 0, k => Core.tame_id a (I k)
  | n + 1, k => by
      have h2 := Core.Tame.rep h n (k + 1)
      rw [show k + 1 + n = k + (n + 1) by omega] at h2
      exact Core.Tame.seq (h k) h2

/-! ## Tracking data and data -/

section Track

variable {F : Type} [Field F] [Field E] [Algebra F E] {C : ℕ → Core P E a a} {ra : Reads F E a}

/-- The tracking data of the sequence: every step exposes what was exposed before it. -/
def Core.Track.rep (t : ∀ f, (C f).Track ra ra) : (n k : ℕ) → (Core.rep C n k).Track ra ra
  | 0, _ => Core.Track.id ra
  | n + 1, k => (t k).seq (Core.Track.rep t n (k + 1))

theorem Core.Track.OK.rep {t : ∀ f, (C f).Track ra ra} (h : ∀ f, (t f).OK) :
    ∀ n k : ℕ, (Core.Track.rep t n k).OK
  | 0, _ => Core.Track.ok_id ra
  | n + 1, k => (h k).seq (Core.Track.OK.rep h n (k + 1))

theorem Core.Track.All.rep {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop}
    {t : ∀ f, (C f).Track ra ra} (h : ∀ f, (t f).All Q) :
    ∀ n k : ℕ, (Core.Track.rep t n k).All Q
  | 0, _ => Core.Track.all_id ra
  | n + 1, k => (h k).seq (Core.Track.All.rep h n (k + 1))

theorem Core.Track.sum_rep (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) (t : ∀ f, (C f).Track ra ra) :
    ∀ n k : ℕ, (Core.Track.rep t n k).sum f = ∑ j ∈ Finset.range n, (t (k + j)).sum f
  | 0, _ => rfl
  | n + 1, k => by
      show ((t k).seq (Core.Track.rep t n (k + 1))).sum f = _
      rw [Core.Track.sum_seq, Core.Track.sum_rep f t n (k + 1), Finset.sum_range_succ', add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [show k + 1 + j = k + (j + 1) by omega]

/-- The data of the sequence. -/
def Core.Data.rep {t : ∀ f, (C f).Track ra ra} (D : ∀ f, (C f).Data (t f)) :
    (n k : ℕ) → (Core.rep C n k).Data (Core.Track.rep t n k)
  | 0, _ => Core.Data.id ra
  | n + 1, k => (D k).seq (Core.Data.rep D n (k + 1))

end Track

end Blocks
