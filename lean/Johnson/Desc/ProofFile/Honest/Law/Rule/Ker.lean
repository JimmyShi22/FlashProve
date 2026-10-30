-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Ker.lean: the hypothesis of the chain rule
(Honest/Law/Rule/Stages.lean: `real_eq_sim`), list by list. The hypothesis says: at every cut of a
list of stages the pair (what the stages before produce, what the stage shows) has this
distribution: what has been produced, and then the stage's kernel on it. Here it is stated of a list
l after a list pre (`Ker`), and it carries over two consecutive lists. And one kind of stage meets
it with no further hypothesis (`kerAt_det`). K, Φ, V are type parameters; no part and no run of a
protocol occurs.

  1  `KerAt`, `Ker`   the condition at one stage after a list; at every stage of a list
  2  `Ker.nil`, `Ker.cons`, `Ker.append`, `Ker.cut`, `real_eq_sim_of`   over two consecutive lists;
     the chain rule from it
  3  `kerAt_det`   a stage that shows a function of what has been produced, and whose kernel is the
     point mass at that value

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Kit
open Prob

variable {K Φ V : Type} [Fintype K] [Nonempty K]

/-! ## 1 The condition -/

/-- The hypothesis `hker` of `real_eq_sim` (Honest/Law/Rule/Stages.lean) at one stage s after a list
pre, from L₀. -/
def KerAt (L₀ : Φ) (pre : List (Stage K Φ V)) (s : Stage K Φ V) : Prop :=
  (unif K).map (fun k => (real pre k L₀, some (s.shows k (real pre k L₀)))) =
    ((unif K).map fun k => real pre k L₀).bind fun φ => (s.tells φ).map fun o => (φ, o)

/-- `KerAt` at every stage of a list l after a list pre. -/
def Ker (L₀ : Φ) : List (Stage K Φ V) → List (Stage K Φ V) → Prop
  | _, [] => True
  | pre, s :: l => KerAt L₀ pre s ∧ Ker L₀ (pre ++ [s]) l

/-! ## 2 Over two consecutive lists -/

theorem Ker.nil (L₀ : Φ) (pre : List (Stage K Φ V)) : Ker L₀ pre [] := trivial

theorem Ker.cons {L₀ : Φ} {pre : List (Stage K Φ V)} {s : Stage K Φ V} {l : List (Stage K Φ V)}
    (h1 : KerAt L₀ pre s) (h2 : Ker L₀ (pre ++ [s]) l) : Ker L₀ pre (s :: l) := by
  show KerAt L₀ pre s ∧ Ker L₀ (pre ++ [s]) l
  exact ⟨h1, h2⟩

theorem Ker.append {L₀ : Φ} : ∀ (l₁ l₂ pre : List (Stage K Φ V)), Ker L₀ pre l₁ →
    Ker L₀ (pre ++ l₁) l₂ → Ker L₀ pre (l₁ ++ l₂)
  | [], l₂, pre, _, h2 => by
    rw [List.append_nil] at h2
    exact h2
  | s :: l₁, l₂, pre, h1, h2 => by
    obtain ⟨a1, a2⟩ : KerAt L₀ pre s ∧ Ker L₀ (pre ++ [s]) l₁ := h1
    show KerAt L₀ pre s ∧ Ker L₀ (pre ++ [s]) (l₁ ++ l₂)
    refine ⟨a1, Ker.append l₁ l₂ (pre ++ [s]) a2 ?_⟩
    rw [List.append_assoc]
    exact h2

/-- At every cut. -/
theorem Ker.cut {L₀ : Φ} : ∀ (l pre : List (Stage K Φ V)), Ker L₀ pre l →
    ∀ l₁ s l₂, l = l₁ ++ s :: l₂ → KerAt L₀ (pre ++ l₁) s
  | [], _, _, l₁, s, l₂, h => by cases l₁ <;> cases h
  | t :: l, pre, hk, [], s, l₂, h => by
    have e : t = s := (List.cons.inj h).1
    subst e
    obtain ⟨a1, -⟩ : KerAt L₀ pre t ∧ Ker L₀ (pre ++ [t]) l := hk
    rw [List.append_nil]
    exact a1
  | t :: l, pre, hk, u :: l₁, s, l₂, h => by
    have e1 : t = u := (List.cons.inj h).1
    have e2 : l = l₁ ++ s :: l₂ := (List.cons.inj h).2
    subst e1
    obtain ⟨-, a2⟩ : KerAt L₀ pre t ∧ Ker L₀ (pre ++ [t]) l := hk
    have := Ker.cut l (pre ++ [t]) a2 l₁ s l₂ e2
    rw [List.append_assoc] at this
    exact this

/-- **The chain rule, from the condition list by list.** -/
theorem real_eq_sim_of (l : List (Stage K Φ V)) (L₀ : Φ) (h : Ker L₀ [] l) :
    (unif K).map (fun k => some (real l k L₀)) = sim l L₀ :=
  real_eq_sim l L₀ fun l₁ s l₂ hl => Ker.cut l [] h l₁ s l₂ hl

/-! ## 3 A stage that draws nothing -/

/-- `KerAt` holds of a stage that shows a function f of what has been produced, and whose kernel is
the point mass at that value. -/
theorem kerAt_det (L₀ : Φ) (pre : List (Stage K Φ V)) (s : Stage K Φ V) (f : Φ → V)
    (h1 : ∀ k φ, s.shows k φ = f φ) (h2 : ∀ φ, s.tells φ = PMF.pure (some (f φ))) :
    KerAt L₀ pre s := by
  unfold KerAt
  have e : (fun k => (real pre k L₀, some (s.shows k (real pre k L₀)))) =
      (fun φ => (φ, some (f φ))) ∘ fun k => real pre k L₀ := by
    funext k
    show _ = (real pre k L₀, some (f (real pre k L₀)))
    rw [h1]
  rw [e, ← PMF.map_comp]
  show ((unif K).map fun k => real pre k L₀).bind (PMF.pure ∘ fun φ => (φ, some (f φ))) = _
  refine congrArg (fun F => ((unif K).map fun k => real pre k L₀).bind F) (funext fun φ => ?_)
  rw [h2, PMF.pure_map]
  rfl

end ProofFile.Honest.Kit

#print axioms ProofFile.Honest.Kit.Ker.nil
#print axioms ProofFile.Honest.Kit.Ker.cons
#print axioms ProofFile.Honest.Kit.Ker.append
#print axioms ProofFile.Honest.Kit.Ker.cut
#print axioms ProofFile.Honest.Kit.real_eq_sim_of
#print axioms ProofFile.Honest.Kit.kerAt_det
