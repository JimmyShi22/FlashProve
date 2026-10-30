-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Stages.lean: a list of stages, in the abstract. A stage shows
something, as a function of a run's coins and of what has been produced before it. Beside it there
is a kernel, which reads only what has been produced. There are two folds: one at coins (`real`),
the other over the kernels (`sim`). No protocol, no type of Honest/Frame.lean and no part occurs
here: K, Φ and V are type parameters.

  1  `Stage`, `real`, `onSome`, `sim`   the structure and the two folds
  2  `real_append`, `real_congr`, `real_factor`   the fold at coins: cut in two; at two coins at
     which every stage shows the same; at two coins that differ in what one lens shows
  3  `sim_append`, `sim_one`   the kernels' fold: cut in two; for one stage
  4  `real_eq_sim`   the chain rule: if at every cut of the list, over uniform coins, what the next
     stage shows has its kernel's distribution given what has been produced before, then what the
     whole list produces has the distribution of the kernels' fold

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Kit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Kit
open Prob

variable {K Φ V : Type}

/-! ## 1 The structure and the two folds -/

/-- **A stage.** `K`: a run's coins. `Φ`: what has been produced. `V`: what a stage shows. -/
structure Stage (K Φ V : Type) where
  /-- what it shows, at coins and at what has been produced before it -/
  shows : K → Φ → V
  /-- the kernel beside it, a function of what has been produced before: a distribution of what is
  shown, or of `none` -/
  tells : Φ → PMF (Option V)
  /-- what has been produced after it -/
  add : Φ → V → Φ

/-- The fold at coins. -/
def real : List (Stage K Φ V) → K → Φ → Φ
  | [], _, L => L
  | s :: ss, k, L => real ss k (s.add L (s.shows k L))

/-- To go on after an option: `none` stays. -/
noncomputable def onSome {α β : Type} (f : α → PMF (Option β)) : Option α → PMF (Option β)
  | none => PMF.pure none
  | some a => f a

/-- The kernels' fold. -/
noncomputable def sim : List (Stage K Φ V) → Φ → PMF (Option Φ)
  | [], L => PMF.pure (some L)
  | s :: ss, L => (s.tells L).bind (onSome fun v => sim ss (s.add L v))

/-! ## 2 The fold at coins -/

theorem real_append (l₂ : List (Stage K Φ V)) (k : K) : ∀ (l₁ : List (Stage K Φ V)) (L : Φ),
    real (l₁ ++ l₂) k L = real l₂ k (real l₁ k L)
  | [], _ => rfl
  | s :: l₁, L => real_append l₂ k l₁ (s.add L (s.shows k L))

/-- At two coins at which every stage shows the same, the same is produced. -/
theorem real_congr (k k' : K) : ∀ (l : List (Stage K Φ V)),
    (∀ s ∈ l, ∀ L, s.shows k L = s.shows k' L) → ∀ L, real l k L = real l k' L
  | [], _, _ => rfl
  | s :: l, h, L => by
    show real l k (s.add L (s.shows k L)) = real l k' (s.add L (s.shows k' L))
    rw [h s (List.mem_cons_self ..) L]
    exact real_congr k k' l (fun t ht => h t (List.mem_cons_of_mem _ ht)) _

/-- **Through what one stage's coins are read.** `put`: the setter of a lens. The stages before o do
not read what the lens shows; those after o read it through η alone. Then two settings at which o
shows the same, and η is the same, produce the same. -/
theorem real_factor {C Hh : Type} {put : C → K → K} (pre mid : List (Stage K Φ V))
    (o : Stage K Φ V) (η : C → Hh) (L₀ : Φ)
    (hpre : ∀ s ∈ pre, ∀ c k L, s.shows (put c k) L = s.shows k L)
    (hmid : ∀ s ∈ mid, ∀ k c c' L, η c = η c' → s.shows (put c k) L = s.shows (put c' k) L)
    (k : K) (c c' : C)
    (hv : o.shows (put c k) (real pre k L₀) = o.shows (put c' k) (real pre k L₀))
    (hη : η c = η c') :
    real (pre ++ o :: mid) (put c k) L₀ = real (pre ++ o :: mid) (put c' k) L₀ := by
  have e : ∀ c, real pre (put c k) L₀ = real pre k L₀ := fun c =>
    real_congr (put c k) k pre (fun s hs L => hpre s hs c k L) L₀
  rw [real_append, real_append, e c, e c']
  show real mid (put c k) (o.add (real pre k L₀) (o.shows (put c k) (real pre k L₀))) =
    real mid (put c' k) (o.add (real pre k L₀) (o.shows (put c' k) (real pre k L₀)))
  rw [hv]
  exact real_congr (put c k) (put c' k) mid (fun s hs L => hmid s hs k c c' L hη) _

/-! ## 3 The kernels' fold -/

theorem sim_append (l₂ : List (Stage K Φ V)) : ∀ (l₁ : List (Stage K Φ V)) (L : Φ),
    sim (l₁ ++ l₂) L = (sim l₁ L).bind (onSome (sim l₂))
  | [], L => by
    show sim l₂ L = (PMF.pure (some L)).bind (onSome (sim l₂))
    rw [PMF.pure_bind]
    rfl
  | s :: l₁, L => by
    show (s.tells L).bind (onSome fun v => sim (l₁ ++ l₂) (s.add L v)) =
      ((s.tells L).bind (onSome fun v => sim l₁ (s.add L v))).bind (onSome (sim l₂))
    rw [PMF.bind_bind]
    refine congrArg (fun f => (s.tells L).bind f) (funext fun o => ?_)
    cases o with
    | none =>
      show PMF.pure none = (PMF.pure none).bind (onSome (sim l₂))
      rw [PMF.pure_bind]
      rfl
    | some v => exact sim_append l₂ l₁ (s.add L v)

theorem sim_one (s : Stage K Φ V) (L : Φ) :
    sim [s] L = (s.tells L).map fun o => o.map (s.add L) := by
  show (s.tells L).bind (onSome fun v => PMF.pure (some (s.add L v))) =
    (s.tells L).bind (PMF.pure ∘ fun o => o.map (s.add L))
  refine congrArg (fun f => (s.tells L).bind f) (funext fun o => ?_)
  cases o <;> rfl

/-! ## 4 The chain rule -/

/-- **The chain rule.** `hker`: at every cut l₁ | s | l₂ of the list, over uniform coins, the pair
(what l₁ produces, what s shows after it) has this distribution: what l₁ produces, and then the
kernel of s on it. -/
theorem real_eq_sim [Fintype K] [Nonempty K] (l : List (Stage K Φ V)) (L₀ : Φ)
    (hker : ∀ l₁ s l₂, l = l₁ ++ s :: l₂ →
      (unif K).map (fun k => (real l₁ k L₀, some (s.shows k (real l₁ k L₀)))) =
        ((unif K).map fun k => real l₁ k L₀).bind fun φ => (s.tells φ).map fun o => (φ, o)) :
    (unif K).map (fun k => some (real l k L₀)) = sim l L₀ := by
  have key : ∀ l₁ l₂ : List (Stage K Φ V), l = l₁ ++ l₂ →
      (unif K).map (fun k => some (real l₁ k L₀)) = sim l₁ L₀ := by
    intro l₁
    refine List.reverseRecOn l₁ ?_ ?_
    · intro _ _
      exact PMF.map_const _ (some L₀)
    · intro l₁ s ih l₂ hl
      have hl' : l = l₁ ++ s :: l₂ := hl.trans (by simp)
      have h1 := hker l₁ s l₂ hl'
      have ih' := ih (s :: l₂) hl'
      calc (unif K).map (fun k => some (real (l₁ ++ [s]) k L₀))
          = (unif K).map ((fun y : Φ × Option V => y.2.map (s.add y.1)) ∘
              fun k => (real l₁ k L₀, some (s.shows k (real l₁ k L₀)))) := by
            refine congrArg (fun f => (unif K).map f) (funext fun k => ?_)
            exact congrArg some (real_append [s] k l₁ L₀)
        _ = ((unif K).map fun k => (real l₁ k L₀, some (s.shows k (real l₁ k L₀)))).map
              (fun y : Φ × Option V => y.2.map (s.add y.1)) := (PMF.map_comp _ _ _).symm
        _ = (((unif K).map fun k => real l₁ k L₀).bind fun φ =>
              (s.tells φ).map fun o => (φ, o)).map
              (fun y : Φ × Option V => y.2.map (s.add y.1)) := by rw [h1]
        _ = ((unif K).map fun k => real l₁ k L₀).bind fun φ => sim [s] φ := by
            rw [PMF.map_bind]
            refine congrArg (fun f => ((unif K).map fun k => real l₁ k L₀).bind f)
              (funext fun φ => ?_)
            exact (PMF.map_comp _ _ _).trans (sim_one s φ).symm
        _ = ((unif K).map fun k => some (real l₁ k L₀)).bind (onSome (sim [s])) := by
            rw [PMF.bind_map, PMF.bind_map]
            rfl
        _ = (sim l₁ L₀).bind (onSome (sim [s])) := by rw [ih']
        _ = sim (l₁ ++ [s]) L₀ := (sim_append [s] l₁ L₀).symm
  exact key l [] (List.append_nil l).symm

end ProofFile.Honest.Kit

#print axioms ProofFile.Honest.Kit.real_append
#print axioms ProofFile.Honest.Kit.real_congr
#print axioms ProofFile.Honest.Kit.real_factor
#print axioms ProofFile.Honest.Kit.sim_append
#print axioms ProofFile.Honest.Kit.sim_one
#print axioms ProofFile.Honest.Kit.real_eq_sim
