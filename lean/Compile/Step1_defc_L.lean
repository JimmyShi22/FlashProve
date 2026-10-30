-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_defc_L.lean: generic facts on the language `LStep` of Rom/DeferLate.lean; used in
Compile/Step1_defc_EqSetup.lean and Compile/Batch/ (words of this library: lean/GLOSSARY.md).

  `virtL`, `late_virt`
                       The renumbering of tokens (`Life2.virt`) for `LStep`; related programs stay
                       related (conditions at `late_virt`).

Notation: `LStep` (Rom/DeferLate.lean): "One step of a challenger that supplies points at the
release. As Step, but for marked and reveal."; `Late post n Γ P Q` (the same file): a `Prop` on a
`Step` program P and an `LStep` program Q: "P and Q have the same constructors; Q has no closures at
its marked evaluations" (the rest: its doc comment); `n`: a natural number: "a lower bound on the
number of tokens that exist"; `post`: of type `ℕ → Ctx S → α → β → Prop`: "post relates the results,
with the bound and the context at the end"; `Γ`, `Γv`, `Γa`: a `Ctx S`: "the ghost context: which
closure the Step program gave when it charged token t at oracle o"; `N₀`, `δ`: natural numbers;
`up N₀ δ v`: `if v < N₀ then v else v + δ`; `down N₀ δ t`: `if t < N₀ then t else t - δ`
(Compile/Step1_life2_Virt.lean).
-/
import Rom.DeferLate
import Compile.Step1_life2_Virt

open scoped ENNReal
open Prob Rom

namespace Compile.DefC

open Compile.Life2 (up down vis virt up_injective down_up)

variable {S : OSpec} {sp : Split S} {α β : Type}

theorem run_bind (P : LStep S sp α) (g : α → LStep S sp β) :
    ∀ w, (P.bind g).run w = (P.run w).bind fun x => (g x.1).run x.2 := by
  induction P with
  | pure a => intro w; simp only [LStep.bind, LStep.run, PMF.pure_bind]
  | sample n k ih => intro w; simp only [LStep.bind, LStep.run, ih, PMF.bind_bind]
  | plain o q k ih => intro w; simp only [LStep.bind, LStep.run, ih, PMF.bind_bind]
  | fresh ℓ k ih => intro w; simp only [LStep.bind, LStep.run, ih, PMF.bind_bind]
  | marked o t us A hA k ih => intro w; simp only [LStep.bind, LStep.run, ih, PMF.bind_bind]
  | reveal ts pts k ih => intro w; simp only [LStep.bind, LStep.run, ih]

theorem lbind_assoc {γ : Type} (P : LStep S sp α) (g : α → LStep S sp β) (h : β → LStep S sp γ) :
    (P.bind g).bind h = P.bind fun a => (g a).bind h := by
  induction P with
  | pure a => rfl
  | sample n k ih => simp only [LStep.bind, ih]
  | plain o q k ih => simp only [LStep.bind, ih]
  | fresh ℓ k ih => simp only [LStep.bind, ih]
  | marked o t us A hA k ih => simp only [LStep.bind, ih]
  | reveal ts pts k ih => simp only [LStep.bind, ih]

variable (N₀ δ : ℕ)

/-- the program under the renumbering of tokens, as Life2.virt -/
def virtL : LStep S sp α → LStep S sp α
  | .pure a => .pure a
  | .sample n k => .sample n fun r => virtL (k r)
  | .plain o q k => .plain o q fun r => virtL (k r)
  | .fresh ℓ k => .fresh ℓ fun t => virtL (k (t - δ))
  | .marked o t us A hA k => .marked o (up N₀ δ t) (us.map (up N₀ δ)) A hA fun v t' => virtL (k v (t' - δ))
  | .reveal ts pts k => .reveal (ts.map (up N₀ δ)) (fun a o => pts (down N₀ δ a) o) fun vs => virtL (k vs)

theorem virtL_bind (P : LStep S sp α) (g : α → LStep S sp β) :
    virtL N₀ δ (P.bind g) = (virtL N₀ δ P).bind fun a => virtL N₀ δ (g a) := by
  induction P with
  | pure a => rfl
  | sample n k ih => simp only [LStep.bind, virtL, ih]
  | plain o q k ih => simp only [LStep.bind, virtL, ih]
  | fresh ℓ k ih => simp only [LStep.bind, virtL, ih]
  | marked o t us A hA k ih => simp only [LStep.bind, virtL, ih]
  | reveal ts pts k ih => simp only [LStep.bind, virtL, ih]

/-- Related programs stay related under the renumbering, if N₀ ≤ n and the context of the renumbered
programs, read at up v, is the context of the programs. -/
theorem late_virt {post : ℕ → Ctx S → α → β → Prop} {n : ℕ} {Γv : Ctx S} {P : Step S sp α}
    {Q : LStep S sp β} (h : Late post n Γv P Q) :
    ∀ Γa : Ctx S, (∀ v, Γa (up N₀ δ v) = Γv v) → N₀ ≤ n →
      Late (fun n' Γ' a b => N₀ + δ ≤ n' ∧ post (n' - δ) (fun v => Γ' (up N₀ δ v)) a b) (n + δ) Γa
        (virt N₀ δ P) (virtL N₀ δ Q) := by
  induction h with
  | @pure n Γ a b h =>
    intro Γa hΓ hn
    refine Late.pure ⟨by omega, ?_⟩
    have e : (fun v => Γa (up N₀ δ v)) = Γ := funext hΓ
    rw [e, Nat.add_sub_cancel]
    exact h
  | sample _ ih => intro Γa hΓ hn; exact Late.sample fun r => ih r Γa hΓ hn
  | plain _ ih => intro Γa hΓ hn; exact Late.plain fun r => ih r Γa hΓ hn
  | @fresh n Γ ℓ k k' _ ih =>
    intro Γa hΓ hn
    refine Late.fresh fun t ht => ?_
    have := ih (t - δ) (by omega) Γa hΓ (by omega)
    rwa [show t - δ + 1 + δ = t + 1 by omega] at this
  | @marked n Γ o t us pt inj k k' _ ih =>
    intro Γa hΓ hn
    refine Late.marked fun v t' ht => ?_
    have := ih v (t' - δ) (by omega) (Γa.set (up N₀ δ t) o pt) (fun v' => ?_) (by omega)
    · rwa [show t' - δ + 1 + δ = t' + 1 by omega] at this
    · by_cases e : v' = t
      · subst e
        simp only [Ctx.set, Function.update_self, hΓ]
      · have e' : up N₀ δ v' ≠ up N₀ δ t := fun h => e (up_injective N₀ δ h)
        simp only [Ctx.set, Function.update_of_ne e, Function.update_of_ne e', hΓ]
  | @reveal n Γ ts pts k k' hp _ ih =>
    intro Γa hΓ hn
    refine Late.reveal (fun a ha o pt hpt => ?_) fun vs => ih vs Γa hΓ hn
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
    rw [down_up]
    exact hp v hv o pt (by rw [← hΓ]; exact hpt)

end Compile.DefC
