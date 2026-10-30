-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_life2_Chall.lean: lemmas to show that the real experiment is mode R of a challenger
(`Chall`, Rom/Defer.lean: a state, and "a step for each call of the adversary"; mode R:
`Chall.world` at `false`: "modeI = true is mode I, false is mode R", `Step.run`).

  `ofOComp_reply`, `chall_reply`     The replies of `World.ofOComp` and of `Chall.world`, written
                                     out.
  `runLazy_bind_pure`, `run_fresh0`  A lazy run followed by a function of the result; a token for
                                     the empty string.
  `map_fst_call`, `map_fst_query`    The run of an adversary that starts with a call, or with a
                                     query, if the reply, or the answer, has the form μ.map f.
  `viewVals_dummy`                   The list of strings without all that follows its first N₀
                                     strings.

Limits: it does not define the challenger and does not prove that the real experiment is its mode R.
-/
import Compile.Spec
import Compile.Step1_life2_Erase
import Rom.Forget

noncomputable section

namespace Compile
namespace Life2
open Iop Rom Prob

variable {I X : Type} {lam : ℕ} (p : Params) (i : I)

/-! ## On challengers -/


/-! ### The replies, written out -/

section Replies

variable {S : OSpec} {sp : Split S}

theorem ofOComp_reply {Out In τ : Type} (step : τ → Out → OComp S (In × τ))
    (s : τ × Table S) (m : Out) :
    (World.ofOComp step).reply s m =
      ((step s.1 m).runLazy s.2).map fun p => (p.1.1, (p.1.2, p.2)) := rfl

theorem chall_reply {Out In : Type} (Ch : Chall S sp Out In) (m : Bool)
    (s : Ch.τ × DSt S) (c : Out) :
    (Ch.world m).reply s c = ((Ch.step s.1 c).run m s.2).map fun p => (p.1.1, (p.1.2, p.2)) := rfl

theorem runLazy_bind_pure {β γ : Type} (c : OComp S β) (f : β → γ) (T : Table S) :
    (c.bind fun o => pure (f o)).runLazy T = (c.runLazy T).map fun y => (f y.1, y.2) := by
  rw [OComp.runLazy_bind]
  rfl

/-- A token for the empty string. -/
theorem run_fresh0 {β : Type} (m : Bool) (k : ℕ → Step S sp β) (D : DSt S) :
    (Step.fresh 0 k).run m D = (k D.vals.length).run m { D with vals := D.vals ++ [[]] } := by
  have h : PMF.uniformOfFintype (Fin 0 → Bool) = PMF.pure fun j => j.elim0 := by
    refine PMF.ext fun u => ?_
    rw [Subsingleton.elim u fun j => j.elim0]
    simp
  simp only [Step.run, h, PMF.pure_bind]
  rfl

/-- The run of an adversary that starts with a call, if the reply has the form μ.map f. -/
theorem map_fst_call {Out In α γ : Type} (G : World S Out In) (c : Out) (k : In → Adv S Out In α)
    (s : G.σ) (μ : PMF γ) (f : γ → In × G.σ) (h : G.reply s c = μ.map f) :
    (interact G (.call c k) s).map Prod.fst =
      μ.bind fun y => (interact G (k (f y).1) (f y).2).map Prod.fst := by
  simp only [interact, PMF.map_bind, h, PMF.bind_map]
  rfl

theorem map_fst_query {Out In α γ : Type} (G : World S Out In) (o : S.ι)
    (q : S.Dom o) (k : S.Rng o → Adv S Out In α) (s : G.σ) (μ : PMF γ)
    (f : γ → S.Rng o × G.σ) (h : G.answer s o q = μ.map f) :
    (interact G (.query o q k) s).map Prod.fst =
      μ.bind fun y => (interact G (k (f y).1) (f y).2).map Prod.fst := by
  simp only [interact, PMF.map_bind, h, PMF.bind_map]
  rfl

end Replies







theorem viewVals_dummy {N₀ : ℕ} {l : List Bits} (h : N₀ ≤ l.length) (x : Bits) :
    viewVals N₀ (l.length + 1 - N₀) (l ++ [x]) = l.take N₀ := by
  unfold viewVals
  rw [List.take_append_of_le_length h,
    List.drop_eq_nil_of_le (by simp only [List.length_append, List.length_singleton]; omega),
    List.append_nil]

end Life2
end Compile
