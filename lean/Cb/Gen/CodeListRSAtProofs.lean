-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gen/CodeListRSAtProofs.lean: the proofs of the statements of
Cb/Gen/CodeListRSAt.lean.

`bchks46At_of_F`: one line.
`rows_cost_nothingAt` applies `Cb.rows_free_abs` (Cb/Ld/LdRelRowsEAbsProofs.lean) at the space of
words over E and the subspaces "agrees on A with a polynomial of degree at most k" (`onRSSub`).
`rsAt_mca`, `rsAt_prox`, `rsAt_group_prox` are proved as `rs_mcaAtF`, `rs_proxF`, `rs_group_proxF`
in Cb/Gen/CodeListRSF.lean, with `rows_cost_nothingAt` in the place of `rows_cost_nothingF`.
BCHKS46At F E is a hypothesis by name, no axiom.
-/
import Cb.Gen.CodeListRSAt
import Cb.Ld.LdRelRowsEAbsProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Polynomial
open CodeListRows CodeListRS CodeRep

/-- The words that agree on A with a polynomial of degree at most k: a subspace. -/
def onRSSub {K : Type} [Field K] {n : ℕ} (x : Fin n → K) (k : ℕ) (A : Finset (Fin n)) :
    Submodule K (Fin n → K) where
  carrier := {u | OnRS x k u A}
  zero_mem' :=
    ⟨0, by rw [degree_zero]; exact WithBot.bot_lt_coe _, fun j _ => by rw [eval_zero]; rfl⟩
  add_mem' := fun {a b} ⟨p, hp, ha⟩ ⟨q, hq, hb⟩ =>
    ⟨p + q, lt_of_le_of_lt (degree_add_le p q) (max_lt hp hq),
      fun j hj => by rw [eval_add, ← ha j hj, ← hb j hj]; rfl⟩
  smul_mem' := fun c a ⟨p, hp, ha⟩ =>
    ⟨c • p, lt_of_le_of_lt (degree_smul_le c p) hp, fun j hj => by rw [eval_smul, ← ha j hj]; rfl⟩

section
variable (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E]

theorem bchks46At_of_F : Spec.bchks46At_of_F F E := fun H n k e x hx hk he hJ u₀ u₁ => H E n k e x hx hk he hJ u₀ u₁

theorem rows_cost_nothingAt : Spec.rows_cost_nothingAt F E := by
  intro H n k e x hx hk he hJ R _ u₀ u₁
  cases nonempty_fintype R
  obtain ⟨w, hw⟩ := rows_free_abs E R (Fin n → E) (Finset (Fin n)) (fun A => n ≤ A.card + e)
    (onRSSub (fun j => algebraMap F E (x j)) k) u₀ u₁
  refine le_trans (Nat.cast_le.mpr (cnt_mono fun z hz => ?_))
    (H n k e x hx hk he hJ (∑ a, w a • u₀ a) (∑ a, w a • u₁ a))
  obtain ⟨A, hA, h1, h2⟩ := hz
  obtain ⟨A', hA', h3, h4⟩ := hw z ⟨A, hA, h1, h2⟩
  exact ⟨A', hA', h3, h4⟩

theorem rsAt_mca : Spec.rsAt_mca F E := by
  intro H n k msg r e₀ mca₀ x hx e hk he hJ R _ f₀ f₁
  have h := rows_cost_nothingAt F E H n k e x hx hk he hJ R f₀ f₁
  refine Nat.le_floor
    (le_trans (Nat.cast_le.mpr (le_of_eq (cnt_congr fun θ => exists_congr fun S => ?_))) h)
  rw [CodeListRS.onCode_iff, CodeListRS.onCode_iff, CodeListRS.onCode_iff]
  exact Iff.rfl

theorem rsAt_prox : Spec.rsAt_prox F E := by
  intro H n k msg r e₀ mca₀ x hx hk
  refine ⟨fun e he R _ f => ?_,
    fun e he R _ => rsAt_mca F E H n k msg r e₀ mca₀ x hx e hk he.1 he.2 R⟩
  have hkn := lt_of_radius he.2
  have h := johnson_enc F E (Code.RS.code x (k + 1) msg r e₀ mca₀) e (Code.RS.code_dist hx hkn)
    (by
      show InJohnson n (n - (k + 1) + 1) e
      rw [dist_eq hkn]
      exact inJohnson_of_radius he.2) R f
  have h' : cnt (fun M => DecodesTo ((Code.RS.code x (k + 1) msg r e₀ mca₀).GE E) e f M) ≤
      listMax n (n - (k + 1) + 1) e := h
  rwa [dist_eq hkn] at h'

theorem rsAt_group_prox : Spec.rsAt_group_prox F E := by
  intro H A _ n k msg r x hx hk hkn T hT D hD R _
  have hd : ∀ a, HasDist (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).G
      (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d :=
    fun a => Code.RS.code_dist (hx a) (hkn a)
  have hD' : ∀ a, D ≤ T.mult a * (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d := fun a => by
    show D ≤ T.mult a * (n a - (k a + 1) + 1)
    rw [dist_eq (hkn a)]
    exact hD a
  have hP := prox_johnson_of_comps F E A _ T hT hd D hD' R _ _ _ fun a =>
    rsAt_prox F E H (n a) (k a) (msg a) (r a) 0 0 (x a) (hx a) (hk a)
  have hok : ∀ e, (InJohnson (Fintype.card T.P) D e ∧ ∀ a, T.mult a ≤ e) →
      InJohnson (Fintype.card T.P) D e ∧
      ∀ a, 0 < e / T.mult a ∧ n a * k a < (n a - e / T.mult a) ^ 2 := by
    intro e he
    refine ⟨he.1, fun a => ⟨Nat.div_pos (he.2 a) (hT a).1, ?_⟩⟩
    have hc : Fintype.card T.P = T.mult a * n a := even_card F A _ T hT a
    have h1 := he.1
    rw [hc] at h1
    have h2 := inJohnson_comp (n a) (n a - k a) (T.mult a) D e (hD a) h1
    unfold InJohnson at h2
    rwa [Nat.sub_sub_self (hkn a).le] at h2
  exact ⟨fun e he => hP.list e (hok e he), fun e he => hP.mca e (hok e he)⟩

end
end Cb
