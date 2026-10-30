-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartAllotProofs.lean: the proofs of the statements of Cb/Part/LdPartAllot.lean (the rule
that allots mask entries: a running sum). Nothing is stated here that is not stated there, but for
three lemmas on the running sum (`LdAllot.off_succ`, `LdAllot.off_mono`, `LdAllot.pos_block`).
-/
import Cb.Part.LdPartAllot

set_option autoImplicit false

namespace Cb

namespace LdAllot
variable (A : LdAllot)

theorem off_succ (b : ℕ) : A.off (b + 1) = A.off b + A.n b := Finset.sum_range_succ _ _

theorem off_mono {b b' : ℕ} (h : b ≤ b') : A.off b ≤ A.off b' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [off_succ]; exact Nat.le_add_right _ _)

/-- Under `h`, a number names its block. -/
theorem pos_block (h : A.OK) {b b' : ℕ} (x : A.Nm b) (x' : A.Nm b') (e : A.pos b x = A.pos b' x') :
    b = b' := by
  by_contra hne
  have key : ∀ {c c' : ℕ} (y : A.Nm c) (y' : A.Nm c'),
      c < c' → A.pos c y < A.pos c' y' := fun {c c'} y y' hc => by
    have h1 : A.off (c + 1) ≤ A.off c' := A.off_mono hc
    rw [off_succ] at h1
    have h2 := h.lt c y
    unfold LdAllot.pos
    omega
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd e (Nat.ne_of_lt (key x x' hlt))
  · exact absurd e.symm (Nat.ne_of_lt (key x' x hlt))

end LdAllot

theorem ldAllot_lt : Spec.ldAllot_lt := fun A h B b hb x => by
  have h1 : A.off (b + 1) ≤ A.off B := A.off_mono hb
  rw [LdAllot.off_succ] at h1
  have h2 := h.lt b x
  unfold LdAllot.pos
  omega

theorem ldAllot_inj : Spec.ldAllot_inj := by
  rintro A h ⟨b, x⟩ ⟨b', x'⟩ e
  obtain rfl : b = b' := A.pos_block h x x' e
  have e' : A.off b + A.num b x = A.off b + A.num b x' := e
  rw [h.inj b (Nat.add_left_cancel e')]

theorem ldAllot_places : Spec.ldAllot_places := fun A _ _ _ _ B h hf hc =>
  ⟨fun b hb b' hb' x x' e =>
      ldAllot_inj A h
        (hf.inj _ (lt_of_lt_of_le (ldAllot_lt A h B b hb x) hc) _
          (lt_of_lt_of_le (ldAllot_lt A h B b' hb' x') hc) e),
    fun b hb x => hf.dat _ (lt_of_lt_of_le (ldAllot_lt A h B b hb x) hc)⟩

theorem ldAllot_in : Spec.ldAllot_in := fun A N fr cap Dat B h hf hc b hb x x' e =>
  eq_of_heq (Sigma.mk.inj ((ldAllot_places A N fr cap Dat B h hf hc).1 b hb b hb x x' e)).2

theorem ldAllot_apart : Spec.ldAllot_apart := fun A N fr cap Dat B h hf hc b hb b' hb' hne x x' e =>
  hne (Sigma.mk.inj ((ldAllot_places A N fr cap Dat B h hf hc).1 b hb b' hb' x x' e)).1

theorem ldAllot_bound : Spec.ldAllot_bound := fun A B c h => by
  have h1 : A.off B ≤ ∑ _k ∈ Finset.range B, c :=
    Finset.sum_le_sum fun k hk => h k (Finset.mem_range.1 hk)
  rwa [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1

theorem ldAllot_std : Spec.ldAllot_std := fun Nm _ =>
  ⟨fun b _ _ e => (Fintype.equivFin (Nm b)).injective (Fin.ext e),
    fun b x => (Fintype.equivFin (Nm b) x).isLt⟩

theorem ldAllot_need : Spec.ldAllot_need := fun Nm _ B cap f hf => by
  have h1 := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma, Fintype.card_fin] at h1
  have h2 : (LdAllot.std Nm).off B = ∑ b : Fin B, Fintype.card (Nm b) :=
    (Fin.sum_univ_eq_sum_range (fun b => Fintype.card (Nm b)) B).symm
  rw [h2]
  exact h1

theorem ldFree_grid : Spec.ldFree_grid := fun _ at' R w Dat hi hd => by
  have hw : ∀ k, k < R * w → k / w < R ∧ k % w < w := fun k hk => by
    have hw0 : 0 < w := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
    exact ⟨Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hk), Nat.mod_lt _ hw0⟩
  refine ⟨fun k hk k' hk' e => ?_, fun k hk => hd _ (hw k hk).1 _ (hw k hk).2⟩
  obtain ⟨e1, e2⟩ := hi _ (hw k hk).1 _ (hw k hk).2 _ (hw k' hk').1 _ (hw k' hk').2 e
  rw [← Nat.div_add_mod k w, ← Nat.div_add_mod k' w, e1, e2]

theorem ldFree_fin : Spec.ldFree_fin := fun X _ _ x₀ at' Dat hi hd =>
  ⟨fun k hk k' hk' e => by
    have e1 := hi e
    unfold ldFrFin at e1
    rw [dif_pos hk, dif_pos hk'] at e1
    exact congrArg Fin.val ((Fintype.equivFin X).symm.injective e1), fun _ _ => hd _⟩

end Cb
