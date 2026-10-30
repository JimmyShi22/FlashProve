-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`IsGlJ`, `IsGlS` (Cb/Gl/GlLdJ.lean) do not ask a radius within half the distance. The theorems under
`BCHKS46F F` below have a premise that this file does not prove.
Cb/Gl/GlLdJProofs.lean: the proofs of the statements of Cb/Gl/GlLdJ.lean (below the Johnson radius
over p = 2^64 - 2^32 + 1: the bound on lists is proved; agreement follows from BCHKS46F F, a premise
by name).
`Cb.BCHKS46F F` (Cb/Gen/CodeListRSF.lean) is a hypothesis; this file does not prove it.
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.) It is the premise H of
`glJ_rows0`, `glS_rows`, `glJ_rows`, and a premise of `Spec.glJ_mca`, `Spec.glJ_errOK`,
`Spec.glJ_base`; `glJ_glC`, `glJ_list`, `john_lt`, `glJ_mono`, `glJ_one` do not have it.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Inductions over the closure; the base case of agreement is Cb/Gl/GlCodesLdF.lean's `gl_group_proxF`
through Cb/Ld/LdRelRows.lean's `ld_rows_ld`.

Notation: `F`: the integers modulo p (Cb/Gl/GlField.lean); `E`: the challenge field
(Cb/Gl/GlField.lean); `C`: a code read under a transformation (`LdCode E P`, Cb/Ld/LdRel.lean); `P`:
its long positions; `d`, `t`, `e`, `bad`: numbers, the arguments of `GlJ C d t e bad`
(Cb/Gl/GlLdJ.lean); d and e stand as distance and radius in `InJohnson n d e`; `InJohnson n d e`:
below the Johnson radius: n positions, distance d, radius e (Cb/Gen/JohnsonList.lean); `base`,
`sub`, `copy`, `il`, `pair`, `fam`, `up`: the constructors of `GlJ`, the closure (Cb/Gl/GlLdJ.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlLdJ
import Cb.Gl.GlCopyJ
import Cb.Gl.GlCodesLdF
import Cb.Ld.LdRelRowsProofs
import Cb.Ld.LdRelSubProofs
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

theorem glJ_glC : Spec.glJ_glC := by
  intro P _ C d t e bad h
  induction h with
  | base h =>
      obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, -, hk, hp, hE, hd, ht, -, -⟩ :=
        h
      exact .base
        ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk,
          fun i => le_of_eq (hp i), hE, hd, ht⟩
  | sub h =>
      obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, -, hk, hp, hE, hd, ht, -, -⟩ :=
        h
      exact .base ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk, hp, hE, hd, ht⟩
  | copy h => exact .copy (glCpJ_cp P _ _ _ _ _ h)
  | il R _ ih => exact .il R ih
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | fam _ ih => exact .fam ih
  | up _ _ ih => exact ih

theorem glJ_list : Spec.glJ_list := fun P _ C d t e bad h hJ =>
  have g := glC_code P C d t (glJ_glC P C d t e bad h)
  ⟨ld_list_johnson E P C d e g.1 g.2.2.2.1 hJ,
    fun R _ _ =>
      ld_list_johnson E P (C.il R) d e (ld_laws_il E P C R g.1) (ld_dist_il E P C R d g.2.2.2.1) hJ⟩

theorem john_lt {n d e : ℕ} (h : InJohnson n d e) : e < d := by
  by_contra hn
  have h1 : n - e ≤ n - d := Nat.sub_le_sub_left (Nat.le_of_not_lt hn) n
  have h2 : (n - e) ^ 2 ≤ n * (n - d) := by
    rw [pow_two]
    exact Nat.mul_le_mul (Nat.sub_le n e) h1
  exact absurd h (not_lt.2 h2)

/-- the families whose message and randomness fill the dimension. Limit: the statement has the
premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it. -/
theorem glJ_rows0 (H : Cb.BCHKS46F F) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : IsGlJ C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk, hp, hE, hd, -, hm, hb⟩ :=
    h
  exact ld_rows_mono E P _ _ _ _ hb
    (ld_rows_ld F E A (grp a k msg r) (⟨P, pos, mult⟩ : Reading (grp a k msg r)) _ _ hp
      (fun R' _ _ =>
        (gl_group_proxF H A a k msg r ha hk0 hk
            (⟨P, pos, mult⟩ : Reading (grp a k msg r)) hE _ hd R').mca
          _ ⟨hJ, hm⟩) R)

/-- a subcode: one more term. Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis;
this file does not prove it. -/
theorem glS_rows (H : Cb.BCHKS46F F) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : IsGlS C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk,
      hp, hE, hd, ht, hm, hb⟩ := h
  have hW : IsGlJ ((⟨P, pos, mult⟩ : Reading (grp a k msg fun i => k i + 1 - msg i)).ld E R) d 0 e
      (∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / mult i)⌋₊) :=
    ⟨A, iA, dA, a, k, msg, fun i => k i + 1 - msg i, pos, mult, R, fR, dR, rfl, ha, hk0, hk, fun i => by
      have := hp i
      show msg i + (k i + 1 - msg i) = k i + 1
      omega, hE, hd, fun _ => Nat.zero_le _, hm, le_rfl⟩
  have gW := glC_code P _ d 0 (.base
    ⟨A, iA, dA, a, k, msg, fun i => k i + 1 - msg i, pos, mult, R, fR, dR, rfl, ha, hk, fun i => by
      have := hp i
      show msg i + (k i + 1 - msg i) ≤ k i + 1
      omega, hE, hd, fun _ => Nat.zero_le _⟩)
  have gS := glC_code P _ d t
    (.base ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk, hp, hE, hd, ht⟩)
  have hsub : ((⟨P, pos, mult⟩ : Reading (grp a k msg fun i => k i + 1 - msg i)).ld E R).SubOf
      ((⟨P, pos, mult⟩ : Reading (grp a k msg r)).ld E R) fun α => α :=
    ld_sub_ld F E A (grp a k msg r) (fun i => k i + 1 - msg i) P pos mult R fun i => by
      have := hp i
      show r i ≤ k i + 1 - msg i
      omega
  exact ld_rows_mono E P _ _ _ _ hb
    (ld_sub_rows E P _ _ _ d e _ _ hsub gW.1 gS.1 gW.2.2.2.1 (john_lt hJ)
      (glJ_rows0 H P _ d 0 e _ hW hJ) fun R' _ _ =>
        ld_list_johnson E P _ d e (ld_laws_il E P _ Bool (ld_laws_il E P _ R' gW.1))
          (ld_dist_il E P _ Bool d (ld_dist_il E P _ R' d gW.2.2.2.1)) hJ)

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_rows (H : Cb.BCHKS46F F) (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ)
    (h : GlJ C d t e bad) (hJ : InJohnson (Fintype.card P) d e) : C.MCArows e bad := by
  induction h with
  | base h => exact glJ_rows0 H P _ _ _ _ _ h hJ
  | sub h => exact glS_rows H P _ _ _ _ _ h hJ
  | copy h => exact glCp_rows_of (fun P _ C d t e bad h hJ => glJ_rows0 H P C d t e bad h hJ) P _ _ _ _ _ h hJ
  | il R _ ih => exact ld_rows_il E P _ R _ _ (ih hJ)
  | pair _ _ ih₁ ih₂ => exact ld_rows_pair E P _ _ _ _ _ (ih₁ hJ) (ih₂ hJ)
  | fam _ ih => exact ld_rows_fam E P _ _ _ _ fun a => ih a hJ
  | up _ hb ih => exact ld_rows_mono E P _ _ _ _ hb (ih hJ)

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_mca : Spec.glJ_mca := fun H P _ C d t e bad h hJ =>
  ⟨glJ_rows H P C d t e bad h hJ, ld_rows_self E P C e bad (glJ_rows H P C d t e bad h hJ)⟩

theorem glJ_mono : Spec.glJ_mono := by
  intro P _ C d t e bad t' h h2
  induction h with
  | base h =>
      obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk0, hk,
          hp, hE, hd, ht, hm, hb⟩ := h
      exact .base
        ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk0, hk, hp, hE, hd,
          fun i => le_trans h2 (ht i), hm, hb⟩
  | sub h =>
      obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk0, hk,
          hp, hE, hd, ht, hm, hb⟩ := h
      exact .sub
        ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, hC, ha, hk0, hk, hp, hE, hd,
          fun i => le_trans h2 (ht i), hm, hb⟩
  | copy h => exact .copy (glCpJ_mono P _ _ _ _ _ t' h h2)
  | il R _ ih => exact .il R (ih h2)
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ h2) (ih₂ h2)
  | fam _ ih =>
      obtain rfl : t' = 0 := Nat.le_zero.1 h2
      exact .fam fun a => ih a le_rfl
  | up _ hb ih => exact .up (ih h2) hb

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_errOK : Spec.glJ_errOK := by
  intro H P _ Y d t e bC bZ bW hC hZ hW hJ
  have gC := glC_code P _ d 0 (glJ_glC P _ d 0 e bC hC)
  have gZ := glC_code P _ d 0 (glJ_glC P _ d 0 e bZ hZ)
  have gW := glC_code P _ d t (glJ_glC P _ d t e bW hW)
  refine ⟨fun j _ => ?_,
    fun j _ _ => glJ_rows H P _ d 0 e bC hC hJ _,
    fun j _ _ => glJ_rows H P _ d 0 e bZ hZ hJ _,
    fun j _ _ => glJ_rows H P _ d t e bW hW hJ _⟩
  exact ld_list_johnson E P (Y.stage j) d e
    (ld_laws_pair E P _ _ (ld_laws_il E P Y.C _ gC.1)
      (ld_laws_pair E P _ _ (ld_laws_il E P Y.Z _ gZ.1) (ld_laws_il E P Y.Zw _ gW.1)))
    (ld_dist_pair E P _ _ d (ld_dist_il E P Y.C _ d gC.2.2.2.1)
      (ld_dist_pair E P _ _ d (ld_dist_il E P Y.Z _ d gZ.2.2.2.1)
        (ld_dist_il E P Y.Zw _ d gW.2.2.2.1))) hJ

-- Limit: the statement has the premise `Cb.BCHKS46F F`, a hypothesis; this file does not prove it.
theorem glJ_base : Spec.glJ_base := fun H a d bad h hJ hlt =>
  have g := glC_code a.P a.C d 0 (glJ_glC a.P a.C d 0 a.e bad h)
  ⟨g.1, g.2.1, hlt, (glJ_mca H a.P a.C d 0 a.e bad h hJ).2,
    (glJ_list a.P a.C d 0 a.e bad h hJ).2 Bool⟩

theorem glJ_one : Spec.glJ_one := fun a k msg r e R fR dR ha hk0 hk hp he  =>
  ⟨Unit, inferInstance, inferInstance, fun _ => a, fun _ => k, fun _ => msg, fun _ => r,
    fun _ x => x, fun _ => 1, fun _ => R, fun _ => fR, fun _ => dR, rfl, fun _ => ha, fun _ => hk0,
    fun _ => hk, fun _ => hp, one_even F (rs a k msg r 0 0), fun _ => by rw [Nat.one_mul],
    fun _ => le_rfl, fun _ => he,  by simp⟩

end Cb.Gl
