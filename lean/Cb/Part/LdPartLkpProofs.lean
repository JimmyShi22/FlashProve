-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartLkpProofs.lean: the proofs of the statements of Cb/Part/LdPartLkp.lean (from a
segment's key functions and tables to the data of "shift ; assembled lookup").
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Named tools: `lkStd_nm`, `lkStd_plN` (at the standard data the place of an own mask is its name);
`ldPartLk_validBits` (see its docstring).
-/
import Cb.Part.LdPartLkp
import Cb.Ld.LdLkpMultProofs
import Cb.Ld.LdLkpAsm2PullProofs
import Mathlib.Algebra.CharP.Basic

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

/-! ## The standard data -/

section Std
variable (E : Type) [Field E] [Fintype E] (v' d w n : ℕ)

/-- an own mask's name at the standard data, as a name in `LkOwn` -/
def lkStd_nm : (lkStd E v' d w n).Nm → LkOwn E v' d w n
  | .s i => .s i
  | .t l h i => .t l h i
  | .k l h i => .k l h i
  | .f l h i => .f l h i
  | .e i => .e i
  | .b i => .b i

theorem lkStd_nm_inj : Function.Injective (lkStd_nm E v' d w n) := by
  rintro (i | ⟨l, h, i⟩ | ⟨l, h, i⟩ | ⟨l, h, i⟩ | i | i)
      (i' | ⟨l', h', i'⟩ | ⟨l', h', i'⟩ | ⟨l', h', i'⟩ | i' | i') hh
    <;> simp only [lkStd_nm] at hh <;> first
    | (cases hh; rfl)
    | exact absurd hh (by simp)

theorem lkStd_plN (x : (lkStd E v' d w n).Nm) :
    (lkStd E v' d w n).plN x = .inr (lkStd_nm E v' d w n x) := by
  rcases x with (i | b) | ⟨l, h, (i | b)⟩ | ⟨l, h, (i | b)⟩ | ⟨l, h, (i | b)⟩ | i | (i | b)
  · rfl
  · rfl
  · exact dif_pos h
  · exact dif_pos h
  · exact dif_pos h
  · exact dif_pos h
  · exact dif_pos h
  · exact dif_pos h
  · rfl
  · rfl
  · rfl

theorem lkStd_placesIn :
    (lkStd E v' d w n).PlacesIn fun j => j ∈ Set.range (id : LkNm E v' d w n → LkNm E v' d w n) :=
  ⟨fun _ _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩, fun _ _ => ⟨_, rfl⟩,
    fun _ _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end Std

/-! ## The sizes -/

theorem ldPartSz_nk (L : LdPartSz) : L.nk ≤ 2 ^ L.g := Nat.le_pow_clog (by norm_num) _

theorem ldPartSz_kv (L : LdPartSz) {f : ℕ} (hf : f < L.nk) : L.kv f ≤ L.v := by
  have h : L.kv f ≤ (range L.nk).sup L.kv := le_sup (f := L.kv) (mem_range.2 hf)
  unfold LdPartSz.v LdPartSz.vm
  omega

theorem ldPartSz_kT (L : LdPartSz) {f : ℕ} (hf : f < L.nk) : L.kT f ≤ L.d :=
  le_sup (f := L.kT) (mem_range.2 hf)

theorem ldPartSz_fits : Spec.ldPartSz_fits := by
  intro L G V D p hn hv hV hT hp
  have hg : L.g ≤ G := Nat.clog_le_of_le_pow hn
  have hd : L.d ≤ D := Finset.sup_le fun f hf => hT f (mem_range.1 hf)
  have hs : (range L.nk).sup L.kv ≤ V := Finset.sup_le fun f hf => hv f (mem_range.1 hf)
  have hv' : L.v ≤ V := by
    unfold LdPartSz.v LdPartSz.vm
    omega
  refine lt_of_le_of_lt ?_ hp
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)

/-! ## Padding -/

theorem ldPartLk_inC (E : Type) [Field E] : Spec.ldPartLk_inC E := by
  intro St J L st m
  constructor
  · intro h f hf b hb
    obtain ⟨u, _, hu⟩ := h f (lt_of_lt_of_le hf (ldPartSz_nk L.toLdPartSz)) b
      (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (ldPartSz_kv L.toLdPartSz hf)))
    have hu' : (if f < L.nk then L.key st m f (b % 2 ^ L.kv f) else 0) =
      if f < L.nk then L.tab st f (u % 2 ^ L.kT f) else 0 := hu
    rw [if_pos hf, if_pos hf, Nat.mod_eq_of_lt hb] at hu'
    exact ⟨u % 2 ^ L.kT f, Nat.mod_lt _ (Nat.two_pow_pos _), hu'⟩
  · intro h f _ b _
    by_cases hf : f < L.nk
    · obtain ⟨u, hu, he⟩ := h f hf (b % 2 ^ L.kv f) (Nat.mod_lt _ (Nat.two_pow_pos _))
      refine ⟨u,
        lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (ldPartSz_kT L.toLdPartSz hf)),
        ?_⟩
      show (if f < L.nk then L.key st m f (b % 2 ^ L.kv f) else 0) =
        if f < L.nk then L.tab st f (u % 2 ^ L.kT f) else 0
      rw [if_pos hf, if_pos hf, Nat.mod_eq_of_lt hu]
      exact he
    · refine ⟨0, Nat.two_pow_pos _, ?_⟩
      show (if f < L.nk then L.key st m f (b % 2 ^ L.kv f) else 0) =
        if f < L.nk then L.tab st f (0 % 2 ^ L.kT f) else 0
      rw [if_neg hf, if_neg hf]

/-! ## Numbers -/

theorem ldPartSz_g_lt (L : LdPartSz) {p : ℕ} (h : L.Fits p) : 2 ^ L.g < p := by
  refine lt_of_le_of_lt ?_ h
  have h1 : 2 ^ L.g ≤ 2 ^ (L.g + L.d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 1 ≤ 2 ^ (L.g + L.v + 1) - 1 := by
    have : 2 ^ 1 ≤ 2 ^ (L.g + L.v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 2 ^ L.g ≤ 2 ^ (L.g + L.d) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem ldPartLk_tags (E : Type) [Field E] : Spec.ldPartLk_tags E := by
  intro p _ St J L hF f hf f' hf' he
  have hp := ldPartSz_g_lt L.toLdPartSz hF
  have he' : ((f : ℕ) : E) = ((f' : ℕ) : E) := he
  exact Nat.ModEq.eq_of_lt_of_lt
    ((CharP.natCast_eq_natCast E p).1 he') (lt_trans hf hp) (lt_trans hf' hp)

section
variable (E : Type) [Field E] [Fintype E]

theorem ldPartLk_nums : Spec.ldPartLk_nums E := fun _ _ _ _ _ => ⟨rfl, rfl⟩

theorem ldPartSz_w (L : LdPartSz) : L.n + 1 ≤ 2 ^ L.w := Nat.le_pow_clog (by norm_num) _

theorem ldPartLk_adm : Spec.ldPartLk_adm E := by
  intro p St J _ L e hF
  refine ⟨ldPartSz_w L.toLdPartSz, ?_, hF⟩
  show 2 ^ (L.g + L.vm + 1) < 2 ^ (L.g + (L.vm + 1) + 1)
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem ldPartLk_mu : Spec.ldPartLk_mu E := fun _ _ _ L e =>
  ldLkpAsm2_muValid E (L.A e) (ldPartSz_w L.toLdPartSz)

theorem ldPartLk_muU : Spec.ldPartLk_muU E := by
  intro St J _ L e st m h θ
  have h1 := ldLkpMult_shift E L.g L.v L.d L.w (L.n + 1) (L.P.key st m) (L.P.tab st) L.P.tag
    (fun f u j => m ((L.A0 e).bAt (f * 2 ^ L.d + u) j)) h θ
  have e1 : shBit L.d (fun f u j => m ((L.A0 e).bAt (f * 2 ^ L.d + u) j)) =
      fun u j => m ((L.A0 e).bAt u j) := by
    funext u j
    show m ((L.A0 e).bAt (u / 2 ^ L.d * 2 ^ L.d + u % 2 ^ L.d) j) = _
    rw [Nat.div_add_mod']
  rw [e1] at h1
  exact h1

omit [Fintype E] in
/-- for W ≤ 2^w "valid" reads the bits inside the table and the bit positions only -/
theorem ldPartLk_validBits {n T w W : ℕ} {key t : ℕ → E} {M M' : ℕ → ℕ → E} (hW : W ≤ 2 ^ w)
    (hM : ∀ u < 2 ^ T, ∀ j < 2 ^ w, M u j = M' u j) (h : Valid n T w W key t M') :
    Valid n T w W key t M := by
  classical
  refine ⟨fun u hu j hj => ?_, fun u hu j hj hj' => ?_, fun x => ?_⟩
  · rw [hM u hu j hj]
    exact h.1 u hu j hj
  · rw [hM u hu j hj']
    exact h.2.1 u hu j hj hj'
  · rw [← h.2.2 x]
    refine sum_congr rfl fun u hu => ?_
    unfold multOf Alg.Lookup.mult
    refine sum_congr rfl fun j hj => ?_
    show (if decide (M u j = 1) = true then 2 ^ j else 0) =
      if decide (M' u j = 1) = true then 2 ^ j else 0
    rw [hM u (mem_range.1 (mem_filter.1 hu).1) j (lt_of_lt_of_le (mem_range.1 hj) hW)]

theorem ldPartLk_honest : Spec.ldPartLk_honest E := by
  intro St J _ L e st m hin hb f hf
  refine ldPartLk_validBits E (ldPartSz_w L.toLdPartSz) (hb f hf)
    (ldLkpMult_honest E L.v L.d L.w (L.n + 1) _ _ ?_ (hin f hf))
  show 2 ^ L.v < 2 ^ (L.g + L.v + 1)
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem ldPartLk_honestNm : Spec.ldPartLk_honestNm E := by
  intro St J _ L e st m hin H
  refine ldPartLk_honest E St J L e st m hin fun f hf u hu j hj => ?_
  have hY : f * 2 ^ L.d + u < 2 ^ L.dd := by
    show f * 2 ^ L.d + u < 2 ^ (L.g + L.d)
    rw [pow_add]
    calc f * 2 ^ L.d + u < f * 2 ^ L.d + 2 ^ L.d := Nat.add_lt_add_left hu _
      _ = (f + 1) * 2 ^ L.d := by ring
      _ ≤ 2 ^ L.g * 2 ^ L.d := Nat.mul_le_mul_right _ hf
  have e1 : (f * 2 ^ L.d + u) / 2 ^ L.d = f := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hu, Nat.zero_add]
  have e2 : (f * 2 ^ L.d + u) % 2 ^ L.d = u := Nat.mul_add_mod_of_lt hu
  refine (H ⟨(f * 2 ^ L.d + u) % 2 ^ L.dd, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    ⟨j % 2 ^ L.w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩).trans ?_
  show hbit L.v (L.n + 1) (L.P.key st m ((f * 2 ^ L.d + u) % 2 ^ L.dd / 2 ^ L.d))
      (L.P.tab st ((f * 2 ^ L.d + u) % 2 ^ L.dd / 2 ^ L.d))
      ((f * 2 ^ L.d + u) % 2 ^ L.dd % 2 ^ L.d) (j % 2 ^ L.w) = _
  rw [Nat.mod_eq_of_lt hY, Nat.mod_eq_of_lt hj, e1, e2]

theorem ldPartLk_placesIn : Spec.ldPartLk_placesIn E := fun _ _ _ L e =>
  re2_placesIn (lkStd E L.v' L.dd L.w L.n) e _ _ id (lkStd_placesIn E L.v' L.dd L.w L.n)

theorem ldPartLk_placesOK : Spec.ldPartLk_placesOK E := by
  intro St J _ L e Dt he hb hm hk
  refine re2_placesOK (lkStd E L.v' L.dd L.w L.n) e _ _ he (Dt := fun j => ∃ x, j = .inl x)
    (Dt' := Dt) ?_ ?_ (fun _ _ => ⟨_, rfl⟩) ?_ ?_ ?_
  · intro x y h
    rw [lkStd_plN, lkStd_plN] at h
    exact lkStd_nm_inj E _ _ _ _ (Sum.inr_injective h)
  · rintro i ⟨x, hx⟩
    rw [lkStd_plN] at hx
    cases hx
  · rintro j ⟨x, rfl⟩
    exact hb x
  · rintro (x | x) h
    · exact ⟨x, rfl⟩
    · exact absurd h (hm x)
  · intro x m m' h
    show shKey L.P.v (L.P.key x.1 m) L.P.tag x.2 = shKey L.P.v (L.P.key x.1 m') L.P.tag x.2
    have : L.P.key x.1 m = L.P.key x.1 m' := by
      show (fun f b => if f < L.nk then L.key x.1 m f (b % 2 ^ L.kv f) else 0) =
        fun f b => if f < L.nk then L.key x.1 m' f (b % 2 ^ L.kv f) else 0
      rw [hk x.1 m m' h]
    rw [this]

end
end Cb
