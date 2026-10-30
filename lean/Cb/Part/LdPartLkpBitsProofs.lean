-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartLkpBitsProofs.lean: the proofs of the statements of Cb/Part/LdPartLkpBits.lean (the
bits of the front lookups' multiplicities as data: the value of the parameters "honest bits", its
law, the tie to the lookup's own clause).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
-/
import Cb.Part.LdPartLkpBits
import Cb.Part.LdPartLkpFamProofs

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset Cb.LdLkp Cb.Lkp

theorem ldPartSz_pair (L : LdPartSz) {f u : ℕ} (hf : f < 2 ^ L.g) (hu : u < 2 ^ L.d) :
    f * 2 ^ L.d + u < 2 ^ L.dd ∧
    (f * 2 ^ L.d + u) / 2 ^ L.d = f ∧
    (f * 2 ^ L.d + u) % 2 ^ L.d = u := by
  refine ⟨?_, ?_, Nat.mul_add_mod_of_lt hu⟩
  · show f * 2 ^ L.d + u < 2 ^ (L.g + L.d)
    rw [pow_add]
    calc f * 2 ^ L.d + u < f * 2 ^ L.d + 2 ^ L.d := Nat.add_lt_add_left hu _
      _ = (f + 1) * 2 ^ L.d := by ring
      _ ≤ 2 ^ L.g * 2 ^ L.d := Nat.mul_le_mul_right _ hf
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hu, Nat.zero_add]

theorem ldPartSz_bitNo (L : LdPartSz) (Y : ℕ) {j : ℕ} (hj : j < 2 ^ L.w) :
    L.bitNo Y j / 2 ^ L.w = Y ∧ L.bitNo Y j % 2 ^ L.w = j := by
  refine ⟨?_, Nat.mul_add_mod_of_lt hj⟩
  show (Y * 2 ^ L.w + j) / 2 ^ L.w = Y
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hj, Nat.zero_add]

theorem ldPartLk_honN : Spec.ldPartLk_honN := by
  intro E St J _ L st m hin f hf
  refine ldPartLk_validBits E (ldPartSz_w L.toLdPartSz) (fun u hu j hj => ?_)
    (ldLkpMult_honest E L.v L.d L.w (L.n + 1) _ _ ?_ (hin f hf))
  · obtain ⟨_, e1, e2⟩ := ldPartSz_pair L.toLdPartSz hf hu
    obtain ⟨e3, e4⟩ := ldPartSz_bitNo L.toLdPartSz (f * 2 ^ L.d + u) hj
    show hbit L.v (L.n + 1) (L.P.key st m (L.bitNo (f * 2 ^ L.d + u) j / 2 ^ L.w / 2 ^ L.d))
        (L.P.tab st (L.bitNo (f * 2 ^ L.d + u) j / 2 ^ L.w / 2 ^ L.d))
        (L.bitNo (f * 2 ^ L.d + u) j / 2 ^ L.w % 2 ^ L.d) (L.bitNo (f * 2 ^ L.d + u) j % 2 ^ L.w) =
      _
    rw [e3, e4, e1, e2]
  · show 2 ^ L.v < 2 ^ (L.g + L.v + 1)
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem ldPartLk_validN : Spec.ldPartLk_validN := by
  intro E St J _ _ _ L e st m b hb
  have key : ∀ f < 2 ^ L.g, ∀ u < 2 ^ L.d,
      ∀ j < 2 ^ L.w, m ((L.A0 e).bAt (f * 2 ^ L.d + u) j) = b (L.bitNo (f * 2 ^ L.d + u) j) := by
    intro f hf u hu j hj
    refine (hb ⟨(f * 2 ^ L.d + u) % 2 ^ L.dd, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      ⟨j % 2 ^ L.w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩).trans ?_
    show b (L.bitNo ((f * 2 ^ L.d + u) % 2 ^ L.dd) (j % 2 ^ L.w)) = _
    rw [Nat.mod_eq_of_lt (ldPartSz_pair L.toLdPartSz hf hu).1, Nat.mod_eq_of_lt hj]
  exact ⟨fun h f hf => ldPartLk_validBits E (ldPartSz_w L.toLdPartSz) (key f hf) (h f hf),
    fun h f hf =>
      ldPartLk_validBits E (ldPartSz_w L.toLdPartSz)
        (fun u hu j hj => (key f hf u hu j hj).symm) (h f hf)⟩

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

omit [Algebra F E] in
theorem ldPartKeys_fam (l : List (Fam X E × Tab F)) {f : ℕ} (hf : f < l.length) :
    (LdPartKeys.ofList l).fam f = l[f].1 := by
  show (l.getD f _).1 = _
  rw [List.getD_eq_getElem _ _ hf]

/-- Under the hypotheses below, the keys are the same at two matrices of cells that agree at the
places read. -/
theorem ldPartKeys_keyEq (l : List (Fam X E × Tab F)) (Φ : IdxFmt F) (hw : ∀ q ∈ l, q.1.WF Φ)
    {St St' J J' : Type} (R : LdPartRd E J) (R' : LdPartRd E J') (xs : St → X) (xs' : St' → X)
    (st : St) (st' : St') (m : J → E) (m' : J' → E) (W : ℕ → ℕ → F) (hx : xs st = xs' st')
    (hW : R.W m = fun y c => algebraMap F E (W y c))
    (hW' : R'.W m' = fun y c => algebraMap F E (W y c))
    (hA : ∀ q ∈ l, ∀ z ∈ q.1.places, R.A m z.1 z.2.1 z.2.2 = R'.A m' z.1 z.2.1 z.2.2) :
    ((LdPartKeys.ofList l).lk Φ.h (Φ.hi + Φ.lo) R xs).P.key st m =
      ((LdPartKeys.ofList l).lk Φ.h (Φ.hi + Φ.lo) R' xs').P.key st' m' := by
  funext f b
  show (if f < l.length then
        ((LdPartKeys.ofList l).fam f).ext Φ.h (Φ.hi + Φ.lo) (xs st) (R.W m) (R.A m)
          (vtx ((LdPartKeys.ofList l).fam f).v (b % 2 ^ ((LdPartKeys.ofList l).fam f).v))
      else 0) =
    if f < l.length then
      ((LdPartKeys.ofList l).fam f).ext Φ.h (Φ.hi + Φ.lo) (xs' st') (R'.W m') (R'.A m')
        (vtx ((LdPartKeys.ofList l).fam f).v (b % 2 ^ ((LdPartKeys.ofList l).fam f).v))
    else 0
  by_cases hf : f < l.length
  · rw [if_pos hf, if_pos hf, ldPartKeys_fam l hf, hW, hW', hx]
    have hm := List.getElem_mem hf
    have hb : b % 2 ^ l[f].1.v < 2 ^ l[f].1.v := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [ldPart_vtxF Φ (xs' st') W (R.A m) l[f].1 _ (hw _ hm) hb,
      ldPart_vtxF Φ (xs' st') W (R'.A m') l[f].1 _ (hw _ hm) hb]
    exact fam_val_congr X F E l[f].1 Φ (xs' st') W _ _ (hw _ hm) (hA _ hm) _ hb
  · rw [if_neg hf, if_neg hf]

end

theorem ldPartBits_ok : Spec.ldPartBits_ok := by
  intro F E _ _ _ _ Cf P hw j hj x W g hH
  refine ldPartLk_honN E Unit Unit (P.lkAt j x W g) () 0 ?_
  exact (ldPartKeys_holds Cf.Xm F E Unit Unit (P.seg j).keys P.fmt
    ⟨fun _ => fun y c => algebraMap F E (W y c), fun _ => LdPartD.castM (E := E) g⟩ (fun _ => x) ()
    0 W (hw j hj).2 rfl).2 hH.2

theorem ldPartBits_tie : Spec.ldPartBits_tie := by
  intro F E _ _ _ _ Cf P j St J _ R xs e st mm W g b hw hW hA hb hok
  refine (ldPartLk_validN E St J _ e st mm b hb).1 fun f hf => ?_
  have h1 := hok f hf
  have ek := ldPartKeys_keyEq (P.seg j).keys P.fmt hw.2 R
    (⟨fun _ => fun y c => algebraMap F E (W y c),
      fun _ => LdPartD.castM (E := E) g⟩ : LdPartRd E Unit)
    xs (fun _ : Unit => xs st) st () mm 0 W rfl hW rfl fun q hq z hz => hA z (Or.inr ⟨q, hq, hz⟩)
  show Valid _ _ _ _ (((P.keysOf j).lk P.fmt.h (P.fmt.hi + P.fmt.lo) R xs).P.key st mm f) _ _
  unfold LdPartD.keysOf
  rw [ek]
  exact h1

end Cb
