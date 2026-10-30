-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartCfProofs.lean: the proofs of Cb/Part/LdPartCf.lean: the configuration over which a
request is built from a partition: its relation pair against the model's.

The lemmas, of use to other files on packed cells:
  `ldPartCf_pack`: the data that are made from integer matrices that are in absolute value below a
    bound b > 0 are, at each layer j < P.n (hj), the packing of these matrices (`PackBy` b).
  `ldPartCf_row`: with at least one lane, a row of a segment's matrix lies in a packed row of the
    layer and in a lane.
  `ldPartCf_cast`: the cells unpacked from the data, in E, are the images of the integers unpacked
    from them: at all places, by unfolding.
  `ldPartCf_small`: if 0 < P.D (hD): where every layer is a packing of cells below 2 D in absolute
    value, the integers unpacked are below 2 D in absolute value in all shapes.
  `ldPartCf_hon`: under unique packing (hU, at the characteristic p of E), with at least one lane
    (hK): where layer j is the packing of g's matrix j below b ≤ 2 D in absolute value and the
    segment's columns fit the public width, the cells unpacked from it are g's, inside the shape.
  `ldPartCf_holds`: a well-formed segment's (hw) conditions are the same at two families of matrices
    that agree at the places that the segment reads.

Limits: what the head of Cb/Part/LdPartCf.lean lists as not said is not said here either. In
`ldPartCf_no` the premise "at least one lane" is not used.
-/
import Cb.Part.LdPartCf
import Cb.Ld.LdRngAlgProofs
import Cb.Req.ReqSpecProofs

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk

/-- a well-formed segment's conditions read the matrices at its places only -/
theorem ldPartCf_holds {X F E : Type} [Field F] [Field E] [Algebra F E] (S : SegSpec X F E)
    (Φ : IdxFmt F) (x : X) (W : ℕ → ℕ → F) (A A' : ℕ → ℕ → ℕ → E) (hw : S.WF Φ)
    (h : ∀ q ∈ S.places, A q.1 q.2.1 q.2.2 = A' q.1 q.2.1 q.2.2) :
    S.Holds Φ x W A → S.Holds Φ x W A' := by
  rintro ⟨h1, h2⟩
  refine ⟨fun f hf b hb => ?_, fun k hk b hb => ?_⟩
  · rw [← fam_val_congr X F E f Φ x W A A' (hw.1 f hf) (fun q hq => h q (Or.inl ⟨f, hf, hq⟩)) b hb]
    exact h1 f hf b hb
  · obtain ⟨u, hu, e⟩ := h2 k hk b hb
    refine ⟨u, hu, ?_⟩
    rw [← fam_val_congr X F E k.1 Φ x W A A' (hw.2 k hk)
        (fun q hq => h q (Or.inr ⟨k, hk, hq⟩)) b hb]
    exact e

/-- the virtual matrix of a packing is below the bound in absolute value -/
theorem ldPartCf_cells_lt {E Rp C : Type} [CommRing E] [Fintype Rp] (P : ℕ) (b ϱ : ℤ)
    (mpk : Rp → C → E) (h : Packed P b ϱ mpk) (r : Rp × Fin P) (c : C) :
    |cells P b ϱ mpk r c| < b := by
  unfold cells
  rw [dif_pos h]
  exact h.choose_spec.1 r c

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E}
  (P : LdPartD Cf) (K : LdPartPk)

theorem ldPartCf_pack (Bt : LdPartBits P) (x : Cf.Xm) (W : ℕ → ℕ → F) (g : LdPartGh) (b : ℤ)
    (hb : 0 < b) (hg : P.Below b g) (j : ℕ) (hj : j < P.n) :
    PackBy b K.rdx (P.layX K g j) (P.layW K (P.packW K Bt x W g) j) := by
  refine ⟨fun r c => ?_, fun i c => ?_⟩
  · unfold LdPartD.layX
    split_ifs with h
    · exact hg (j, r.1.val * K.P + r.2.val, c.val) ⟨hj, h.1, h.2⟩
    · simpa using hb
  · exact (Fin.sum_univ_eq_sum_range
      (fun l =>
        ((K.rdx : ℤ) : E) ^ l *
          (((if i.val * K.P + l < 2 ^ (P.seg j).rowsLog ∧ c.val < (P.seg j).cols then
              g j (i.val * K.P + l) c.val
            else 0 : ℤ)) : E)) K.P).symm

theorem ldPartCf_row (hK : 0 < K.P) (j r : ℕ) (hr : r < 2 ^ (P.seg j).rowsLog) :
    r / K.P < P.rp K j ∧ r % K.P < K.P := by
  refine ⟨?_, Nat.mod_lt _ hK⟩
  unfold LdPartD.rp
  rw [Nat.div_lt_iff_lt_mul hK]
  have h1 := Nat.div_add_mod (2 ^ (P.seg j).rowsLog + K.P - 1) K.P
  have h2 := Nat.mod_lt (2 ^ (P.seg j).rowsLog + K.P - 1) hK
  rw [Nat.mul_comm] at h1
  omega

theorem ldPartCf_cast (w : LdPartW E) :
    (fun s => P.cellsW K w s) = LdPartD.castM (E := E) (P.unpackW K w) := by
  funext j r c
  unfold LdPartD.cellsW LdPartD.castM LdPartD.unpackW
  split_ifs <;> simp

theorem ldPartCf_small (hD : 0 < P.D) (w : LdPartW E)
    (h : ∀ j < P.n, Packed K.P (2 * P.D) K.rdx (P.layW K w j)) :
    P.Below (2 * P.D) (P.unpackW K w) := by
  intro q hq
  unfold LdPartD.unpackW
  split_ifs
  · exact ldPartCf_cells_lt K.P (2 * P.D) K.rdx _ (h q.1 hq.1) _ _
  · simpa using hD
  · simpa using hD

theorem ldPartCf_hon (p : ℕ) [CharP E p] (hK : 0 < K.P) (hU : Uniq (2 * P.D) K.rdx K.P p)
    (w : LdPartW E) (g : LdPartGh) (b : ℤ) (hb : b ≤ 2 * P.D) (j : ℕ) (hW : (P.seg j).cols ≤ K.Cw)
    (hpk : PackBy b K.rdx (P.layX K g j) (P.layW K w j)) (r c : ℕ)
    (hr : r < 2 ^ (P.seg j).rowsLog) (hc : c < (P.seg j).cols) :
    P.cellsW K w j r c = ((g j r c : ℤ) : E) := by
  have e := rngPk_cells E p (Fin (P.rp K j)) (Fin K.Cw) K.P (2 * P.D) b K.rdx (P.layX K g j)
    (P.layW K w j) hU hb hpk
  have hr' : r / K.P * K.P + r % K.P = r := Nat.div_add_mod' r K.P
  unfold LdPartD.cellsW
  rw [dif_pos ⟨ldPartCf_row P K hK j r hr, lt_of_lt_of_le hc hW⟩, if_pos ⟨hr, hc⟩, e]
  show (((if r / K.P * K.P + r % K.P < 2 ^ (P.seg j).rowsLog ∧ c < (P.seg j).cols then
        g j (r / K.P * K.P + r % K.P) c
      else 0 : ℤ)) : E) = _
  rw [hr', if_pos ⟨hr, hc⟩]

end

theorem ldPartCf_yes : Spec.ldPartCf_yes := by
  intro F E _ _ _ _ Cf P K Bt p hP hB i x c hc
  obtain ⟨h1, h2⟩ := hP.admit i x c hc
  exact ⟨hP.formY i x c hc,
    h1,
    fun j hj => ldPartCf_pack P K Bt x _ _ P.B (lt_of_lt_of_le one_pos hP.one_le) h1 j hj,
    fun j hj => hB j hj x _ _ (h2 j hj),
    h2⟩

theorem ldPartCf_no : Spec.ldPartCf_no := by
  intro F E _ _ _ _ Cf P K p hP _ i x t h
  obtain ⟨h1, h2, h3⟩ := h
  have hD : 0 < P.D := lt_of_lt_of_le one_pos (hP.one_le.trans hP.le_D)
  exact hP.force i x _ h1 (ldPartCf_small P K hD t.1 h2) (ldPartCf_cast P K t.1 ▸ h3)

theorem ldPartCf_sub : Spec.ldPartCf_sub := by
  intro F E _ _ _ _ Cf P K Bt p _ hP hWd hK hU i x t h
  obtain ⟨h1, _, h3, _, h5⟩ := h
  have hBD : P.B ≤ 2 * P.D := by
    have := hP.le_D
    have := hP.one_le
    omega
  refine ⟨h1,
    fun j hj => ⟨P.layX K t.2 j, fun r c => lt_of_lt_of_le ((h3 j hj).1 r c) hBD, (h3 j hj).2⟩,
    fun s hs => ?_⟩
  refine ldPartCf_holds (P.seg s) P.fmt x _ _ _ (hP.wf s hs) (fun q hq => ?_) (h5 s hs)
  have hq' := (hP.reads s hs q hq).2
  exact (ldPartCf_hon P K p hK hU t.1 t.2 P.B hBD q.1 (hWd q.1 hq'.1) (h3 q.1 hq'.1)
    q.2.1 q.2.2 hq'.2.1 hq'.2.2).symm

theorem ldPartCf_model : Spec.ldPartCf_model := by
  intro F E _ _ _ _ Cf P K Bt p _ hP hWd hB hK hU hM hT
  exact ⟨fun i x t h => ldPartCf_sub F E Cf P K Bt p hP hWd hK hU i x t h,
    fun i x t h =>
      ldPartCf_yes F E Cf P K Bt p hP hB i x _
        (hT i x _ (ldPartCf_no F E Cf P K p hP hK i x t
            (ldPartCf_sub F E Cf P K Bt p hP hWd hK hU i x t h))),
    hM.held, hM.reads⟩

theorem ldPartCf_langs : Spec.ldPartCf_langs := by
  intro F E _ _ _ _ Cf P K Bt p _ hP hWd hB hK hU hT i x
  have up : (∃ c, Cf.Rno i x c) → ∃ t, P.RyesB K Bt i x t := fun ⟨c, hc⟩ =>
    ⟨_, ldPartCf_yes F E Cf P K Bt p hP hB i x _ (hT i x c hc)⟩
  have mid : (∃ t, P.RyesB K Bt i x t) → ∃ t, P.RnoB K i x t := fun ⟨t, ht⟩ =>
    ⟨t, ldPartCf_sub F E Cf P K Bt p hP hWd hK hU i x t ht⟩
  have dn : (∃ t, P.RnoB K i x t) → ∃ c, Cf.Rno i x c := fun ⟨t, ht⟩ =>
    ⟨_, ldPartCf_no F E Cf P K p hP hK i x t ht⟩
  exact ⟨⟨dn, fun h => mid (up h)⟩, ⟨fun h => dn (mid h), up⟩⟩

end Cb
