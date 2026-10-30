-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartTieNmProofs.lean: the proofs of the statements of Cb/Part/LdPartTieNm.lean (a body's
matrix of cells made of the kept packed rows and of one new layer).

The theorem that proves a statement of `Cb.Spec` has that statement's name.

Main names (tools):
  `ldPartNm_layAt`, `ldPartNm_layZero`: what is laid at a named pair (under `nm.OK`: the entry of
    Z); 0 at a pair that no cell names.
  `ldPartTieNm_cells`: under the hypotheses of its statement (unique packing; the whole is a
    packing): the cells of a part are the cells of the whole, for two packing factors that are equal
    as numbers, lanes compared by their values.
-/
import Cb.Part.LdPartTieNm

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

theorem ldPartNm_layAt {p : RngPar} (nm : LdPartNm p) (Z : ℕ → ℕ → ℕ → ℤ) (h : nm.OK) {s r c : ℕ}
    (hr : r < nm.R s) (hc : c < nm.C s) :
    nm.lay Z (nm.rowAt s r) (nm.colAt s c) = Z s r c := by
  have h1 := (ldPartCells_lay p nm Z h).1 s r c hr hc
  unfold LdPartNm.mats at h1
  rwa [if_pos ⟨hr, hc⟩] at h1

theorem ldPartNm_layZero {p : RngPar} (nm : LdPartNm p) (Z : ℕ → ℕ → ℕ → ℤ) {ρ : p.Row} {κ : p.C}
    (h : ¬ ∃ x : ℕ × ℕ × ℕ,
      x.2.1 < nm.R x.1 ∧ x.2.2 < nm.C x.1 ∧ nm.rowAt x.1 x.2.1 = ρ ∧ nm.colAt x.1 x.2.2 = κ) :
    nm.lay Z ρ κ = 0 := by
  unfold LdPartNm.lay
  exact dif_neg h

theorem ldPartTieNm_cells {E : Type} [CommRing E] (pp : ℕ) [CharP E pp] {Rp Rp' C C' : Type}
    [Fintype Rp] [Fintype Rp'] {P₀ P₁ : ℕ} (h : P₀ = P₁) (b ϱ : ℤ) (ι : Rp' → Rp) (κ : C' → C)
    (mpk : Rp → C → E) (hU : Uniq b ϱ P₁ pp) (hP : Packed P₁ b ϱ mpk) (i : Rp') (c : C')
    (l₀ : Fin P₀) (l₁ : Fin P₁) (hl : (l₀ : ℕ) = l₁) :
    cells P₀ b ϱ (resM ι κ mpk) (i, l₀) c = cells P₁ b ϱ mpk (ι i, l₁) (κ c) := by
  subst h
  obtain rfl : l₀ = l₁ := Fin.ext hl
  rw [ldPartRes_cells E pp Rp Rp' C C' P₀ b ϱ ι κ mpk hU hP]
  rfl

theorem ldPartTieNm_layPart : Spec.ldPartTieNm_layPart := by
  intro p₀ p₁ nm₀ nm₁ ι κ Z h0 h1 hp i c l₀ l₁ hl
  by_cases hx : ∃ x : ℕ × ℕ × ℕ,
    x.2.1 < nm₀.R x.1 ∧ x.2.2 < nm₀.C x.1 ∧ nm₀.rowAt x.1 x.2.1 = (i, l₀) ∧ nm₀.colAt x.1 x.2.2 = c
  · obtain ⟨⟨s, r, c'⟩, hr, hc, er, ec⟩ := hx
    have hr' : r < nm₀.R s := hr
    have hc' : c' < nm₀.C s := hc
    have er' : nm₀.rowAt s r = (i, l₀) := er
    have ec' : nm₀.colAt s c' = c := ec
    obtain ⟨hr1, e1, e2⟩ := hp.row s r hr'
    obtain ⟨eC, ecol⟩ := hp.col s (lt_of_le_of_lt (Nat.zero_le _) hr')
    have er1 : nm₁.rowAt s r = (ι i, l₁) :=
      Prod.ext (by rw [e1, er']) (Fin.ext (by rw [e2, er']; exact hl))
    have ec1 : nm₁.colAt s c' = κ c := by rw [ecol c' hc', ec']
    rw [← er1, ← ec1, ldPartNm_layAt nm₁ Z h1 hr1 (eC ▸ hc'), ← er',
      ← ec', ldPartNm_layAt nm₀ Z h0 hr' hc']
  · rw [ldPartNm_layZero nm₀ Z hx]
    refine ldPartNm_layZero nm₁ Z ?_
    rintro ⟨⟨s, r, c'⟩, hr, hc, er, ec⟩
    have hr' : r < nm₁.R s := hr
    have hc' : c' < nm₁.C s := hc
    have er' : nm₁.rowAt s r = (ι i, l₁) := er
    have ec' : nm₁.colAt s c' = κ c := ec
    have hr0 := hp.back s r i hr' (congrArg Prod.fst er')
    obtain ⟨_, e1, e2⟩ := hp.row s r hr0
    obtain ⟨eC, ecol⟩ := hp.col s (lt_of_le_of_lt (Nat.zero_le _) hr0)
    have hc0 : c' < nm₀.C s := eC ▸ hc'
    exact hx ⟨(s, r, c'), hr0, hc0,
        Prod.ext (hp.injR (e1.symm.trans (congrArg Prod.fst er')))
          (Fin.ext (e2.symm.trans ((congrArg (fun x : p₁.Row => (x.2 : ℕ)) er').trans hl.symm))),
        hp.injC ((ecol c' hc0).symm.trans ec')⟩

theorem ldPartTieNm_layOwn : Spec.ldPartTieNm_layOwn := by
  intro p nm P' j rows cols rp Cw oR oC Z h ho i c l' l hl
  have hP' : 0 < P' := lt_of_le_of_lt (Nat.zero_le _) l'.2
  have ediv : (i.val * P' + l'.val) / P' = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP', Nat.div_eq_of_lt l'.2, Nat.zero_add]
  have emod : (i.val * P' + l'.val) % P' = l'.val := Nat.mul_add_mod_of_lt l'.2
  show _ = if i.val * P' + l'.val < rows ∧ c.val < cols then Z j (i.val * P' + l'.val) c.val else 0
  by_cases hh : i.val * P' + l'.val < rows ∧ c.val < cols
  · rw [if_pos hh]
    obtain ⟨i2, ei, e1, e2⟩ := ho.row _ hh.1
    obtain ⟨c2, ec, ecol⟩ := ho.col _ hh.2
    obtain rfl : i2 = i := Fin.ext (ei.trans ediv)
    obtain rfl : c2 = c := Fin.ext ec
    have er : nm.rowAt j (i2.val * P' + l'.val) = (oR i2, l) :=
      Prod.ext e1 (Fin.ext (e2.trans (emod.trans hl)))
    rw [← er, ← ecol]
    exact ldPartNm_layAt nm Z h (ho.R.symm ▸ hh.1) (ho.C.symm ▸ hh.2)
  · rw [if_neg hh]
    refine ldPartNm_layZero nm Z ?_
    rintro ⟨⟨s, r, c'⟩, hr, hc, er, ec⟩
    have hr' : r < nm.R s := hr
    have hc' : c' < nm.C s := hc
    have er' : nm.rowAt s r = (oR i, l) := er
    have ec' : nm.colAt s c' = oC c := ec
    obtain rfl := ho.back s r i hr' (congrArg Prod.fst er')
    have hr2 : r < rows := ho.R ▸ hr'
    have hc2 : c' < cols := ho.C ▸ hc'
    obtain ⟨i2, ei, e1, e2⟩ := ho.row r hr2
    obtain ⟨c2, ec2, ecol⟩ := ho.col c' hc2
    have hi : i2 = i := ho.injR (e1.symm.trans (congrArg Prod.fst er'))
    have hcc : c2 = c := ho.injC (ecol.symm.trans ec')
    have hl2 : r % P' = l'.val :=
      e2.symm.trans ((congrArg (fun x : p.Row => (x.2 : ℕ)) er').trans hl.symm)
    have hr3 : i.val * P' + l'.val = r := by
      rw [← hi, ei, ← hl2, Nat.mul_comm]
      exact Nat.div_add_mod r P'
    exact hh ⟨hr3 ▸ hr2, by rw [← hcc, ec2]; exact hc2⟩

theorem ldPartTieNm_packPart : Spec.ldPartTieNm_packPart := by
  intro E _ p₀ p₁ nm₀ nm₁ ι κ Z b ϱ mpk h₀ hk0 hk1 hp h
  refine ⟨fun r c => ?_, fun i c => ?_⟩
  · obtain ⟨i, l⟩ := r
    rw [← ldPartTieNm_layPart p₀ p₁ nm₀ nm₁ ι κ Z hk0 hk1 hp i c l (Fin.cast h₀ l) rfl]
    exact h.1 _ _
  · refine (h.2 (ι i) (κ c)).trans ?_
    unfold pack
    refine (Fintype.sum_equiv (finCongr h₀) _ _ fun l => ?_).symm
    show (ϱ : E) ^ (l : ℕ) * ((nm₀.lay Z (i, l) c : ℤ) : E) =
      (ϱ : E) ^ ((finCongr h₀ l : Fin p₁.P) : ℕ) * ((nm₁.lay Z (ι i, finCongr h₀ l) (κ c) : ℤ) : E)
    rw [ldPartTieNm_layPart p₀ p₁ nm₀ nm₁ ι κ Z hk0 hk1 hp i c l (finCongr h₀ l) rfl]
    rfl

theorem ldPartTieNm_packX : Spec.ldPartTieNm_packX := by
  intro E _ p₀ p₁ nm₀ nm₁ ι κ P' j rows cols rp Cw oR oC Z b ϱ mpk h₀ h' hk0 hk1 hp ho hcov hK hO
  refine ⟨fun r c => ?_, fun i c => ?_⟩
  · obtain ⟨i, l⟩ := r
    rcases hcov i c with ⟨i', c', rfl, rfl⟩ | ⟨i', c', rfl, rfl⟩
    · rw [ldPartTieNm_layPart p₀ p₁ nm₀ nm₁ ι κ Z hk0 hk1 hp i' c' (Fin.cast h₀.symm l) l rfl]
      exact hK.1 _ _
    · rw [ldPartTieNm_layOwn p₁ nm₁ P' j rows cols rp Cw oR oC Z hk1 ho i' c'
          (Fin.cast h'.symm l) l rfl]
      exact hO.1 _ _
  · rcases hcov i c with ⟨i', c', rfl, rfl⟩ | ⟨i', c', rfl, rfl⟩
    · refine (hK.2 i' c').trans ?_
      unfold pack
      refine Fintype.sum_equiv (finCongr h₀) _ _ fun l => ?_
      show (ϱ : E) ^ (l : ℕ) * ((nm₀.lay Z (i', l) c' : ℤ) : E) =
        (ϱ : E) ^ ((finCongr h₀ l : Fin p₁.P) : ℕ) *
          ((nm₁.lay Z (ι i', finCongr h₀ l) (κ c') : ℤ) : E)
      rw [ldPartTieNm_layPart p₀ p₁ nm₀ nm₁ ι κ Z hk0 hk1 hp i' c' l (finCongr h₀ l) rfl]
      rfl
    · refine (hO.2 i' c').trans ?_
      unfold pack
      refine Fintype.sum_equiv (finCongr h') _ _ fun l => ?_
      show (ϱ : E) ^ (l : ℕ) * ((layO P' j rows cols Z (i', l) c' : ℤ) : E) =
        (ϱ : E) ^ ((finCongr h' l : Fin p₁.P) : ℕ) *
          ((nm₁.lay Z (oR i', finCongr h' l) (oC c') : ℤ) : E)
      rw [ldPartTieNm_layOwn p₁ nm₁ P' j rows cols rp Cw oR oC Z hk1 ho i' c' l (finCongr h' l) rfl]
      rfl

theorem ldPartTieNm_packOwn : Spec.ldPartTieNm_packOwn := by
  intro E _ p nm P' j rows cols rp Cw oR oC Z b ϱ mpk h' hk ho hcov hO
  refine ⟨fun r c => ?_, fun i c => ?_⟩
  · obtain ⟨i, l⟩ := r
    obtain ⟨i', c', rfl, rfl⟩ := hcov i c
    rw [ldPartTieNm_layOwn p nm P' j rows cols rp Cw oR oC Z hk ho i' c' (Fin.cast h'.symm l) l rfl]
    exact hO.1 _ _
  · obtain ⟨i', c', rfl, rfl⟩ := hcov i c
    refine (hO.2 i' c').trans ?_
    unfold pack
    refine Fintype.sum_equiv (finCongr h') _ _ fun l => ?_
    show (ϱ : E) ^ (l : ℕ) * ((layO P' j rows cols Z (i', l) c' : ℤ) : E) =
      (ϱ : E) ^ ((finCongr h' l : Fin p.P) : ℕ) *
        ((nm.lay Z (oR i', finCongr h' l) (oC c') : ℤ) : E)
    rw [ldPartTieNm_layOwn p nm P' j rows cols rp Cw oR oC Z hk ho i' c' l (finCongr h' l) rfl]
    rfl

theorem ldPartTieNm_readPart : Spec.ldPartTieNm_readPart := by
  intro E _ pp _ p₀ p₁ nm₀ nm₁ ι κ b ϱ mpk h₀ hp hU hP s r c hr
  obtain ⟨hr1, e1, e2⟩ := hp.row s r hr
  obtain ⟨eC, ecol⟩ := hp.col s (lt_of_le_of_lt (Nat.zero_le _) hr)
  unfold LdPartNm.mats
  by_cases hc : c < nm₀.C s
  · rw [if_pos ⟨hr1, eC ▸ hc⟩, if_pos ⟨hr, hc⟩, ecol c hc]
    have er : nm₁.rowAt s r = (ι (nm₀.rowAt s r).1, (nm₁.rowAt s r).2) := Prod.ext e1 rfl
    rw [er]
    exact (ldPartTieNm_cells pp h₀ b ϱ ι κ mpk hU hP (nm₀.rowAt s r).1 (nm₀.colAt s c)
      (nm₀.rowAt s r).2 (nm₁.rowAt s r).2 e2.symm).symm
  · rw [if_neg fun h => hc (eC ▸ h.2), if_neg fun h => hc h.2]

theorem ldPartTieNm_readOwn : Spec.ldPartTieNm_readOwn := by
  intro E _ pp _ p nm P' j rows cols rp Cw oR oC b ϱ mpk h' ho hU hP r c i l c' hr hc hi hl hc'
  obtain ⟨i2, ei, e1, e2⟩ := ho.row r hr
  obtain ⟨c2, ec, ecol⟩ := ho.col c hc
  obtain rfl : i2 = i := Fin.ext (ei.trans hi.symm)
  obtain rfl : c2 = c' := Fin.ext (ec.trans hc'.symm)
  unfold LdPartNm.mats
  rw [if_pos ⟨ho.R.symm ▸ hr, ho.C.symm ▸ hc⟩, ecol]
  have er : nm.rowAt j r = (oR i2, (nm.rowAt j r).2) := Prod.ext e1 rfl
  rw [er]
  exact (ldPartTieNm_cells pp h' b ϱ oR oC mpk hU hP i2 c2 l
    (nm.rowAt j r).2 (hl.trans e2.symm)).symm

end Cb
