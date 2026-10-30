-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/InnerSum.lean: the sum over the cube of the summand of the batched sumcheck of a
layers' sub-proof, at the value of Cb/Pv/Lay/At/Inner.lean.

Main names:
  `vecA_eq`, `vecB_eq`: the long vector of each side is the sum of the panels' blocks.
  `pan_share`: the inner product of the two vectors on a panel's block is the panel's share, under
  the drawn element for a late panel.
  `inn_hc`: the sum of the summand over the cube is the matrix products' side of the lookup's join
  (accS in Cb/Pv/Lay/At/Line.lean) plus the drawn element times the kept part of the sumcheck of the
  terms.
Limits: inn_hc asks that an expert has no more hidden units than a layer. That the programs' vectors
and factors are these is not said here. Nothing is said on an honest prover, on completeness or on
zero knowledge.


-/
import Cb.Pv.Lay.At.Inner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Cb Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Pan Rd rdTrue pans offP lamS Sig0 Sig1 wc call hhU zpos Hh1t fSh)
open Cb.Pv.Lay.End.Sig (off_inside pans_nodup sum_om sig0_acc)

noncomputable section

/-- A constant factor moves into a block. -/
theorem blk_smul {E : Type} [Field E] (g n : ℕ) (c : E) (v : ℕ → E) (y : ℕ) :
    c * blk g n v y = blk g n (fun t => c * v t) y := by
  unfold blk
  by_cases h : y / 2 ^ g = n
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- A block reads its vector below 2^g alone. -/
theorem blk_congr {E : Type} [Field E] (g n : ℕ) {v w : ℕ → E} (h : ∀ t, v t = w t) (y : ℕ) :
    blk g n v y = blk g n w y := by
  rw [show v = w from funext h]

/-- A sum over the members of a list without repetitions. -/
theorem sum_mem {E : Type} [Field E] (l : List Pan) (hl : l.Nodup) (f : Pan → E) :
    ∑ x : {x : Pan // x ∈ l}, f x.1 = (l.map f).sum := by
  rw [← List.sum_toFinset f hl]
  exact (Finset.sum_subtype l.toFinset (fun _ => List.mem_toFinset) f).symm

variable {E : Type} [Field E] [Fintype E] [scl : Scl]

namespace InnPar0
variable (P : InnPar0 E)

/-- The pieces of a panel on the first side make up the panel's block. -/
theorem piecesA (st : P.St) (m : P.J → E) (p : Pan) (hv : isVirt p = true) (y : ℕ) :
    ∑ e ∈ range (if p.three then p.nr P.D else 1),
        P.κA st p e * blk (if p.three then p.wcol P.D else p.wid P.D)
          ((if p.three then nP P.D p * 2 ^ wrow P.D p else nP P.D p) + e) (P.vA st m p) y =
      P.onP (P.VA st m) p y := by
  unfold onP VA
  rw [if_pos hv]
  by_cases h3 : p.three = true
  · simp only [if_pos h3]
    rw [wid_eq, ← rows_blk (wrow P.D p) (p.wcol P.D) (nP P.D p) (p.nr P.D)
      (Nat.le_pow_clog (by decide) _) (fun e ι => P.κA st p e * P.vA st m p ι) y]
    exact sum_congr rfl fun e _ => blk_smul _ _ _ _ _
  · simp only [if_neg h3]
    rw [sum_range_one, Nat.add_zero]
    exact blk_smul _ _ _ _ _

/-- The pieces of a panel on the second side make up the panel's block. -/
theorem piecesB (st : P.St) (m : P.J → E) (p : Pan) (y : ℕ) :
    ∑ c ∈ range (cntB P.D p),
        (if p.three then 1 else P.κB st p c) * blk (if p.three then p.wid P.D else p.wcol P.D)
          ((if p.three then nP P.D p else nP P.D p * 2 ^ wrow P.D p + c) + 0)
          (if p.three then P.VB st m p
            else fun ι => if ι < p.nc P.D then P.FB st m p c ι else 0) y =
      if p.weight then P.onP (P.VB st m) p y else 0 := by
  unfold cntB
  by_cases hw : p.weight = true
  · rw [if_pos hw, if_pos hw]
    by_cases h3 : p.three = true
    · simp only [if_pos h3]
      rw [sum_range_one, one_mul, Nat.add_zero]
      rfl
    · simp only [if_neg h3, Nat.add_zero]
      unfold onP
      rw [wid_eq, blk_congr (wrow P.D p + p.wcol P.D) (nP P.D p)
        (w := fun t => if t / 2 ^ p.wcol P.D < p.nr P.D then
          P.κB st p (t / 2 ^ p.wcol P.D) *
            (if t % 2 ^ p.wcol P.D < p.nc P.D then
              P.FB st m p (t / 2 ^ p.wcol P.D) (t % 2 ^ p.wcol P.D) else 0) else 0)
        (fun t => by
          unfold VB cellOf
          beta_reduce
          by_cases a : t / 2 ^ p.wcol P.D < p.nr P.D
          · by_cases b : t % 2 ^ p.wcol P.D < p.nc P.D
            · rw [if_pos ⟨a, b⟩, if_pos a, if_pos b]
            · rw [if_neg fun h => b h.2, if_pos a, if_neg b, mul_zero]
          · rw [if_neg fun h => a h.1, if_neg a]) y,
        ← rows_blk (wrow P.D p) (p.wcol P.D) (nP P.D p) (p.nr P.D)
          (Nat.le_pow_clog (by decide) _)
          (fun e ι => P.κB st p e * (if ι < p.nc P.D then P.FB st m p e ι else 0)) y]
      exact sum_congr rfl fun e _ => blk_smul _ _ _ _ _
  · rw [if_neg hw, if_neg hw, range_zero, sum_empty]

omit [Fintype E] scl in
/-- The form part of a side, read inside the cube. -/
theorem blk_whole {k y : ℕ} (hy : y < 2 ^ k) (V : ℕ → E) :
    ∑ e ∈ range 1, (1 : E) * blk k (0 + e) V y = V y := by
  rw [sum_range_one, one_mul, Nat.add_zero]
  unfold blk
  rw [if_pos (Nat.div_eq_of_lt hy), Nat.mod_eq_of_lt hy]

omit [Fintype E] scl in
/-- A sum over the panels, cut in two by a test. -/
theorem pans_cut (l : List Pan) (c : Pan → Bool) (f : Pan → E) :
    (l.map fun p => if c p then 0 else f p).sum + (l.map fun p => if c p then f p else 0).sum =
      (l.map f).sum := by
  rw [← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  by_cases h : c p = true
  · rw [if_pos h, if_pos h, zero_add]
  · rw [if_neg h, if_neg h, add_zero]

/-- The first long vector is the sum of the panels' blocks. -/
theorem vecA_eq (st : P.St) (m : P.J → E) {y : ℕ} (hy : y < 2 ^ lamS P.D) :
    P.sideA.vec st m y = ((pans P.D).map fun p => P.onP (P.VA st m) p y).sum := by
  have hS : ∀ p : {p : Pan // p ∈ pans P.D},
      (∑ c : Fin (cntA p.1), ∑ e ∈ range (P.sideA.R (Sum.inr ⟨p, c⟩)),
        P.sideA.κ (Sum.inr ⟨p, c⟩) st e * blk (P.sideA.g (Sum.inr ⟨p, c⟩))
          (P.sideA.n0 (Sum.inr ⟨p, c⟩) + e) (P.sideA.v st m (Sum.inr ⟨p, c⟩)) y) =
        if isVirt p.1 then P.onP (P.VA st m) p.1 y else 0 := by
    intro p
    show ∑ _c : Fin (cntA p.1), (∑ e ∈ range (if p.1.three then p.1.nr P.D else 1),
        P.κA st p.1 e * blk (if p.1.three then p.1.wcol P.D else p.1.wid P.D)
          ((if p.1.three then nP P.D p.1 * 2 ^ wrow P.D p.1 else nP P.D p.1) + e)
          (P.vA st m p.1) y) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    unfold cntA
    by_cases hv : isVirt p.1 = true
    · rw [if_pos hv, if_pos hv, one_smul]
      exact P.piecesA st m p.1 hv y
    · rw [if_neg hv, if_neg hv, zero_smul]
  show (∑ i : Unit ⊕ (Σ p : {p : Pan // p ∈ pans P.D}, Fin (cntA p.1)),
    ∑ e ∈ range (P.sideA.R i), P.sideA.κ i st e *
      blk (P.sideA.g i) (P.sideA.n0 i + e) (P.sideA.v st m i) y) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique,
    Finset.sum_congr rfl fun p _ => hS p,
    sum_mem (pans P.D) (pans_nodup P.D) fun p => if isVirt p then P.onP (P.VA st m) p y else 0,
    ← pans_cut (pans P.D) isVirt fun p => P.onP (P.VA st m) p y]
  exact congrArg (· + _) (blk_whole (E := E) (k := kS P.D) (by rw [kS_eq]; exact hy) _)

/-- The second long vector is the sum of the panels' blocks. -/
theorem vecB_eq (st : P.St) (m : P.J → E) {y : ℕ} (hy : y < 2 ^ lamS P.D) :
    P.sideB.vec st m y = ((pans P.D).map fun p => P.onP (P.VB st m) p y).sum := by
  have hS : ∀ p : {p : Pan // p ∈ pans P.D},
      (∑ c : Fin (cntB P.D p.1), ∑ e ∈ range (P.sideB.R (Sum.inr ⟨p, c⟩)),
        P.sideB.κ (Sum.inr ⟨p, c⟩) st e * blk (P.sideB.g (Sum.inr ⟨p, c⟩))
          (P.sideB.n0 (Sum.inr ⟨p, c⟩) + e) (P.sideB.v st m (Sum.inr ⟨p, c⟩)) y) =
        if p.1.weight then P.onP (P.VB st m) p.1 y else 0 := by
    intro p
    rw [← P.piecesB st m p.1 y, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun c _ => ?_
    exact sum_range_one _
  show (∑ i : Unit ⊕ (Σ p : {p : Pan // p ∈ pans P.D}, Fin (cntB P.D p.1)),
    ∑ e ∈ range (P.sideB.R i), P.sideB.κ i st e *
      blk (P.sideB.g i) (P.sideB.n0 i + e) (P.sideB.v st m i) y) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique,
    Finset.sum_congr rfl fun p _ => hS p,
    sum_mem (pans P.D) (pans_nodup P.D) fun p => if p.weight then P.onP (P.VB st m) p y else 0,
    ← pans_cut (pans P.D) Pan.weight fun p => P.onP (P.VB st m) p y]
  exact congrArg (· + _) (blk_whole (E := E) (k := kS P.D) (by rw [kS_eq]; exact hy) _)

/-- The factor of a piece of the second side is 1 but on the panel D. -/
theorem κB_one (st : P.St) {p : Pan} (h : isVirt p = false) (ρ : ℕ) : P.κB st p ρ = 1 := by
  cases p <;> first | rfl | exact absurd h (by decide)

/-- One entry of a panel: the product of the two long vectors is the product of the two factors with
all weights. -/
theorem entry_mul (st : P.St) (m : P.J → E) (p : Pan) {ρ ι : ℕ} (hρ : ρ < p.nr P.D)
    (hι : ι < p.nc P.D) :
    P.VA st m p (ρ * 2 ^ p.wcol P.D + ι) * (P.κB st p ρ * P.FB st m p ρ ι) =
      P.FA st m p ρ ι * P.FB st m p ρ ι := by
  have hc : ι < 2 ^ p.wcol P.D := Nat.lt_of_lt_of_le hι (Nat.le_pow_clog (by decide) _)
  by_cases hv : isVirt p = true
  · cases p with
    | D =>
      show (1 * Hh1t P.D (P.rd m) (zpos P.D st.z) (ρ * 2 ^ Pan.D.wcol P.D + ι)) *
        (wc P.D st.z (call .D) * Pan.D.wt P.D st.z ρ * P.FB st m .D ρ ι) =
        (1 * wc P.D st.z (call .D) * Pan.D.wt P.D st.z ρ *
          (if ι < fSh P.D ρ then hhU P.D (P.rd m) ρ ι (zpos P.D st.z) else 0)) * P.FB st m .D ρ ι
      have e : Hh1t P.D (P.rd m) (zpos P.D st.z) (ρ * 2 ^ Pan.D.wcol P.D + ι) =
          hhU P.D (P.rd m) ρ ι (zpos P.D st.z) := by
        show hhU P.D (P.rd m) ((ρ * 2 ^ Pan.D.wcol P.D + ι) / 2 ^ Pan.D.wcol P.D)
          ((ρ * 2 ^ Pan.D.wcol P.D + ι) % 2 ^ Pan.D.wcol P.D) (zpos P.D st.z) = _
        rw [div_at _ ρ hc, mod_at _ ρ hc]
      rw [e]
      by_cases hf : ι < fSh P.D ρ
      · rw [if_pos hf]
        ring
      · have hB : P.FB st m .D ρ ι = 0 := if_neg hf
        rw [hB]
        ring
    | Dr l' =>
      show (if (ρ * 2 ^ (Pan.Dr l').wcol P.D + ι) / 2 ^ (Pan.Dr l').wcol P.D < (Pan.Dr l').nr P.D
          then P.κA st (.Dr l') ((ρ * 2 ^ (Pan.Dr l').wcol P.D + ι) / 2 ^ (Pan.Dr l').wcol P.D) *
            P.vA st m (.Dr l') ((ρ * 2 ^ (Pan.Dr l').wcol P.D + ι) % 2 ^ (Pan.Dr l').wcol P.D)
          else 0) * (1 * P.FB st m (.Dr l') ρ ι) = _
      rw [div_at _ ρ hc, mod_at _ ρ hc, if_pos hρ]
      show (st.β * wc P.D st.o3.st (call .D) * (Pan.Dr l').wt P.D st.o3.st ρ * P.selV st l' ρ *
          hhU P.D (P.rd m) (2 * l' + 1) (P.D.fe + ι) (P.rt st)) * (1 * P.FB st m (.Dr l') ρ ι) =
        (st.β * wc P.D st.o3.st (call .D) * (Pan.Dr l').wt P.D st.o3.st ρ *
          (P.selV st l' ρ * hhU P.D (P.rd m) (2 * l' + 1) (P.D.fe + ι) (P.rt st))) *
            P.FB st m (.Dr l') ρ ι
      ring
    | _ => exact absurd hv Bool.false_ne_true
  · have hv' : isVirt p = false := by simpa using hv
    unfold VA cellOf
    rw [if_neg hv, div_at _ ρ hc, mod_at _ ρ hc, if_pos ⟨hρ, hι⟩, P.κB_one st hv', one_mul]

/-- The share of a panel at its own record and point. -/
def shareP (st : P.St) (m : P.J → E) (p : Pan) : E :=
  p.share P.D (P.rP st m p) P.tb P.L0 (P.rw m) (P.zP st p) (P.rt st)

/-- The inner product of the two long vectors on a panel's block. -/
theorem pan_share (st : P.St) (m : P.J → E) (p : Pan) :
    ∑ t ∈ range (2 ^ p.wid P.D), P.VA st m p t * P.VB st m p t =
      p.om st.β * P.shareP st m p := by
  unfold VB
  rw [local_sum, sum_congr rfl fun ρ hρ => sum_congr rfl fun ι hι =>
    P.entry_mul st m p (mem_range.mp hρ) (mem_range.mp hι)]
  unfold shareP Pan.share FA FB
  simp only [mul_sum]
  exact sum_congr rfl fun ρ _ => sum_congr rfl fun ι _ => by ring

/-- The sum of the summand over the cube. -/
theorem inn_hc (hfe : P.D.fe ≤ P.D.f) (st : P.St) (m : P.J → E) :
    ∑ b : Fin (kS P.D) → Bool, P.inn.Kp.val st m (Alg.corner b) =
      accS P.D (P.rd m) (P.rw m) st.z + st.β * keptAt P.Y3 st.o3 m := by
  have h1 := cube_eq P.par P.sideA P.sideB rfl rfl st m
  have hk : 2 ^ kS P.D = 2 ^ lamS P.D := by rw [kS_eq]
  have h2 : ∑ y ∈ range (2 ^ kS P.D), P.sideA.vec st m y * P.sideB.vec st m y =
      ((pans P.D).map fun p => p.om st.β * P.shareP st m p).sum := by
    rw [hk, sum_congr rfl fun y hy => by
      rw [P.vecA_eq st m (mem_range.mp hy), P.vecB_eq st m (mem_range.mp hy)]]
    unfold onP
    rw [pans_sum]
    exact congrArg List.sum (List.map_congr_left fun p _ => P.pan_share st m p)
  have h3 : (((pans P.D).filter fun p => !p.late).map (P.shareP st m)).sum =
      accS P.D (P.rd m) (P.rw m) st.z := by
    unfold accS
    rw [← sig0_acc P.D (P.rd m) P.tb P.L0 (P.rw m) st.z (P.rt st) (P.rt st)
      (fun l j => hhU P.D (P.rd m) l j (zpos P.D st.z)) (fun _ _ => 0) hfe fun _ _ _ _ => rfl]
    unfold Sig0
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hl : p.late = false := by simpa using (List.mem_filter.mp hp).2
    unfold shareP rP zP
    rw [hl]
    rfl
  have h4 : (((pans P.D).filter fun p => p.late).map (P.shareP st m)).sum =
      keptAt P.Y3 st.o3 m := by
    rw [P.T.tm_kept st.o3 m]
    unfold Sig1
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hl : p.late = true := (List.mem_filter.mp hp).2
    unfold shareP rP zP
    rw [hl]
    rfl
  refine h1.trans (h2.trans ?_)
  rw [sum_om, h3, h4]

end InnPar0

end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.InnPar0.inn_hc
