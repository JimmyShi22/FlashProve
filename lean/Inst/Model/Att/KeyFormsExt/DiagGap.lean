-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/DiagGap.lean: region D of an attention segment (the diagonal blocks): the
extension of the extended gap.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean). An entry of D is (g | I | i' | j'); Y stands
for (g | I).
Main names:
  `nestD`: the extension over the entries of D, part by part. `sum_tail`: a sum over (Y | n) as a
    double sum.
  `tailD_i`, `tailD_j`: the tails of u^D are z_i' and z_j', which Inst/Model/Att/Points.lean cuts
    from u^M.
  `gpD_at`: the extended gap `gp D t .D b` (Inst/Model/Att/Trace.lean) at an entry. `scD`: the
    scores' term at Y.
  `gpD_ext`: the extension of the gap at u^D is the maxima's term, minus the scores' term, plus Om
    (1 - LE(z_j', z_i')).
Limits: `tailD_i`, `tailD_j`, `gpD_ext` stand under D.lM ≤ C.Dk ≤ C.a 0. Coordinate 0 of a point
belongs to the most significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.LessEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls)

theorem nBlk_pow : D.nBlk = 2 ^ (D.lP + 1) := by
  unfold AttSeg.Dim.nBlk AttSeg.Dim.hP
  rw [pow_succ, Nat.mul_comm]

/-- a sum over (Y | n) -/
theorem sum_tail (A l : ℕ) (F : ℕ → ℕ → E) :
    ∑ X ∈ range (2 ^ (A + l)), F (X / 2 ^ l) (X % 2 ^ l) = ∑ Y ∈ range (2 ^ A), ∑ n ∈ range (2 ^ l),
        F Y n := by
  rw [pow_add, Alg.sum_range_mul_add]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.1 hn
  rw [div_pow l Y hn', mod_pow l Y hn']

/-- the extension over the entries of D, part by part -/
theorem nestD (v u : ℕ → E) :
    Blocks.ext D.lD v u =
      Blocks.ext (D.lg + (D.lP + 1))
          (fun Y => Blocks.ext D.lB (fun i' =>
          Blocks.ext D.lB (fun j' => v ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j'))
        (AttSeg.sh u (D.lg + (D.lP + 1) + D.lB))) (AttSeg.sh u (D.lg + (D.lP + 1)))) u := by
  unfold AttSeg.Dim.lD
  rw [ext_split' (D.lg + (D.lP + 1) + D.lB) D.lB, ext_split' (D.lg + (D.lP + 1)) D.lB]

variable (p : AttSeg.Pub E) (t : AttSeg.Raw → E)

omit [Field E] in
/-- the tails of u^D are z_i', z_j' -/
theorem tailD_i (hM : D.lM ≤ C.Dk) (ha : C.Dk ≤ C.a 0) (k : ℕ) :
    AttSeg.sh (AttSeg.uD D C p.z) (D.lg + (D.lP + 1)) k = AttSeg.zi' D C p.z k := by
  have hD : D.lD ≤ C.Dk := by
    have : D.lD ≤ D.lM := by unfold AttSeg.Dim.lD AttSeg.Dim.lM; omega
    omega
  have a1 := inn_tail D C p.z .d1 hD ha (D.lg + (D.lP + 1) + k)
  have a2 := inn_tail D C p.z .m1 hM ha (D.lg + D.lP + (D.lP + 1) + k)
  show AttSeg.inn D C p.z .d1 (D.lg + (D.lP + 1) + k) =
      AttSeg.inn D C p.z .m1 (D.lg + D.lP + (D.lP + 1) + k)
  rw [a1, a2]
  show p.z (C.Dk - D.lD + _) = p.z (C.Dk - D.lM + _)
  congr 1
  unfold AttSeg.Dim.lD AttSeg.Dim.lM at *
  omega

omit [Field E] in
theorem tailD_j (hM : D.lM ≤ C.Dk) (ha : C.Dk ≤ C.a 0) (k : ℕ) :
    AttSeg.sh (AttSeg.uD D C p.z) (D.lg + (D.lP + 1) + D.lB) k = AttSeg.zj' D C p.z k := by
  have hD : D.lD ≤ C.Dk := by
    have : D.lD ≤ D.lM := by unfold AttSeg.Dim.lD AttSeg.Dim.lM; omega
    omega
  have a1 := inn_tail D C p.z .d1 hD ha (D.lg + (D.lP + 1) + D.lB + k)
  have a2 := inn_tail D C p.z .m1 hM ha (D.lg + D.lP + (D.lP + 1) + D.lB + k)
  show AttSeg.inn D C p.z .d1 (D.lg + (D.lP + 1) + D.lB + k) =
      AttSeg.inn D C p.z .m1 (D.lg + D.lP + (D.lP + 1) + D.lB + k)
  rw [a1, a2]
  show p.z (C.Dk - D.lD + _) = p.z (C.Dk - D.lM + _)
  congr 1
  unfold AttSeg.Dim.lD AttSeg.Dim.lM at *
  omega

/-- the gap at the entry (Y | i' | j'), Y = (g | I) -/
theorem gpD_at [scl : Scl] (b Y : ℕ) {i' j' : ℕ} (hi : i' < 2 ^ D.lB) (hj : j' < 2 ^ D.lB) :
    AttSeg.gp D t .D b ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') =
      AttSeg.mxV t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i') -
        AttSeg.scV D t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i') (D.B * (Y % D.nBlk) + j') +
        ((AttSeg.Om D : ℤ) : E) * (1 - if j' ≤ i' then 1 else 0) := by
  have e1 : ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') / D.B = Y * 2 ^ D.lB + i' := div_pow D.lB _ hj
  have e2 : ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') % D.B = j' := mod_pow D.lB _ hj
  have e3 : (Y * 2 ^ D.lB + i') / D.B = Y := div_pow D.lB _ hi
  have e4 : (Y * 2 ^ D.lB + i') % D.B = i' := mod_pow D.lB _ hi
  have hG : D.dG ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') = Y / D.nBlk := by
    unfold AttSeg.Dim.dG
    rw [e1, e3]
  have hI : D.iD ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') = D.B * (Y % D.nBlk) + i' := by
    unfold AttSeg.Dim.iD AttSeg.Dim.dI AttSeg.Dim.mI
    rw [e1, e3, e4]
  have hJ : D.jD ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') = D.B * (Y % D.nBlk) + j' := by
    unfold AttSeg.Dim.jD AttSeg.Dim.dI AttSeg.Dim.mJ
    rw [e1, e3, e2]
  have hMk : D.MaskedD ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j') ↔ i' < j' := by
    unfold AttSeg.Dim.MaskedD AttSeg.Dim.mI AttSeg.Dim.mJ
    rw [e1, e2, e4]
  show AttSeg.mxV t b (D.dG _) (D.iD _) - AttSeg.scV D t b (D.dG _) (D.iD _) (D.jD _) +
    (if D.MaskedD _ then ((AttSeg.Om D : ℤ) : E) else 0) = _
  rw [hG, hI, hJ]
  by_cases h : j' ≤ i'
  · rw [if_neg (fun hm => absurd (hMk.1 hm) (by omega)), if_pos h]
    ring
  · rw [if_pos (hMk.2 (by omega)), if_neg h]
    ring

/-- the score term at (Y): ∑_n (∑_i' eq(z_i', i') qry) (∑_j' eq(z_j', j') key) -/
def scD (b Y : ℕ) : E :=
  ∑ n ∈ range D.ch,
    AttSeg.conB D (AttSeg.zi' D C p.z)
        (fun i' => AttSeg.qryV t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i') n) *
    AttSeg.conB D (AttSeg.zj' D C p.z)
        (fun j' => AttSeg.keyV t (D.lamOf b) (Y / D.nBlk) (D.B * (Y % D.nBlk) + j') n)

/-- The extension of the extended gap on region D. -/
theorem gpD_ext [scl : Scl] (hM : D.lM ≤ C.Dk) (ha : C.Dk ≤ C.a 0) (b : ℕ) :
    Blocks.ext D.lD (AttSeg.gp D t .D b) (AttSeg.uD D C p.z) =
      Blocks.ext (D.lg + (D.lP + 1))
          (fun Y => Blocks.ext D.lB (fun i' =>
          AttSeg.mxV t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i'))
        (AttSeg.zi' D C p.z)) (AttSeg.uD D C p.z) -
      Blocks.ext (D.lg + (D.lP + 1)) (scD D C p t b) (AttSeg.uD D C p.z) +
      ((AttSeg.Om D : ℤ) : E) * (1 - AttSeg.LE D.lB (AttSeg.zj' D C p.z) (AttSeg.zi' D C p.z)) := by
  rw [nestD]
  have inner : ∀ Y, Blocks.ext D.lB
      (fun i' => Blocks.ext D.lB (fun j' =>
      AttSeg.gp D t .D b ((Y * 2 ^ D.lB + i') * 2 ^ D.lB + j'))
        (AttSeg.sh (AttSeg.uD D C p.z) (D.lg + (D.lP + 1) + D.lB)))
            (AttSeg.sh (AttSeg.uD D C p.z) (D.lg + (D.lP + 1))) =
      Blocks.ext D.lB (fun i' => AttSeg.mxV t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i'))
          (AttSeg.zi' D C p.z) - scD D C p t b Y +
        ((AttSeg.Om D : ℤ) : E) * (1 - AttSeg.LE D.lB (AttSeg.zj' D C p.z) (AttSeg.zi' D C p.z)) :=
            by
    intro Y
    rw [Blocks.ext_congr_point (fun k _ => tailD_i D C p hM ha k)]
    rw [Blocks.ext_congr (w := fun i' => AttSeg.mxV t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i') -
        Blocks.ext D.lB (fun j' => AttSeg.scV D t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i')
            (D.B * (Y % D.nBlk) + j')) (AttSeg.zj' D C p.z) +
        ((AttSeg.Om D : ℤ) : E) * (1 -
            Blocks.ext D.lB (fun j' => if j' ≤ i' then 1 else 0) (AttSeg.zj' D C p.z)))
      (fun i' hi => by
        rw [Blocks.ext_congr_point (fun k _ => tailD_j D C p hM ha k),
          Blocks.ext_congr (fun j' hj => gpD_at D t b Y hi hj),
          Blocks.ext_add, Blocks.ext_sub, Blocks.ext_const, Blocks.ext_smul, Blocks.ext_sub,
              Blocks.ext_const])]
    rw [Blocks.ext_add, Blocks.ext_sub, Blocks.ext_smul, Blocks.ext_sub, Blocks.ext_const,
      ext_swap D.lB D.lB (fun i' j' => if j' ≤ i' then (1 : E) else 0), ext_le]
    have hs : Blocks.ext D.lB (fun i' => Blocks.ext D.lB (fun j' =>
        AttSeg.scV D t b (Y / D.nBlk) (D.B * (Y % D.nBlk) + i') (D.B * (Y % D.nBlk) + j'))
            (AttSeg.zj' D C p.z)) (AttSeg.zi' D C p.z) =
        scD D C p t b Y := by
      unfold AttSeg.scV scD
      exact ext_ext_sum D.lB D.lB D.ch _ _ _ _
    rw [hs]
  simp only [inner]
  rw [Blocks.ext_add, Blocks.ext_sub, Blocks.ext_const]

end Inst.Model.AttSeg.KeyFormsExt
