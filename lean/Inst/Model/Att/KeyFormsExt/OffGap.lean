-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/OffGap.lean: region M of an attention segment (the blocks off the
diagonal): the extension of the extended gap.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean). An entry of M is (g | P | s | i' | j'); Y
stands for (g | P). The entries with the last s are empty.
Main names:
  `nestM`: the extension over the entries of M, part by part.
  `gpM_at`: the extended gap `gp D t .M b` (Inst/Model/Att/Trace.lean) at an entry. `scM`: the
    scores' term at (Y, s).
  `gpM_ext`: the extension of the gap at u^M is C ones(z_s), plus the maxima's term, minus the
    scores' term; both terms are summed over s < 2 hP - 1 alone.
Limits: no hypothesis on sizes. Coordinate 0 of a point belongs to the most significant bit, as in
Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.DiagLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls)

/-- the extension over the entries of M, part by part -/
theorem nestM (v u : ℕ → E) :
    Blocks.ext D.lM v u =
      Blocks.ext (D.lg + D.lP) (fun Y =>
          Blocks.ext (D.lP + 1) (fun s => Blocks.ext D.lB (fun i' => Blocks.ext D.lB (fun j' =>
          v (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j'))
        (AttSeg.sh u (D.lg + D.lP + (D.lP + 1) + D.lB))) (AttSeg.sh u (D.lg + D.lP + (D.lP + 1))))
            (AttSeg.sh u (D.lg + D.lP))) u := by
  unfold AttSeg.Dim.lM
  rw [ext_split' (D.lg + D.lP + (D.lP + 1) + D.lB) D.lB, ext_split' (D.lg + D.lP + (D.lP + 1)) D.lB,
    ext_split' (D.lg + D.lP) (D.lP + 1)]

variable (p : AttSeg.Pub E) (t : AttSeg.Raw → E)

/-- the gap at the entry (Y | s | i' | j') -/
theorem gpM_at [scl : Scl] (b Y : ℕ) {s i' j' : ℕ} (hs : s < 2 ^ (D.lP + 1)) (hi : i' < 2 ^ D.lB)
    (hj : j' < 2 ^ D.lB) :
    AttSeg.gp D t .M b (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') =
      if s = 2 ^ (D.lP + 1) - 1 then ((D.cutC : ℤ) : E)
      else AttSeg.mxV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i') -
        AttSeg.scV D t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i')
            (D.B * D.colBlk (Y % D.hP) s + j') := by
  have e1 : (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') / D.B =
      (Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i' :=
    div_pow D.lB _ hj
  have e2 : (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') % D.B = j' :=
      mod_pow D.lB _ hj
  have e3 : ((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') / D.B = Y * 2 ^ (D.lP + 1) + s :=
      div_pow D.lB _ hi
  have e4 : ((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') % D.B = i' := mod_pow D.lB _ hi
  have e5 : (Y * 2 ^ (D.lP + 1) + s) / D.nBlk = Y := by rw [nBlk_pow]; exact div_pow _ _ hs
  have e6 : (Y * 2 ^ (D.lP + 1) + s) % D.nBlk = s := by rw [nBlk_pow]; exact mod_pow _ _ hs
  have hS : D.mS (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') = s := by
    unfold AttSeg.Dim.mS
    rw [e1, e3, e6]
  have hP : D.mP (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') = Y % D.hP := by
    unfold AttSeg.Dim.mP
    rw [e1, e3, e5]
  have hG : D.mG (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') = Y / D.hP := by
    unfold AttSeg.Dim.mG
    rw [e1, e3, e5]
  have hI : D.iM (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') = D.B *
      D.rowBlk (Y % D.hP) s + i' := by
    unfold AttSeg.Dim.iM AttSeg.Dim.mI
    rw [hP, hS, e1, e4]
  have hJ : D.jM (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') = D.B *
      D.colBlk (Y % D.hP) s + j' := by
    unfold AttSeg.Dim.jM AttSeg.Dim.mJ
    rw [hP, hS, e2]
  have hE : D.EmptyM (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j') ↔ s =
      2 ^ (D.lP + 1) - 1 := by
    unfold AttSeg.Dim.EmptyM
    rw [hS, nBlk_pow]
  show (if D.EmptyM _ then ((D.cutC : ℤ) : E) else AttSeg.mxV t b (D.mG _) (D.iM _) -
      AttSeg.scV D t b (D.mG _) (D.iM _) (D.jM _)) = _
  by_cases h : s = 2 ^ (D.lP + 1) - 1
  · rw [if_pos (hE.2 h), if_pos h]
  · rw [if_neg (fun hm => h (hE.1 hm)), if_neg h, hG, hI, hJ]

/-- the score term at (Y, s) -/
def scM (b Y s : ℕ) : E :=
  ∑ n ∈ range D.ch,
    AttSeg.conB D (AttSeg.zi' D C p.z)
        (fun i' => AttSeg.qryV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i') n) *
    AttSeg.conB D (AttSeg.zj' D C p.z)
        (fun j' => AttSeg.keyV t (D.lamOf b) (Y / D.hP) (D.B * D.colBlk (Y % D.hP) s + j') n)

/-- The extension of the extended gap on region M. -/
theorem gpM_ext [scl : Scl] (b : ℕ) :
    Blocks.ext D.lM (AttSeg.gp D t .M b) (AttSeg.uM D C p.z) =
      ((D.cutC : ℤ) : E) * AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) +
      Blocks.ext (D.lg + D.lP) (fun Y => ∑ s ∈ range (2 ^ (D.lP + 1) - 1),
          Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) s *
        Blocks.ext D.lB (fun i' => AttSeg.mxV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i'))
            (AttSeg.zi' D C p.z)) (AttSeg.uM D C p.z) -
      Blocks.ext (D.lg + D.lP) (fun Y => ∑ s ∈ range (2 ^ (D.lP + 1) - 1),
          Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) s *
        scM D C p t b Y s) (AttSeg.uM D C p.z) := by
  rw [nestM]
  have inner : ∀ Y, Blocks.ext (D.lP + 1)
      (fun s => Blocks.ext D.lB (fun i' => Blocks.ext D.lB (fun j' =>
          AttSeg.gp D t .M b (((Y * 2 ^ (D.lP + 1) + s) * 2 ^ D.lB + i') * 2 ^ D.lB + j'))
        (AttSeg.sh (AttSeg.uM D C p.z) (D.lg + D.lP + (D.lP + 1) + D.lB)))
            (AttSeg.sh (AttSeg.uM D C p.z) (D.lg + D.lP + (D.lP + 1))))
        (AttSeg.sh (AttSeg.uM D C p.z) (D.lg + D.lP)) =
      ((D.cutC : ℤ) : E) * AttSeg.ones (D.lP + 1) (AttSeg.zs D C p.z) +
        (∑ s ∈ range (2 ^ (D.lP + 1) - 1), Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) s *
          Blocks.ext D.lB (fun i' => AttSeg.mxV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i'))
              (AttSeg.zi' D C p.z) -
        ∑ s ∈ range (2 ^ (D.lP + 1) - 1), Blocks.eqN (D.lP + 1) 0 (AttSeg.zs D C p.z) s *
            scM D C p t b Y s) := by
    intro Y
    show Blocks.ext (D.lP + 1) _ (AttSeg.zs D C p.z) = _
    rw [Blocks.ext_congr (w := fun s => if s = 2 ^ (D.lP + 1) - 1 then ((D.cutC : ℤ) : E) else
        Blocks.ext D.lB (fun i' => AttSeg.mxV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i'))
            (AttSeg.zi' D C p.z) - scM D C p t b Y s)
      (fun s hs => by
        beta_reduce
        by_cases h : s = 2 ^ (D.lP + 1) - 1
        · rw [if_pos h, Blocks.ext_congr (w := fun _ => ((D.cutC : ℤ) : E)) (fun i' hi => by
            rw [Blocks.ext_congr (w := fun _ => ((D.cutC : ℤ) : E)) (fun j' hj => by
              rw [gpM_at D t b Y hs hi hj, if_pos h]),
              Blocks.ext_const]), Blocks.ext_const]
        · rw [if_neg h]
          show Blocks.ext D.lB (fun i' => Blocks.ext D.lB _ (AttSeg.zj' D C p.z))
              (AttSeg.zi' D C p.z) = _
          rw [Blocks.ext_congr (w := fun i' =>
              AttSeg.mxV t b (Y / D.hP) (D.B * D.rowBlk (Y % D.hP) s + i') -
              Blocks.ext D.lB (fun j' => AttSeg.scV D t b (Y / D.hP)
                  (D.B * D.rowBlk (Y % D.hP) s + i') (D.B * D.colBlk (Y % D.hP) s + j'))
                (AttSeg.zj' D C p.z))
            (fun i' hi => by
              rw [Blocks.ext_congr (fun j' hj => by rw [gpM_at D t b Y hs hi hj, if_neg h]),
                  Blocks.ext_sub, Blocks.ext_const]),
            Blocks.ext_sub]
          congr 1
          unfold AttSeg.scV scM
          exact ext_ext_sum D.lB D.lB D.ch _ _ _ _), ext_last]
    rw [← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [inner]
  rw [Blocks.ext_add, Blocks.ext_const, Blocks.ext_sub]
  ring

end Inst.Model.AttSeg.KeyFormsExt
