-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegModelOf.lean: the 25 segments of the model over p = 2^64 - 2^32 + 1, with the attention
segments as a parameter.

The fields
are `Gl.F`, `Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean);
`castW` is `Cm.TP.castW Gl.p` (Cm/TargetPRel.lean: an integer index matrix, read modulo p); segment
24 is the plain head with the scaled table (Cm/TargetPHead.lean) and with the identity on y
(Cm/TargetSegHeadY.lean: `segHeadY`).

Main names:
  `segOf s att k`: segment k: for even k < 24 `ffSeg` of group k / 2 (Cm/TargetSegFFAll.lean), for
    odd k `att (k / 2)`, for k = 24 `segHeadY`.
  `AttOK s att`: what is asked of the attention segments (its fields: see the record). `segsOK_of`:
    `AttOK s att` gives `SegsOK s (segOf s att)` (Cm/TargetSegAll.lean).

Limits: this file does not say that attention segments with `AttOK` exist. It says nothing on
protocols.
The top record of the partition is another
file's: Cm/TargetPart.lean: `targetPart R s`.



Terms: lean/GLOSSARY.md.
-/
import Cm.ReqModel
import Cm.TargetSegAll
import Cm.TargetSegLayoutPlain
import Cm.TargetSegIdxModel
import Cm.TargetSegLayoutPlainProofs
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegFFAllProofs
import Cm.TargetSegFFAll
import Cm.TargetSegFFMat
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass
import Cm.TargetSegFFCellKeys
import Cm.TargetSegFFCellIdnOK
import Cm.TargetSegFFMatProofsE
import Cm.TargetSegFFMatProofsA
import Cm.TargetSegFFMatProofs
import Cm.TargetSegFFMatProofsC
import Cm.TargetSegFFMatProofsB
import Cm.TargetSegFFMatProofsD
import Cm.TargetSegHeadAsm
import Cm.TargetSegHeadProofs
import Cm.TargetSegHead
import Cm.TargetSegAllProofs
import Cm.TargetSegHeadY
noncomputable section -- Lean tags what it cannot compile


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-- Segment k of the model, with the attention segments att as a parameter. -/
def segOf (s : Scales) (att : ℕ → SegSpec XI Cb.Gl.F Cb.Gl.E) (k : ℕ) :
    SegSpec XI Cb.Gl.F Cb.Gl.E :=
  if k = 24 then segHeadY s.nf else if k % 2 = 0 then ffSeg s.kap s.nf (k / 2) tokX else att (k / 2)

/-- What is asked of the attention segments. -/
structure AttOK (s : Scales) (att : ℕ → SegSpec XI Cb.Gl.F Cb.Gl.E) : Prop where
  rows   : ∀ g < nGr, (att g).rowsLog = rowsLog (2 * g + 1)
  cols   : ∀ g < nGr, (att g).cols = cols (2 * g + 1)
  wf     : ∀ g < nGr, (att g).WF fmtRef
  places : ∀ g < nGr, ∀ p ∈ (att g).places, p ∈ reads Hd.plain (2 * g + 1)
  toM    : ∀ g < nGr, ∀ (x : XI) (T : Trace) (W : Mat),
    (att g).Holds fmtRef x (TP.castW Cb.Gl.p W) (cM (toMat Hd.plain T)) ↔ AttAt s g T
  ofM    : ∀ g < nGr, ∀ (x : XI) (M : ℕ → ℕ → ℕ → ℤ) (W : Mat),
    (att g).Holds fmtRef x (TP.castW Cb.Gl.p W) (cM M) ↔ AttAt s g (ofMat Hd.plain M)

variable (s : Scales) (att : ℕ → SegSpec XI Cb.Gl.F Cb.Gl.E)

theorem seg_ff {g : ℕ} (hg : g < nGr) : segOf s att (2 * g) = ffSeg s.kap s.nf g tokX := by
  have hg : g < 12 := hg
  unfold segOf
  rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega]

theorem seg_att {g : ℕ} (_hg : g < nGr) : segOf s att (2 * g + 1) = att g := by
  unfold segOf
  rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega]

theorem seg_head : segOf s att 24 = segHeadY s.nf := if_pos rfl

variable {s att}

theorem segsOK_of (hA : AttOK s att) : SegsOK s (segOf s att) where
  rows := fun k hk => by
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · rw [seg_ff s att hg]
      show 19 = rowsLog (2 * g)
      unfold rowsLog
      rw [if_neg (by omega)]
    · rw [seg_att s att hg]
      exact hA.rows g hg
    · rw [seg_head]
      rfl
  cols := fun k hk => by
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · rw [seg_ff s att hg]
      have hg : g < 12 := hg
      show colsFF = cols (2 * g)
      unfold cols
      rw [if_neg (by omega), if_neg (by omega)]
    · rw [seg_att s att hg]
      exact hA.cols g hg
    · rw [seg_head]
      rfl
  wf := fun k hk => by
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · rw [seg_ff s att hg]
      exact ffSeg_wf XI s.kap s.nf g tokX hg
    · rw [seg_att s att hg]
      exact hA.wf g hg
    · rw [seg_head]
      exact headY_wf s.nf
  places := fun k hk => by
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · rw [seg_ff s att hg]
      exact ffSeg_reads XI s.kap s.nf Hd.plain g tokX hg
    · rw [seg_att s att hg]
      exact hA.places g hg
    · rw [seg_head]
      exact headY_places s.nf
  ffTo := fun g hg x T W => by
    rw [seg_ff s att hg]
    exact ffSeg_toMat XI s.kap s.nf Hd.plain g tokX plainOK hg x T W
  ffOf := fun g hg x M W => by
    rw [seg_ff s att hg]
    exact ffSeg_ofMat XI s.kap s.nf Hd.plain g tokX hg x M W
  attTo := fun g hg x T W => by
    rw [seg_att s att hg]
    exact hA.toM g hg x T W
  attOf := fun g hg x M W => by
    rw [seg_att s att hg]
    exact hA.ofM g hg x M W
  headTo := fun x T W => by
    rw [seg_head, headY_holds]
    exact (and_congr_left'
      (head_holds_int s.nf x W (toMat Hd.plain T) T.vHead (readsAt_toMat T))).trans and_assoc
  headOf := fun x M W => by
    rw [seg_head, headY_holds]
    exact (and_congr_left'
      (head_holds_int s.nf x W M (ofMat Hd.plain M).vHead (readsAt_ofMat M))).trans and_assoc

variable (s att)

variable {s att}

end Cm.Seg.TS
