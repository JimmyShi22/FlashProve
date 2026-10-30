-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegAllProofs.lean: the statements of Cm/TargetSegAll.lean, proved: putting together.

Main names (statements and hypotheses: Cm/TargetSegAll.lean):
  `cond_iff`: the conditions modulo p (`Cm.TP.Cond Gl.p`, Cm/TargetPRel.lean) as the clauses of the
    25 segments.
  `equiv_of`: the one equivalence, from `SegsOK`: `Cm.TP.Cond Gl.p` at the trace of M ⇔ the 25
    segments' conditions at integer matrices M of cells.
  `equiv_to`: the same at T ⇔ at the matrices of a trace T.

Limits: what the head of Cm/TargetSegAll.lean lists as not said is not said here either. This file
does not say that segments with `SegsOK` exist: Cm/TargetSegModel.lean.
Terms: lean/GLOSSARY.md.
-/
import Cm.TargetSegAll
import Cm.SegAllProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All

theorem cond_iff : Spec.cond_iff := by
  intro s W x T
  constructor
  · intro h
    exact ⟨fun g hg => ⟨h.ffKey g hg, h.ffIdn g hg⟩, fun g hg => ⟨h.attKey g hg, h.attIdn g hg⟩,
      h.headKey, h.headIdn, h.yZero⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨fun g hg => (h1 g hg).1, fun g hg => (h1 g hg).2,
        fun g hg => (h2 g hg).1, fun g hg => (h2 g hg).2⟩,
      h3, h4, h5⟩

theorem two_lt {g : ℕ} (hg : g < nGr) : 2 * g < nSeg ∧ 2 * g + 1 < nSeg := by
  have hg : g < 12 := hg
  constructor
  · show 2 * g < 25
    omega
  · show 2 * g + 1 < 25
    omega

theorem equiv_of : Spec.equiv_of := by
  intro s seg hS W x M
  rw [cond_iff s W x (ofMat Hd.plain M)]
  constructor
  · rintro ⟨h1, h2, h3⟩ k hk
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · exact (hS.ffOf g hg x M W).2 (h1 g hg)
    · exact (hS.attOf g hg x M W).2 (h2 g hg)
    · exact (hS.headOf x M W).2 h3
  · intro h
    exact ⟨fun g hg => (hS.ffOf g hg x M W).1 (h _ (two_lt hg).1),
      fun g hg => (hS.attOf g hg x M W).1 (h _ (two_lt hg).2),
      (hS.headOf x M W).1 (h 24 (by show 24 < 25; norm_num))⟩

theorem equiv_to : Spec.equiv_to := by
  intro s seg hS W x T
  rw [cond_iff s W x T]
  constructor
  · rintro ⟨h1, h2, h3⟩ k hk
    rcases seg_cases hk with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
    · exact (hS.ffTo g hg x T W).2 (h1 g hg)
    · exact (hS.attTo g hg x T W).2 (h2 g hg)
    · exact (hS.headTo x T W).2 h3
  · intro h
    exact ⟨fun g hg => (hS.ffTo g hg x T W).1 (h _ (two_lt hg).1),
      fun g hg => (hS.attTo g hg x T W).1 (h _ (two_lt hg).2),
      (hS.headTo x T W).1 (h 24 (by show 24 < 25; norm_num))⟩

end Cm.Seg.TS
