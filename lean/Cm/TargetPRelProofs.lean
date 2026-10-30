-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPRelProofs.lean: the statements of Cm/TargetPRel.lean, proved. The head of
Cm/TargetPRel.lean tells them in words.

The statements are for a prime p (`Fact p.Prime`) with 2^61 - 1 ≤ p (the class `Big p`:
Inst/Model/Bound/Base.lean); the exceptions: Limits.

Main names:
  `below_cond_trace`, `ryes_trace`: at a lawful table, if the program runs and at every covered
    position the checked token has gap 0, and y = 0 where e < `ppref.T`, the honest trace has the
    cells that some segment reads below 129 in absolute value (`Below2 129`) and meets the
    conditions modulo p; with r < e it is a witness in `Ryes`.
  `sub`, `admits`, `forces`, `lang_yes`, `lang_no`, `trace_iff`, `lang_main`: the statements of
    `Cm.TP.Spec` (Cm/TargetPRel.lean).

The substance of the proofs lies in these files. Layers: Cm/TargetPLayers.lean over
Cm/TargetInst*.lean, Inst/Model/Bound/*.lean; the honest side of the layers holds modulo every prime
(Cm/Rel2LayersHon.lean). Head: Cm/TargetPHeadNoWrap.lean, Cm/TargetPHeadHonest.lean.

Limits: what the head of Cm/TargetPRel.lean lists as not said is not said here either. But that
head's "nothing below 2^61 - 1" does not hold of `headRF`, `headRFz`, `sub_at` and `sub`, which are
for every number p.
Terms: lean/GLOSSARY.md.
-/
import Cm.TargetPRel
import Cm.TargetPLayers
import Cm.TargetPHeadHonest
import Cm.Rel2Proofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TP

open Inst.Model Inst.Model.All Cm.TI
open Inst.Model.Layout (kRef hRef)

variable {p : ℕ} [Big p] [Fact p.Prime]

/-! ## The request's form -/

theorem y_zero_iff (x : Instance ppref) : ((x.y.val : ℕ) : ZMod p) = 0 ↔ x.y.val = 0 := by
  constructor
  · intro h
    have hd : p ∣ x.y.val := (ZMod.natCast_eq_zero_iff _ _).1 h
    have hlt : x.y.val < 202048 := x.y.isLt
    have hB : 2 ^ 61 - 1 ≤ p := Big.le
    norm_num at hB
    exact Nat.eq_zero_of_dvd_of_lt hd (by omega)
  · intro h
    rw [h, Nat.cast_zero]

theorem form_iff (x : Instance ppref) :
    (x.r < x.e ∧ (x.e < ppref.T → ((x.y.val : ℕ) : ZMod p) = 0)) ↔ Head3 x :=
  ⟨fun h => ⟨h.1, x.e_le, fun he => (y_zero_iff x).1 (h.2 he)⟩,
    fun h => ⟨h.1, fun he => (y_zero_iff x).2 (h.2.2 he)⟩⟩

/-! ## Under the hypotheses below, the conditions force the reply -/

section Force
variable {s : Scales} {i : Idx} {x : Instance ppref} {T : Trace}
  (b : Below2 (2 ^ 18) T) (c : Cond p s i.mat x T)
include b c

omit [Big p] [Fact p.Prime] in
theorem headRF : Plain.TP.RF (F := ZMod p) s.nf (castH p i.mat) (reqOf x) T.vHead :=
  ⟨fun j hj => ⟨b.hf j hj, b.hd j hj, b.hr j hj, fun _ hφ => b.toBelowL.headX hφ hj⟩,
    c.headKey, c.headIdn⟩

omit [Big p] [Fact p.Prime] in
theorem headRFz : Plain.TP.RFz p s.nf i.weights.H (reqOf x) T.vHead :=
  Plain.TP.rfz_of_rf (headRF b c)

omit [Fact p.Prime] in
theorem rfl_of (h : s.Lawful) : Lay.RFL p s.kap s.nf (fun _ => tbRef) i.mat (tokOf x.prompt) T :=
  ⟨fun g hg => ⟨fun a => b.ff g hg a.val a.property, c.ffKey g hg, c.ffIdn g hg⟩,
    fun g hg => ⟨fun a ha => b.att g hg a ha, c.attKey g hg, c.attIdn g hg⟩,
    fun j hj k hk => ((Plain.TP.noWrap (headRFz b c) h.nf (abs_H i.wf)).1 j hj).2.2 k hk⟩

/-- For a prime p with 2^61 - 1 ≤ p (`Fact p.Prime`, `Big p`), at a lawful table (`h`), cells below
2^18 (`b`) and the conditions modulo p (`c`): the program runs, and every covered token is the
first choice. -/
theorem modelS_of (h : s.Lawful) : ModelS ppref s.kap s.nf (fun _ => tbRef) i.weights x := by
  have hL := h.lawfulK
  have hR := rfl_of b c h
  have hS := Lay.stream_eqK (p := p) hL i.wf hR
  have hx : ∀ a < Head.nT, ∀ j < Head.nD, Head.xv T.vHead j a =
      XK ppref s.kap (tbsOf fun _ => tbRef) (Layout.weightsOf ppref kRef i.mat) x.prompt
        (2 * ppref.layers) a j := fun a ha j hj => by
    rw [T.x_head hj ha]
    exact hS 11 (by decide) 8 le_rfl a ha j hj
  have hz := headRFz b c
  have h1 := (Plain.TP.head_stream h.nf (abs_H i.wf) hx hz).1
  have h2 := Plain.TP.head_stream_gap h.nf (abs_H i.wf) (y := reqOf x) (fun t => x.w_lt t) hx hz
  have hrun : RunsK ppref s.kap s.nf (tbsOf fun _ => tbRef)
      (Layout.weightsOf ppref kRef i.mat) x.prompt :=
    Lay.runsK_of (p := p) (T := T) hL i.wf hR h1
  exact ⟨hrun, fun t hr he => h2 t (lt_of_lt_of_le he x.e_le) hr he⟩

end Force

/-! ## Under the hypotheses below, the conditions admit the reply -/

/-- For a prime p with 2^61 - 1 ≤ p (`Fact p.Prime`, `Big p`), at a lawful table (`h`), if the
program runs and every covered token is the first choice (and y = 0 if e < `ppref.T`), the honest
trace meets `Below2 129` (the cells that some segment reads are below 129 in absolute value) and the
conditions; r < e is not asked here. -/
theorem below_cond_trace {s : Scales} (h : s.Lawful) {i : Idx} {x : Instance ppref}
    (hy : x.e < ppref.T → x.y.val = 0) (hm : ModelS ppref s.kap s.nf (fun _ => tbRef) i.weights x) :
    Below2 129 (trace2 s i x) ∧ Cond p s i.mat x (trace2 s i x) := by
  have hL := h.lawfulK
  have hff := fun g (hg : g < nGr) => Lay.ffK_honest (p := p) hL i.wf hm.1 hg
  have hatt := fun g (hg : g < nGr) => Lay.attK (W := i.mat) (prompt := x.prompt) hL hg
  have hin : Head.N.HonIn0 s.nf (Lay.xsK s.kap (fun _ => tbRef) i.mat x.prompt 11 8)
      i.weights.H (reqOf x) :=
    Head.N.honIn0_stream h.nf (abs_H i.wf) hm.1.2
      (fun t _ hr he v hv => ((gapOf_eq_zero_iff _ _ (x.w_lt t)).1 (hm.2 t hr he)).1 v hv)
      (fun t _ hr he v hv => ((gapOf_eq_zero_iff _ _ (x.w_lt t)).1 (hm.2 t hr he)).2 v hv)
  have hv : (trace2 s i x).vHead =
      Plain.hon s.nf (Lay.xsK s.kap (fun _ => tbRef) i.mat x.prompt 11 8) i.weights.H (reqOf x) :=
    Lay.vHead_honTK _ _ _ _ _ _ rfl
  have hF : ∀ g (hg : g < nGr), (segFF p s.kap s.nf g).RF (tokOf x.prompt) (castW p i.mat)
      fun c => (trace2 s i x).vFF g c.val := fun g hg => by
    unfold trace2
    rw [Lay.vFF_honTK]
    exact (hff g hg).1
  have hA : ∀ g (hg : g < nGr),
      AttSeg.RFraw (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef (ZMod p)
        ((trace2 s i x).vAtt g) := fun g hg => by
    unfold trace2
    rw [Lay.vAtt_honTK]
    exact AttSeg.rfraw_of_int (scl := SFK s.kap s.nf g) (DAK s.kap g) tbRef _ (ZMod p) (hatt g hg).1
  have hH : Plain.TP.RF (F := ZMod p) s.nf (castH p i.mat) (reqOf x) (trace2 s i x).vHead := by
    rw [hv]
    exact Plain.TP.rf_of_rfz (Plain.TP.hon_rfz hin)
  refine ⟨⟨⟨fun g hg c hc => ?_, fun g hg c hc => ?_⟩,
      fun a ha φ hφ => ?_, fun a ha φ hφ => ?_,
      fun a ha φ hφ => ?_⟩,
    ⟨⟨fun g hg => (hF g hg).2.1, fun g hg => (hF g hg).2.2,
        fun g hg => (hA g hg).2.1, fun g hg => (hA g hg).2.2⟩,
      hH.keys, hH.idns,
      fun he => (y_zero_iff x).2 (hy he)⟩⟩
  · unfold trace2
    rw [Lay.vFF_honTK]
    exact Int.lt_add_one_iff.2 ((hff g hg).2 c hc)
  · unfold trace2
    rw [Lay.vAtt_honTK]
    exact Int.lt_add_one_iff.2 ((hatt g hg).2 c hc)
  · exact Int.lt_add_one_iff.2 ((Plain.hon_cells_le hin ha).1 φ hφ)
  · exact Int.lt_add_one_iff.2 ((Plain.hon_cells_le hin ha).2.1 φ hφ)
  · exact Int.lt_add_one_iff.2 ((Plain.hon_cells_le hin ha).2.2.1 φ hφ)

theorem ryes_trace {s : Scales} (h : s.Lawful) {i : Idx} {x : Instance ppref} (h3 : Head3 x)
    (hm : ModelS ppref s.kap s.nf (fun _ => tbRef) i.weights x) : Ryes p s i x (trace2 s i x) :=
  ⟨h3.1, below_cond_trace h h3.2.2 hm⟩

/-! ## The statements -/

omit [Big p] [Fact p.Prime] in
theorem sub_at (s : Scales) (i : Idx) (x : Instance ppref) (T : Trace) (h : Ryes p s i x T) :
    Rno p s i x T :=
  ⟨h.1, h.2.1.mono (by norm_num), h.2.2⟩

theorem head3_of_rno {s : Scales} {i : Idx} {x : Instance ppref} {T : Trace} (hR : Rno p s i x T) :
    Head3 x :=
  (form_iff x).1 ⟨hR.1, hR.2.2.yZero⟩

theorem forces_at {s : Scales} (h : s.Lawful) (i : Idx) (x : Instance ppref)
    (T : Trace) (hR : Rno p s i x T) : TrueAt s.kap s.nf i x :=
  (trueAt_iff s.kap s.nf i x).2 ⟨head3_of_rno hR, modelS_of hR.2.1 hR.2.2 h⟩

theorem trace_of_true {s : Scales} (h : s.Lawful) (i : Idx)
    (x : Instance ppref) (ht : TrueAt s.kap s.nf i x) : Ryes p s i x (trace2 s i x) :=
  ryes_trace h ((trueAt_iff s.kap s.nf i x).1 ht).1 ((trueAt_iff s.kap s.nf i x).1 ht).2

end Cm.TP

namespace Cm.TP

open Inst.Model Inst.Model.All Cm.TI

theorem sub : Spec.sub := fun _ s i x T h => sub_at s i x T h

theorem forces : Spec.forces := fun p hp hB _ h i x T hR =>
  haveI : Big p := ⟨hB⟩
  haveI : Fact p.Prime := ⟨hp⟩
  forces_at h i x T hR

theorem trace_iff : Spec.trace_iff := fun p hp hB s h i x =>
  haveI : Big p := ⟨hB⟩
  haveI : Fact p.Prime := ⟨hp⟩
  ⟨fun hR => forces_at h i x _ (sub_at s i x _ hR), trace_of_true h i x⟩

theorem admits : Spec.admits := fun p hp hB s h i x T hR =>
  (trace_iff p hp hB s h i x).2 (forces p hp hB s h i x T (sub p s i x T hR))

theorem lang_yes : Spec.lang_yes := fun p hp hB s h i x =>
  ⟨fun ⟨T, hR⟩ => forces p hp hB s h i x T (sub p s i x T hR),
    fun ht => ⟨_, (trace_iff p hp hB s h i x).2 ht⟩⟩

theorem lang_no : Spec.lang_no := fun p hp hB s h i x =>
  ⟨fun ⟨T, hR⟩ => forces p hp hB s h i x T hR,
    fun ht => ⟨_, sub p s i x _ ((trace_iff p hp hB s h i x).2 ht)⟩⟩

theorem lang_main : Spec.lang_main := fun p hp hB s h i x =>
  (lang_no p hp hB s h i x).trans
    ((trueAt_iff s.kap s.nf i x).trans (RinfS_iff ppref s.kap s.nf (fun _ => tbRef) i.index x).symm)

end Cm.TP
