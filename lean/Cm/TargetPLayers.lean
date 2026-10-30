-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetPLayers.lean: no wrap-around in the 24 segments of the layers, for every lawful table of
scales, whatever the head, at a variable prime.

"No wrap-around": what holds modulo p of the cells' small integers is shown to hold over the
integers, for a prime p (`Fact p.Prime`) with 2^61 - 1 ≤ p (the class `Big p`:
Inst/Model/Bound/Base.lean).

Main names, each under the hypotheses of its statement, among them
`h : RFL p κ nf tbG W (tokOf prompt) T` (Cm/Rel2Layers.lean: the field relations of the 24 segments
over `ZMod p`, and one bound that a head gives):
  `part1K` to `groupK`: the steps of the proof: what a feed-forward segment gives by itself; the
    bound on its last place from the next segment, or from the head; the outputs of attention; the
    steps of the program.
  `stream_eqK`: see its docstring.
  `runsK_of`: the program's range tests hold in all 48 layers; with the final normalisation's
    (`hN`) it is `RunsK`.

Why: `Big p` enters through the theorems on one segment: `noWrap1K`, `noWrap2K`, `noWrap3K`
(Cm/TargetInstFFK.lean), `noWrapK`, `outBoundK` (Inst/Model/Bound/AttK.lean).

Limits: this file says nothing on logits, requests or replies: no request occurs in this file. The
namespace is `Cm.TP.Lay` (`Cm.TI`, the namespace of the lower files Cm/TargetInst*.lean,
Inst/Model/Bound/*.lean, is opened); `settingK` is `Cm.Lay.settingK` to the letter; what else names
no prime is Cm/Rel2Layers.lean's.
Terms: lean/GLOSSARY.md.
THE LABELS "(PL6)", "(PL7)", "(PL13)", "Lemma S15.10" in four doc comments below are the copied
library's own: they point to a paper of ours and its supplement, not to the paper that this
protocol builds on (lean/CREDITS.md).
"The copied library" in this file's comments: folders of this library itself, such as Blocks/, Iop/
and Inst/ (lean/CREDITS.md).
-/
import Cm.Rel2Layers
import Cm.TargetInstFFK
import Inst.Model.Bound.AttK


set_option autoImplicit false

/- No default table of scales is in sight in this file (`Scl.ref` is no instance here): what reads
a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TP.Lay

open Cm Cm.Lay Cm.TI

open Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef hRef)

section Facts
variable {p : ℕ} [Big p] [Fact p.Prime] {κ : ℕ → LayerScale} {nf : NormPar} {tbG : ℕ → Tables}
  {W : Mat} {tok : ℕ → ℕ} {T : Trace} (hL : LawfulK κ nf tbG) (hW : Layout.WFW ppref kRef W hRef)
  (htok : ∀ i, tok i < ppref.V) (h : RFL p κ nf tbG W tok T)

omit [Fact p.Prime] in
include hL hW htok in
theorem settingK {g : ℕ} (hg : g < nGr) :
    FFSeg.SettingK (kapG κ g) nf (tbG g) W (4 * g) tok :=
  FFSeg.Spec.Setting.mk (scl := SFK κ nf g) (hL.tab g hg) hW (by omega) (by
    show 4 * g + 4 ≤ 48
    unfold nGr at hg
    omega) htok

include hL hW htok h in
/-- (1) what a feed-forward segment gives by itself -/
theorem part1K {g : ℕ} (hg : g < nGr) {l : ℕ} (hl : l < 4) :
    FFSeg.Part1 (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g) (T.tR g) l :=
  Cm.TI.FFSeg.noWrap1K (ffK hL hg) (settingK hL hW htok hg) (h.ff g hg) l hl

include hL hW htok h in
/-- Under the hypotheses of its statement: (2) x8 is bounded: it is x0 of the next feed-forward
segment, or x of the head, where the bound is the third clause of RFL -/
theorem lastBoundK {g : ℕ} (hg : g < nGr) : FFSeg.LastBound DF (T.tR g) := by
  letI : Scl := SFK κ nf (g + 1)
  intro i hi j hj
  show |FFSeg.xS DF (T.tR g) 8 j i| < 2 ^ 39
  by_cases h11 : g = 11
  · subst h11
    rw [← T.x_head hj hi]
    exact h.last i hi j hj
  · rw [← T.x0_succ g hj hi]
    exact (part1K hL hW htok h (g := g + 1) (by unfold nGr at hg ⊢; omega)
        (l := 0) (by norm_num)).bound
      0 (by norm_num) i hi j hj

include hL hW htok h in
theorem part3K {g : ℕ} (hg : g < nGr) :
    (∀ l < 4, FFSeg.Part3 (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g) (T.tR g) l) ∧
    (decide (g = 0) = true →
      ∀ i < 1024,
        ∀ j < 5120, FFSeg.xS DF (T.tR g) 0 j i = (Layout.weightsOf ppref kRef W).Emb (tok i) j) :=
  Cm.TI.FFSeg.noWrap3K (ffK hL hg) (settingK hL hW htok hg) (h.ff g hg) (lastBoundK hL hW htok h hg)

include hL hW htok h in
/-- Under the hypotheses of its statement: (3) out is bounded, and it is o -/
theorem oboundK {g : ℕ} (hg : g < nGr) : FFSeg.OBound DF (T.tR g) := by
  letI : Scl := SFK κ nf g
  intro l hl i hi j hj
  obtain ⟨b, g', n, hb, hg', hn, -, -, he⟩ := T.o_eq g hl hj hi
  rw [he]
  have hA := h.att g hg
  refine Cm.TI.AttSeg.outBoundK (sizeOKK hL hg) (expTabK hL hg) hA (fun b hb g' hg' i hi n hn => ?_)
    (fun lam hlam g' hg' j hj n hn => ⟨?_, ?_⟩) b hb g' hg' i hi n hn
  · rw [T.qry_eq g hb hg' hi hn,
      (part1K hL hW htok h hg (Trace.idx_q hb hg' hn).1).q i hi _ (Trace.idx_q hb hg' hn).2]
    exact AttSeg.NW2.abs_clamp _
  · rw [T.key_eq g hlam hg' hj hn, (part1K hL hW htok h hg hlam).kx j hj _ (Trace.idx_kv hg' hn)]
    exact AttSeg.NW2.abs_clamp _
  · rw [T.val_eq g hlam hg' hj hn, (part1K hL hW htok h hg hlam).v j hj _ (Trace.idx_kv hg' hn)]
    exact AttSeg.NW2.abs_clamp _

include hL hW htok h in
theorem part2K {g : ℕ} (hg : g < nGr) {l : ℕ} (hl : l < 4) :
    FFSeg.Part2 (scl := SFK κ nf g) DF (wOf W g) (T.tR g) l :=
  Cm.TI.FFSeg.noWrap2K (ffK hL hg)
    (settingK hL hW htok hg) (h.ff g hg) (oboundK hL hW htok h hg) l hl

/-! ## The computation -/

include hL hW htok h in
/-- Under the hypotheses of its statement: (PL6): the arrays of the attention segment hold the
program's inputs on the trace's stream, so out holds its output -/
theorem o_isK {g : ℕ} (hg : g < nGr) {l : ℕ} (hl : l < 4) {i : ℕ} (hi : i < 1024)
    {c : ℕ} (hc : c < 5120) :
    FFSeg.val (T.tR g) .o l c i =
      Att.o (PG κ g l) (tbG g) (wOf W g l) (4 * g + l) (St T g (2 * l)) i c := by
  letI : Scl := SFK κ nf g
  have hin : AttSeg.InputsAre (DAK κ g) (PG κ g l) (tbG g) (wOf W g l) (4 * g + l)
      (St T g (2 * l)) l (T.vAtt g) := by
    refine ⟨fun b hb hlb g' hg' i hi n hn => ?_, fun g' hg' j hj n hn => ⟨?_, ?_⟩⟩
    · have hlb' : DA.lamOf b = l := hlb
      rw [T.qry_eq g hb hg' hi hn, hlb']
      exact (part1K hL hW htok h hg hl).q i hi _ (Trace.idx_q hb hg' hn).2
    · rw [T.key_eq g hl hg' hj hn]
      exact (part1K hL hW htok h hg hl).kx j hj _ (Trace.idx_kv hg' hn)
    · rw [T.val_eq g hl hg' hj hn]
      exact (part1K hL hW htok h hg hl).v j hj _ (Trace.idx_kv hg' hn)
  obtain ⟨b, g', n, hb, hg', hn, e1, e2, he⟩ := T.o_eq g hl hc hi
  have hA := h.att g hg
  rw [he,
    Cm.TI.AttSeg.noWrapK (sizeOKK hL hg) (expTabK hL hg) hA (fitK hL hg l)
      rfl hin b hb e1 g' hg' i hi n hn]
  exact congrArg _ e2

include hL hW htok h in
/-- (PL7) -/
theorem step_attK {g : ℕ} (hg : g < nGr) {l : ℕ} (hl : l < 4) :
    Agree ppref (St T g (2 * l + 1))
      (Att.x' (PG κ g l) (tbG g) (wOf W g l) (4 * g + l) (St T g (2 * l))) := by
  intro i hi c hc
  show FFSeg.xS DF (T.tR g) (2 * l + 1) c i = _
  rw [show FFSeg.xS DF (T.tR g) (2 * l + 1) c i = _ from part2K hL hW htok h hg hl i hi c hc]
  unfold Att.x'
  refine congrArg₂ _ rfl (congrArg (fun a => rhu a (PG κ g l).ko) ?_)
  exact dot_congr _ fun j hj => o_isK hL hW htok h hg hl hi hj

include hL hW htok h in
/-- (PL13) -/
theorem step_ffK {g : ℕ} (hg : g < nGr) {l : ℕ} (hl : l < 4) :
    Agree ppref (St T g (2 * l + 2))
      (FF.x'' (PG κ g l) (tbG g) (wOf W g l) (4 * g + l) (St T g (2 * l + 1))) :=
  fun i hi c hc => FFSeg.Part3.out (scl := SFK κ nf g) ((part3K hL hW htok h hg).1 l hl) i hi c hc

include hL hW htok h in
/-- **One group of four layers** (Lemma S15.10 at a table of scales). -/
theorem groupK (prompt : Fin ppref.T → Fin ppref.V) {g : ℕ} (hg : g < nGr)
    (h0 : Agree ppref (St T g 0)
      (XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt (8 * g))) :
    ∀ s ≤ 8, Agree ppref (St T g s)
      (XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt (8 * g + s))
  | 0, _ => h0
  | s + 1, hs => by
    have ih := groupK prompt hg h0 s (Nat.le_of_succ_le hs)
    have hg' : g < 12 := hg
    by_cases hev : s % 2 = 0
    · obtain ⟨l, hl, rfl⟩ : ∃ l, l < 4 ∧ s = 2 * l := ⟨s / 2, by omega, by omega⟩
      have e := XK_even (κ := κ) (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt
        (n := 8 * g + 2 * l) (by omega)
      rw [show (8 * g + 2 * l) / 2 = 4 * g + l by omega, layer_eq (by omega),
        tbsOf_at tbG g hl, ← PG_lt κ g hl] at e
      rw [show 8 * g + (2 * l + 1) = 8 * g + 2 * l + 1 by omega, e]
      exact (step_attK hL hW htok h hg hl).trans (att_x'_congr (P := PG κ g l) ih)
    · obtain ⟨l, hl, rfl⟩ : ∃ l, l < 4 ∧ s = 2 * l + 1 := ⟨s / 2, by omega, by omega⟩
      have e := XK_odd (κ := κ) (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt
        (n := 8 * g + (2 * l + 1)) (by omega)
      rw [show (8 * g + (2 * l + 1)) / 2 = 4 * g + l by omega, layer_eq (by omega),
        tbsOf_at tbG g hl, ← PG_lt κ g hl] at e
      rw [show 8 * g + (2 * l + 1 + 1) = 8 * g + (2 * l + 1) + 1 by omega, e]
      exact (step_ffK hL hW htok h hg hl).trans (ff_x''_congr (P := PG κ g l) ih)

end Facts

section Main
variable {p : ℕ} [Big p] [Fact p.Prime] {κ : ℕ → LayerScale} {nf : NormPar} {tbG : ℕ → Tables}
  {W : Mat} {T : Trace} {prompt : Fin ppref.T → Fin ppref.V} (hL : LawfulK κ nf tbG)
  (hW : Layout.WFW ppref kRef W hRef) (h : RFL p κ nf tbG W (tokOf prompt) T)

include hL hW h in
/-- Under the hypotheses of its statement, the trace holds the stream of the program at the table,
at all 97 places. -/
theorem stream_eqK :
    ∀ g < nGr, ∀ s ≤ 8,
      Agree ppref (St T g s)
        (XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt (8 * g + s))
  | 0, hg => by
    refine groupK hL hW (tokOf_lt prompt) h prompt hg fun i hi j hj => ?_
    show FFSeg.xS DF (T.tR 0) 0 j i = XK ppref κ _ _ prompt 0 i j
    rw [(part3K hL hW (tokOf_lt prompt) h hg).2 rfl i hi j hj]
    show _ = if hh : i < ppref.T then _ else _
    rw [dif_pos hi]
    unfold tokOf
    rw [dif_pos hi]
  | g + 1, hg => by
    have hg0 : g < nGr := Nat.lt_of_succ_lt hg
    refine groupK hL hW (tokOf_lt prompt) h prompt hg fun i hi j hj => ?_
    show FFSeg.xS DF (T.tR (g + 1)) 0 j i = _
    rw [T.x0_succ g hj hi, show 8 * (g + 1) = 8 * g + 8 by ring]
    exact stream_eqK g hg0 8 le_rfl i hi j hj

end Main

/-- Under the hypotheses of its statement, the program's range tests hold in all 48 layers; with
the final normalisation's it is "the program runs". -/
theorem runsK_of {p : ℕ} [Big p] [Fact p.Prime] {κ : ℕ → LayerScale}
    {nf : NormPar} {tbG : ℕ → Tables} {W : Mat} {T : Trace}
    {prompt : Fin ppref.T → Fin ppref.V} (hL : LawfulK κ nf tbG)
    (hW : Layout.WFW ppref kRef W hRef) (h : RFL p κ nf tbG W (tokOf prompt) T)
    (hN : ∀ pos < ppref.T,
      NORM.OK nf ppref.d
        (XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt (2 * ppref.layers) pos)) :
    RunsK ppref κ nf (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt := by
  have hS := stream_eqK hL hW h
  have htok := tokOf_lt prompt
  refine ⟨fun L hL' => ?_, hN⟩
  have hL'' : L < 48 := hL'
  obtain ⟨g, l, hl, rfl⟩ : ∃ g l, l < 4 ∧ L = 4 * g + l := ⟨L / 4, L % 4, by omega, by omega⟩
  have hg : g < nGr := by unfold nGr; omega
  rw [layer_eq hL'', show 2 * (4 * g + l) = 8 * g + 2 * l by ring,
    tbsOf_at tbG g hl, ← kapG_lt κ g hl]
  exact ⟨(att_ok_congr (P := PG κ g l) (hS g hg (2 * l) (by omega))).1
      (FFSeg.Part1.att (scl := SFK κ nf g) (part1K hL hW htok h hg hl)),
    (ff_ok_congr (P := PG κ g l) (hS g hg (2 * l + 1) (by omega))).1
      (FFSeg.Part3.ok (scl := SFK κ nf g) ((part3K hL hW htok h hg).1 l hl))⟩

end Cm.TP.Lay
