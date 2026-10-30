-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/Rel2LayersHon.lean: the honest cells of the 24 segments of the layers, for every table of scales
with `LawfulK` and every well-formed matrix, whatever the head: if the program at the table runs on
the tokens, the cells that the rules of the two kinds of segments write satisfy the relations of
these segments (feed-forward: over `ZMod p`, p prime; attention: over the integers), and the valid
cells are at most 128 in absolute value.

Where the nouns are defined: trace, group and the cells that a segment reads (`Trace`, `nGr`, `vFF`,
`vAtt`, `vHead`): Inst/Model/All/Trace.lean; `LawfulK`: Inst/Model/Scales.lean; "the program runs"
(`RunsK`): Inst/Model/Program.lean; well formed (`Layout.WFW`): Inst/Model/Layout.lean.

Main names:
  `honTK κ nf tbG W prompt c`: the honest trace over given cells c of a head.
  `vFF_honTK`, `vAtt_honTK`, `vHead_honTK`: a borrowed cell is written by its owner, and the
    borrower's rule writes the same number (`vHead_honTK`: under `hx`, which says this of c).
  `attK`, `ffK_honest`: what an attention segment and a feed-forward segment contribute: relation
    and valid cells at most 128; `attK` under `hL`, `hg`; `ffK_honest` under `hL`, `hW` (the matrix
    W is well formed), `hm` (the program runs), `hg`, for every prime p.

Limits: this file says nothing on a head's own cells; no request occurs in this file.

The analogue of Inst/Model/All/HonestK.lean, whose honest trace has the cells of its own head built
in; here the head's cells are an argument; the proofs on the layers are the same.

Terms: lean/GLOSSARY.md.
-/
import Cm.Rel2Layers
import Inst.Model.Bound.AttK
import Inst.Model.FF.CastValid
import Inst.Model.Widened

set_option autoImplicit false

/- no default table of scales is in sight in this file: what reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Lay

open Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef hRef)

section Hon
variable (κ : ℕ → LayerScale) (nf : NormPar) (tbG : ℕ → Tables) (W : Mat)
  (prompt : Fin ppref.T → Fin ppref.V) (c : Head.Cells ℤ)

/-- the program's stream at the place s of group g -/
def xsK (g s : ℕ) : ℕ → Vec :=
  XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt (8 * g + s)
/-- the program's output of attention in layer l of group g -/
def osK (g l : ℕ) : ℕ → Vec :=
  Att.o (PG κ g l) (tbG g) (wOf W g l) (4 * g + l) (xsK κ tbG W prompt g (2 * l))

/-- The honest trace at the table, over given cells c of a head: the cells that the rules of the 24
segments of the layers write, and the own cells of c. -/
def honTK : Trace where
  ff := fun g =>
    FFSeg.hon (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g)
      (xsK κ tbG W prompt g) (osK κ tbG W prompt g)
  att := fun g =>
    AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g) (tbG g)
      (wOf W g) (4 * g) fun lam => xsK κ tbG W prompt g (2 * lam)
  hf := c.hf
  hd := c.hd
  hr := c.hr

/-- x0 of a later group: the segment before writes what the rule of this segment writes. -/
theorem vFF_honTK (g : ℕ) :
    (honTK κ nf tbG W prompt c).vFF g =
      FFSeg.hon (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g)
        (xsK κ tbG W prompt g) (osK κ tbG W prompt g) := by
  funext c
  unfold Trace.vFF
  by_cases hc : c.X = .x0 ∧ 0 < g
  · rw [if_pos hc]
    obtain ⟨X, k, inst, j, i⟩ := c
    obtain ⟨h1, h2⟩ := hc
    obtain rfl : X = .x0 := h1
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    show cellW 5 (xsK κ tbG W prompt g 8 i j - 0) k =
      cellW 5 (xsK κ tbG W prompt (g + 1) 0 i j - 0) k
    unfold xsK
    rw [show 8 * (g + 1) + 0 = 8 * g + 8 by ring]
  · rw [if_neg hc]
    rfl

/-- qry, key, val, out: the feed-forward segment writes what the rule of the attention segment
writes. -/
theorem vAtt_honTK (g : ℕ) :
    (honTK κ nf tbG W prompt c).vAtt g =
      AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g) (tbG g)
        (wOf W g) (4 * g) fun lam => xsK κ tbG W prompt g (2 * lam) := by
  funext c
  unfold Trace.vAtt AttSeg.join
  cases c with
  | qry k b g' i n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | out k b g' i n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | key k lam g' j n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | val k lam g' j n =>
    show cellW 2 (_ - 0) k = cellW 2 _ k
    rw [sub_zero]
    rfl
  | c ρ jj b x => rfl
  | mx k b g' i => rfl
  | den k b g' i => rfl
  | ib k b g' i => rfl
  | qh b g' i n => rfl
  | qh' b g' i n => rfl

/-- x of the head: the last feed-forward segment writes the five cells of each value of the stream
after the last layer; if the head's rule writes the same (`hx`), the head reads c. -/
theorem vHead_honTK
    (hx : c.x = fun φ i => cellW 5 (xsK κ tbG W prompt 11 8 i (φ % 5120)) (φ / 5120)) :
    (honTK κ nf tbG W prompt c).vHead = c := by
  have hx' : (honTK κ nf tbG W prompt c).vHead.x = c.x := by
    rw [hx]
    funext φ i
    show cellW 5 (xsK κ tbG W prompt 11 8 i (φ % 5120) - 0) (φ / 5120) =
      cellW 5 (xsK κ tbG W prompt 11 8 i (φ % 5120)) (φ / 5120)
    rw [sub_zero]
  show (⟨_, _, _, _⟩ : Head.Cells ℤ) = _
  rw [show (fun φ i => (honTK κ nf tbG W prompt c).ff (nGr - 1) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩) = _
      from hx']
  rfl

variable {κ nf tbG W prompt c}

/-- Under `hL`, `hg`: the sizes and words of a layer fit the attention segment of its group -/
theorem fitHK (hL : LawfulK κ nf tbG) {g : ℕ} (hg : g < nGr) (l : ℕ) :
    AttSeg.Hon.Fit (scl := SFK κ nf g) (DAK κ g) (PG κ g l) :=
  AttSeg.Hon.Fit.mk (scl := SFK κ nf g) (by decide : ppref.ch = AttSeg.Dim.ref.ch)
    (by decide : ppref.nq / ppref.nkv = AttSeg.Dim.ref.na) (by decide : 0 < AttSeg.Dim.ref.na)
    (rowsK hL hg l) (hL.one g hg (l % 4) (Nat.mod_lt _ (by norm_num)))

/-- Under the hypotheses below: every value of the stream of a run can be written in five cells:
test (N1) (`NORM.OK`, Inst/Model/Program.lean) of the normalisation that reads it bounds it. -/
theorem writableK (hL : LawfulK κ nf tbG) {i : Weights} (hm : RunsK ppref κ nf (tbsOf tbG) i prompt)
    {s : ℕ} (hs : s ≤ 96) {pos : ℕ} (hpos : pos < 1024) {j : ℕ} (hj : j < 5120) :
    Writable 5 (XK ppref κ (tbsOf tbG) i prompt s pos j) := by
  refine writable_of_abs_le _ ?_
  rcases Nat.lt_or_ge s 96 with hlt | hge
  · obtain ⟨hA, hF⟩ := hm.1 (s / 2) (by show s / 2 < 48; omega)
    rcases Nat.mod_two_eq_zero_or_one s with h0 | h1
    · rw [show 2 * (s / 2) = s by omega] at hA
      exact abs_le_of_normOK (hL.ff (s / 2) (by omega)).ranges.n1.1 (hA pos hpos).1 hj
    · rw [show 2 * (s / 2) + 1 = s by omega] at hF
      exact abs_le_of_normOK (hL.ff (s / 2) (by omega)).ranges.n2.1 (hF pos hpos).1 hj
  · obtain rfl : s = 96 := by omega
    exact abs_le_of_normOK hL.nf.1 (hm.2 pos hpos) hj

end Hon

section Runs
variable {κ : ℕ → LayerScale} {nf : NormPar} {tbG : ℕ → Tables} {W : Mat}
  {prompt : Fin ppref.T → Fin ppref.V} (hL : LawfulK κ nf tbG)
include hL

/-- Under `hL`, `hg`: the honest trace of the attention segment of a group satisfies its relation
over the integers, with valid cells of absolute value at most 128. -/
theorem attK {g : ℕ} (hg : g < nGr) :
    AttSeg.RFraw (scl := SFK κ nf g) (DAK κ g) (tbG g) ℤ
      (AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g)
        (tbG g) (wOf W g) (4 * g) fun lam => xsK κ tbG W prompt g (2 * lam)) ∧
    ∀ c : AttSeg.Raw, c.Valid (DAK κ g) →
      |AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g)
          (tbG g) (wOf W g) (4 * g) (fun lam => xsK κ tbG W prompt g (2 * lam)) c| ≤ 128 :=
  AttSeg.Hon.honestK (scl := SFK κ nf g)
    (wOf W g) (4 * g) _ (fitHK hL hg) (fun _ => rfl) (sizeOKK hL hg) (expTabK hL hg)

/-- Under `hL` and the hypotheses below: the outputs of attention are at most 2,047 in absolute
value: the honest trace of the attention segment satisfies its relation, and the relation bounds
out. -/
theorem osK_abs {g : ℕ} (hg : g < nGr) {l : ℕ} (hl : l < 4) {i : ℕ} (hi : i < 1024)
    {c : ℕ} (hc : c < 5120) :
    |osK κ tbG W prompt g l i c| ≤ 2047 := by
  letI : Scl := SFK κ nf g
  haveI : Cm.TI.Big (2 ^ 64 - 2 ^ 32 + 1) := ⟨by norm_num⟩
  have hRF := AttSeg.rfraw_of_int
    (DAK κ g) (tbG g) _ (ZMod (2 ^ 64 - 2 ^ 32 + 1)) (attK (W := W) (prompt := prompt) hL hg).1
  have hin := fun lam =>
    AttSeg.Hon.honK_inputs (D := DAK κ g) (Ps := fun lam => PG κ g lam) (tbs := fun _ => tbG g)
      (tb := tbG g) (wOf W g) (4 * g) (fun lam => xsK κ tbG W prompt g (2 * lam)) lam
  have hb : 5 * l + c / 128 % 5 < 20 := by omega
  have hg' : c / 128 / 5 < 8 := by omega
  have hn : c % 128 < 128 := by omega
  have e1 : DA.lamOf (5 * l + c / 128 % 5) = l := by
    show (5 * l + c / 128 % 5) / 5 = l
    omega
  have e2 : DA.ch * DA.head (c / 128 / 5) (5 * l + c / 128 % 5) + c % 128 = c := by
    show 128 * (5 * (c / 128 / 5) + (5 * l + c / 128 % 5) % 5) + c % 128 = c
    omega
  have hout := Cm.TI.AttSeg.outBoundK (sizeOKK hL hg) (expTabK hL hg) hRF
    (fun b hb g' hg' i hi n hn => by
      rw [(hin ((DAK κ g).lamOf b)).1 b hb rfl g' hg' i hi n hn]
      exact AttSeg.NW2.abs_clamp _)
    (fun lam _ g' hg' j hj n hn => by
      rw [((hin lam).2 g' hg' j hj n hn).1, ((hin lam).2 g' hg' j hj n hn).2]
      exact ⟨AttSeg.NW2.abs_clamp _, AttSeg.NW2.abs_clamp _⟩)
    _ hb _ hg' i hi _ hn
  rw [AttSeg.Hon.honK_output (D := DAK κ g) (Ps := fun lam => PG κ g lam)
      (tbs := fun _ => tbG g) (tb := tbG g) (wOf W g) (4 * g)
      (fun lam => xsK κ tbG W prompt g (2 * lam)) l _ hb e1 _ hg' i hi _ hn] at hout
  rw [show (DAK κ g).ch * (DAK κ g).head (c / 128 / 5) (5 * l + c / 128 % 5) + c % 128 = c
      from e2] at hout
  exact hout

/-- Under `hL`, `hm`, `hg`: the steps of a feed-forward segment lead from place to place of the
program's stream. -/
theorem runs_groupK (hm : RunsK ppref κ nf (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt)
    {g : ℕ} (hg : g < nGr) :
    FFSeg.Runs (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g)
      (xsK κ tbG W prompt g) (osK κ tbG W prompt g) := by
  letI : Scl := SFK κ nf g
  exact
    { att := fun l hl => by
        have hl' : l < 4 := hl
        have hg' : g < 12 := hg
        have := (hm.1 (4 * g + l) (by show 4 * g + l < 48; omega)).1
        rwa [layer_eq (by omega), show 2 * (4 * g + l) = 8 * g + 2 * l by ring,
          tbsOf_at tbG g hl', ← kapG_lt κ g hl'] at this
      ff := fun l hl => by
        have hl' : l < 4 := hl
        have hg' : g < 12 := hg
        have := (hm.1 (4 * g + l) (by show 4 * g + l < 48; omega)).2
        rwa [layer_eq (by omega), show 2 * (4 * g + l) + 1 = 8 * g + (2 * l + 1) by ring,
          tbsOf_at tbG g hl', ← kapG_lt κ g hl'] at this
      pl7 := fun l hl i _ c _ => by
        have hl' : l < 4 := hl
        have hg' : g < 12 := hg
        have e := XK_even (κ := κ) (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt
          (n := 8 * g + 2 * l) (by omega)
        rw [show (8 * g + 2 * l) / 2 = 4 * g + l by omega, layer_eq (by omega),
          tbsOf_at tbG g hl', ← PG_lt κ g hl'] at e
        show XK ppref κ _ _ prompt (8 * g + (2 * l + 1)) i c = _
        rw [show 8 * g + (2 * l + 1) = 8 * g + 2 * l + 1 by omega, e]
        rfl
      pl13 := fun l hl i _ c _ => by
        have hl' : l < 4 := hl
        have hg' : g < 12 := hg
        have e := XK_odd (κ := κ) (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt
          (n := 8 * g + (2 * l + 1)) (by omega)
        rw [show (8 * g + (2 * l + 1)) / 2 = 4 * g + l by omega, layer_eq (by omega),
          tbsOf_at tbG g hl', ← PG_lt κ g hl'] at e
        show XK ppref κ _ _ prompt (8 * g + (2 * l + 2)) i c = _
        rw [show 8 * g + (2 * l + 2) = 8 * g + (2 * l + 1) + 1 by omega, e]
        rfl
      o := fun l hl i hi j hj => osK_abs hL hg hl hi hj
      wr := fun s hs i hi j hj => by
        have hs' : s ≤ 8 := hs
        have hg' : g < 12 := hg
        exact writableK hL hm (by omega) hi hj }

/-- What the feed-forward segment of a group contributes, under `hL`, `hW`, `hm`, `hg`, for every
prime p: its honest trace satisfies its field relation over `ZMod p`, with valid cells of absolute
value at most 128. -/
theorem ffK_honest {p : ℕ} [Fact p.Prime] (hW : Layout.WFW ppref kRef W hRef)
    (hm : RunsK ppref κ nf (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt)
    {g : ℕ} (hg : g < nGr) :
    (FFSeg.trace (scl := SFK κ nf g) DF (tbG g) kRef (4 * g) (decide (g = 0)) (ZMod p)).RF
      (tokOf prompt) (fun r c => ((W r c : ℤ) : ZMod p)) (fun c =>
        FFSeg.hon (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g) (xsK κ tbG W prompt g)
          (osK κ tbG W prompt g) c.val) ∧
    ∀ c : FFSeg.Cell, c.Valid DF →
      |FFSeg.hon (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g) (xsK κ tbG W prompt g)
          (osK κ tbG W prompt g) c| ≤ 128 := by
  letI : Scl := SFK κ nf g
  obtain ⟨h1, -, h3, h4⟩ :=
    FFSeg.honestK (ffK hL hg) (settingK hL hW (tokOf_lt prompt) hg) _ _ (runs_groupK hL hm hg)
  have hE : decide (g = 0) = true →
      ∀ i < DF.T, ∀ j < DF.d, xsK κ tbG W prompt g 0 i j =
        (Layout.weightsOf ppref kRef W).Emb (tokOf prompt i) j := fun h0 i hi j _ => by
    obtain rfl : g = 0 := of_decide_eq_true h0
    show XK ppref κ _ _ prompt 0 i j = _
    have hi' : i < ppref.T := hi
    show (if hh : i < ppref.T then _ else _) = _
    rw [dif_pos hi']
    unfold tokOf
    rw [dif_pos hi']
  refine ⟨(FFSeg.rf_iff (scl := SFK κ nf g) DF (tbG g) (4 * g) (decide (g = 0)) kRef (ZMod p)
      (tokOf prompt) W _).2 ?_,
    h1⟩
  refine FFSeg.rfraw_congr (scl := SFK κ nf g)
    (t := FFSeg.hon (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g)
        (xsK κ tbG W prompt g) (osK κ tbG W prompt g))
    rfl (fun c hc => ?_)
    (FFSeg.rfraw_of_int (scl := SFK κ nf g) DF (tbG g) (4 * g) (decide (g = 0)) _ _ (tokOf prompt) _
      (ZMod p) ⟨fun c hc => lt_of_le_of_lt (h1 c hc) (by norm_num), fun q => ?_, fun j hj => ?_⟩)
  · unfold FFSeg.rd
    rw [dif_pos hc]
    exact Int.cast_id.symm
  · rw [FFSeg.castT_int]
    exact h3 q
  · rw [FFSeg.castT_int]
    exact h4 (decide (g = 0)) hE j hj

end Runs

end Cm.Lay
