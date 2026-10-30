-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/HonestK.lean: the honest trace of the whole model, for all valid scales (`LawfulK`,
Inst/Model/Scales.lean).

The counterpart of Inst/Model/All/Honest.lean (at the reference parameters; with the widened cell
rule of Inst/Model/Widened.lean).
The honest traces of the three kinds are terms: `FFSeg.hon` at the scales of the group's four
layers, `AttSeg.Hon.honK` (Inst/Model/Att/Scales.lean), `Head.N.honCells` at the final normalisation
(Inst/Model/Head/HonestN.lean). `honTK` puts them side by side. A borrowed cell is written by its
owner, and the borrower's rule writes the same number: `vFF_honTK`, `vAtt_honTK`, `vHead_honTK`.
`writableK`: five cells are enough for the stream of a run at valid scales (not all hypotheses are
named here: see its statement).
Of the parts of the trace, each under the hypotheses of its statement: `attK`: the honest trace of a
group's attention segment satisfies its relation over the integers; `ffK_honest`: that of its
feed-forward segment satisfies its field relation over `ZMod p`, for every prime p; both with cells
of at most 128 in absolute value. `osK_abs`: the outputs of attention are at most 2,047 in absolute
value. `runs_groupK`: the steps of a feed-forward segment lead from index to index of the program's
stream. The head's cells: `hon_rfz`, Policy/Rel/LedgerHeadHonest.lean.
Notation:
  `κ`: a map `ℕ → LayerScale`; a `LayerScale`: "The scales of one layer." (Inst/Model/Program.lean)
  `nf`: a `NormPar`, "exponent of the reciprocal; shift; constant" of a normalisation: of the final
    one (`nrmK`, Inst/Model/Program.lean).
  `tbG`: a map `ℕ → Tables`, "the lookup tables tbG of the 12 groups" (`LawfulK`).
  `LawfulK κ nf tbG`: a proposition, "The scales (κ, nf), with the lookup tables tbG of the 12
    groups, are valid." (Inst/Model/Scales.lean; what it asks: its fields).
  `ppref`: `Params`; the reference parameters (Inst/Model/Program.lean); `Layout.kRef`,
    `Layout.hRef`: natural numbers, "rows and columns of W: h; 2^k" (h is `hRef`, k is `kRef`:
    Inst/Model/Layout.lean).
  `W`: a `Mat` (`ℕ → ℕ → ℤ`); `Layout.weightsOf ppref kRef W`: "The weights that the layout reads
    from W." (Inst/Model/Layout.lean).
  `Layout.WFW ppref kRef W hRef` (W is well-formed): a proposition, "WF(i)" of
    Inst/Model/Layout.lean, on the ranges of the entries of W.
  g, l, s: natural numbers: a group of four layers ("Groups are counted from 0 here (g < 12; the
    first layer of group g is 4 g)": the comment at the top of Inst/Model/All/Trace.lean), a layer
    of the group, an index of the stream in the group (in `writableK`, s: an index counted in the
    whole model).
  `8 * g + s`, `4 * g + l`, `2 * l`: that index and that layer, counted in the whole model, and the
    index before layer l; `XK`, as `X` (both Inst/Model/Program.lean): "X_{2L} enters layer L,
    X_{2L+1} follows its attention block, X_{2L+2} follows its feed-forward block".
  the arguments 11 8: the last index of the last group: "x of the head is x8 of the last
    feed-forward segment" (the comment at the top of Inst/Model/All/Trace.lean).
  `cellW n a l`: an integer, "The widened cell rule: cell l of the value a in an array of n cells:
    balanced low bytes, and the rest in the top cell." (Inst/Model/Widened.lean).
Limits: this file says nothing on the chain, and no claim is made that any valid scales suit the
weights of any real model (that the reference scales are valid: `lawfulK_const`,
Inst/Model/All/NoWrapK.lean, under its hypothesis on the tables; where their numbers come from:
lean/CREDITS.md, section 8). (Compare the comment at the top of Inst/Model/FF/Scales.lean: "suits
the weights of any real model".)
-/
import Inst.Model.All.NoWrapK
import Inst.Model.Bound.AttK
import Inst.Model.Head.HonestN
import Inst.Model.FF.CastValid
import Inst.Model.Widened

set_option autoImplicit false

/- no default scales are in sight in this file: what reads scales says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Inst.Model.All

open Finset
open Layout (kRef hRef)

section Hon
variable (κ : ℕ → LayerScale)
  (nf : NormPar) (tbG : ℕ → Tables) (W : Mat) (prompt : Fin ppref.T → Fin ppref.V) (y : Head.Req)

/-- the program's stream at index s of group g -/
def xsK (g s : ℕ) : ℕ → Vec :=
  XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref kRef W) prompt (8 * g + s)
/-- the program's output of attention in layer l of group g -/
def osK (g l : ℕ) : ℕ → Vec :=
  Att.o (PG κ g l) (tbG g) (wOf W g l) (4 * g + l) (xsK κ tbG W prompt g (2 * l))

/-- The honest trace at the scales. -/
def honTK : Trace where
  ff := fun g =>
    FFSeg.hon (scl := SFK κ nf g) DF (tbG g) (wOf W g) (4 * g)
      (xsK κ tbG W prompt g) (osK κ tbG W prompt g)
  att := fun g =>
    AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g) (tbG g)
      (wOf W g) (4 * g) fun lam => xsK κ tbG W prompt g (2 * lam)
  hf := (Head.N.honCells nf (xsK κ tbG W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).hf
  hd := (Head.N.honCells nf (xsK κ tbG W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).hd
  hr := (Head.N.honCells nf (xsK κ tbG W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).hr

/-- x0 of a later group: the segment before writes what the rule of this segment writes. -/
theorem vFF_honTK (g : ℕ) :
    (honTK κ nf tbG W prompt y).vFF g =
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
    (honTK κ nf tbG W prompt y).vAtt g =
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

/-- x of the head: the last feed-forward segment writes what the rule of the head writes. -/
theorem vHead_honTK :
    (honTK κ nf tbG W prompt y).vHead =
      Head.N.honCells nf (xsK κ tbG W prompt 11 8) (Layout.weightsOf ppref kRef W).H y := by
  have hx : (honTK κ nf tbG W prompt y).vHead.x =
      (Head.N.honCells nf (xsK κ tbG W prompt 11 8) (Layout.weightsOf ppref kRef W).H y).x := by
    funext φ i
    show cellW 5 (xsK κ tbG W prompt 11 8 i (φ % 5120) - 0) (φ / 5120) =
      cellW 5 (xsK κ tbG W prompt 11 8 i (φ % 5120)) (φ / 5120)
    rw [sub_zero]
  show (⟨_, _, _, _⟩ : Head.Cells ℤ) = _
  rw [show (fun φ i => (honTK κ nf tbG W prompt y).ff (nGr - 1) ⟨.x8, φ / 5120, 0, φ % 5120, i⟩) = _
      from hx]
  rfl

variable {κ nf tbG W prompt y}

/-- under `hL`: the sizes and scales of a layer fit the attention segment of its group -/
theorem fitHK (hL : LawfulK κ nf tbG) {g : ℕ} (hg : g < nGr) (l : ℕ) :
    AttSeg.Hon.Fit (scl := SFK κ nf g) (DAK κ g) (PG κ g l) :=
  AttSeg.Hon.Fit.mk (scl := SFK κ nf g) (by decide : ppref.ch = AttSeg.Dim.ref.ch)
    (by decide : ppref.nq / ppref.nkv = AttSeg.Dim.ref.na) (by decide : 0 < AttSeg.Dim.ref.na)
    (rowsK hL hg l) (hL.one g hg (l % 4) (Nat.mod_lt _ (by norm_num)))

/-- Under `hL`: every value of the stream of a run can be written in five cells (indices s ≤ 96,
positions below 1,024, channels below 5,120): test (N1) (Inst/Model/Program.lean, `NORM.OK`) of the
normalisation that reads it bounds it. -/
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

/-- Under `hL`: the honest trace of the attention segment of a group satisfies its relation over the
integers, with small cells. -/
theorem attK {g : ℕ} (hg : g < nGr) :
    AttSeg.RFraw (scl := SFK κ nf g) (DAK κ g) (tbG g) ℤ
      (AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g)
        (tbG g) (wOf W g) (4 * g) fun lam => xsK κ tbG W prompt g (2 * lam)) ∧
    ∀ c : AttSeg.Raw, c.Valid (DAK κ g) →
      |AttSeg.Hon.honK (scl := SFK κ nf g) (DAK κ g) (fun lam => PG κ g lam) (fun _ => tbG g)
          (tbG g) (wOf W g) (4 * g) (fun lam => xsK κ tbG W prompt g (2 * lam)) c| ≤ 128 :=
  AttSeg.Hon.honestK (scl := SFK κ nf g)
    (wOf W g) (4 * g) _ (fitHK hL hg) (fun _ => rfl) (sizeOKK hL hg) (expTabK hL hg)

/-- Under `hL`: the outputs of attention in a group are at most 2,047 in absolute value (layers l <
4, positions below 1,024, channels below 5,120): the honest trace of the attention segment satisfies
its relation, and the relation bounds `out`, given that qry, key, val are at most 2,047 in absolute
value. -/
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

/-- Under `hL`, `hm`: the steps of a feed-forward segment lead from index to index of the program's
stream (`FFSeg.Runs`). -/
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

/-- Under `hL`, `hW`, `hm`, for every prime p: the honest trace of a group's feed-forward segment
satisfies its field relation, with cells of absolute value at most 128. -/
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

end Inst.Model.All
