-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/NoWrap.lean: a trace of the whole model and the program's stream, at the reference
parameters: the cells that two segments share (Part A), facts on the weights that a well-formed
matrix holds (Part B), and the stream (Part C).

Notation:
  `DF`, `DA`: `FFSeg.Dim.ref`, `AttSeg.Dim.ref`, the sizes at "the reference parameters"
    (Inst/Model/FF/Index.lean, Inst/Model/Att/Index.lean).
  x0, x8, xs; q, kx, v, o: arrays of a feed-forward segment (`FFSeg.Arr`, Inst/Model/FF/Index.lean):
    "xs holds the stream at the indices 1, .., 2 nl − 1; x0 and x8 hold it at the first and the last
    index".
  qry, key, val, out: arrays of an attention segment: "qry, key, val, out of the attention segment
    of group g are q, kx, v, o of the feed-forward segment of the group" (the comment at the top of
    Inst/Model/All/Trace.lean).
  g (in Part A also gr), l, s: natural numbers: a group of four layers ("Groups are counted from 0
    here (g < 12; the first layer of group g is 4 g)": the comment at the top of
    Inst/Model/All/Trace.lean), a layer of the group, an index of the stream in the group.
  in `idx_q` to `o_eq`, g, b, i, j, n, lam: natural numbers (Inst/Model/Att/Index.lean): "key/value
    heads g"; "pairs b = na λ + a of a layer λ of the segment and the number a of a query head among
    those of its key/value head"; "positions i, j"; "channels n"; lam: a layer λ of the segment.
  X (in Part A), inst, j, i: "the array, ..., the instance, the channel j and the position i" of an
    `FFSeg.Cell` (Inst/Model/FF/Index.lean); `X` in Part C: "The residual stream"
    (Inst/Model/Program.lean).
  `St T g s`: "the stream at index s of group g, as the trace holds it".
-/
import Inst.Model.All.Trace
import Inst.Model.All.Congr
import Inst.Model.Att.NoWrap2
import Inst.Model.Head.NoWrapProgram

set_option autoImplicit false

namespace Inst.Model.All

open Finset
open Layout (kRef hRef)

abbrev DF : FFSeg.Dim := FFSeg.Dim.ref
abbrev DA : AttSeg.Dim := AttSeg.Dim.ref

/-! ## Part A. The same cells. The docstrings of Parts A to C do not name the hypotheses on the
ranges of the indices (g, l, i, j, c, b, n, ..): see the statements. -/

theorem dF : DF.T = 1024 ∧ DF.d = 5120 ∧ DF.dq = 5120 ∧ DF.dkv = 1024 ∧ DF.nl = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem dA : DA.T = 1024 ∧ DA.ch = 128 ∧ DA.nG = 8 ∧ DA.nb = 20 ∧ DA.nl = 4 ∧ DA.na = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Trace
variable (T : Trace)

/-- the cells that the feed-forward segment of group g reads, as its relation and the statements on
it read them -/
def tR (g : ℕ) : FFSeg.Cell → ℤ := FFSeg.rd DF fun c => T.vFF g c.val

theorem tR_valid (g : ℕ) {c : FFSeg.Cell} (hc : c.Valid DF) : T.tR g c = T.vFF g c := by
  unfold tR FFSeg.rd
  rw [dif_pos hc]
  exact Int.cast_id

theorem val_tR (g : ℕ) {X : FFSeg.Arr} {inst j i : ℕ} (h1 : inst < X.cnt DF)
    (h2 : j < X.width DF) (h3 : i < DF.T) :
    FFSeg.val (T.tR g) X inst j i = FFSeg.val (T.vFF g) X inst j i := by
  unfold FFSeg.val
  rw [sum_congr rfl fun k hk => by
      rw [T.tR_valid g (c := ⟨X, k, inst, j, i⟩) ⟨mem_range.mp hk, h1, h2, h3⟩]]

theorem vFF_ne (g : ℕ) {c : FFSeg.Cell} (hc : c.X ≠ .x0) : T.vFF g c = T.ff g c := by
  unfold vFF
  rw [if_neg fun h => hc h.1]

/-- a value of an array other than x0 is read from the segment's own cells -/
theorem val_own (g : ℕ) {X : FFSeg.Arr} (hX : X ≠ .x0) {inst j i : ℕ} (h1 : inst < X.cnt DF)
    (h2 : j < X.width DF) (h3 : i < DF.T) :
    FFSeg.val (T.tR g) X inst j i = FFSeg.val (T.ff g) X inst j i := by
  rw [T.val_tR g h1 h2 h3]
  unfold FFSeg.val
  rw [sum_congr rfl fun k _ => by rw [T.vFF_ne g (c := ⟨X, k, inst, j, i⟩) hX]]

/-- x0 of the next group is x8 of this one. -/
theorem x0_succ (g : ℕ) {j i : ℕ} (hj : j < 5120) (hi : i < 1024) :
    FFSeg.xS DF (T.tR (g + 1)) 0 j i = FFSeg.xS DF (T.tR g) 8 j i := by
  show FFSeg.val (T.tR (g + 1)) .x0 0 j i = FFSeg.val (T.tR g) .x8 0 j i
  rw [T.val_tR (g + 1) (X := .x0) (by decide) hj hi,
    T.val_own g (X := .x8) (by decide) (by decide) hj hi]
  unfold FFSeg.val
  refine congrArg₂ _ (sum_congr rfl fun k _ => ?_) rfl
  unfold vFF
  rw [if_pos ⟨rfl, Nat.succ_pos g⟩]
  rfl

/-- x of the head is x8 of the last group. -/
theorem x_head {j i : ℕ} (hj : j < 5120) (hi : i < 1024) :
    Head.xv T.vHead j i = FFSeg.xS DF (T.tR 11) 8 j i := by
  show _ = FFSeg.val (T.tR 11) .x8 0 j i
  rw [T.val_own 11 (X := .x8) (by decide) (by decide) hj hi]
  unfold Head.xv Head.rd Head.bl FFSeg.val vHead Head.fX
  have e : ∀ l, (5120 * l + j) / 5120 = l ∧ (5120 * l + j) % 5120 = j :=
    fun l => by constructor <;> omega
  simp only [e]
  show _ = _ + (0 : ℤ)
  rw [add_zero]
  rfl

/-- the index of a channel of a query head -/
theorem idx_q {b g n : ℕ} (hb : b < 20) (hg : g < 8) (hn : n < 128) :
    DA.lamOf b < 4 ∧ DA.ch * DA.head g b + n < 5120 := by
  show b / 5 < 4 ∧ 128 * (5 * g + b % 5) + n < 5120
  constructor <;> omega

theorem idx_kv {g n : ℕ} (hg : g < 8) (hn : n < 128) : DA.ch * g + n < 1024 := by
  show 128 * g + n < 1024
  omega

private theorem two_cells (f : ℕ → ℤ) :
    (∑ k ∈ range 2, 256 ^ k * f k) =
      (∑ k ∈ range (FFSeg.Arr.nCell .q), 256 ^ k * f k) + (0 : ℤ) := by
  rw [add_zero]
  rfl

/-- qry, out, key, val are q, o, kx, v. -/
theorem qry_eq (gr : ℕ) {b g i n : ℕ} (hb : b < 20) (hg : g < 8) (hi : i < 1024) (hn : n < 128) :
    AttSeg.qryV (T.vAtt gr) b g i n =
      FFSeg.val (T.tR gr) .q (DA.lamOf b) (DA.ch * DA.head g b + n) i := by
  rw [T.val_own gr (X := .q) (by decide) (idx_q hb hg hn).1 (idx_q hb hg hn).2 hi]
  exact two_cells _

theorem out_eq (gr : ℕ) {b g i n : ℕ} (hb : b < 20) (hg : g < 8) (hi : i < 1024) (hn : n < 128) :
    AttSeg.outV (T.vAtt gr) b g i n =
      FFSeg.val (T.tR gr) .o (DA.lamOf b) (DA.ch * DA.head g b + n) i := by
  rw [T.val_own gr (X := .o) (by decide) (idx_q hb hg hn).1 (idx_q hb hg hn).2 hi]
  exact two_cells _

theorem key_eq (gr : ℕ) {lam g j n : ℕ} (hl : lam < 4) (hg : g < 8) (hj : j < 1024) (hn : n < 128) :
    AttSeg.keyV (T.vAtt gr) lam g j n = FFSeg.val (T.tR gr) .kx lam (DA.ch * g + n) j := by
  rw [T.val_own gr (X := .kx) (by decide) hl (idx_kv hg hn) hj]
  exact two_cells _

theorem val_eq (gr : ℕ) {lam g j n : ℕ} (hl : lam < 4) (hg : g < 8) (hj : j < 1024) (hn : n < 128) :
    AttSeg.valV (T.vAtt gr) lam g j n = FFSeg.val (T.tR gr) .v lam (DA.ch * g + n) j := by
  rw [T.val_own gr (X := .v) (by decide) hl (idx_kv hg hn) hj]
  exact two_cells _

/-- every channel of o is a channel of out -/
theorem o_eq (gr : ℕ) {l c i : ℕ} (hl : l < 4) (hc : c < 5120) (hi : i < 1024) :
    ∃ b g n, b < 20 ∧ g < 8 ∧ n < 128 ∧ DA.lamOf b = l ∧ DA.ch * DA.head g b + n = c ∧
      FFSeg.val (T.tR gr) .o l c i = AttSeg.outV (T.vAtt gr) b g i n := by
  have hb : 5 * l + c / 128 % 5 < 20 := by omega
  have hg : c / 128 / 5 < 8 := by omega
  have hn : c % 128 < 128 := by omega
  have e1 : DA.lamOf (5 * l + c / 128 % 5) = l := by
    show (5 * l + c / 128 % 5) / 5 = l
    omega
  have e2 : DA.ch * DA.head (c / 128 / 5) (5 * l + c / 128 % 5) + c % 128 = c := by
    show 128 * (5 * (c / 128 / 5) + (5 * l + c / 128 % 5) % 5) + c % 128 = c
    omega
  refine ⟨5 * l + c / 128 % 5, c / 128 / 5, c % 128, hb, hg, hn, e1, e2, ?_⟩
  rw [T.out_eq gr hb hg hi hn, e1, e2]

end Trace

/-! ## Part B. Facts on the weights of a well-formed matrix -/

/-- the weights of layer l of group g -/
abbrev wOf (W : Mat) (g : ℕ) : ℕ → LayerW := fun l => Layout.layerOf ppref kRef W (4 * g + l)

section Facts
variable {tb : Tables} {W : Mat} {tok : ℕ → ℕ} (htb : tb.OK ppref)
  (hW : Layout.WFW ppref kRef W hRef) (htok : ∀ i, tok i < ppref.V)

include htb hW htok in
theorem setting {g : ℕ} (hg : g < nGr) : FFSeg.Spec.Setting tb W (4 * g) tok :=
  ⟨htb, hW, by omega, by
    show 4 * g + 4 ≤ 48
    unfold nGr at hg
    omega, htok⟩

include hW in
theorem wf_idx : (Layout.weightsOf ppref kRef W).WF ppref := (Layout.Bridge.indexOf W hW).property

include hW in
theorem abs_H (j v : ℕ) : |(Layout.weightsOf ppref kRef W).H j v| ≤ 2 ^ 12 := by
  have := (wf_idx hW).2.2 j v
  rw [abs_le]
  split_ifs at this
  · constructor <;> omega
  · rw [this]
    norm_num

/-! ## Part C. The stream -/

/-- the stream at index s of group g, as the trace holds it -/
abbrev St (T : Trace) (g s : ℕ) : ℕ → Vec := FFSeg.stream DF (T.tR g) s

theorem Agree.trans {P : Params} {a b c : ℕ → Vec} (h1 : Agree P a b) (h2 : Agree P b c) :
    Agree P a c :=
  fun i hi j hj => (h1 i hi j hj).trans (h2 i hi j hj)

theorem layer_eq {L : ℕ} (hL : L < 48) :
    (Layout.weightsOf ppref kRef W).layer L = Layout.layerOf ppref kRef W L :=
  if_pos hL

theorem X_even (i : Weights) (prompt : Fin ppref.T → Fin ppref.V) {n : ℕ} (hn : n % 2 = 0) :
    X ppref tb i prompt (n + 1) =
      Att.x' ppref tb (i.layer (n / 2)) (n / 2) (X ppref tb i prompt n) := if_pos hn

theorem X_odd (i : Weights) (prompt : Fin ppref.T → Fin ppref.V) {n : ℕ} (hn : ¬ n % 2 = 0) :
    X ppref tb i prompt (n + 1) =
      FF.x'' ppref tb (i.layer (n / 2)) (n / 2) (X ppref tb i prompt n) := if_neg hn

end Facts

theorem tokOf_lt (prompt : Fin ppref.T → Fin ppref.V) (i : ℕ) : tokOf prompt i < ppref.V := by
  unfold tokOf
  split
  · exact (prompt _).isLt
  · decide

end Inst.Model.All
