-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchFitLit.lean: a member of the premise `Fit` at each written record of a code switch:
a frame, numbers and records of the kept members at which the names of the switch's two maps lie in
the tables of the record's sending.

The caller of the laws on the kept messages at a record (`selAt`, Johnson/Top/H/SwitchAtRow.lean)
takes a frame W, numbers num and records plOf of the kept members under the premise `Fit`
(Johnson/Top/H/SwitchMapsFit.lean: fifteen comparisons of public numbers). If no letters met it,
every statement at that caller would speak of nothing. `fit_of_check`
(Johnson/Top/H/SwitchMapsCheck.lean) gives `Fit` at a frame that the program's routine `switchFrame`
returns behind the yes of the program's test `switchTargetCheck` (OnBytes/Iop/Cs.lean), under five
further premises, shown there at no value. Here all are met at each written record
(Johnson/Top/H0/K2Caller/Lit.lean), by one test with code that Lean's kernel evaluates. Definitions,
statements and proofs.
Main names:
  `stAt r`, `oldAt r`, `tgtAt r`, `anewAt r`: what the two routines are called at, MADE HERE OF THE
    RECORD: a statement with the record's codes and, as its oracle messages, the shapes of the list
    in front, a message's number being its place; single rows with the first member's main code,
    the rider's mask code, two mask rows, the record's kept places and their rows' number; the
    target by the rule of the program's `reqGroupAt` (OnBytes/Iop/Req.lean): the first sent shape,
    row 0 for the main row's message, row 1 for the rest, the kept members' shapes; new numbers
    behind the list.
  `plAt r i`, `numAt r a`: the record of kept member number i in the frame; a kept member's number:
    its place in the record's list of kept places. `numAt_inj`.
  `fitB r`: the test, nine clauses: the program's test says yes; the program's routine returns a
    frame; the two codes are the stage's; the kept members' numbers are the record's; the message
    1 + i of the sending has the shape of the target's kept member i; the count of kept rows; each
    frame record's rows are its member's; a kept member's rows are at least as long as the main row.
  `fitB_full`, `fitB_small`: it says yes at each of the 25 and the 5 written records.
  `fitB_no_first`, `fitB_no_swap`, `fitB_no_more`: controls: it says no with the first sent message
    struck out; with two kept places in the other order (12 records keep two); with one place more
    among the kept.
  `fit_at`: `Fit` from the test's yes. **`fit_full`**, `fit_small`: at each written record, at every
    t₀, oM, oZ.
Limits: THE FRAME IS THE PROGRAM's ROUTINE's AT VALUES MADE HERE, NOT THE FRAME OF A RUN: in a run
the oracle messages have the chain's running numbers, the statement holds more than shapes, and the
single rows come out of a fold. Of these a frame's fields that `Fit` reads take the codes, the
shapes, the number of mask rows, the kept members in order and their rows (by reading
`switchFrame`, `switchParts`, `SwitchPlaces.make`; no theorem says it). At the last record of each
table nothing is kept: there the clauses on kept members ask nothing. The records are written
numbers (Lit.lean's limits). Nothing on soundness.

-/
import Johnson.Top.H.SwitchAtRow
import Johnson.Top.H.SwitchMapsCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc.First.K2Caller

/-- A statement of the program, made of the record: its codes; its oracle messages are those of the
list in front, with their shapes and nothing else; the number of a message is its place. -/
def stAt (r : SwRow) : Statement :=
  { codes := r.cs, oracles := (r.lo.map fun x => ({ shape := x.1 } : Oracle)).toArray }

/-- The number of the main code of the first member in front. -/
def codeIx (r : SwRow) : ℕ := ((r.lo.find? fun x => x.1.mainRows != 0).map (·.1.code)).getD noId

/-- Single rows, as far as a frame reads them: the two codes' numbers, two mask rows, the kept
members' numbers, the number of kept rows. -/
def oldAt (r : SwRow) : SingleRows :=
  { code := codeIx r, maskCode := r.rider.maskCode
    layout := { members := r.kept.toArray, kept := (r.kept.map fun _ => true).toArray }
    masks := 2, keptRows := r.keptRows }

/-- The target, by the rule of the program's `reqGroupAt`: the first sent message's shape; its first
row takes the main row's message, its second the rest; the kept members' shapes. -/
def tgtAt (r : SwRow) : SwitchTarget :=
  { shape := (r.l.headD default).1, main := ⟨.main, 0, 0⟩, rest := ⟨.main, 0, 1⟩
    kept := (r.kept.map fun i => ({ shape := (r.lo.getD i default).1 } : KeptTarget)).toArray }

/-- The numbers of the messages that take the kept members: behind g, in order. -/
def anewAt (r : SwRow) : Array ℕ := ((List.range r.kept.length).map (r.lo.length + 1 + ·)).toArray

/-- The record of the kept member number i in the frame that the program makes of these. -/
def plAt (r : SwRow) (i : ℕ) : KeptPlace :=
  { old := (switchKept (oldAt r)).getD i noId, anew := (anewAt r).getD i noId
    rows := ((stAt r).oracles.getD ((switchKept (oldAt r)).getD i noId) default).shape.mainRows
    rowBits := (stAt r).rowBits ((switchKept (oldAt r)).getD i noId) .main
    pad := padOf (stAt r) ((switchKept (oldAt r)).getD i noId)
    oldPadAt := (switchParts (stAt r) (oldAt r)).oldPadAt.getD i 0 }

/-- A kept member's number in the frame: its place in the record's list of kept places. -/
def numAt (r : SwRow) (a : {a // r.kp a}) : ℕ := r.kept.idxOf a.1.1.val

/-- **The test.** -/
def fitB (r : SwRow) : Bool :=
  switchTargetCheck (stAt r) (oldAt r) (tgtAt r) &&
  (switchFrame (stAt r) (oldAt r) (tgtAt r) r.lo.length (anewAt r)).isSome &&
  decide ((r.cs.base[codeIx r]?).map codeOf = some (stageOf r.g 0).C) &&
  decide ((r.cs.mask[r.rider.maskCode]?).map codeOf = some (stageOf r.g 0).Z) &&
  decide (switchKept (oldAt r) = r.kept.toArray) &&
  ((List.range r.kept.length).all fun i =>
    decide ((r.l[1 + i]?).map (·.1) = ((tgtAt r).kept[i]?).map (·.shape))) &&
  decide (r.keptRows = (((List.range r.kept.length).map (plAt r)).map (·.rows)).sum) &&
  ((List.range r.kept.length).all fun i =>
    decide ((plAt r i).rows = ((r.lo[r.kept.getD i 0]?).map (·.1.mainRows)).getD 0)) &&
  ((List.range r.kept.length).all fun i =>
    decide ((r.cs.base.getD (codeIx r) default).ell ≤
      (r.cs.base.getD ((stAt r).oracles.getD (plAt r i).old default).shape.code default).ell))

set_option maxRecDepth 1000000 in
theorem fitB_full : (tableFullLit.all fitB) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem fitB_small : (tableSmallLit.all fitB) = true := by decide +kernel

/-- What its yes says. -/
structure FitOK (r : SwRow) : Prop where
  check : switchTargetCheck (stAt r) (oldAt r) (tgtAt r) = true
  frame : (switchFrame (stAt r) (oldAt r) (tgtAt r) r.lo.length (anewAt r)).isSome = true
  main : (r.cs.base[codeIx r]?).map codeOf = some (stageOf r.g 0).C
  mask : (r.cs.mask[r.rider.maskCode]?).map codeOf = some (stageOf r.g 0).Z
  kept : switchKept (oldAt r) = r.kept.toArray
  copy : ∀ i, i < r.kept.length →
    (r.l[1 + i]?).map (·.1) = ((tgtAt r).kept[i]?).map (·.shape)
  sum : r.keptRows = (((List.range r.kept.length).map (plAt r)).map (·.rows)).sum
  rows : ∀ i, i < r.kept.length →
    (plAt r i).rows = ((r.lo[r.kept.getD i 0]?).map (·.1.mainRows)).getD 0
  long : ∀ i, i < r.kept.length → (r.cs.base.getD (codeIx r) default).ell ≤
    (r.cs.base.getD ((stAt r).oracles.getD (plAt r i).old default).shape.code default).ell

theorem fitB_says {r : SwRow} (h : fitB r = true) : FitOK r := by
  unfold fitB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j⟩

/-- A kept member's number is below the number of kept places, and names its place. -/
theorem numAt_lt (r : SwRow) (a : {a // r.kp a}) : numAt r a < r.kept.length :=
  List.idxOf_lt_length_iff.2 a.2

theorem numAt_get (r : SwRow) (a : {a // r.kp a}) : r.kept.getD (numAt r a) 0 = a.1.1.val := by
  rw [List.getD_eq_getElem _ _ (numAt_lt r a)]
  exact List.getElem_idxOf (numAt_lt r a)

/-- Two kept members with one number are one. -/
theorem numAt_inj (r : SwRow) (a a' : {a // r.kp a}) (h : numAt r a = numAt r a') : a = a' := by
  have e : a.1.1.val = a'.1.1.val := by rw [← numAt_get r a, ← numAt_get r a', h]
  exact Subtype.ext (Subtype.ext (Fin.ext e))

section
variable (r : SwRow) (H : r.OK) (K : FitOK r) (t₀ : ℕ) (oM oZ : Fin r.lo.length → ℕ)

include K in
/-- **`Fit` at the record**: at the frame W that the program's `switchFrame` returns at the values
made above, the kept members numbered by their places in the record's list, each with its record in
that frame. -/
theorem fit_at : ∃ W, switchFrame (stAt r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W ∧
    Fit r.cs r.l (stageOf r.g t₀) W
      (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r))
      (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp)
      (slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
        fun a => plAt r (numAt r a)) := by
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.1 K.frame
  obtain ⟨f1, f2, -, -, -, -, -, f8⟩ := frame_fields _ _ _ _ _ W hW
  have hsz : (switchKept (oldAt r)).size = r.kept.length := by rw [K.kept]; rfl
  have f8' : W.kept = (List.range r.kept.length).map (plAt r) := by rw [f8, hsz]; rfl
  have f1' : r.cs.base[codeIx r]? = some W.code := f1
  have f2' : r.cs.mask[r.rider.maskCode]? = some W.zk := f2
  have g0 : 0 < r.l.length := List.length_pos_iff.2 H.ne
  have hhead : ∀ (l : List (OracleShape × ℕ)) (g0 : 0 < l.length),
      (l.get ⟨0, g0⟩).1 = (l.headD default).1 := by
    intro l g0
    cases l with
    | nil => cases g0
    | cons x xs => rfl
  refine ⟨W, hW, fit_of_check (stAt r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) W hW K.check r.l
    g0 (hhead r.l g0) ?_ (stageOf r.g t₀) ?_ ?_ _ _ _ ?_ ?_ ?_ ?_⟩
  · intro i hi
    have hi' : i < r.kept.length := by
      have : (tgtAt r).kept.size = r.kept.length := by simp [tgtAt]
      omega
    have h := K.copy i hi'
    rw [Array.getElem?_eq_getElem hi, Option.map_some] at h
    obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hl, e2⟩ := List.getElem?_eq_some_iff.1 hx
    exact ⟨hl, by show (r.l[1 + i]).1 = _; rw [e2, e]⟩
  · have h := K.main
    rw [f1', Option.map_some] at h
    exact (Option.some.inj h).symm
  · have h := K.mask
    rw [f2', Option.map_some] at h
    exact (Option.some.inj h).symm
  · intro κ
    show W.kept[numAt r κ.1]? = some (plAt r (numAt r κ.1))
    rw [f8', List.getElem?_map, List.getElem?_range (numAt_lt r κ.1)]
    rfl
  · intro κ
    show κ.2.val < (plAt r (numAt r κ.1)).rows
    rw [K.rows _ (numAt_lt r κ.1), numAt_get, List.getElem?_eq_getElem κ.1.1.1.isLt]
    exact κ.2.isLt
  · show r.keptRows = _
    rw [f8']
    exact K.sum
  · intro κ
    have h := K.long _ (numAt_lt r κ.1)
    have e : r.cs.base.getD (codeIx r) default = W.code := by
      rw [Array.getD_eq_getD_getElem?, f1']
      rfl
    rw [e] at h
    exact h

end

/-- **At each of the 25 written records of the full example `Fit` has a member.** -/
theorem fit_full (r : SwRow) (H : r.OK) (hr : r ∈ tableFullLit) (t₀ : ℕ)
    (oM oZ : Fin r.lo.length → ℕ) :
    ∃ W, switchFrame (stAt r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W ∧
      Fit r.cs r.l (stageOf r.g t₀) W
        (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r))
        (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp)
        (slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
          fun a => plAt r (numAt r a)) :=
  fit_at r H (fitB_says (List.all_eq_true.1 fitB_full r hr)) t₀ oM oZ

/-- **At each of the 5 written records of the small example.** -/
theorem fit_small (r : SwRow) (H : r.OK) (hr : r ∈ tableSmallLit) (t₀ : ℕ)
    (oM oZ : Fin r.lo.length → ℕ) :
    ∃ W, switchFrame (stAt r) (oldAt r) (tgtAt r) r.lo.length (anewAt r) = some W ∧
      Fit r.cs r.l (stageOf r.g t₀) W
        (slotNum r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp (numAt r))
        (slotRow r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp)
        (slotPl r.cs r.lo r.mem (stageOf r.g t₀) r.rad oM oZ (H.hM t₀) (H.hZ t₀) r.kp
          fun a => plAt r (numAt r a)) :=
  fit_at r H (fitB_says (List.all_eq_true.1 fitB_small r hr)) t₀ oM oZ

/-! ### The test can say no -/

set_option maxRecDepth 1000000 in
/-- A control: with the first sent message struck out the test says no at each record: what then
stands first is not a target's shape. -/
theorem fitB_no_first : (tableFullLit.all fun r => !fitB { r with l := r.l.tail }) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the two kept places in the other order the test says no at each record that
keeps two: the copies then have the wrong shapes. There are such records. -/
theorem fitB_no_swap :
    ((tableFullLit.filter fun r => r.kept.length == 2).all fun r =>
      !fitB { r with kept := r.kept.reverse }) = true ∧
    (tableFullLit.filter fun r => r.kept.length == 2).length = 12 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the message number 0 of the list in front laid among the kept places as well,
the test says no at each record. -/
theorem fitB_no_more : (tableFullLit.all fun r =>
    !fitB { r with kept := r.kept ++ [0] }) = true := by decide +kernel

end Johnson.G

#print axioms Johnson.G.fit_full
#print axioms Johnson.G.fit_small
#print axioms Johnson.G.fitB_no_first
#print axioms Johnson.G.fitB_no_swap
#print axioms Johnson.G.fitB_no_more
#print axioms Johnson.G.fitB_says
#print axioms Johnson.G.numAt_inj
#print axioms Johnson.G.fit_at
#print axioms Johnson.G.fitB_full
#print axioms Johnson.G.fitB_small
