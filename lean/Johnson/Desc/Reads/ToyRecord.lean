-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Reads/ToyRecord.lean: a record of the first chain (here and below: the state that the
verifier carries along that chain, `S`, Johnson/Desc/First/State.lean, a part of it, or the plan's
value of such a part; no out-of-domain sample), laid by hand, at which all premises of
`runIs_at_twelve` (Johnson/Desc/Reads/RunIsLean.lean) and of `head_at`
(Johnson/Desc/Reads/HeadAtRecord.lean) hold together.

All of this file is a toy. The record is of no run and of no fold: its points are made up, its
ledger shows 0 under every number, its tables are what the description's own text makes of these
points.

Why. The two theorems stand under many premises. Without an object that meets them all, they might
say nothing.

What is here. The head's public numbers are `hR` of Johnson/Desc/Kinds/Law/K07MemberAt.lean, typed
after the stored full-size example. That they are that example's is held by an evaluation alone, by
no theorem; a theorem says that nine of the numbers are those at which the library's head is written
(`hR_full`): see that file's head. It bears on nothing that is proved here. The lookup's points are
made up, as the same file has them (`zxR`, `zkR`).
  `gT`: the lookup's record: these points, a largest table of 2 ^ 10 rows, and two points of 15
    coordinates on the planes.
  `LT`: a layout: the sizes of `NumH`; six calls, each with the kind's own number of coordinates on
    its columns; the two segments that the text asks for, in calls 2 and 5.
  `bT`, `hpT`: a border and a plan: the list `matsH` of eight matrices, the list of tables open, and
    60,531 reads.
  `xT`: what was heard: the lookup's record; the last 16 coordinates of its point; points of 10, 23,
    10, 10, 10 and 13 coordinates; two made-up pairs (the fields gp and omV).
  `s0`, `covT`, `tT`, `sT`: the record without tables; its covered positions; the tables that the
    text makes; the record with these tables and with the closed list in its record of the smallness
    test.
  `ZT`: the filling: the public table of the tables is `tT`'s.
  `cov_ok`, `made_ok`, `letters_ok`: the three texts say yes at the toy.
  `toy_lies`: **`Lies ZT sT …`: the record lies as Johnson/Desc/Reads/HeadAtRecord.lean asks.**
  `toy_public`: the public premises of `foldFits_at` at the toy.
  `toy_runIs`: **`RunIs` holds at the toy**, by `runIs_at_twelve`.
  `toy_foldFits`: **`FoldFits` has a member**, by `foldFits_at`.
  `tab_is`, `seat_is`, `toy_count`, `toy_close`, `toy_ne`, `toy_sane`: the table of the tables that
    the text makes, row by row; what the seat finds in it; the letters are sane.
  `toy_head`: **`HeadClaimW ZT.letters`: the statement at the head, with the clause on the weights,
    has a member at the letters filled from the record**, by `head_at`.

Four facts are decided by the kernel's evaluation of the description's own texts at the toy (`decide
+kernel`): the three texts say yes, and the table of the tables.

Limits. The reads' quiet step itself says no at the toy's plan: the plan's record of the smallness
test holds no shape for its eight matrices (read off the step's text; no statement here shows it).
So the toy does not lie behind a yes of that step: what the step would lay is laid by hand. The
layout's numbers of coordinates on the columns are the kind's by the toy's definition: so the
premise hJ is met here and shown of no real layout. `ZT.AtClose` holds of every record that lies so,
not of the toy's alone. The relation in front of the smallness test's round is met by nothing here.
Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadAtRecord
import Johnson.Desc.Kinds.Law.K07MemberAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat.Toy

open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork)
open OnBytes.Model.Head (Shape HL Border HPlanH2 Covered Tables matsH callNo)
open OnBytes.Road.Hd (NumH)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.K07Real (hR co zxR zyR zkR)
open VerifiableInference.Reads.AtHead

/-- An answer that is there is the answer. -/
theorem ok_of_isSome {α : Type} {x : Except String α} (d : α) (h : x.toOption.isSome = true) :
    x = .ok (x.toOption.getD d) := by
  cases x with
  | error e => cases h
  | ok a => rfl

/-- The lookup's record. -/
def gT : OnBytes.Model.Forest.Heard :=
  { shape := { kT := 10 }, leaves := {}, zx := zxR, zy := zyR
    zk := #[zkR 0, zkR 1, zkR 2, zkR 3, zkR 4, zkR 5]
    zb0 := ⟨(List.range 15).map co⟩, zb1 := ⟨(List.range 15).map co⟩ }

/-- A call of the layout: the kind's own number of coordinates on its columns. -/
def callT (q : ℕ) (segs : List OnBytes.Model.Seg) : OnBytes.Model.CallD :=
  { name := "", kind := "", segs := segs, J := 0
    lJ := (letI := sizesOf hR; lJ (OnBytes.Model.Head.keyFloor hR) (callKeys q)), used := #[] }

/-- The layout. -/
def LT : HL :=
  { m := 65536, k := 4816, mD := 16384, kD := 640, mR := 8192, kR := 15, kb := 1
    calls := #[callT 0 [], callT 1 [], callT 2 [{ name := "ROW", n := 0, pos := #[] }],
      callT 3 [], callT 4 [], callT 5 [{ name := "CNF", n := 0, pos := #[] }]] }

/-- The border of the stream's matrix. -/
def bT : Border := { mxb := 65536, kxb := 400, off := 0, nl := 5, cnt := 1, J := 5120 }

/-- The plan. -/
def hpT : HPlanH2 :=
  { tl := { mats := matsH hR LT bT 0 0, NM := 8 }, Fp := {}, Tp := {}, nU := #[0, 0, 60531] }

/-- n made-up coordinates. -/
def pts (n : ℕ) : Point := ⟨(List.range n).map co⟩

/-- What was heard. -/
def xT : OnBytes.Model.Head.Heard :=
  { VerifiableInference.Desc.First.blankHeard with
    g1 := gT, Zl := Point.last zxR 16, PV := pts 10, gp := #[oneE, co 1], omV := #[oneE, co 2]
    wpl := { r := pts 23 }, tV := { r := pts 10 }, tN := { r := pts 10 }, tH := { r := pts 10 }
    rs := pts 13 }

/-- A ledger that shows 0 under each of 64 numbers, with one array of 60,531 columns. -/
def FT : Fork :=
  { trees := #[{ R := 1, K := 60531 }], ns := 64, vp := Array.replicate 64 zeroE
    gotF := Array.replicate 64 true }

/-- The request's words: 1,024 tokens 0; the first covered position 0; the position behind the last
1,023. -/
def reqT : Array UInt32 := ⟨List.replicate 1024 0 ++ [0, 1023]⟩

/-- The head's part of the record. -/
def ownT (t : Option Tables) (tl : OnBytes.Model.HTailF2) : HeadOwn :=
  { fr := S.blank.check.frame, kept := #[], ids := #[], L := { check := S.blank.check }, F := FT
    tl := tl, Fm := {}, opened := true, lookHeard := some gT, x := some xT, t := t
    squaresP := some {} }

/-- The record, with what is handed in for the tables and the smallness test's record. -/
def recT (t : Option Tables) (tl : OnBytes.Model.HTailF2) : S :=
  { S.blank with
    failed := none
    req := reqT
    out := { S.blank.out with reply := some (E.mk3 0 0 0) }
    here := .head (ownT t tl) }

/-- The record without tables. -/
def s0 : S := recT none {}

/-- Its covered positions. -/
def covT : Covered := ((s0.covered hR.T hR.V).toOption).getD default

/-- The tables that the text makes. -/
def tT : Tables := ((ReadsQuiet.tables hR LT hpT covT xT).toOption).getD {}

/-- The record's record of the smallness test: the plan's, with the closed list. -/
def tlT : OnBytes.Model.HTailF2 := { hpT.tl with funClosed := true, funs := tT.funs }

/-- The record. -/
def sT : S := recT (some tT) tlT

/-- The filling. -/
def ZT : Fill :=
  { h := hR, L := LT, b := bT, hp := hpT, iU3 := 0, work := 0, cols := 60531, tab := tT.tab }

set_option maxRecDepth 100000 in
theorem cov_some : (s0.covered hR.T hR.V).toOption.isSome = true := by decide +kernel

theorem cov_ok : sT.covered hR.T hR.V = .ok covT := ok_of_isSome default cov_some

set_option maxRecDepth 100000 in
theorem made_some : (ReadsQuiet.tables hR LT hpT covT xT).toOption.isSome = true := by
  decide +kernel

theorem made_ok : ReadsQuiet.tables hR LT hpT covT xT = .ok tT :=
  ok_of_isSome ({} : Tables) made_some

set_option maxRecDepth 100000 in
theorem letters_some : (lettersAt (parOf hR 0) (seatAt hR 0) sT).toOption.isSome = true := by
  decide +kernel

theorem letters_ok : ∃ g bh pl, lettersAt (parOf hR 0) (seatAt hR 0) sT = .ok (g, bh, pl) := by
  cases h : lettersAt (parOf hR 0) (seatAt hR 0) sT with
  | error e =>
    have h' := letters_some
    rw [h] at h'
    cases h'
  | ok a => exact ⟨a.1, a.2.1, a.2.2, rfl⟩

/-- **The record lies as Johnson/Desc/Reads/HeadAtRecord.lean asks.** -/
theorem toy_lies : ∃ g bh pl, Lies ZT sT (ownT (some tT) tlT) covT xT tT g bh pl := by
  obtain ⟨g, bh, pl, hl⟩ := letters_ok
  exact ⟨g, bh, pl,
    { here := rfl, opened := rfl, covered := cov_ok, heard := rfl, made := made_ok, laid := rfl
      cols := ⟨_, rfl, rfl⟩, mats := rfl, funs := rfl, nm := rfl, letters := hl, tab := rfl
      hX1 := rfl, hX2 := rfl, hqH := by decide, hqN := by decide, hsPV := by decide
      hsSq := by decide, hsTV := by decide, hsTH := by decide, hzb0 := by decide
      hzb1 := by decide }⟩

/-- The public premises of foldFits_at, at the toy. -/
theorem toy_public :
    NumH hR LT ∧ (∃ gid sid, hpT.tl.mats = matsH hR LT bT gid sid) ∧ hpT.tl.NM = 8 ∧ hR.la = 16 ∧
    (∀ q, q < 6 → (LT.calls.getD q default).lJ =
      (letI := sizesOf hR; lJ (OnBytes.Model.Head.keyFloor hR) (callKeys q))) ∧
    (∀ q, q < 6 → hR.ls ≤ (LT.calls.getD q default).lJ) ∧
    (∀ seg q, callNo LT seg = some q → q < 6) ∧
    hR.ls ≤ (letI := sizesOf hR; Norm.lNI + Norm.lPd) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨0, 0, rfl⟩, rfl, rfl,
    fun q hq => ?_, fun q hq => ?_, fun seg q hq => ?_, by decide⟩
  · interval_cases q <;> rfl
  · interval_cases q <;> decide
  · obtain ⟨h, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hq
    exact h

/-- **RunIs holds at the toy.** -/
theorem toy_runIs : ∃ (g : Given) (bh : Behind),
    @RunIs g.sizes g.request g.normIn bh.norm bh.final bh.head
      ⟨hR, LT, bT, hpT, covT, xT, tT, 0⟩ := by
  obtain ⟨g, bh, pl, Q⟩ := toy_lies
  obtain ⟨-, -, -, -, hJ, hlsJ, hc6, hls⟩ := toy_public
  exact ⟨g, bh, runIs_at_twelve (g := g) (bh := bh) hR LT bT hpT 0 0 sT _ covT xT tT Q.here
    Q.opened Q.covered Q.heard Q.made Q.hX1 Q.hX2 Q.letters hJ hlsJ hc6 Q.hqH Q.hqN Q.hsPV Q.hsSq
    Q.hsTV Q.hsTH hls⟩

/-- **FoldFits has a member.** -/
theorem toy_foldFits : ∃ A, FoldFits ZT.letters sT A tT := by
  obtain ⟨g, bh, pl, Q⟩ := toy_lies
  obtain ⟨hN, hm, hNM, hla, hJ, hlsJ, hc6, hls⟩ := toy_public
  exact foldFits_at ZT hN hm hNM hla hJ hlsJ hc6 hls Q

/-! ## The statement at the head has a member at the record's letters -/

set_option maxRecDepth 100000 in
/-- The table of the tables that the text makes. -/
theorem tab_is : tT.tab =
    [("hf@Z", 0, 19264), ("hf@phiZ", 19264, 19264), ("xbL@Z_V", 38528, 400),
      ("xbL@Y_N", 38928, 400), ("hd@zt_FC", 39328, 10240), ("hd@r_H", 49568, 10240),
      ("hr@zt_ROW", 59808, 120), ("hr@P_V", 59928, 120), ("hr@r_tV", 60048, 120),
      ("hr@rt_N", 60168, 120), ("hr@phiC", 60288, 120), ("hr@rhoC", 60408, 120),
      ("bH-bits-0", 60528, 1), ("bH-bits-1", 60529, 1), ("bH-pin", 60530, 1)] := by
  decide +kernel

/-- What the seat finds under a read's name. -/
theorem seat_is (r : Head.Read) :
    (ZT.seat.first r).isSome = true ∧
      ZT.seat.count r = (match r with
        | .wideAtKeys => 19264 | .wideAtCosts => 19264 | .actAtLogits => 10240
        | .rowAtCosts => 120 | .rowCount => 120) := by
  have e1 : ZT.seat.first r = (tT.tab.find? fun e => e.1 == nameH r).map (·.2.1) := rfl
  have e2 : ZT.seat.count r = ((tT.tab.find? fun e => e.1 == nameH r).map (·.2.2)).getD 0 := rfl
  rw [e1, e2, tab_is]
  cases r <;> decide

/-- Every use's index lies below the length of its read's table. -/
theorem toy_count : ∀ u : Use, u ∈ (letI := sizesOf hR; usesH) →
    (letI := sizesOf hR; u.index) < ZT.seat.count u.read := by
  intro u hu
  rcases mem_usesH (iS := sizesOf hR) hu with ⟨cl, x, l, rfl, hl⟩ | ⟨l, blk, rfl, hl, hb⟩
  · have key : x.number.digits.1 + x.bytes.2 ≤ 21 := by cases x <;> decide
    have hc : ZT.seat.count (Use.read (.byte cl x l)) = 120 := by
      cases cl <;> exact (seat_is _).2
    rw [hc]
    show NR + x.number.digits.1 + l < 120
    have hN : NR = 99 := rfl
    omega
  · have hb' : blk < 202048 / 64 := hb
    rw [show ZT.seat.count (Use.read (.ex l blk)) = 19264 from (seat_is .wideAtCosts).2]
    show (4 * 5120 + (3 + l) * 202048) / 64 + blk < 19264
    omega

/-- The record lies so. -/
theorem toy_close : ZT.AtClose sT := by
  obtain ⟨g, bh, pl, Q⟩ := toy_lies
  exact ⟨_, _, _, _, g, bh, pl, Q⟩

/-- The part in U3 of the form mean is not the zero form. -/
theorem toy_ne :
    u3Value OnBytes.Model.Reading.gl.val ZT.seat.iU3 ZT.seat.cols (ZT.letters.form sT .B2)
      (fun p => if p = ZT.seat.start .rowCount + (NR + 0) then 1 else 0) ≠ 0 := by
  have e := (u3Value_part (ρ := OnBytes.Model.Reading.gl) ZT.seat.iU3 ZT.seat.cols
    (fun p => if p = ZT.seat.start .rowCount + (NR + 0) then 1 else 0)
    (ZT.letters.form sT .B2)).trans
    (mean_part (iS := ZT.letters.sizes) (iP := ZT.letters.policy) (iR := ZT.letters.request sT)
      OnBytes.Model.Reading.gl ZT.seat
      (fun p => if p = ZT.seat.start .rowCount + (NR + 0) then 1 else 0))
  refine ne_of_eq_of_ne e ?_
  rw [bytesAt_ind, bytesAt_ind, bytesAt_ind, if_pos (by decide), if_neg (by decide),
    if_neg (by decide)]
  simp

theorem toy_sane : ZT.letters.Sane :=
  ⟨fun r => (seat_is r).1, toy_public.1,
    ⟨List.cons_ne_nil _ _, fun _ _ => ⟨sT, toy_close, ZT.letters.form sT .B2,
      List.mem_cons.2 (Or.inl rfl),
      fun p => if p = ZT.seat.start .rowCount + (NR + 0) then 1 else 0, toy_ne⟩⟩,
    ⟨OnBytes.Model.Reading.gl, rfl⟩⟩

/-- **The statement at the head has a member at the letters filled from the record.** -/
theorem toy_head : HeadClaimW ZT.letters := by
  obtain ⟨-, hm, hNM, hla, hJ, hlsJ, hc6, hls⟩ := toy_public
  exact head_at ZT toy_sane hm hNM hla hJ hlsJ hc6 hls (by decide) rfl rfl rfl rfl toy_count

end VerifiableInference.Reads.AtSeat.Toy

#print axioms VerifiableInference.Reads.AtSeat.Toy.ok_of_isSome
#print axioms VerifiableInference.Reads.AtSeat.Toy.cov_some
#print axioms VerifiableInference.Reads.AtSeat.Toy.cov_ok
#print axioms VerifiableInference.Reads.AtSeat.Toy.made_some
#print axioms VerifiableInference.Reads.AtSeat.Toy.made_ok
#print axioms VerifiableInference.Reads.AtSeat.Toy.letters_some
#print axioms VerifiableInference.Reads.AtSeat.Toy.letters_ok
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_lies
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_public
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_runIs
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_foldFits
#print axioms VerifiableInference.Reads.AtSeat.Toy.tab_is
#print axioms VerifiableInference.Reads.AtSeat.Toy.seat_is
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_count
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_close
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_ne
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_sane
#print axioms VerifiableInference.Reads.AtSeat.Toy.toy_head
