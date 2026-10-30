-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatFitsPlan.lean: the code switch: "THE SEATS FIT" AT THE SWITCH's TWO
TYPED LISTS, FROM THE NAMED TEST THAT THE COMPOSED MEANING's HEAD ALREADY HOLDS, AND ONE NEW TEST
WITH CODE. A law file; no running text imports it.

The head's structure PlanOk (Johnson/P5J/PlanOk.lean) has the field
  fit : P5T.seatsFitP G cs ps = true      (Johnson/P5T/MembersPlain.lean)
"no entry of the plan's seats with a sample has a fault at its (tree, tenant)", and the table's
numbers are made of these very entries (Johnson/P5T/NumbersOf.lean: `numbersOf ps`): `sent m t` and
`keptOf m` are the seats of two filters of ps. So at a seat of these two lists the seven clauses
hold AT THE ENTRY's OWN SHAPE. WHAT IS LEFT IS THAT THE TYPED LIST HAS THAT SHAPE AT THAT PLACE.

  `newAt ps m`, `sent_is`     the entries behind `(numbersOf ps).sent m 0`; that they are: by rfl.
  `keptAtP ps m`, `keptOf_is`   the entries behind `(numbersOf ps).keptOf m`; the like.
  `fit_at`          what the head's test says of one entry with a sample.
  `shapesNewB ps m l`    THE NEW TEST, first half: the typed list's shapes are, by place, those of a
                    first stretch of `newAt ps m`.
  `shapesKeptB ps m lo kept`   second half: the kept members' shapes are, by place, those of
                    `keptAtP ps m`, and there are as many.
  `seatFits_new`    SeatFits G cs l seatN, at seatN i := ((numbersOf ps).sent m 0).getD i (0, 0).
  `seatFitOne_kept`  SeatFitOne G cs lo seat i AT EVERY KEPT MEMBER i, at
                    seat i := ((numbersOf ps).keptOf m).getD (kept.idxOf i) (0, 0).
  `seats25B ps cs rows`, `seats25_says`   both halves and "the row's codes are the plan's", at each
                    row of a list: row number m is the switch that spends "carry m", into group m +
                    1.
  `faults25`        the same as a report: which rows fail, and in which of the three clauses.
  Behind the theorems: tests at made entries, by evaluation (#guard).
AT A MEMBER OF lo THAT IS NOT KEPT NOTHING IS SAID: there the caller's seat is a stand-in (0, 0),
and SeatFits over all of lo may be false.
Limits. BOTH YESES ARE PREMISES HERE. The new test's value at the written full size, by Lean's
kernel: SeatFitsFull.lean. `shapesNewB` accepts any FIRST STRETCH of the entries, the empty list
too: a yes alone does not say that l is the whole sending. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Caller.SeatFitsB
import Johnson.Top.H0.K2Caller.LitRows
import Johnson.P5T.MembersPlain
import Johnson.P5T.NumbersOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (FileDescription seatFaultAt)
open VerifiableInference.Desc.Sound (SeatFits)
open P5T (PSeat numbersOf seatsFitP keyOf)

/-- The entries behind `(numbersOf ps).sent m 0`. -/
def newAt (ps : List PSeat) (m : ℕ) : List PSeat :=
  ps.filter fun p => p.seg == some (m, 0) && p.smpd && !p.isStart

theorem sent_is (ps : List PSeat) (m : ℕ) :
    (numbersOf ps).sent m 0 = (newAt ps m).map (·.seat) := rfl

/-- The entries behind `(numbersOf ps).keptOf m`. -/
def keptAtP (ps : List PSeat) (m : ℕ) : List PSeat :=
  let next := (ps.filter fun p => p.seg == some (m + 1, 0)).filterMap fun p =>
    match p.role with
    | .kept l k => some ((0, l, k) : Nat × Nat × Nat)
    | _ => none
  ps.filter fun p => p.seg.map (·.1) == some m && p.smpd && !p.isStart && next.contains (keyOf p)

theorem keptOf_is (ps : List PSeat) (m : ℕ) :
    (numbersOf ps).keptOf m = (keptAtP ps m).map (·.seat) := rfl

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) {ps : List PSeat}

/-- What the head's test says of one entry with a sample. -/
theorem fit_at (h : seatsFitP G cs ps = true) {p : PSeat} (hp : p ∈ ps) (hs : p.smpd = true) :
    seatFaultAt G cs "" p.shape p.seat.1 p.seat.2 = none :=
  Option.isNone_iff_eq_none.1
    (List.all_eq_true.1 h p (List.mem_filter.2 ⟨hp, hs⟩))

theorem newAt_mem {m : ℕ} {p : PSeat} (h : p ∈ newAt ps m) : p ∈ ps ∧ p.smpd = true := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  simp only [Bool.and_eq_true] at h2
  exact ⟨h1, h2.1.2⟩

theorem keptAtP_mem {m : ℕ} {p : PSeat} (h : p ∈ keptAtP ps m) : p ∈ ps ∧ p.smpd = true := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 h
  simp only [Bool.and_eq_true] at h2
  exact ⟨h1, h2.1.1.2⟩

end

/-- **The new test, first half**: the typed list's shapes are, by place, those of a first stretch of
the entries. -/
def shapesNewB (ps : List PSeat) (m : ℕ) (l : List (OnBytes.OracleShape × ℕ)) : Bool :=
  decide (l.map (·.1) = ((newAt ps m).map (·.shape)).take l.length)

/-- **Second half**: the kept members' shapes are, by place, the entries'. -/
def shapesKeptB (ps : List PSeat) (m : ℕ) (lo : List (OnBytes.OracleShape × ℕ)) (kept : List ℕ) :
    Bool :=
  decide (kept.map (fun i => (lo[i]?).map (·.1)) = (keptAtP ps m).map fun p => some p.shape)

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) {ps : List PSeat}

/-- **The seats fit at the list that the switch sends.** -/
theorem seatFits_new (hfit : seatsFitP G cs ps = true) {m : ℕ}
    {l : List (OnBytes.OracleShape × ℕ)} (hs : shapesNewB ps m l = true)
    (seatN : Fin l.length → ℕ × ℕ)
    (hN : ∀ i : Fin l.length, seatN i = ((numbersOf ps).sent m 0).getD i.val (0, 0)) :
    SeatFits G cs l seatN :=
  seatFits_of_noFault G cs l seatN fun i => by
    have e := of_decide_eq_true hs
    have e1 : (l.map (·.1))[i.val]? = some (l.get i).1 := by
      rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt]
      rfl
    rw [e, List.getElem?_take_of_lt i.isLt, List.getElem?_map] at e1
    obtain ⟨p, hp, e2⟩ := Option.map_eq_some_iff.1 e1
    have hm := newAt_mem (List.mem_of_getElem? hp)
    have e3 : seatN i = p.seat := by
      rw [hN i, sent_is, List.getD_eq_getElem?_getD, List.getElem?_map, hp]
      rfl
    rw [e3, ← e2]
    exact fit_at G cs hfit hm.1 hm.2

/-- **The seven clauses at every kept member of the list in front.** -/
theorem seatFitOne_kept (hfit : seatsFitP G cs ps = true) {m : ℕ}
    {lo : List (OnBytes.OracleShape × ℕ)} {kept : List ℕ} (hs : shapesKeptB ps m lo kept = true)
    (seat : Fin lo.length → ℕ × ℕ) (i : Fin lo.length) (hi : i.val ∈ kept)
    (hS : seat i = ((numbersOf ps).keptOf m).getD (kept.idxOf i.val) (0, 0)) :
    SeatFitOne G cs lo seat i :=
  seatFitOne_of_noFault G cs lo seat i (by
    have e := of_decide_eq_true hs
    have ha : kept.idxOf i.val < kept.length := List.idxOf_lt_length_iff.2 hi
    have e1 : (kept.map fun j => (lo[j]?).map (·.1))[kept.idxOf i.val]? =
        some (some (lo.get i).1) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem ha, List.getElem_idxOf ha]
      show some ((lo[i.val]?).map (·.1)) = _
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    rw [e, List.getElem?_map] at e1
    obtain ⟨p, hp, e2⟩ := Option.map_eq_some_iff.1 e1
    have hm := keptAtP_mem (List.mem_of_getElem? hp)
    have e3 : seat i = p.seat := by
      rw [hS, keptOf_is, List.getD_eq_getElem?_getD, List.getElem?_map, hp]
      rfl
    rw [e3, ← Option.some.inj e2]
    exact fit_at G cs hfit hm.1 hm.2)

end

/-- **Both halves, and "the row's codes are the plan's", at each row of a list.** Row number m is
the switch that spends "carry m", into group m + 1. -/
def seats25B (ps : List PSeat) (cs : OnBytes.Codes) (rows : List SwRow) : Bool :=
  rows.zipIdx.all fun x =>
    decide (x.1.cs = cs) && shapesNewB ps (x.2 + 1) x.1.l && shapesKeptB ps x.2 x.1.lo x.1.kept

/-- The same as a report: the rows that fail, each with its three clauses' values. -/
def faults25 (ps : List PSeat) (cs : OnBytes.Codes) (rows : List SwRow) :
    List (ℕ × Bool × Bool × Bool) :=
  (rows.zipIdx.map fun x => (x.2, decide (x.1.cs = cs), shapesNewB ps (x.2 + 1) x.1.l,
    shapesKeptB ps x.2 x.1.lo x.1.kept)).filter fun y => !(y.2.1 && y.2.2.1 && y.2.2.2)

theorem seats25_says {ps : List PSeat} {cs : OnBytes.Codes} {rows : List SwRow}
    (h : seats25B ps cs rows = true) {m : ℕ} {r : SwRow} (hr : rows[m]? = some r) :
    r.cs = cs ∧ shapesNewB ps (m + 1) r.l = true ∧ shapesKeptB ps m r.lo r.kept = true := by
  have h1 := List.all_eq_true.1 h (r, m) (List.mem_zipIdx_iff_getElem?.2 hr)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

/-- **At a row of the list: both sentences, in the caller's letters.** -/
theorem seats_at_row {Xi : Type} (G : FileDescription Xi) {ps : List PSeat} {cs : OnBytes.Codes}
    {rows : List SwRow} (hfit : seatsFitP G cs ps = true) (h : seats25B ps cs rows = true) {m : ℕ}
    {r : SwRow} (hr : rows[m]? = some r) :
    SeatFits G r.cs r.l (fun i => ((numbersOf ps).sent (m + 1) 0).getD i.val (0, 0)) ∧
      ∀ i : Fin r.lo.length, i.val ∈ r.kept →
        SeatFitOne G r.cs r.lo
          (fun i => ((numbersOf ps).keptOf m).getD (r.kept.idxOf i.val) (0, 0)) i := by
  obtain ⟨e, h1, h2⟩ := seats25_says h hr
  rw [e]
  exact ⟨seatFits_new G cs hfit h1 _ fun _ => rfl,
    fun i hi => seatFitOne_kept G cs hfit h2 _ i hi rfl⟩

/-! ## Tests at made entries, by evaluation -/

namespace ToyP
open P5T

def shA : OnBytes.OracleShape := { code := 0, mainRows := 1, mainDeg := 1, maskRows := 0 }
def shB : OnBytes.OracleShape := { code := 0, mainRows := 2, mainDeg := 1, maskRows := 0 }
def shM : OnBytes.OracleShape := { mainRows := 0, maskRows := 1, answers := 0 }

/-- Segment 0 sends A (its message 0) and B (its message 1) at its moment 1; segment 1's first
sending: the carried message, a copy of segment 0's message 1, and a mask without a sample. -/
def ps : List PSeat :=
  [⟨"a", 0, some (0, 1), 0, 0, 0, shA, .own 0⟩, ⟨"b", 0, some (0, 1), 1, 0, 1, shB, .own 1⟩,
   ⟨"c", 1, some (1, 0), 0, 1, 0, shA, .carried⟩, ⟨"k", 1, some (1, 0), 1, 1, 1, shB, .kept 0 1⟩,
   ⟨"m", 1, some (1, 0), 2, 2, 0, shM, .mask⟩]

-- the list that the switch sends: the carried message and the copy, by place
#guard shapesNewB ps 1 [(shA, 0), (shB, 0)]
-- a first stretch of it
#guard shapesNewB ps 1 [(shA, 0)]
-- the two in the other order; a third member (the mask has no sample: it is no entry of the filter)
#guard !shapesNewB ps 1 [(shB, 0), (shA, 0)]
#guard !shapesNewB ps 1 [(shA, 0), (shB, 0), (shM, 0)]
-- another segment
#guard !shapesNewB ps 2 [(shA, 0)]
-- what is kept of segment 0: its message 1, which stands at place 1 of the list in front
#guard (numbersOf ps).keptOf 0 == [(0, 1)]
#guard shapesKeptB ps 0 [(shA, 0), (shB, 0)] [1]
-- the other member; no member; a place outside the list
#guard !shapesKeptB ps 0 [(shA, 0), (shB, 0)] [0]
#guard !shapesKeptB ps 0 [(shA, 0), (shB, 0)] []
#guard !shapesKeptB ps 0 [(shA, 0), (shB, 0)] [7]

end ToyP

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seatFits_new
#print axioms VerifiableInference.Desc.First.K2Caller.seatFitOne_kept
#print axioms VerifiableInference.Desc.First.K2Caller.seats25_says
#print axioms VerifiableInference.Desc.First.K2Caller.seats_at_row
