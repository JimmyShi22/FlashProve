-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KeysIff.lean

The lookup's clause at attention, both ways, at any cells: "every key of the four key vectors kvA,
a term of this library over the verifier's records, lies in the verifier's own table of its call"
if and only if "every looked-up value of the library's attention segment, in a piece, is an entry
of the library's table at the letters made from the shape". Over the protocol's field, for every
reading cell of the names of OnBytes/Tie/Pv/Lookup/Ends/A.lean: no integers are asked.

Main definitions and theorems:
* "callsC S fs cell": the letters of the lookup's calls ("CallsAt", Lane5Split.lean) at a reading
  cell. "callsA_eq": callsA S fs Z (Lane5BridgeA.lean) is callsC S fs (cellZ Z), by rfl.
* "KeysC S cell": the library's clause on looked-up values at the trace tC S cell, over the
  protocol's field.
* "TabsEq S fs": the verifier's table of call c is the library's table at the letters made from the
  shape (the shift and the table of exponentials are the shape's own; that these exponentials are
  the library's is another premise: ExpP, Lane5SeamCheck.lean [not in this library]; a theorem at S
  = 12 and rx = 8: exp_of_hid, Lane5AttHid.lean): as many rows; row by row, between
  integers; the pieces fit into the call; the padding row is a row. "InsideA S cs": no piece of call
  q reaches behind the library's "used q". Public. Premises here; theorems at what the verifier's
  shapeHid returns, at the reference numbers (CfRef), kFD = 16, S = 12, rx = 8 and the call list of
  four lines with one shift (tabsEq_of_usual, inside_of_four, Lane5AttTabsEq.lean); as tests with
  their theorems: "tabsEqB", "tabsEq_of_test", "insideB", "inside_of_test"; the runs:
  Lane5KvWit.lean.
* **"keys_iff"**: under NumsA, LaidA, TabsEq, InsideA: (callsC S fs cell).InTables ↔ KeysC S cell.
* "keys_iff_of_tests": the same from the tests.

How, from right to left: a key in a piece is the library's looked-up value (kvA_eq_keyVecC); a key
behind the pieces is the call's padding row, which is row t0 of its table.

What the clause weighs. kvA (OnBytes/Tie/Pv/Lookup/Ends/A.lean) is a term written for this library
over the verifier's records; the verifier holds no key vector. The keys of calls 1 and 2 are
formed from products of cells: the scores (query times key) and the accumulators (softmax weight
times value; denominator times output). So "every call's keys lie in its table", at kvA, holds all
of attention's products, and the part without the lookup clause is thin: small cells, index bits,
the row maximum, the denominator. The equivalence moves that weight; it does not carry it.
-/
import Johnson.Road.Lane5KvCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (Shape ACall)
open Inst.Model.AttSeg

/-- **The letters of the lookup's calls at attention, at a reading of the cells.** -/
def callsC (S : Shape) (fs : Model.Forest.Shape) (cell : NameA → Cb.Gl.E) : CallsAt where
  NC := 4
  n := fun c => (S.calls.getD c default).call.n
  k := fun c => kN fs c
  K := fun c => kvA S fs cell c
  T := fun c u => ((tauN fs c u : ℕ) : Cb.Gl.E)

theorem callsA_eq (S : Shape) (fs : Model.Forest.Shape) (Z : Zs) :
    callsA S fs Z = callsC S fs (cellZ Z) := rfl

/-- **The library's clause on looked-up values, at a reading of the cells.** -/
def KeysC (S : Shape) (cell : NameA → Cb.Gl.E) : Prop :=
  ∀ (c : Fin 4) (Y : ℕ), Y < (dimOf S).used c →
    keyVec (scl := sclOf S) (dimOf S) (tbOf S) (tC S cell) c Y ∈
      lutSet (lut (scl := sclOf S) (dimOf S) (tbOf S) c)

/-- **The verifier's tables are the library's, at the letters made from the shape.** Public. -/
structure TabsEq (S : Shape) (fs : Model.Forest.Shape) : Prop where
  rows : ∀ c : Fin 4, (lut (scl := sclOf S) (dimOf S) (tbOf S) c).rows = 2 ^ kN fs c.val
  row : ∀ (c : Fin 4) (u : ℕ), u < 2 ^ kN fs c.val →
    ((tauN fs c.val u : ℕ) : ℤ) = (lut (scl := sclOf S) (dimOf S) (tbOf S) c).row u
  room : ∀ c : Fin 4, (dimOf S).used c ≤ 2 ^ (S.calls.getD c.val default).call.n
  pad : ∀ c : Fin 4, t0N fs c.val < 2 ^ kN fs c.val

/-- **No piece reaches behind the library's "used".** Public. -/
def InsideA (S : Shape) (cs : Fin 4 → ACall) : Prop :=
  ∀ q : Fin 4, ∀ p ∈ (cs q).pcs.toList, p.off + 2 ^ p.b ≤ (dimOf S).used q

/-- **The lookup's clause at attention, both ways.** -/
theorem keys_iff {S : Shape} (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs)
    {fs : Model.Forest.Shape} (T : TabsEq S fs) (hin : InsideA S cs) (cell : NameA → Cb.Gl.E) :
    (callsC S fs cell).InTables ↔ KeysC S cell := by
  constructor
  · intro I c Y hY
    obtain ⟨u, hu, e⟩ := I c.val c.isLt Y (lt_of_lt_of_le hY (T.room c))
    have e1 : kvA S fs cell c.val Y = ((tauN fs c.val u : ℕ) : Cb.Gl.E) := e
    refine ⟨u, by rw [T.rows c]; exact hu, ?_⟩
    rw [← kvA_eq_keyVecC N L fs cell c Y hY, e1, ← T.row c u hu, Int.cast_natCast]
  · intro H c hc X _
    by_cases hX : X < (dimOf S).used ⟨c, hc⟩
    · obtain ⟨ι, hι, e⟩ := H ⟨c, hc⟩ X hX
      rw [T.rows ⟨c, hc⟩] at hι
      refine ⟨ι, hι, ?_⟩
      show kvA S fs cell c X = ((tauN fs c ι : ℕ) : Cb.Gl.E)
      have e2 := kvA_eq_keyVecC N L fs cell ⟨c, hc⟩ X hX
      have e3 := T.row ⟨c, hc⟩ ι hι
      rw [e, ← e3, Int.cast_natCast] at e2
      exact e2
    · refine ⟨t0N fs c, T.pad ⟨c, hc⟩, ?_⟩
      show kvA S fs cell c X = ((tauN fs c (t0N fs c) : ℕ) : Cb.Gl.E)
      rw [kvA_eq S fs cell c (cs ⟨c, hc⟩) (L.isCall ⟨c, hc⟩)]
      apply pwVec_outside
      intro p hp hXp
      have := hin ⟨c, hc⟩ p hp
      omega

/-! ## The two further premises as tests -/

/-- TabsEq, line by line. -/
def tabsEqB (S : Shape) (fs : Model.Forest.Shape) : Bool :=
  tabsB S fs && (List.finRange 4).all fun c => decide (t0N fs c.val < 2 ^ kN fs c.val)

theorem tabsEq_of_test {S : Shape} {fs : Model.Forest.Shape} (h : tabsEqB S fs = true) :
    TabsEq S fs := by
  simp only [tabsEqB, tabsB, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun c => (h1 c (List.mem_finRange c)).1.1,
    fun c u hu => (h1 c (List.mem_finRange c)).1.2 u hu,
    fun c => (h1 c (List.mem_finRange c)).2, fun c => h2 c (List.mem_finRange c)⟩

/-- InsideA at cs q := call number q, line by line. -/
def insideB (S : Shape) : Bool :=
  (List.finRange 4).all fun q => (callAt S q.val).pcs.toList.all fun p =>
    decide (p.off + 2 ^ p.b ≤ (dimOf S).used q)

theorem inside_of_test {S : Shape} (h : insideB S = true) :
    InsideA S fun q : Fin 4 => callAt S q.val := by
  simp only [insideB, List.all_eq_true, decide_eq_true_eq] at h
  exact fun q p hp => h q (List.mem_finRange q) p hp

/-- **The lookup's clause at attention, both ways, from the tests.** -/
theorem keys_iff_of_tests {S : Shape} {fs : Model.Forest.Shape} (h1 : numsB S = true)
    (h2 : laidB S = true) (h3 : tabsEqB S fs = true) (h4 : insideB S = true)
    (cell : NameA → Cb.Gl.E) : (callsC S fs cell).InTables ↔ KeysC S cell :=
  keys_iff (numsA_of_numsB h1) (laidA_of_laidB h2) (tabsEq_of_test h3) (inside_of_test h4) cell

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.keys_iff
#print axioms OnBytes.Road.L5.tabsEq_of_test
#print axioms OnBytes.Road.L5.inside_of_test
#print axioms OnBytes.Road.L5.keys_iff_of_tests
