-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/HearShape.lean: THE SMALLNESS TEST, ITS FIRST HALF (the draw of the matrix):
THE DECISION's GUARDS AS ONE Bool AND ONE UPDATE ON A SHAPE WITHOUT A DRAWN OR SENT VALUE. General
laws: nothing is evaluated.

The decision's eight tests read flags, counts and public numbers of the carried record alone, and
the library has them as a proposition, both ways (decide_atS_iff,
Johnson/Desc/First/K8/HearMeans.lean). Here the same as code on a small shape.

  DrawSh, drawSh  what the decision reads and lays of the smallness test's record: the list of
                  tables is closed; the number of drawn entries; the count of draws; the number of
                  matrices; their columns and rows; the number of combinations; the tables' shapes;
                  each matrix's first column. The drawn entries themselves (-1, 0, 1) are left out:
                  their number alone is kept.
  drawB           THE ONE Bool: of the place's numbers, the count of batched rows that are owed, and
                  the shape.
  drawU           THE ONE UPDATE: the number of entries of the round, and the first columns, laid.
  **draw_iff**    the decision says yes on one round if and only if the Bool accepts; then the state
                  behind is the state in front with the round's entries and the first columns laid
                  into the record.
  drawSh_laid     that record's shape is the update of the shape in front.
  drawB_open, drawB_twice   with no link open, and with entries drawn already, the Bool rejects.

Here the Bool is necessary and sufficient. The decision has no test on values.
Limits. The number of the round's entries is a letter here: that it is columns x tau is asked by the
frame in front of the decision (Block.step), not by the decision. BEHIND A YES ON A ROUND OF NO
ENTRIES THE SHAPE PASSES drawB AGAIN: drawU lays the round's number of entries and leaves the count
of draws. The shape of the whole carried record is not made here. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.First.K8.HearMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- What the draw's decision reads and lays of the smallness test's record. -/
abbrev DrawSh : Type :=
  Bool × Nat × Nat × Nat × List Nat × List Nat × Nat × List (Nat × Nat × Nat) × List Nat

namespace DrawSh
def mk (closed : Bool) (entries draws matrices : Nat) (ks ms : List Nat) (tau : Nat)
    (tabs : List (Nat × Nat × Nat)) (firsts : List Nat) : DrawSh :=
  (closed, entries, draws, matrices, ks, ms, tau, tabs, firsts)
def closed (t : DrawSh) : Bool := t.1
def entries (t : DrawSh) : Nat := t.2.1
def draws (t : DrawSh) : Nat := t.2.2.1
def matrices (t : DrawSh) : Nat := t.2.2.2.1
def ks (t : DrawSh) : List Nat := t.2.2.2.2.1
def ms (t : DrawSh) : List Nat := t.2.2.2.2.2.1
def tau (t : DrawSh) : Nat := t.2.2.2.2.2.2.1
def tabs (t : DrawSh) : List (Nat × Nat × Nat) := t.2.2.2.2.2.2.2.1
def firsts (t : DrawSh) : List Nat := t.2.2.2.2.2.2.2.2
end DrawSh

def drawSh (tl : HTailF2) : DrawSh :=
  DrawSh.mk tl.funClosed tl.cfF.size tl.foldDrawn tl.NM (tl.mats.toList.map (·.k))
    (tl.mats.toList.map (·.m)) tl.tau (tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start))
    tl.cfFirst.toList

/-- **THE ONE Bool.** owed: the count of batched rows that are owed; t: the record's shape, where a
link is open. -/
def drawB (p : Par) (owed : Option Nat) (t : Option DrawSh) : Bool :=
  t.any fun t => t.closed && (owed == none || owed == some 0) && t.entries == 0 && t.draws == 0 &&
    t.matrices == p.ks.length && t.ks == p.ks && t.ms == p.ms && t.tau == p.tau && t.tabs == tabs p

/-- **THE ONE UPDATE.** n: the number of the round's entries. -/
def drawU (p : Par) (n : Nat) (t : DrawSh) : DrawSh :=
  DrawSh.mk t.closed n t.draws t.matrices t.ks t.ms t.tau t.tabs (firstColumns p).toList

/-- The record behind a yes has the update's shape. -/
theorem drawSh_laid (p : Par) (tl : HTailF2) (trits : List Int) :
    drawSh { tl with cfF := trits.toArray, cfFirst := firstColumns p } =
      drawU p trits.length (drawSh tl) := rfl

/-- **The decision says yes on one round if and only if the Bool accepts**, and what lies behind. -/
theorem draw_iff {Cl : Type} (p : Par) (s s' : S) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' ↔
      drawB p s.rowsOwed (s.tl?.map drawSh) = true ∧
      ∃ tl, s.tl? = some tl ∧
        s' = s.putTl { tl with cfF := r.drawn.trits.toArray, cfFirst := firstColumns p } := by
  rw [decide_atS_iff]
  constructor
  · rintro ⟨tl, ht, a1, a2, ⟨a3, a3'⟩, a4, a5, a7, a6, a8, e⟩
    refine ⟨?_, tl, ht, e⟩
    rw [ht]
    show (tl.funClosed && (s.rowsOwed == none || s.rowsOwed == some 0) && tl.cfF.size == 0 &&
      tl.foldDrawn == 0 && tl.NM == p.ks.length && tl.mats.toList.map (·.k) == p.ks &&
      tl.mats.toList.map (·.m) == p.ms && tl.tau == p.tau &&
      (tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) == tabs p) = true
    rw [a1, a3, a3', a4, a5, a7, a6, a8]
    rcases a2 with a2 | a2 <;> rw [a2] <;> simp
  · rintro ⟨hb, tl, ht, e⟩
    rw [ht] at hb
    have hb' : (tl.funClosed && (s.rowsOwed == none || s.rowsOwed == some 0) && tl.cfF.size == 0 &&
      tl.foldDrawn == 0 && tl.NM == p.ks.length && tl.mats.toList.map (·.k) == p.ks &&
      tl.mats.toList.map (·.m) == p.ms && tl.tau == p.tau &&
      (tl.funs.toList.map fun Fn => (Fn.mat, Fn.len, Fn.start)) == tabs p) = true := hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hb'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a3'⟩, a4⟩, a5⟩, a7⟩, a6⟩, a8⟩ := hb'
    exact ⟨tl, ht, a1, a2, ⟨a3, a3'⟩, a4, a5, a7, a6, a8, e⟩

/-- With no link open the Bool rejects. -/
theorem drawB_open (p : Par) (owed : Option Nat) : drawB p owed none = false := rfl

/-- With entries drawn already (t.entries ≠ 0) the Bool rejects. -/
theorem drawB_twice (p : Par) (owed : Option Nat) (t : DrawSh) (h : t.entries ≠ 0) :
    drawB p owed (some t) = false := by
  have e : (t.entries == 0) = false := by simpa using h
  show (t.closed && (owed == none || owed == some 0) && t.entries == 0 && t.draws == 0 &&
    t.matrices == p.ks.length && t.ks == p.ks && t.ms == p.ms && t.tau == p.tau &&
    t.tabs == tabs p) = false
  rw [e]
  simp

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.drawSh_laid
#print axioms VerifiableInference.Desc.First.K8.draw_iff
#print axioms VerifiableInference.Desc.First.K8.drawB_open
#print axioms VerifiableInference.Desc.First.K8.drawB_twice
#print axioms VerifiableInference.Desc.First.K8.DrawSh
#print axioms VerifiableInference.Desc.First.K8.DrawSh.mk
#print axioms VerifiableInference.Desc.First.K8.DrawSh.closed
#print axioms VerifiableInference.Desc.First.K8.DrawSh.entries
#print axioms VerifiableInference.Desc.First.K8.DrawSh.draws
#print axioms VerifiableInference.Desc.First.K8.DrawSh.matrices
#print axioms VerifiableInference.Desc.First.K8.DrawSh.ks
#print axioms VerifiableInference.Desc.First.K8.DrawSh.ms
#print axioms VerifiableInference.Desc.First.K8.DrawSh.tau
#print axioms VerifiableInference.Desc.First.K8.DrawSh.tabs
#print axioms VerifiableInference.Desc.First.K8.DrawSh.firsts
#print axioms VerifiableInference.Desc.First.K8.drawSh
#print axioms VerifiableInference.Desc.First.K8.drawB
#print axioms VerifiableInference.Desc.First.K8.drawU
