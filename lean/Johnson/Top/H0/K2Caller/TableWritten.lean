-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TableWritten.lean: code switching: A NAMED TEST WITH CODE ON THE THREE
PUBLIC FILES: THE TYPED TABLE OF THE SWITCHES THAT IS MADE OF THE FILES (tableOf,
K2Caller/Table.lean) IS THE WRITTEN ONE (tableFullLit, K2Caller/LitRows.lean); and what its accept
gives. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY A TEST AND NO THEOREM. tableOf reads the three files anew by two roads that no pinned value
holds: the planner's sizes at the files' own digest, and the second reading's rows
(Johnson.G.sendRowsOf). The closed facts on the 25 typed rows are all shown at tableFullLit, by
Lean's kernel. To spend them at the row ProofFile.rowAtK2 pol lay KL m
(Johnson/Desc/ProofFile/CarryAt.lean) the two tables must be one.
  swSampleB · swSamplesB · swRowB · swRowsB   equality as Bools, field by field, with their
                    laws (SwRow and SampleSize bear no decidable equality here; none is derived, so
                    that no instance's name is declared twice beside another file's)
  tableWrittenB     THE TEST
  tableWritten_is   its accept: tableOf pol lay KL = .ok tableFullLit
  tableWritten_says its accept: ProofFile.rowAtK2 pol lay KL m = tableFullLit[m]? at every m
LIMITS. A NAMED TEST, NOT A THEOREM, AND NOT A TEST THAT THE VERIFIER RUNS. NOT EVALUATED HERE. The
full size alone. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.Table
import Johnson.Top.H0.K2Caller.LitRows
import Johnson.Desc.ProofFile.CarryAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

def swSampleB (a b : SampleSize) : Bool :=
  decide (a.cubeBits = b.cubeBits) && decide (a.groups = b.groups)

theorem swSampleB_eq {a b : SampleSize} (h : swSampleB a b = true) : a = b := by
  unfold swSampleB at h
  rw [Bool.and_eq_true] at h
  cases a
  cases b
  simp only [SampleSize.mk.injEq]
  exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩

def swSamplesB : List SampleSize → List SampleSize → Bool
  | [], [] => true
  | a :: l, b :: m => swSampleB a b && swSamplesB l m
  | _, _ => false

theorem swSamplesB_eq : ∀ {l m : List SampleSize}, swSamplesB l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    unfold swSamplesB at h
    rw [Bool.and_eq_true] at h
    rw [swSampleB_eq h.1, swSamplesB_eq h.2]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- Two typed rows are one, field by field. -/
def swRowB (a b : SwRow) : Bool :=
  decide (a.set = b.set) && decide (a.cs = b.cs) && decide (a.lo = b.lo) && decide (a.g = b.g) &&
    decide (a.rad = b.rad) && decide (a.l = b.l) && swSamplesB a.o b.o &&
    decide (a.roots = b.roots) && decide (a.kept = b.kept) && decide (a.rider = b.rider)

theorem swRowB_eq {a b : SwRow} (h : swRowB a b = true) : a = b := by
  unfold swRowB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  cases a
  cases b
  simp only [SwRow.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, swSamplesB_eq h7, h8, h9, h10⟩

def swRowsB : List SwRow → List SwRow → Bool
  | [], [] => true
  | a :: l, b :: m => swRowB a b && swRowsB l m
  | _, _ => false

theorem swRowsB_eq : ∀ {l m : List SwRow}, swRowsB l m = true → l = m
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    unfold swRowsB at h
    rw [Bool.and_eq_true] at h
    rw [swRowB_eq h.1, swRowsB_eq h.2]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- **The test**: the table that is made of the three public files is the written one. -/
def tableWrittenB (pol lay KL : ByteArray) : Bool :=
  match tableOf pol lay KL with
  | .ok t => swRowsB t tableFullLit
  | .error _ => false

theorem tableWritten_is {pol lay KL : ByteArray} (h : tableWrittenB pol lay KL = true) :
    tableOf pol lay KL = .ok tableFullLit := by
  unfold tableWrittenB at h
  split at h
  · rename_i t e
    rw [e, swRowsB_eq h]
  · cases h

/-- **What its accept gives at the row of the sentence on the carried claim.** -/
theorem tableWritten_says {pol lay KL : ByteArray} (h : tableWrittenB pol lay KL = true) (m : ℕ) :
    ProofFile.rowAtK2 pol lay KL m = tableFullLit[m]? := by
  unfold ProofFile.rowAtK2
  rw [tableWritten_is h]
  rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.swRowB_eq
#print axioms VerifiableInference.Desc.First.K2Caller.swRowsB_eq
#print axioms VerifiableInference.Desc.First.K2Caller.tableWritten_is
#print axioms VerifiableInference.Desc.First.K2Caller.tableWritten_says
