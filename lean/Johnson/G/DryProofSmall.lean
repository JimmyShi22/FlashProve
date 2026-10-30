-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/DryProofSmall.lean: facts on the first written list of the full-size proof file
(Johnson/G/DryProofLit.lean): which of its rounds have `isSmall` (Johnson/Flat/SmallOk.lean), how
many, and of what shape.

Definitions.
  `cntE recs q a runs`: a plus the number of members with q of a list that is written as runs,
    counted along the runs, each step forced (`force`, Johnson/G/Eager.lean).
Statements and proofs.
  `cntE_eq`, `mem_unrunR`: TOOLS on a list that is written as runs.
  `written_small`: on the first written list `isSmall` is "draws a matrix entry".
  `written_count`: just 25 rounds of that list have `isSmall`. `first_ne`: so the list has a round.
  `written_shape`: each of them has the entry "RNG" with its number of matrix entries and every
    other number as the format's default has it (count 1, all else 0), the kind "entries", no item,
    opens nothing, and draws 3,083,008 or 1,311,744 or 2,649,984 matrix entries, a multiple of 128.
    `written_div`: these are 128 times 24,086, 10,248, 20,703.
  `written_sorts`: 12, 12 and 1 rounds of the list are of the three sorts. `exists_written`: so each
    sort has a round in the list.
BY EVALUATIONS IN LEAN's KERNEL (`decide +kernel`): `recs_small`, `recs_shape`; `cnt_all`,
`cnt_sorts`, under `set_option maxRecDepth 1000000`. By `decide`: numerals in `written_div`,
`exists_written`. All else is by proof.

FACTS ON A WRITTEN LIST, and tools. Not claimed: that the written list is what the planner makes of
the public files: no theorem says so (the owed row planValues_are_written; the list's own head). A
ROUND OF THE LIST IS TAKEN BY ITS VALUE: the twelve of a sort are one value: no place in the chain
is named. Nothing on a description of the protocol.

-/
import Johnson.G.DryProofLit
import Johnson.Flat.SmallOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.Written
open VerifiableInference.Number (isSmall)
open Johnson.G (force force_eq unrunR dryProofFull dryProofRecsFull dryProofRunsFull0)

/-- a plus the number of members with q, counted along the runs. -/
def cntE (recs : List (Fmt.Round × List Fmt.Stored)) (q : Fmt.Round × List Fmt.Stored → Bool) :
    Nat → List (Nat × Nat) → Nat
  | a, [] => a
  | a, x :: xs => force (a + if (recs[x.2]?).any q then x.1 else 0) fun v => cntE recs q v xs

theorem cntE_eq (recs : List (Fmt.Round × List Fmt.Stored))
    (q : Fmt.Round × List Fmt.Stored → Bool) (runs : List (Nat × Nat)) :
    ∀ a, cntE recs q a runs = a + ((unrunR recs runs).filter q).length := by
  induction runs with
  | nil => intro a; rfl
  | cons x xs ih =>
    intro a
    have e : unrunR recs (x :: xs) =
        (recs[x.2]?).elim [] (List.replicate x.1) ++ unrunR recs xs := by
      simp [unrunR, List.flatMap_cons]
    have c : (((recs[x.2]?).elim [] (List.replicate x.1)).filter q).length =
        if (recs[x.2]?).any q then x.1 else 0 := by
      cases recs[x.2]? with
      | none => simp
      | some r =>
        cases hq : q r <;> simp [hq]
    simp only [cntE, force_eq, ih]
    rw [e, List.filter_append, List.length_append, c]
    omega

theorem mem_unrunR {recs : List (Fmt.Round × List Fmt.Stored)} {runs : List (Nat × Nat)}
    {x : Fmt.Round × List Fmt.Stored} (h : x ∈ unrunR recs runs) : x ∈ recs := by
  unfold unrunR at h
  obtain ⟨y, _, hy⟩ := List.mem_flatMap.1 h
  cases hr : recs[y.2]? with
  | none => simp [hr] at hy
  | some r =>
    simp only [hr, Option.elim] at hy
    obtain rfl := (List.mem_replicate.1 hy).2
    exact List.mem_of_getElem? hr

/-- On the proof's distinct written rounds `isSmall` is "draws a matrix entry". -/
theorem recs_small :
    dryProofRecsFull.all (fun x => isSmall x.1.entry == (x.1.entry.trits != 0)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem cnt_all :
    cntE dryProofRecsFull (fun x => x.1.entry.trits != 0) 0 dryProofRunsFull0 = 25 := by
  decide +kernel

/-- On the first written list `isSmall` is "draws a matrix entry". -/
theorem written_small {x : Fmt.Round × List Fmt.Stored} (hx : x ∈ dryProofFull.1) :
    isSmall x.1.entry = (x.1.entry.trits != 0) :=
  eq_of_beq (List.all_eq_true.1 recs_small x (mem_unrunR hx))

/-- **Just 25.** -/
theorem written_count : (dryProofFull.1.filter fun x => isSmall x.1.entry).length = 25 := by
  have e : (dryProofFull.1.filter fun x => isSmall x.1.entry) =
      dryProofFull.1.filter fun x => x.1.entry.trits != 0 :=
    List.filter_congr fun x hx => written_small hx
  have c := cntE_eq dryProofRecsFull (fun x => x.1.entry.trits != 0) dryProofRunsFull0 0
  rw [cnt_all] at c
  rw [e]
  show ((unrunR dryProofRecsFull dryProofRunsFull0).filter _).length = 25
  omega

/-- The first written list has a round. -/
theorem first_ne : dryProofFull.1 ≠ [] := by
  intro e
  have c := written_count
  rw [e] at c
  simp at c

/-! ## Of what shape -/

/-- The test on a written round. -/
def shapeB (x : Fmt.Round × List Fmt.Stored) : Bool :=
  x.1.entry.trits == 0 ||
    ((x.1.entry == { name := "RNG", trits := x.1.entry.trits }) && decide (x.1.kind = .entries) &&
      x.1.items.isEmpty && x.1.opens.isEmpty && x.2.isEmpty &&
      [3083008, 1311744, 2649984].contains x.1.entry.trits && x.1.entry.trits % 128 == 0)

theorem recs_shape : dryProofRecsFull.all shapeB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem cnt_sorts :
    (cntE dryProofRecsFull (fun x => x.1.entry.trits == 3083008) 0 dryProofRunsFull0,
      cntE dryProofRecsFull (fun x => x.1.entry.trits == 1311744) 0 dryProofRunsFull0,
      cntE dryProofRecsFull (fun x => x.1.entry.trits == 2649984) 0 dryProofRunsFull0) =
      (12, 12, 1) := by
  decide +kernel

/-- **Every round of the first written list with `isSmall`.** -/
theorem written_shape {x : Fmt.Round × List Fmt.Stored} (hx : x ∈ dryProofFull.1)
    (hs : isSmall x.1.entry = true) :
    x.1.entry = { name := "RNG", trits := x.1.entry.trits } ∧ x.1.kind = .entries ∧
      x.1.items = [] ∧ x.1.opens = [] ∧ x.2 = [] ∧
      x.1.entry.trits ∈ [3083008, 1311744, 2649984] ∧ x.1.entry.trits % 128 = 0 := by
  have h := List.all_eq_true.1 recs_shape x (mem_unrunR hx)
  unfold shapeB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.isEmpty_iff, List.contains_iff_mem] at h
  have hn : x.1.entry.trits ≠ 0 := by
    have h0 := written_small hx
    rw [hs] at h0
    simpa using h0.symm
  rcases h with h1 | ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩
  · exact absurd h1 hn
  · exact ⟨a, b, c, d, e, f, g⟩

/-- **12, 12 and 1 of the three sorts.** -/
theorem written_sorts :
    (dryProofFull.1.filter fun x => x.1.entry.trits == 3083008).length = 12 ∧
      (dryProofFull.1.filter fun x => x.1.entry.trits == 1311744).length = 12 ∧
      (dryProofFull.1.filter fun x => x.1.entry.trits == 2649984).length = 1 := by
  have c1 := cntE_eq dryProofRecsFull (fun x => x.1.entry.trits == 3083008) dryProofRunsFull0 0
  have c2 := cntE_eq dryProofRecsFull (fun x => x.1.entry.trits == 1311744) dryProofRunsFull0 0
  have c3 := cntE_eq dryProofRecsFull (fun x => x.1.entry.trits == 2649984) dryProofRunsFull0 0
  have s := cnt_sorts
  rw [Prod.mk.injEq, Prod.mk.injEq] at s
  rw [s.1] at c1
  rw [s.2.1] at c2
  rw [s.2.2] at c3
  refine ⟨?_, ?_, ?_⟩
  · show ((unrunR dryProofRecsFull dryProofRunsFull0).filter _).length = 12
    omega
  · show ((unrunR dryProofRecsFull dryProofRunsFull0).filter _).length = 12
    omega
  · show ((unrunR dryProofRecsFull dryProofRunsFull0).filter _).length = 1
    omega

/-- The three numbers are 128 times 24,086, 10,248, 20,703. -/
theorem written_div {n : Nat} (h : n ∈ [3083008, 1311744, 2649984]) :
    n / 128 * 128 = n ∧ n / 128 ∈ [24086, 10248, 20703] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

/-- Each sort has a round in the list. -/
theorem exists_written {n : Nat} (h : n ∈ [3083008, 1311744, 2649984]) :
    ∃ x ∈ dryProofFull.1, isSmall x.1.entry = true ∧ x.1.entry.trits = n := by
  have key : ∀ m : Nat, m ≠ 0 → 0 < (dryProofFull.1.filter fun x => x.1.entry.trits == m).length →
      ∃ x ∈ dryProofFull.1, isSmall x.1.entry = true ∧ x.1.entry.trits = m := by
    intro m hm hl
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos hl
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hx
    have e : x.1.entry.trits = m := eq_of_beq h2
    refine ⟨x, h1, ?_, e⟩
    rw [written_small h1, e]
    simpa using hm
  obtain ⟨s1, s2, s3⟩ := written_sorts
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact key _ (by decide) (by rw [s1]; decide)
  · exact key _ (by decide) (by rw [s2]; decide)
  · exact key _ (by decide) (by rw [s3]; decide)

end VerifiableInference.Number.Written

#print axioms VerifiableInference.Number.Written.cntE_eq
#print axioms VerifiableInference.Number.Written.mem_unrunR
#print axioms VerifiableInference.Number.Written.recs_small
#print axioms VerifiableInference.Number.Written.cnt_all
#print axioms VerifiableInference.Number.Written.written_small
#print axioms VerifiableInference.Number.Written.written_count
#print axioms VerifiableInference.Number.Written.first_ne
#print axioms VerifiableInference.Number.Written.recs_shape
#print axioms VerifiableInference.Number.Written.cnt_sorts
#print axioms VerifiableInference.Number.Written.written_shape
#print axioms VerifiableInference.Number.Written.written_sorts
#print axioms VerifiableInference.Number.Written.written_div
#print axioms VerifiableInference.Number.Written.exists_written
