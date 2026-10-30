-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsNeedIs.lean.
WHAT IT DOES NOT SHOW. No soundness. That the program's tables are as long as the seat asks at a
real
record: no run is in it. That an entry below a read's length lies inside the read's OWN table and in
no neighbour's also wants where the table starts: Law/ReadsFit.lean, Law/ReadsFitNorm.lean. A
harness's seat.
LETTERS. reads_answer: under "there is": o, F: pinned by s.here = .head o and s.fork? = some F; tt,
tr:
by o.t = some tt and F.trees[iU3]? = some tr; e (for each row): by the table's find?.
OBJECT. Stored/HeadSeatAt.lean's seatAt h iU3, its field reads, and its list readsNeed h.
WHAT IT IS. The seat's reader of a read refuses unless twelve tables are found and are long enough.
Its list of names and lengths is typed in the seat's file, which cannot import the laws.
  readsNeed_is      THE LIST IS THE LAWS' OWN: the normalization's seven reads with their names
                    (Law/ReadsFitNorm.lean: nameOfN) and lengths (Law/CoveredNorm.lean: readLenN),
                    then the head's five (Law/ReadsFit.lean: nameOf; Law/K06Statement.lean:
                    readLen):
                    by rfl.
  wide_covers       the length asked of the wide read covers what the normalization spends of it.
  reads_answer      WHERE THE SEAT's READS ANSWER: the record stands in the head's link with a
  ledger,
                    the tables are laid, the reads' array is there WITH A COLUMN, and every row of
                    the
                    list is found in the table of tables and is no shorter than asked.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsFitNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- **The seat's list is the laws' own names and lengths.** -/
theorem readsNeed_is (h : Model.Head.Shape) :
    readsNeed h =
      ([.streamAtSquares, .streamAtNormed, .actAtKeys, .rowAtKeys, .rowAtPV, .rowAtProducts,
        .rowAtNormed] : List FinalNorm.Read).map (fun r => (nameOfN r, @readLenN (sizesOf h) r)) ++
      ([.wideAtKeys, .wideAtCosts, .actAtLogits, .rowAtCosts, .rowCount] : List Read).map
        (fun r => (nameOf r, @readLen (sizesOf h) r)) := rfl

/-- What the normalization spends of the wide read is within what the seat asks of it. -/
theorem wide_covers (h : Model.Head.Shape) :
    @wideLenN (sizesOf h) ≤ @readLen (sizesOf h) .wideAtKeys := by
  letI := sizesOf h
  show 4 * Norm.d / Norm.S2 ≤ (4 * Norm.d + 6 * JV) / Norm.S2
  exact Nat.div_le_div_right (Nat.le_add_right _ _)

/-- **WHERE THE SEAT's READS ANSWER.** -/
theorem reads_answer (h : Model.Head.Shape) (iU3 : Nat) (s : S) (x : FinalNorm.Reads × Reads)
    (hx : (seatAt h iU3).reads s = some x) :
    ∃ (o : VerifiableInference.Desc.First.HeadOwn) (F : Fork) (tt : Model.Head.Tables)
      (tr : Model.HTree), s.here = .head o ∧ s.fork? = some F ∧ o.t = some tt ∧
      F.trees[iU3]? = some tr ∧ tr.K ≠ 0 ∧
      ∀ n ∈ readsNeed h, ∃ e, tt.tab.find? (fun e => e.1 == n.1) = some e ∧ n.2 ≤ e.2.2 := by
  unfold seatAt at hx
  dsimp only at hx
  split at hx
  · rename_i o F ho hF
    cases ht : o.t with
    | none => rw [ht] at hx; simp at hx
    | some tt =>
      rw [ht] at hx
      cases htr : F.trees[iU3]? with
      | none => rw [htr] at hx; simp at hx
      | some tr =>
        rw [htr] at hx
        simp only [Option.bind_some] at hx
        split at hx
        · cases hx
        · rename_i hc
          simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', not_or,
            Bool.not_eq_false] at hc
          refine ⟨o, F, tt, tr, ho, hF, ht, htr, hc.1, fun n hn => ?_⟩
          have h1 := (List.all_eq_true.mp hc.2) n hn
          cases hf : tt.tab.find? (fun e => e.1 == n.1) with
          | none => rw [hf] at h1; cases h1
          | some e =>
            rw [hf] at h1
            exact ⟨e, rfl, Nat.le_of_ble_eq_true h1⟩
  · cases hx

end VerifiableInference.Desc.Kinds.Head.Law
