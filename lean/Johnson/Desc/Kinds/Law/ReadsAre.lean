-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsAre.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing of a real record. That the tables do not overlap, and
that a table's first entry is the layout's: Law/ReadsFit.lean and Law/ReadsFitNorm.lean take these
as premises.
LETTERS. reads_are: under "there is": o, F: pinned by s.here = .head o and s.fork? = some F; tt, tr:
by o.t = some tt and F.trees[iU3]? = some tr. NO LETTER FOR THE NUMBER OF COLUMNS OR FOR A TABLE's
FIRST ENTRY IS LEFT UNDER "there is": the columns are tr.K, which is not 0; the first entry of the
table under a name is firstOf tt name.
OBJECT. Stored/HeadSeatAt.lean's seatAt h iU3, its field reads.
WHAT IT IS. WHERE THE SEAT's READS ANSWER, EVERY ENTRY OF ALL THIRTEEN READERS, WRITTEN OUT: entry i
of the read under a name is the entry of array iU3 at position firstOf tt name + i, row and column
by
tr.K. (Law/CoveredSeat.lean's seat_entry and the two files named above say "there are cols and base"
and let go of what they are.)
  firstOf           the first entry of the table under a name; 0 if no table bears it.
  entryAt           the form at a position of the reads' array.
  reads_are         the statement.
  reads_within      with Law/ReadsNeedIs.lean's reads_answer: below a read's length the position
  lies
                    inside the table that was found under the read's name.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsNeedIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- The first entry of the table under a name. -/
def firstOf (tt : Model.Head.Tables) (name : String) : Nat :=
  ((tt.tab.find? fun e => e.1 == name).map (·.2.1)).getD 0

/-- The form at a position of array iU3 with K columns. -/
def entryAt (iU3 K pos : Nat) : Form := Aff.ent iU3 (pos / K) (pos % K)

/-- **WHERE THE SEAT's READS ANSWER: EVERY ENTRY.** -/
theorem reads_are (h : Model.Head.Shape) (iU3 : Nat) (s : S) (x : FinalNorm.Reads × Reads)
    (hx : (seatAt h iU3).reads s = some x) :
    ∃ (o : VerifiableInference.Desc.First.HeadOwn) (F : Fork) (tt : Model.Head.Tables)
      (tr : Model.HTree), s.here = .head o ∧ s.fork? = some F ∧ o.t = some tt ∧
      F.trees[iU3]? = some tr ∧ tr.K ≠ 0 ∧
      (∀ r i, x.1.entry r i = entryAt iU3 tr.K (firstOf tt (nameOfN r) + i)) ∧
      (∀ i, x.1.wide i = entryAt iU3 tr.K (firstOf tt "hf@Z" + i)) ∧
      (∀ r i, x.2.entry r i = entryAt iU3 tr.K (firstOf tt (nameOf r) + i)) := by
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
          simp only [Option.some.injEq] at hx
          subst hx
          refine ⟨o, F, tt, tr, ho, hF, ht, htr, hc.1, fun r i => ?_, fun i => rfl,
            fun r i => ?_⟩
          · cases r <;> rfl
          · cases r <;> rfl
  · cases hx

/-- **Below a read's length the position lies inside the table found under the read's name.** -/
theorem reads_within (h : Model.Head.Shape) (iU3 : Nat) (s : S) (x : FinalNorm.Reads × Reads)
    (hx : (seatAt h iU3).reads s = some x) (tt : Model.Head.Tables)
    (o : VerifiableInference.Desc.First.HeadOwn) (ho : s.here = .head o) (ht : o.t = some tt) :
    (∀ r, ∃ e, tt.tab.find? (fun e => e.1 == nameOfN r) = some e ∧ firstOf tt (nameOfN r) = e.2.1 ∧
      @readLenN (sizesOf h) r ≤ e.2.2) ∧
    (∀ r, ∃ e, tt.tab.find? (fun e => e.1 == nameOf r) = some e ∧ firstOf tt (nameOf r) = e.2.1 ∧
      @readLen (sizesOf h) r ≤ e.2.2) := by
  obtain ⟨o', F, tt', tr, ho', _, ht', _, _, hall⟩ := reads_answer h iU3 s x hx
  obtain rfl : o = o' := by
    rw [ho] at ho'
    injection ho'
  obtain rfl : tt = tt' := Option.some.inj (ht.symm.trans ht')
  rw [readsNeed_is] at hall
  constructor
  · intro r
    obtain ⟨e, he, hle⟩ := hall (nameOfN r, @readLenN (sizesOf h) r) (by
      apply List.mem_append_left
      cases r <;> simp)
    exact ⟨e, he, by unfold firstOf; rw [he]; rfl, hle⟩
  · intro r
    obtain ⟨e, he, hle⟩ := hall (nameOf r, @readLen (sizesOf h) r) (by
      apply List.mem_append_right
      cases r <;> simp)
    exact ⟨e, he, by unfold firstOf; rw [he]; rfl, hle⟩

end VerifiableInference.Desc.Kinds.Head.Law
