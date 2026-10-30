-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanesRefuses.lean.
WHAT IT DOES NOT SHOW. No soundness. MADE-UP RECORDS, laid by hand: no run, no file, no proof. Not
that a whole description refuses: at a real link the output head's run "norm" stands in front of the
lookup's run "planes" and reads the same array. Controls on one function.
OBJECT. Stored/HeadSeatAt.lean's planesAt: the reader of the three further reads for the lookup's
run
"planes".
WHAT IT IS. THE READER ANSWERS NOTHING WHERE THE READS' ARRAY IS STRUCK OR HAS NO COLUMN, AND IT IS
THIS READER's OWN TEST THAT REFUSES: the same text without that test, typed here, answers at the
same two records.
  planesOlder       without the test: a missing array reads as one column; no column is not refused.
  recAt F           a record in the head's link, opened, the tables laid, with the ledger F.
  planes_yes        with an array of one column: both answer.
  planes_struck     the array struck: the reader answers nothing; planesOlder answers.
  planes_no_column  an array without a column: the same.
  planes_other      an array is there, but not under the number asked: the same.
  planes_same       where the array is there with a column the two texts are one.
  planesAt_none     AT EVERY RECORD: no array under the number, or one without a column: nothing.
  planesAt_some     where it answers: every letter pinned: the link's part, the ledger, the tables,
                    the array, its columns not 0, and what is answered.

-/
import Mathlib
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- `planesAt` without its test on the array. -/
def planesOlder (iU3 : Nat) : PlaneSeat S := fun s =>
  match s.here, s.fork? with
  | .head o, some F =>
    o.t.map fun tt => planeEntry tt.tab iU3 (((F.trees[iU3]?).map (·.K)).getD 1)
  | _, _ => none

/-- A record in the head's link, opened, the tables laid, with a given ledger. -/
def recAt (F : Fork) : S :=
  { S.blank with
    failed := none
    here := .head { fr := S.blank.check.frame, kept := #[], ids := #[],
                    L := { check := S.blank.check }, F := F, tl := {}, Fm := {},
                    opened := true, t := some {} } }

theorem planes_yes : (planesAt 0 (recAt { trees := #[{ K := 1 }] })).isSome = true ∧
    (planesOlder 0 (recAt { trees := #[{ K := 1 }] })).isSome = true := ⟨rfl, rfl⟩

theorem planes_struck : (planesAt 0 (recAt {})).isSome = false ∧
    (planesOlder 0 (recAt {})).isSome = true := ⟨rfl, rfl⟩

theorem planes_no_column : (planesAt 0 (recAt { trees := #[{ K := 0 }] })).isSome = false ∧
    (planesOlder 0 (recAt { trees := #[{ K := 0 }] })).isSome = true := ⟨rfl, rfl⟩

theorem planes_other : (planesAt 1 (recAt { trees := #[{ K := 1 }] })).isSome = false ∧
    (planesOlder 1 (recAt { trees := #[{ K := 1 }] })).isSome = true := ⟨rfl, rfl⟩

/-- **Where the array is there with a column the two texts are one.** -/
theorem planes_same (iU3 : Nat) (s : S) (F : Fork) (tr : HTree) (hF : s.fork? = some F)
    (htr : F.trees[iU3]? = some tr) (hK : tr.K ≠ 0) : planesAt iU3 s = planesOlder iU3 s := by
  unfold planesAt planesOlder
  rw [hF]
  cases s.here with
  | head o =>
    cases ht : o.t with
    | none => simp [ht]
    | some tt => simp [ht, htr, hK]
  | _ => rfl

/-- **No array under the number, or an array without a column: the reader answers nothing**, at
every record. -/
theorem planesAt_none (iU3 : Nat) (s : S)
    (h : ∀ F tr, s.fork? = some F → F.trees[iU3]? = some tr → tr.K = 0) : planesAt iU3 s = none :=
    by
  unfold planesAt
  cases hh : s.here with
  | head o =>
    cases hF : s.fork? with
    | none => rfl
    | some F =>
      cases ht : o.t with
      | none => simp [ht]
      | some tt =>
        cases htr : F.trees[iU3]? with
        | none => simp [ht, htr]
        | some tr => simp [ht, htr, h F tr hF htr]
  | _ => rfl

/-- **Where the reader answers: the record stands in the head's link with a ledger, the tables are
laid, and the array is there with a column.** -/
theorem planesAt_some (iU3 : Nat) (s : S) (f : PlaneRead → Nat → Option Form)
    (h : planesAt iU3 s = some f) :
    ∃ (o : VerifiableInference.Desc.First.HeadOwn) (F : Fork) (tt : Model.Head.Tables)
      (tr : HTree), s.here = .head o ∧ s.fork? = some F ∧ o.t = some tt ∧
      F.trees[iU3]? = some tr ∧ tr.K ≠ 0 ∧ f = planeEntry tt.tab iU3 tr.K := by
  unfold planesAt at h
  split at h
  · rename_i o F ho hF
    cases ht : o.t with
    | none => rw [ht] at h; simp at h
    | some tt =>
      rw [ht] at h
      cases htr : F.trees[iU3]? with
      | none => rw [htr] at h; simp at h
      | some tr =>
        rw [htr] at h
        simp only [Option.bind_some] at h
        split at h
        · cases h
        · rename_i hc
          exact ⟨o, F, tt, tr, ho, hF, ht, htr, by simpa using hc, (Option.some.inj h).symm⟩
  · cases h

end VerifiableInference.Desc.Kinds.Head.Law
