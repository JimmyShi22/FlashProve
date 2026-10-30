-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/FileUp.lean: the m claims of a lookup with parts are filed into the library's house
by m calls of the library's own filing. It imports the library alone.

Why. In the library's house for a witness file (Cb/Ld/LdWf.lean) a lookup leaves one masked claim,
filed at «forest» l by `P.file l`. A lookup whose keys come in m parts leaves m claims. Here claim i
is filed at forest a + i, and no type of the house turns.
  `fileUp P a cl rw k`   claims cl 0 … cl (k − 1) are filed at forests a … a + k − 1, claim i with
                   the rows rw i. The fold runs from below, so «a + (k + 1)» is «a + k + 1» by
                   unfolding and the library's lemma done_file fits as it stands.
  `fileUp_some`          if the filing succeeds: record and samples are kept; «all is done up to a +
                   k» holds of the filed state exactly if each claim and its rows hold and all was
                   done up to a.
  `OutN`, `fileOut`, `fileOut_some`   the same for a read-out with claims by Fin m and one list of
                   rows, all filed at forest a (1 ≤ m).
  `fileUp_ok`, `fileOut_ok`   where each claim with its rows meets the library's own test
                   `P.FileOK`, the filing succeeds. In fileOut that test asks of the record: P.nR a
                   = the number of rows, and P.nR (a + i) = 0 for 0 < i < m; at the library's own
                   builder (`BldWfN.nR`) no forest has 0 rows, and there fileOut at m ≥ 2 refuses
                   every read-out (said here without a theorem).
  `fileOut_one`          at one part the filing is the library's `P.file`.
Under: each statement's own binders; 1 ≤ m in fileOut_some (a public number). Does not say: that any
record and read-out pass; anything on the link. After: P.file, file_eq, done_file are the library's
(Cb/Ld/LdWf.lean; Cb/Ld/LdWfProofsRel.lean). No list of claims stands anywhere: the claims are a
function (ℕ → MCl, or Fin m → MCl in a read-out) and the recursion runs on the number k of claims
filed.

-/
import Cb.Ld.LdWfProofsRel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.LdWfP

variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C)

/-- The claims cl 0, …, cl (k − 1) are filed at the forests a, …, a + k − 1, claim i with the rows
rw i: k calls of the library's own filing. -/
noncomputable def fileUp (a : ℕ) (cl : ℕ → MCl E P.N) (rw : ℕ → List (Row E P.N)) :
    ℕ → P.X → Option P.X
  | 0, x => some x
  | k + 1, x => (fileUp a cl rw k x).bind fun x' => P.file (a + k) ((x'.1, cl k, rw k), x'.2)

/-- Record and samples are kept; and what is done after the filing. -/
theorem fileUp_some (a : ℕ) (cl : ℕ → MCl E P.N) (rw : ℕ → List (Row E P.N)) :
    ∀ (k : ℕ) (x x' : P.X), fileUp P a cl rw k x = some x' →
      x'.1.1 = x.1.1 ∧ x'.2 = x.2 ∧
      ∀ (U : C.Msg) (m : P.S.Msg), P.Done (a + k) x'.1 U m ↔
        (∀ i, i < k →
          (cl i).Holds (P.v (a + i)) (P.key (a + i) U) (P.ent m) ∧ RowsHold (rw i) (P.ent m)) ∧
        P.Done a x.1 U m
  | 0, x, x', h => by
      obtain rfl : x = x' := Option.some.inj h
      exact ⟨rfl, rfl, fun U m =>
        ⟨fun g => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), g⟩, fun g => g.2⟩⟩
  | k + 1, x, x', h => by
      obtain ⟨x₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨e1, e2, e3⟩ := fileUp_some a cl rw k x x₁ h1
      obtain ⟨hF, rfl⟩ := file_eq (a + k) _ x' h2
      refine ⟨e1, e2, fun U m =>
        (done_file (a + k) ((x₁.1, cl k, rw k), x₁.2) hF U m).trans ⟨fun g => ?_, fun g => ?_⟩⟩
      · obtain ⟨g1, g2⟩ := (e3 U m).1 g.2.2
        exact ⟨fun i hi =>
          (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi)).elim (fun e => e ▸ ⟨g.1, g.2.1⟩) (g1 i), g2⟩
      · exact ⟨(g.1 k (Nat.lt_succ_self k)).1, (g.1 k (Nat.lt_succ_self k)).2,
          (e3 U m).2 ⟨fun i hi => g.1 i (Nat.lt_succ_of_lt hi), g.2⟩⟩

/-- If claim i and the rows rw i can be filed at forest a + i (the library's own test `P.FileOK`,
which reads the claim and the rows and neither the state nor the samples: so it is asked here at the
state at the start), for each i < k, then the filing succeeds. That any claims and rows pass that
test is not shown here. -/
theorem fileUp_ok (a : ℕ) (cl : ℕ → MCl E P.N) (rw : ℕ → List (Row E P.N)) :
    ∀ (k : ℕ) (x : P.X), (∀ i, i < k → P.FileOK (a + i) ((x.1, cl i, rw i), x.2)) →
      ∃ x', fileUp P a cl rw k x = some x'
  | 0, x, _ => ⟨x, rfl⟩
  | k + 1, x, h => by
      obtain ⟨x₁, h1⟩ := fileUp_ok a cl rw k x fun i hi => h i (Nat.lt_succ_of_lt hi)
      refine ⟨(fileSt (a + k) (x₁.1, cl k, rw k), x₁.2), ?_⟩
      rw [fileUp, h1]
      exact file_some (a + k) ((x₁.1, cl k, rw k), x₁.2) (h k (Nat.lt_succ_self k))

/-- what a lookup with m parts leaves, on the named entries -/
abbrev OutN (St E N : Type) (m : ℕ) : Type := St × (Fin m → MCl E N) × List (Row E N)

/-- The filing of a lookup's read-out at the forests a, …, a + m − 1; all rows at a. -/
noncomputable def fileOut (a m : ℕ) (x : OutN P.WSt E P.N m × P.S.Smp) : Option P.X :=
  fileUp P a (fun i => if h : i < m then x.1.2.1 ⟨i, h⟩ else ⟨fun _ => 0, fun _ => 0, 0⟩)
    (fun i => if i = 0 then x.1.2.2 else []) m (x.1.1, x.2)

theorem fileOut_some (a m : ℕ) (hm : 1 ≤ m) (x : OutN P.WSt E P.N m × P.S.Smp) (x' : P.X)
    (h : fileOut P a m x = some x') :
    x'.1.1 = x.1.1.1 ∧ x'.2 = x.2 ∧
    ∀ (U : C.Msg) (μ : P.S.Msg), P.Done (a + m) x'.1 U μ ↔
      (∀ i : Fin m, (x.1.2.1 i).Holds (P.v (a + i)) (P.key (a + i) U) (P.ent μ)) ∧
      RowsHold x.1.2.2 (P.ent μ) ∧ P.Done a x.1.1 U μ := by
  obtain ⟨e1, e2, e3⟩ := fileUp_some P a _ _ m (x.1.1, x.2) x' h
  refine ⟨e1, e2, fun U μ => (e3 U μ).trans ⟨fun g => ?_, fun g => ?_⟩⟩
  · refine ⟨fun i => ?_, ?_, g.2⟩
    · have t := (g.1 i.1 i.2).1
      rw [dif_pos i.2] at t
      exact t
    · have t := (g.1 0 hm).2
      rw [if_pos rfl] at t
      exact t
  · refine ⟨fun i hi => ⟨?_, ?_⟩, g.2.2⟩
    · rw [dif_pos hi]
      exact g.1 ⟨i, hi⟩
    · by_cases h0 : i = 0
      · rw [if_pos h0]
        exact g.2.1
      · rw [if_neg h0]
        exact fun _ hr => absurd hr (List.not_mem_nil)

/-- The same for a read-out: if each claim can be filed at its forest, the rows with the first and
no row with the others, the filing succeeds. -/
theorem fileOut_ok (a m : ℕ) (x : OutN P.WSt E P.N m × P.S.Smp)
    (h : ∀ i : Fin m,
      P.FileOK (a + i) ((x.1.1, x.1.2.1 i, if (i : ℕ) = 0 then x.1.2.2 else []), x.2)) :
    ∃ x', fileOut P a m x = some x' := by
  refine fileUp_ok P a _ _ m (x.1.1, x.2) fun i hi => ?_
  rw [dif_pos hi]
  exact h ⟨i, hi⟩

/-- At one part the filing is the library's. -/
theorem fileOut_one (a : ℕ) (x : OutN P.WSt E P.N 1 × P.S.Smp) :
    fileOut P a 1 x = P.file a ((x.1.1, x.1.2.1 0, x.1.2.2), x.2) := rfl

end Lk6

#print axioms Lk6.fileUp_some
#print axioms Lk6.fileOut_some
#print axioms Lk6.fileOut_one
#print axioms Lk6.fileUp_ok
#print axioms Lk6.fileOut_ok
