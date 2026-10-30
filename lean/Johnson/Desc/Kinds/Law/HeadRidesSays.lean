-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadRidesSays.lean: WHAT Johnson/Stored/HeadRidesB.lean's TWO TESTS SAY, THAT
THE OUTPUT HEAD's OWN BLOCK KEEPS THE FIRST, AND WHAT THEY PAY BEHIND THAT BLOCK's YES. Statements
and proofs.

  noTablesB_iff    the first test is the sentence NoTables (Law/TablesNotYet.lean).
  noTables_below, wide_below   both are kept by a yes of the strict reading of the head's block.
  wide_says        the second test gives hK of Law/K6RecordPaid.lean's below_of_width: withTables
                   turns no ledger.
  readers_of_B     hRd: at the table's own filling of the readers, with k6Silent in the second hole.
  below_of_B       hBelow.
  four_behind      TOGETHER: four clauses on the record behind that yes, from K6On and the two tests
                   at the record IN FRONT.

WHAT IT IS NOT. Implications. That the tests say yes at any record of a chain is the promise's, once
the table's door books them. K6States is a premise of readers_of_B and four_behind. Nothing on
soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Stored.HeadRidesB
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.TablesNotYet
import Johnson.Desc.Kinds.Law.KeepsTrees

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S HeadOwn)

/-- The first test is the sentence. -/
theorem noTablesB_iff (s : S) : noTablesB s = true ↔ NoTables s := by
  unfold noTablesB NoTables
  constructor
  · intro h
    split at h
    · rename_i o ho
      exact ⟨o, ho, Option.isNone_iff_eq_none.mp h⟩
    · cases h
  · rintro ⟨o, ho, ht⟩
    rw [ho]
    exact Option.isNone_iff_eq_none.mpr ht

/-- **The head's own block keeps it**: behind a yes of the strict reading of the head's block. -/
theorem noTables_below (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok s')
    (Z : noTablesB s = true) : noTablesB s' = true := by
  obtain ⟨_, hd⟩ := canonical_of_below b s s' rs gs h
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact (noTablesB_iff s').2 (k6_noTables _ _ _ _ hd ((noTablesB_iff s).1 Z))

/-- **The head's own block keeps the second test too**: it leaves the ledger's arrays
(Law/KeepsTrees.lean). -/
theorem wide_below (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok s')
    (iU n : Nat) (Z : readsWideB iU n s = true) : readsWideB iU n s' = true := by
  obtain ⟨_, hd⟩ := canonical_of_below b s s' rs gs h
  have ht := blockOf_trees W l b hb s s' rs gs hd
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  obtain ⟨a, F1, X, Q, ha, hop, _, rfl⟩ := Came.decide_record _ _ _ _ hd
  have f1 : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
    simp [hop]
  have f2 : ({ s with here := .head { a with F := F1, x := some X, squaresP := some Q } } :
      S).fork? = some F1 := by
    unfold S.fork?
    simp [hop]
  rw [f1, f2] at ht
  have ht' : F1.trees = a.F.trees := ht
  unfold readsWideB at Z ⊢
  rw [f1] at Z
  rw [f2]
  show (match F1.trees[iU]? with
    | some tr => Decidable.decide (n ≤ tr.K)
    | none => false) = true
  rw [ht']
  exact Z

/-- **The second test gives hK**: withTables turns no ledger. -/
theorem wide_says (P : K8.ReadsQuiet.PH) (s : S) (iU3 : Nat)
    (Z : readsWideB iU3 (P.hp.nU.getD 2 0) s = true) :
    ∀ e F tr, withTables P s = some e → e.fork? = some F → F.trees[iU3]? = some tr →
      P.hp.nU.getD 2 0 ≤ tr.K := by
  intro e F tr he hF htr
  obtain ⟨a, cov, x, tt, ha, hop, _, _, _, rfl⟩ := (withTables_iff P s e).1 he
  have e1 : ({ s with here := .head { a with t := some tt } } : S).fork? = s.fork? := by
    unfold S.fork?
    rw [ha]
  rw [e1] at hF
  unfold readsWideB at Z
  rw [hF] at Z
  simp only [htr, decide_eq_true_eq] at Z
  exact Z

/-- **hBelow of Law/K6Stated.lean's tops, from the second test.** -/
theorem below_of_B (P : K8.ReadsQuiet.PH) (s : S) (iU3 : Nat)
    (Z : readsWideB iU3 (P.hp.nU.getD 2 0) s = true) :
    ∀ e o tt F tr, withTables P s = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[iU3]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K :=
  below_of_width P s iU3 (wide_says P s iU3 Z)

/-- **hRd of Law/K6Silent.lean's tops, from the first test**: at the table's own filling of the
readers, with k6Silent in the second hole. -/
theorem readers_of_B (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) (l piece b : Nat)
    (Lk : Link S Claim) (KS : K6States h iU3 p l piece (K9.statesOfLink Lk) b)
    (P : K8.ReadsQuiet.PH) (small : S → Option K9.Read) (s : S) (Z : noTablesB s = true)
    (name : String) (hn : K6Name name) :
    (K9.readersOfLink ⟨small, k6Silent P (K9.statesOfLink Lk)⟩ Lk).forms b name s =
      k6Silent P (K9.statesOfLink Lk) b name s := by
  obtain ⟨o, ho, ht⟩ := (noTablesB_iff s).1 Z
  exact readers_silent h iU3 p l piece b Lk KS P small s o ho ht name hn

/-- **FOUR CLAUSES ON THE RECORD BEHIND A YES OF THE STRICT READING OF THE HEAD's BLOCK**:
the readers' second hole speaks · what was heard is a hearing's · the tables are apart · each table
ends inside the array: from K6On and the two tests AT THE RECORD IN FRONT. -/
theorem four_behind (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (Sound.below b).decide s rs gs = .ok s')
    (hOn : K6On W s) (P : K8.ReadsQuiet.PH) (Z1 : noTablesB s = true)
    (Z2 : readsWideB (readsOf W) (P.hp.nU.getD 2 0) s = true) (l' piece n : Nat)
    (Lk : Link S Claim)
    (KS : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l' piece (K9.statesOfLink Lk) n)
    (small : S → Option K9.Read) :
    (∀ name, K6Name name →
      (K9.readersOfLink ⟨small, k6Silent P (K9.statesOfLink Lk)⟩ Lk).forms n name s' =
        k6Silent P (K9.statesOfLink Lk) n name s') ∧
    K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s' ∧
    (∀ e o tt, withTables P s' = some e → e.here = .head o → o.t = some tt → TabsApart tt) ∧
    (∀ e o tt F tr, withTables P s' = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[readsOf W]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K) :=
  ⟨readers_of_B _ _ _ l' piece n Lk KS P small s' (noTables_below W l b hb s s' rs gs h Z1),
    heardAt_of_below W l b hb s s' rs gs hOn h, tabsApart_at P s',
    below_of_B P s' _ (wide_below W l b hb s s' rs gs h _ _ Z2)⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.wide_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.four_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.noTablesB_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.noTables_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.wide_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.below_of_B
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readers_of_B
