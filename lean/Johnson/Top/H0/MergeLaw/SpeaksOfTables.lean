-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SpeaksOfTables.lean: the test `speaksAt` (RunsAre.lean: the stated run's own
reader answers at the state) from two things: the segment's readers answer there, in either arm; and
the reads' tables that lie in the state are the ones that the second arm would lay in thought. One
definition, two theorems with their proofs.

Why. At the output head's segment the readers have two arms (`readersOfLink`,
Johnson/Desc/First/Batch/ReadersOfLink.lean): the run's own reader; and, where that is silent, the
same reader at the state with the reads' tables laid in thought (`k6Silent`, `withTables`,
Johnson/Desc/Kinds/Law/K6SilentCode.lean). The laws that carry a reader's answer across the merge
want the first arm (`Speaks`). A public test on a run's forms says only that the readers answer.
Where the tables in the state are already those that `tablesAt` computes, laying them in thought
turns nothing: the two arms ask one reader at one state.

Main names.
  `TablesLaid P s`: at a state in the output head's segment: what `tablesAt P s` gives is what lies.
  `withTables_self`: under it `withTables P s` is s, where it answers.
  `speaks_of_forms`: so where the readers answer, the run's own reader answers.

Limits. `TablesLaid` is shown of no state. It is false where no tables lie and `tablesAt` answers:
right behind the output head's own sub-protocol. That the second arm is `k6Silent` is a premise on
the readers. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RunsAre
import Johnson.Desc.Kinds.Law.K6SilentCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (statesOfLink readerOf readersOfLink LinkHoles)
open VerifiableInference.Desc.Kinds.Head.Law (tablesAt withTables k6Silent)

/-- The reads' tables that lie in the state are the ones that the second arm would lay. -/
def TablesLaid (P : K8.ReadsQuiet.PH) (s : S) : Prop :=
  ∀ o t, s.here = .head o → tablesAt P s = some t → o.t = some t

/-- Under it, laying the tables in thought turns nothing. -/
theorem withTables_self {P : K8.ReadsQuiet.PH} {s e : S} (ht : TablesLaid P s)
    (h : withTables P s = some e) : e = s := by
  unfold withTables at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    obtain ⟨t, htb, rfl⟩ := Option.map_eq_some_iff.1 h
    have e1 : a.t = some t := ht a t hh htb
    have e2 : ({ a with t := some t } : HeadOwn) = a := by rw [← e1]
    rw [e2, ← hh]
  | between => rw [hh] at h; cases h
  | lay a => rw [hh] at h; cases h
  | att a => rw [hh] at h; cases h
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- **Where the segment's readers answer and the tables lie, the run's own reader answers.** -/
theorem speaks_of_forms (H : LinkHoles) (l : Link S Claim) (P : K8.ReadsQuiet.PH) (k : ℕ)
    {name : String} {s : S} (hne : (name == "K8.equations") = false)
    (hsil : H.silent = k6Silent P (statesOfLink l)) (ht : TablesLaid P s)
    (hf : ((readersOfLink H l).forms k name s).isSome = true) : speaksAt l k name s = true := by
  unfold speaksAt
  cases h1 : readerOf (statesOfLink l) k name s with
  | some R => rfl
  | none =>
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hf
    have hR' : (if (name == "K8.equations") = true then H.small s
      else
        match readerOf (statesOfLink l) k name s with
        | some R => some R
        | Option.none => H.silent k name s) = some R := hR
    rw [hne, h1, hsil] at hR'
    have hR'' : (withTables P s).bind (readerOf (statesOfLink l) k name) = some R := hR'
    obtain ⟨e, he, h2⟩ := Option.bind_eq_some_iff.1 hR''
    rw [withTables_self ht he, h1] at h2
    cases h2

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.withTables_self
#print axioms VerifiableInference.Desc.First.MergeLaw.speaks_of_forms
