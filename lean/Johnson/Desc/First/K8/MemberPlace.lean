-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/MemberPlace.lean: the place's numbers of the smallness test's first half
(Johnson/Desc/First/K8/Hear.lean) against a plan's round and a setting, and against the rounds "RNG"
of the library's written list of the full-size proof file's first chain
(Johnson/G/DryProofLit.lean). Definitions and rules; no test is evaluated in this file.
Johnson/Desc/First/K8/Member.lean builds its example on them, and
Johnson/Desc/First/K8/MemberTeeth.lean shows where the tests defined here say no.

Definitions.
  `placeOk st p d`: one test with code, of three clauses: the kind's block at p declares just the
    round d; its own tests on the plan say yes; and the entry that the planner's routine adds under
    the setting st at p's number of columns (`rngRound`, OnBytes/Tie/Pv/Tail/Plan.lean; `rngSize`,
    OnBytes/Tie/Pv/Tail/CallRng.lean) is the kind's declared entry. That one equation gives the
    second and the third premise of the row on the round's price (a row: a proposition stated by
    name, with a theorem of just that type; here `K08RoundsHearing`,
    Johnson/Desc/First/K8/LawRowsText.lean) (`setting_of_entry`,
    Johnson/Desc/First/K8/LawRounds.lean): p's number of combinations is the one that follows from
    st for a request's own part, and st asks no work of this round.
  `settingB st`: a test on a setting: it gives 128 combinations for a request's own part, asks no
    work of this round, and has at most one instance.
  `rngE e`: a test on an entry: it is the entry with the name "RNG", e's number of matrix entries,
    and every other number as the format's default has it (count 1, all else 0).
Statements and proofs.
  `placeOk_yes`, `placeOk_of`, `settingB_yes`: what a yes says, and from what it follows.
  `tie`: for an entry with `rngE`: the kind's round at p has that entry if and only if columns p *
    p.tau is its number of matrix entries. The round pins the product alone: it cannot tell c
    columns at 128 combinations from 2 c at 64 (`place_half_tau`,
    Johnson/Desc/First/K8/MemberTeeth.lean). The third clause of `placeOk` pins tau to the setting's
    number, and the setting is a free variable; `settingB` is what reads 128.
  `written_rngE`: every round of the written first chain that has `isSmall`
    (Johnson/Flat/SmallOk.lean) has `rngE`. The facts on that list (25 such rounds; their shape; the
    three numbers of matrix entries, 12, 12 and 1 times) stand in Johnson/G/DryProofSmall.lean.
  `member_place`: at each such round x: every p whose number of combinations is the setting's, at a
    setting that asks no work of this round, whose columns times that number are x's matrix entries,
    which names a message for the matrices and one for the reads, which has as many numbers of rows
    as of columns, and none of whose asks has a 0 in its two numbers, has `placeOk` at x's declared
    form; x opens no tree and no stored part, so that form is the entry alone.
No evaluation here: those in Lean's kernel stand in Johnson/G/DryProofSmall.lean.

Limits. Tools, and facts on a written list. Not claimed: that the written list is what the planner
makes of the public files: no theorem in this file says so, and none is known in the files that it
imports (see the head of Johnson/G/DryProofLit.lean; what is shown elsewhere of the data that are
made of this list: the Limits of Johnson/Desc/First/K8/Member.lean). A round of the list is taken by
its value: the rounds of a sort (12, 12 and 1) are one value: no place in the chain is named, and
p's link is free. The numbers pin the sum of the matrices' columns, not the list of them, and
neither list of messages: these stay free variables. The setting is a free variable: no plan, state
or public file gives it here, and by the text of `rngCombinations` (OnBytes/Params/Planner.lean) the
setting with the target t, no work and one instance gives t combinations, for every t; no theorem
here says so. (At the library's written setting: Johnson/Desc/First/K8/MemberSetting.lean.)
`placeOk` does not ask the planner's own bound on the number of columns. No statement here names a
description of the protocol. Nothing on soundness.
-/
import Johnson.Desc.First.K8.MemberReady
import Johnson.G.DryProofSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member

open VerifiableInference.Number (isSmall)
open VerifiableInference.Number.Written (written_small written_shape)
open OnBytes.Params (Setting rngCombinations)
open OnBytes.Tie.Pv.Tail (rngRound rngSize)
open Johnson.G (dryProofFull)

/-- The kind's block at p declares just the round d; its tests on the plan say yes; the entry that
the planner's routine adds under st at p's columns is the kind's declared entry. -/
def placeOk (st : Setting) (p : Par) (d : Fmt.DeclaredRound) : Bool :=
  ((approximateRangeProofDrawKind (S := S) (Cl := Unit) atS p).rounds == [d]) &&
    (approximateRangeProofDrawKind (S := S) (Cl := Unit) atS p).planOk &&
    ((rngRound st (rngSize st (columns p))).entry == (round p).entry)

/-- What a yes says. -/
theorem placeOk_yes {st : Setting} {p : Par} {d : Fmt.DeclaredRound} (h : placeOk st p d = true) :
    round p = d ∧ p.tau = rngCombinations st .request ∧ st.workOf .small .request = 0 ∧
      p.ks ≠ [] ∧ columns p ≠ 0 ∧ p.tau ≠ 0 ∧ p.matsIn ≠ [] ∧ p.readsIn ≠ [] ∧
      p.ms.length = p.ks.length ∧ ∀ a ∈ p.asks, a.2.1 ≠ 0 ∧ a.2.2 ≠ 0 := by
  have c := Bool.and_eq_true_iff.1 h
  have c' := Bool.and_eq_true_iff.1 c.1
  have e : [round p] = [d] := eq_of_beq c'.1
  have q := (planOk_iff (Cl := Unit) atS p).1 c'.2
  obtain ⟨t, w⟩ := setting_of_entry p st q.2.1 (eq_of_beq c.2)
  exact ⟨(List.cons.inj e).1, t, w, q⟩

/-- From what it follows. -/
theorem placeOk_of {st : Setting} {p : Par} {d : Fmt.DeclaredRound} (e : round p = d)
    (ht : p.tau = rngCombinations st .request) (hw : st.workOf .small .request = 0)
    (h : p.ks ≠ [] ∧ columns p ≠ 0 ∧ p.tau ≠ 0 ∧ p.matsIn ≠ [] ∧ p.readsIn ≠ [] ∧
      p.ms.length = p.ks.length ∧ ∀ a ∈ p.asks, a.2.1 ≠ 0 ∧ a.2.2 ≠ 0) :
    placeOk st p d = true := by
  refine Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨?_, (planOk_iff (Cl := Unit) atS p).2 h⟩, ?_⟩
  · show ([round p] == [d]) = true
    rw [e]
    exact beq_self_eq_true _
  · rw [entry_eq p st ht hw]
    exact beq_self_eq_true _

/-- The setting gives 128 combinations for a request's own part, asks no work of this round, and has
at most one instance. -/
def settingB (st : Setting) : Bool :=
  rngCombinations st .request == 128 && st.workOf .small .request == 0 &&
    decide (st.instances ≤ 1)

/-- What a yes says. -/
theorem settingB_yes {st : Setting} (h : settingB st = true) :
    rngCombinations st .request = 128 ∧ st.workOf .small .request = 0 ∧ st.instances ≤ 1 := by
  have c := Bool.and_eq_true_iff.1 h
  have c' := Bool.and_eq_true_iff.1 c.1
  exact ⟨eq_of_beq c'.1, eq_of_beq c'.2, of_decide_eq_true c.2⟩

/-- The entry "RNG" with e's number of matrix entries and nothing else. -/
def rngE (e : Fmt.Entry) : Bool := e == { name := "RNG", trits := e.trits }

/-- **The tie.** -/
theorem tie (p : Par) {e : Fmt.Entry} (h : rngE e = true) :
    (round p).entry = e ↔ columns p * p.tau = e.trits := by
  have he : e = { name := "RNG", trits := e.trits } := eq_of_beq h
  constructor
  · intro h1
    rw [← h1]
    rfl
  · intro h1
    rw [he, ← h1]
    rfl

/-! ## The written list -/

/-- Every round of the written first chain with `isSmall` has `rngE`. -/
theorem written_rngE {x : Fmt.Round × List Fmt.Stored} (hx : x ∈ dryProofFull.1)
    (hs : isSmall x.1.entry = true) : rngE x.1.entry = true :=
  beq_iff_eq.2 (written_shape hx hs).1

/-- **The place, at a written round with `isSmall`.** -/
theorem member_place {x : Fmt.Round × List Fmt.Stored} (hx : x ∈ dryProofFull.1)
    (hs : isSmall x.1.entry = true) (st : Setting) (p : Par)
    (ht : p.tau = rngCombinations st .request) (hw : st.workOf .small .request = 0)
    (hc : columns p * p.tau = x.1.entry.trits) (hm : p.matsIn ≠ []) (hr : p.readsIn ≠ [])
    (hrows : p.ms.length = p.ks.length) (hasks : ∀ a ∈ p.asks, a.2.1 ≠ 0 ∧ a.2.2 ≠ 0) :
    placeOk st p { entry := x.1.entry } = true ∧ x.1.opens = [] ∧ x.2 = [] := by
  obtain ⟨_, _, _, ho, hst, _⟩ := written_shape hx hs
  have a := written_rngE hx hs
  have hn : x.1.entry.trits ≠ 0 := by
    have := written_small hx
    rw [hs] at this
    simpa using this.symm
  have hcol : columns p ≠ 0 := by
    intro e
    rw [e, Nat.zero_mul] at hc
    exact hn hc.symm
  have htau : p.tau ≠ 0 := by
    intro e
    rw [e, Nat.mul_zero] at hc
    exact hn hc.symm
  have hks : p.ks ≠ [] := by
    intro e
    apply hcol
    unfold columns
    rw [e]
    rfl
  have he : (round p).entry = x.1.entry := (tie p a).2 hc
  refine ⟨placeOk_of ?_ ht hw ⟨hks, hcol, htau, hm, hr, hrows, hasks⟩, ho, hst⟩
  show ({ entry := (round p).entry } : Fmt.DeclaredRound) = _
  rw [he]

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.placeOk_yes
#print axioms VerifiableInference.Desc.First.K8.Member.placeOk_of
#print axioms VerifiableInference.Desc.First.K8.Member.settingB_yes
#print axioms VerifiableInference.Desc.First.K8.Member.tie
#print axioms VerifiableInference.Desc.First.K8.Member.written_rngE
#print axioms VerifiableInference.Desc.First.K8.Member.member_place
