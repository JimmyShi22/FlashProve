-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Returns.lean.
WHAT IT IS NOT. NOT YET A LAW OF THE FORM "premises on the state's own book-keeping fields and the
named tests on values: the routine returns, and the book-keeping fields behind are these": ONE
PREMISE, hh, IS ITSELF A ROUTINE's RETURN: that the head's hearing (hear, Kinds/Head.lean) returns
on the rounds and uses them up. Under a law "room in the ledger and rounds of the table's shape: the
hearing returns", which is not here, k6_decides becomes a law of that form by one call. Every
statement is CONDITIONAL. No state and no rounds are shown at which the premises hold. What an
accept leaves of the state as it was is not said here, but for the ledger. Nothing on soundness, on
completeness or on hiding.
WHAT IT IS. When the decision of the output head's bare sub-protocol (K6; blockAt h iU3 work l,
Stored/HeadSeatAt.lean) accepts, and three things on the state behind, CUT BY WHAT EACH SPENDS (BUT
FOR ONE: k6_reads_back asks its two premises more for three clauses and spends them for the first).
  k6_yes_is      the other way: CONDITIONAL on an accept: the letters were read, the hearing
                 returned and used the rounds up, no mark in front, the opened head's link with what
                 the lookup left; and the ledger behind is the hearing's own return.
  k6_decides     (i) CONDITIONAL: no mark, the opened head's link, the letters are read, rounds of
                 the table's shape (ShapedNZ, Law/K06EveryList.lean), the hearing returns: THE
                 DECISION ACCEPTS, and the ledger behind is the hearing's own return. IT SPENDS NO
                 TEST ON A SENT VALUE: not "every word is below the prime" (Canonical), not "the
                 ledger is well laid", not the plan's test. So, BESIDE WHAT THE HEARING's RETURN MAY
                 ASK, this kind's list of named tests on values is empty.
  k6_ledger      CONDITIONAL: behind ANY accept the ledger is the hearing's own return.
  k6_takes       (ii) CONDITIONAL: the plan's test, a well laid ledger, the letters, the hearing's
                 return; no accept: the hearing has taken just 41 + 8 lt + 4 lPd slots (Takes,
                 Law/Takes.lean): a number of the plan's.
  k6_reads_back  (iii) CONDITIONAL: a well laid ledger and Canonical besides: behind any accept the
                 seat reads back what was heard, the same letters, the same points of the lookup.
                 (In the library's seatBack_at the first clause alone spends these two premises.)
LETTERS. g: the letters that are read at the state: pinned by hg. H, G: the hearing's return: pinned
by hh. hear is read at g's letters, through the class Given (Kinds/HeadFrame.lean).
CALLED: tape_returnsNZ (Law/K06EveryList.lean), rounds_plain, lays_of, decide_returns,
decide_hears_at, Came.decide_record, Came.given_ok, seatAt_fit, seatBack_at, letters_of_lookup,
hear_takes_plan, sized_of_wellLaid.
TYPED ANEW, AND WHY: k6_decides has the lines of Law/K06EveryList.lean's yes_of_heard but the last:
that one takes HeardK6 whole, Canonical in it, and a well laid ledger, which the yes does not spend.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06EveryList
import Johnson.Desc.Kinds.Law.RowPromise
import Johnson.Desc.Kinds.Law.Takes
import Johnson.Desc.Kinds.Law.KeepsAt
import Johnson.Desc.Kinds.Law.HeardBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)
open OnBytes.Model (Fork)
open Norm (lt lPd)
open VerifiableInference.Desc.First.Tape (tapeT)

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat)

/-- EVERY ACCEPT OF THE DECISION: the letters were read, the hearing returned and used the rounds
up, no mark, the opened head's link; AND THE LEDGER BEHIND IS THE HEARING's OWN RETURN. CONDITIONAL:
the accept is a premise. -/
theorem k6_yes_is {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (G : Fork), given (parOf h work) (seatAt h iU3) s = .ok g ∧
      hear ((seatAt h iU3).ledger s) rs = some (H, G, []) ∧ s.failed = none ∧ HeadOpen s ∧
      (seatAt h iU3).ledger s' = G := by
  obtain ⟨o, F1, X, Q, ho, hop, hf, _⟩ := Came.decide_record h iU3 work l hd
  obtain ⟨g, H, F, w, s1, s2, hg, hh, e1, e2, hs'⟩ := decide_hears_at h iU3 work l s s' rs gs hd
  obtain ⟨z, _, hz, _⟩ := Came.given_ok _ _ s g hg
  have hz' : (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = some z := hz
  have hl : o.lookHeard.isSome = true := by
    cases hx : o.lookHeard with
    | some x => rfl
    | none =>
      have hn : s.lookHeard? = none := by simp [S.lookHeard?, ho, hop, hx]
      rw [hn] at hz'
      cases hz'
  exact ⟨g, H, F, hg, hh, hf, ⟨o, ho, hop, hl⟩,
    by rw [hs']; exact seatAt_fit h iU3 s F H w s1 s2 e1 e2⟩

/-- (i) THE DECISION RETURNS. CONDITIONAL. No premise TESTS a value that is sent or sampled, but for
«the last sampled element of a round that asks so is not 0» inside ShapedNZ; hh speaks of the rounds
whole: it is a routine's return. -/
theorem k6_decides (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (H : HeardAll)
    (G : Fork) (hfail : s.failed = none) (hopen : HeadOpen s) (g : Given)
    (hg : given (parOf h work) (seatAt h iU3) s = .ok g)
    (hsh : ShapedNZ rs (@rounds (parOf h work).sizes))
    (hh : hear ((seatAt h iU3).ledger s) rs = some (H, G, [])) :
    ∃ s' : S, (blockAt h iU3 work l).decide s rs gs = .ok s' ∧
      (seatAt h iU3).ledger s' = G := by
  obtain ⟨z, y, _, _, _, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
  letI : Sizes := (parOf h work).sizes
  letI : Policy := (parOf h work).policy
  letI : Request := (seatAt h iU3).request s
  letI : Token := ⟨y⟩
  letI : FinalNorm.In := (fromLookup (parOf h work).floor z.1 z.2).norm
  letI : In := (fromLookup (parOf h work).floor z.1 z.2).head
  have htape := tape_returnsNZ (parOf h work).work rs rounds hsh rounds_plain
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp htape
  have ht' : tapeT { rows := fun e => e.name == "BAT-sigma" } rs
      (((parOf h work).declare rounds).map (·.entry)) = some t := by
    rw [← ht]
    unfold Par.declare headRule
    rw [List.map_map]
    rfl
  obtain ⟨s1, s2, e1, e2⟩ := lays_of h iU3 s hfail hopen G H
  obtain ⟨w, hd⟩ := decide_returns (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s s1 s2 rs gs
    _ t H G hg ht' hh e1 e2
  exact ⟨_, hd, seatAt_fit h iU3 s G H w s1 s2 e1 e2⟩

/-- Behind ANY accept the ledger is the hearing's own return. CONDITIONAL. -/
theorem k6_ledger {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {H : HeardAll} {G : Fork} (g : Given) (hg : given (parOf h work) (seatAt h iU3) s = .ok g)
    (hh : hear ((seatAt h iU3).ledger s) rs = some (H, G, []))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') : (seatAt h iU3).ledger s' = G := by
  obtain ⟨g2, H2, F2, w, s1, s2, hg2, hh2, e1, e2, hs'⟩ :=
    decide_hears_at h iU3 work l s s' rs gs hd
  rw [hg] at hg2
  obtain rfl : g = g2 := Except.ok.inj hg2
  have hsame : (H2, F2, ([] : List Fmt.RoundView)) = (H, G, []) := Option.some.inj (hh2.symm.trans hh)
  obtain ⟨rfl, hrest⟩ := Prod.mk.inj hsame
  obtain ⟨rfl, _⟩ := Prod.mk.inj hrest
  rw [hs']
  exact seatAt_fit h iU3 s F2 H2 w s1 s2 e1 e2

/-- (ii) WHAT THE HEARING TAKES OF THE LEDGER. CONDITIONAL. (The numbers lt and lPd are the plan's
own, by the letI; by hg they are g's too.) -/
theorem k6_takes (hplan : (parOf h work).ok = true) {s : S} {rs : List Fmt.RoundView} {H : HeardAll}
    {G : Fork} (hWL : WellLaid ((seatAt h iU3).ledger s)) (g : Given)
    (hg : given (parOf h work) (seatAt h iU3) s = .ok g)
    (hh : hear ((seatAt h iU3).ledger s) rs = some (H, G, [])) :
    letI : Sizes := (parOf h work).sizes
    Takes ((seatAt h iU3).ledger s) G (41 + 8 * lt + 4 * lPd) := by
  obtain ⟨z, y, _, _, hP, rfl⟩ := Came.given_ok (parOf h work) (seatAt h iU3) s g hg
  letI : Sizes := (parOf h work).sizes
  letI : Policy := (parOf h work).policy
  letI : Request := (seatAt h iU3).request s
  letI : Token := ⟨y⟩
  obtain ⟨_, hzt, _⟩ :=
    letters_of_lookup (parOf h work).sT (parOf h work).floor z.1 z.2 hplan hP
  letI : FinalNorm.In := (fromLookup (parOf h work).floor z.1 z.2).norm
  letI : In := (fromLookup (parOf h work).floor z.1 z.2).head
  exact hear_takes_plan (sized_of_wellLaid hWL) hzt hh

/-- (iii) WHAT THE SEAT READS BACK BEHIND AN ACCEPT. CONDITIONAL. -/
theorem k6_reads_back {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {H : HeardAll} {G : Fork} (hWL : WellLaid ((seatAt h iU3).ledger s)) (hcan : Canonical rs)
    (g : Given) (hg : given (parOf h work) (seatAt h iU3) s = .ok g)
    (hh : hear ((seatAt h iU3).ledger s) rs = some (H, G, []))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    (seatAt h iU3).heard s' = some H ∧
      given (parOf h work) (seatAt h iU3) s' = given (parOf h work) (seatAt h iU3) s ∧
      (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
  obtain ⟨g2, H2, F2, w, s1, s2, hg2, hh2, e1, e2, hs'⟩ :=
    decide_hears_at h iU3 work l s s' rs gs hd
  rw [hg] at hg2
  obtain rfl : g = g2 := Except.ok.inj hg2
  have hsame : (H2, F2, ([] : List Fmt.RoundView)) = (H, G, []) := Option.some.inj (hh2.symm.trans hh)
  obtain ⟨rfl, hrest⟩ := Prod.mk.inj hsame
  obtain ⟨rfl, _⟩ := Prod.mk.inj hrest
  obtain ⟨_, bH, bG, bZ⟩ :=
    seatBack_at h iU3 work s g rs [] F2 H2 w s1 s2 hg hWL hcan hh2 e1 e2
  rw [hs']
  exact ⟨bH, bG, bZ⟩

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_yes_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_decides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_ledger
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_takes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_reads_back
