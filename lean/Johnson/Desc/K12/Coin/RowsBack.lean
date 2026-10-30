-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/RowsBack.lean: **WHAT THE OPEN ROWS OF ANOTHER GROUP, AND AN ELDER MESSAGE's SAMPLE ROWS, SAY RIDES BACK (AND ON) OVER A YES OF A PROXIMITY TEST AT THE SHARED CHAIN's TWO SEATS.** Statements and proofs.

What for. The ledger's clause at the shared chain's block 9 (NineAt.lean: the premise hrows) asks that three classes of rows on G_omega, shown at the record BEHIND the test on G_u, hold at the record IN FRONT of it. A row's claim is a
sum over all messages of the statement at which it is said (Means.Says), and the test brings messages: so the two records' statements part. The law says_extends (Johnson/Desc/Means/Keeps.lean) carries a row THAT HAS PASSED THE
TESTS OF THE ADDING (RowIn) between a statement and a later one. Here are its premises at the test.
  seat_extends   the statement behind a yes is a later statement (Means.Extends: the codes · every message there with its shape): k12_out has just these two clauses.
  rowsOn_same    the open rows of a group that the yes leaves to the letter are the same list (seat_leaves, SamplesThrough.lean: every OTHER group that stood).
  **allSay_onGu | allSay_onGomega**  for a statement in order in front (Means.InOrder d.st) and a group that stood, other than the one under test: any slice of g's open rows says of the words m behind the test just what it says in front: an
                                    equivalence.
  **samples_onGu | samples_onGomega**  for an elder message o (at G_u: not the mask handed in): its sample rows are the same list, and they say behind just what they say in front.
WHAT IS NOT HERE: the extractor's half of hrows (the words read off the witness that the block's extractor returns agree with the words read off the witness handed to it, at G_omega's members): it stands at the filling's reader of
words. THAT THE STATEMENT IN FRONT IS IN ORDER is a premise: an invariant of the chain's walk up to that border.
Limits. On plain data. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Coin.SamplesThrough
import Johnson.Desc.Means.Order
import Johnson.Desc.K14.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open OnBytes.Means (Extends InOrder Says AllSay says_extends)
open _root_.Desc.K14 (St Lin)
open _root_.Desc.K14.Law (rowsOn)

/-- **The statement behind a yes is a later statement.** -/
theorem seat_extends (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') : Extends d.st d'.st := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  have o1 := k12_out p he ha _ t' rs gs ht'
  exact ⟨o1.codes, o1.shapes⟩

/-- The open rows of a group that the yes leaves to the letter. -/
theorem rowsOn_same (d d' : St) (q : ℕ) (h : d'.st.groups[q]? = d.st.groups[q]?) :
    rowsOn d' q = rowsOn d q := by
  unfold rowsOn
  rw [h]

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- The core: a later statement, one list of rows that have passed the tests in front. -/
theorem allSay_later (S S' : Statement) (hE : Extends S S') (G : Group) (l : List OnBytes.Row)
    (hr : ∀ r ∈ l, Means.RowIn S G r) (m : Means.Words K) : AllSay ρ S' l m ↔ AllSay ρ S l m :=
  ⟨fun c r hm => (says_extends ρ hE (hr r hm) m).1 (c r hm),
    fun c r hm => (says_extends ρ hE (hr r hm) m).2 (c r hm)⟩

/-- **Another group's open rows, at a seat.** -/
theorem allSay_seat (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') (hI : InOrder d.st) (q : ℕ) (lt : q < d.st.groups.size) (hq : q ≠ g d.loc) (i n : ℕ)
    (m : Means.Words K) :
    AllSay ρ d'.st (((rowsOn d' q).drop i).take n) m ↔
      AllSay ρ d.st (((rowsOn d q).drop i).take n) m := by
  have hE := seat_extends g mask p he ha d d' rs gs h
  have e := (seat_leaves g mask p he ha d d' rs gs h).2.2.1 q lt hq
  rw [rowsOn_same d d' q e]
  refine allSay_later ρ d.st d'.st hE d.st.groups[q] _ (fun r hr => ?_) m
  have hr' : r ∈ rowsOn d q := List.mem_of_mem_drop (List.mem_of_mem_take hr)
  unfold rowsOn at hr'
  rw [Array.getElem?_eq_getElem lt] at hr'
  exact hI.rows q _ (Array.getElem?_eq_getElem lt) r hr'

/-- **An elder message's sample rows, at a seat.** -/
theorem samples_seat (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') (hI : InOrder d.st) (o : ℕ) (lt : o < d.st.oracles.size) (hm : mask d.loc ≠ some o)
    (m : Means.Words K) :
    (∀ x', d'.st.oracles[o]? = some x' → ∀ r ∈ x'.sampleRows.toList, Says ρ d'.st r m) ↔
      ∀ x, d.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Says ρ d.st r m := by
  have hE := seat_extends g mask p he ha d d' rs gs h
  have e := (seat_leaves g mask p he ha d d' rs gs h).2.1 o lt hm
  have hx : d.st.oracles[o]? = some d.st.oracles[o] := Array.getElem?_eq_getElem lt
  rw [hx] at e
  obtain ⟨x', hx', ex⟩ := Option.map_eq_some_iff.1 e
  have er : x'.sampleRows = d.st.oracles[o].sampleRows := congrArg (fun q => q.2.2) ex
  constructor
  · intro c x hx0 r hr
    obtain rfl : d.st.oracles[o] = x := Option.some.inj (hx.symm.trans hx0)
    exact (says_extends ρ hE (hI.samples o _ hx r hr) m).1 (c x' hx' r (by rw [er]; exact hr))
  · intro c y hy r hr
    obtain rfl : x' = y := Option.some.inj (hx'.symm.trans hy)
    rw [er] at hr
    exact (says_extends ρ hE (hI.samples o _ hx r hr) m).2 (c _ hx r hr)

/-- **AT THE TEST ON G_u.** -/
theorem allSay_onGu (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hI : InOrder d.st) (q : ℕ) (lt : q < d.st.groups.size) (hq : q ≠ d.loc.gU) (i n : ℕ)
    (m : Means.Words K) :
    AllSay ρ d'.st (((rowsOn d' q).drop i).take n) m ↔
      AllSay ρ d.st (((rowsOn d q).drop i).take n) m :=
  allSay_seat ρ _ _ p he ha d d' rs gs h hI q lt hq i n m

theorem samples_onGu (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hI : InOrder d.st) (o : ℕ) (lt : o < d.st.oracles.size) (hm : d.loc.firstMask ≠ some o)
    (m : Means.Words K) :
    (∀ x', d'.st.oracles[o]? = some x' → ∀ r ∈ x'.sampleRows.toList, Says ρ d'.st r m) ↔
      ∀ x, d.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Says ρ d.st r m :=
  samples_seat ρ _ _ p he ha d d' rs gs h hI o lt hm m

/-- **AT THE TEST ON G_omega.** -/
theorem allSay_onGomega (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hI : InOrder d.st) (q : ℕ) (lt : q < d.st.groups.size) (hq : q ≠ d.loc.gOmega) (i n : ℕ)
    (m : Means.Words K) :
    AllSay ρ d'.st (((rowsOn d' q).drop i).take n) m ↔
      AllSay ρ d.st (((rowsOn d q).drop i).take n) m :=
  allSay_seat ρ _ _ p he ha d d' rs gs h hI q lt hq i n m

theorem samples_onGomega (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hI : InOrder d.st) (o : ℕ) (lt : o < d.st.oracles.size) (m : Means.Words K) :
    (∀ x', d'.st.oracles[o]? = some x' → ∀ r ∈ x'.sampleRows.toList, Says ρ d'.st r m) ↔
      ∀ x, d.st.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, Says ρ d.st r m :=
  samples_seat ρ _ (fun _ => none) p he ha d d' rs gs h hI o lt (by simp) m

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.seat_extends
#print axioms VerifiableInference.Desc.K12.Coin.allSay_onGu
#print axioms VerifiableInference.Desc.K12.Coin.samples_onGu
#print axioms VerifiableInference.Desc.K12.Coin.allSay_onGomega
#print axioms VerifiableInference.Desc.K12.Coin.samples_onGomega
