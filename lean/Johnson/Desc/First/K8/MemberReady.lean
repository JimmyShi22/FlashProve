-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/MemberReady.lean: the smallness test's first half (the draw of the matrix,
Johnson/Desc/First/K8/Hear.lean) at the state that the verifier carries along the first chain (`S`,
Johnson/Desc/First/State.lean; the docstrings below and the neighbouring files call it the carried
record; it is no out-of-domain sample): when the block says yes, as a property of the state in front
alone. Definitions and rules; no test is evaluated in this file. Johnson/Desc/First/K8/Member.lean
builds its example on them.

Why. The rows on this block (the propositions by name in Johnson/Desc/First/K8/LawRowsText.lean and
Johnson/Desc/First/K8/LawRowsMeans.lean) hold "for all", and some have a yes of the block's step
among their premises. No byte of the prover belongs to the block's stretch: its one round shows
nothing and opens nothing. So whether the step says yes at a written transcript of the round hangs
on the place's numbers and on the state in front, and on nothing else. Here that is said.

Definitions.
  `ReadyAt p s tl`: nine clauses, by name. `link`: a link is open in s with the smallness test's
    state tl. `closed`: tl's list of tables is closed. `nothingOwed`: no count of batched rows is
    owed. `notDrawn`, which is double: tl's field for the matrix is empty, and no draw is counted.
    `matrices`, `ks`, `ms`, `tau`, `tabs`: tl's number of matrices, their columns, their rows, its
    number of combinations and the shapes of its closed list of tables are the place's. They are the
    clauses of `MeansAtS` (Johnson/Desc/First/K8/HearMeans.lean) that do not name the state handed
    on. `Ready p s`: for some tl.
  `readyB p s`: the same as one test with code: the seat's eight readings. Eight for nine: that a
    link is open follows from the readings (`ready_of_tests`).
Statements and proofs.
  `ReadyAt.tests`, `ready_of_tests`: from the nine clauses to the eight readings, and back.
  `ready_iff`: readyB p s = true if and only if Ready p s.
  `decide_iff_ready`: the decision says yes on a round r, and hands on s', if and only if Ready p s
    and s' is s with r's entries and the first columns laid into the state.
  `step_yes_of_ready`: at every ready state and every written transcript of the round the step says
    yes, takes no column, and lays the list of the typed challenge.
  `ready_of_step`: a yes of the step, on whatever rounds, has a ready state in front.
  `fits_of_ready`: at a ready state the place's numbers (how many matrices, each one's columns, the
    combinations) are those of the library's sizes of the state. `good_at_sizes`: the proved block
    is good at every caller with the library's sizes of a state: of every state: it reads no clause
    of `ReadyAt`.

Limits. These are tools: they hold of every place and state and name no description of the
protocol. Not claimed: that the state in front of the block's place is ready in any run: that is a
law on the blocks in front, or a run. Not claimed: that the place's numbers are a plan's.
Nothing on soundness.
-/
import Johnson.Desc.First.K8.LawRowsMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Member

open Iop Prob Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
  OnBytes.Tie.Pv.Row OnBytes.Tie.Pv.Tail KObj VerifiableInference.OnPublicFiles

/-- The record in front is ready for the draw, with the smallness test's record tl. -/
structure ReadyAt (p : Par) (s : S) (tl : HTailF2) : Prop where
  link : s.tl? = some tl
  closed : tl.funClosed = true
  nothingOwed : s.rowsOwed = none ∨ s.rowsOwed = some 0
  notDrawn : tl.cfF.size = 0 ∧ tl.foldDrawn = 0
  matrices : tl.NM = p.ks.length
  ks : tl.mats.toList.map (·.k) = p.ks
  ms : tl.mats.toList.map (·.m) = p.ms
  tau : tl.tau = p.tau
  tabs : tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = K8.tabs p

/-- The record in front is ready for the draw. -/
def Ready (p : Par) (s : S) : Prop := ∃ tl, ReadyAt p s tl

/-- The same as one test, with code. -/
def readyB (p : Par) (s : S) : Bool :=
  atS.closed s && atS.nothingOwed s && !atS.drawn s && atS.matrices s == p.ks.length &&
    atS.ks s == p.ks && atS.ms s == p.ms && atS.tau s == p.tau && atS.tabs s == K8.tabs p

/-- The seat's eight readings at a ready record. -/
theorem ReadyAt.tests {p : Par} {s : S} {tl : HTailF2} (R : ReadyAt p s tl) :
    atS.closed s = true ∧ atS.nothingOwed s = true ∧ atS.drawn s = false ∧
      atS.matrices s = p.ks.length ∧ atS.ks s = p.ks ∧ atS.ms s = p.ms ∧ atS.tau s = p.tau ∧
      atS.tabs s = K8.tabs p :=
  ⟨(closed_atS s).2 ⟨tl, R.link, R.closed⟩, (nothingOwed_atS s).2 R.nothingOwed,
    (drawn_atS s).2 ⟨tl, R.link, R.notDrawn⟩, by simpa [atS, R.link] using R.matrices,
    by simpa [atS, R.link] using R.ks, by simpa [atS, R.link] using R.ms,
    by simpa [atS, R.link] using R.tau, by simpa [atS, R.link] using R.tabs⟩

/-- And the way back. -/
theorem ready_of_tests {p : Par} {s : S} (c1 : atS.closed s = true)
    (c2 : atS.nothingOwed s = true) (c3 : atS.drawn s = false)
    (c4 : atS.matrices s = p.ks.length) (c5 : atS.ks s = p.ks) (c5' : atS.ms s = p.ms)
    (c6 : atS.tau s = p.tau) (c7 : atS.tabs s = K8.tabs p) : Ready p s := by
  obtain ⟨tl, ht, a1⟩ := (closed_atS s).1 c1
  obtain ⟨t3, e3, a3⟩ := (drawn_atS s).1 c3
  rw [ht] at e3
  obtain rfl : tl = t3 := Option.some.inj e3
  exact ⟨tl, ht, a1, (nothingOwed_atS s).1 c2, a3, by simpa [atS, ht] using c4,
    by simpa [atS, ht] using c5, by simpa [atS, ht] using c5', by simpa [atS, ht] using c6,
    by simpa [atS, ht] using c7⟩

/-- **The test says yes just at the ready records.** -/
theorem ready_iff (p : Par) (s : S) : readyB p s = true ↔ Ready p s := by
  unfold readyB
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c5'⟩, c6⟩, c7⟩
    exact ready_of_tests c1 c2 c3 c4 c5 c5' c6 c7
  · rintro ⟨tl, R⟩
    obtain ⟨c1, c2, c3, c4, c5, c5', c6, c7⟩ := R.tests
    exact ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c5'⟩, c6⟩, c7⟩

/-- **The decision, in terms of the record in front.** -/
theorem decide_iff_ready {Cl : Type} (p : Par) (s s' : S) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s [r] gs = .ok s' ↔
      ∃ tl, ReadyAt p s tl ∧
        s' = s.putTl { tl with cfF := r.drawn.trits.toArray, cfFirst := firstColumns p } := by
  rw [decide_atS_iff]
  constructor
  · rintro ⟨tl, a0, a1, a2, a3, a4, a5, a5', a6, a7, e⟩
    exact ⟨tl, ⟨a0, a1, a2, a3, a4, a5, a5', a6, a7⟩, e⟩
  · rintro ⟨tl, R, e⟩
    exact ⟨tl, R.link, R.closed, R.nothingOwed, R.notDrawn, R.matrices, R.ks, R.ms, R.tau, R.tabs,
      e⟩

/-- At a ready record the place's numbers are those of the library's sizes of the record. -/
theorem fits_of_ready {p : Par} {s : S} {tl : HTailF2} (R : ReadyAt p s tl) :
    Fits p (OnBytes.Tie.Pv.Tail.sizeOf tl).size := fits_of_tests tl p R.matrices R.ks R.tau

/-- The proved block is good at every caller with the library's sizes of a record: of every record:
no clause of `ReadyAt` is read. -/
theorem good_at_sizes (tl : HTailF2) (d : TailCallerOn)
    (hd : d.c.s = (OnBytes.Tie.Pv.Tail.sizeOf tl).size) : (KTailRngOn.blk d).Good :=
  block_good_atS d tl hd

/-- **At every ready record and every written transcript of the round the step says yes.** -/
theorem step_yes_of_ready {Cl : Type} {p : Par} {st : S} {tl : HTailF2} (R : ReadyAt p st tl)
    (m : (roundT (Run.ckP .two) (rdt p)).up.Msg) (c : (roundT (Run.ckP .two) (rdt p)).up.Chal)
    (ft : Nat) (cols : List Col) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st
        (vT [rdt p] ((m, c, ()) : Tr (uLT (Run.ckP .two) [rdt p]))) cols =
      .ok (st.putTl { tl with
        cfF := listOf (matrixOf (fits_of_ready R) c), cfFirst := firstColumns p }, 0) := by
  obtain ⟨c1, c2, c3, c4, c5, c5', c6, c7⟩ := R.tests
  refine (hearLaw S Cl p _ (fits_of_ready R) atS m c ft st _ 0 cols).2
    ⟨c1, c2, c3, c4, c5, c5', c6, c7, ?_, rfl⟩
  simp [atS, R.link]

/-- **A yes of the step has a ready record in front.** -/
theorem ready_of_step {Cl : Type} {p : Par} {ft : Nat} {st st' : S} {rs : List Fmt.RoundView}
    {cols : List Col} {n : Nat} (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols = .ok (st', n)) :
    Ready p st := by
  obtain ⟨_, _, _, _, c1, c2, c3, c4, c5, c5', c6, c7, _⟩ := step_ok atS p ft st st' rs cols n h
  exact ready_of_tests c1 c2 c3 c4 c5 c5' c6 c7

end VerifiableInference.Desc.First.K8.Member

#print axioms VerifiableInference.Desc.First.K8.Member.ReadyAt.tests
#print axioms VerifiableInference.Desc.First.K8.Member.ready_of_tests
#print axioms VerifiableInference.Desc.First.K8.Member.ready_iff
#print axioms VerifiableInference.Desc.First.K8.Member.decide_iff_ready
#print axioms VerifiableInference.Desc.First.K8.Member.fits_of_ready
#print axioms VerifiableInference.Desc.First.K8.Member.good_at_sizes
#print axioms VerifiableInference.Desc.First.K8.Member.step_yes_of_ready
#print axioms VerifiableInference.Desc.First.K8.Member.ready_of_step
