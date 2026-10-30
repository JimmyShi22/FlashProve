-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksDry.lean: what the rounds of a proof file's chains owe to the request, and what of
it is shown.

A description of a protocol has one list of rounds for all instances. The rounds of a proof's first
chain are those of a dry run of `Proof.firstBlock` (OnBytes/Proof/File.lean), whose links know the
request. The rounds of the second chain are those of a dry run of `Proof.secondBlock`
(OnBytes/Proof/Tail.lean), which starts from what the first dry run has returned (`FirstEnd`: the
statement, the book of trees, and `lin`, what the first part of the test on the table passes on).

What a dry run computes of the request. The checks of two sub-proofs read the request outside the
calls that a dry run skips: the first group of layers (the embedding's claim, `Layer.hearOwn`) and
the head (`Head.runForkHidH2`). So the VALUES in the state of these checks, in the rows that they
leave on the table, and in `FirstEnd.lin.claim`, differ from request to request in a dry run too.
The two dry runs are not equal as values. What is wanted is less: the same rounds.

 1. The second chain: SHOWN. `linSecondVerify` reads the claim of the first part only in a call that
    a dry run skips. So the second block gives the same result at every dry context, whatever the
    claim (`dryEq_secondBlock`), and its rounds are the same at two values of `lin` with the same
    four numbers (`LinFirst.Alike`, `secondBlock_rounds_alike`). The shape of the claim has no part.
 2. The first chain: NOT SHOWN HERE. `FirstFree p links links'` says, as a hypothesis by name: at
    all replies and every start the two dry runs both fail, or both return, with the same rounds,
    the same statement, the same book, and values of `lin` with the same four numbers.
    `PlannedFirstFree p` says it of the program's links at any two requests that
    `Head.coveredOf` takes. OnBytes/Flat/LinksFreeAll.lean shows it, under one premise.
 3. From that hypothesis: the first chain's rounds are the same (`first_rounds_free`), and so are
    the second chain's (`second_rounds_free`).

Main definitions: `LinFirst.Alike`, `FirstEnd.Alike`, `DryAlike`, `FirstFree`, `PlannedFirstFree`.
Main theorems: `dryEq_secondBlock`, `secondBlock_rounds_alike`, `first_rounds_free`,
`second_rounds_free`.

Not claimed: `FirstFree` of any links. Two dry runs that both fail count as alike, whatever the
names of the two failures. The statement speaks of the requests that `Head.coveredOf` takes and at
which `Verify.linksOf` returns: at a p where one of the two never returns it holds idly.
`PlannedFirstFree p` IS SAID OF EVERY VALUE p OF THE TYPE, AND NEED NOT HOLD AT EVERY ONE:
`Head.coveredOf` tests the tokens against `p.X.P.h.V`, the first group's check against
`p.X.layers.V`; at a p with a smaller number in the second place one request's tokens are refused in
the dry run and another's are taken. OnBytes/Flat/LinksFreeAll.lean shows it under `p.X.P.h.V ≤
p.X.layers.V`; `Verify.publicOf` lays one number at both places (read from its text). That the
statement and the book at the end of the first dry run are free of the request is read from the text
(a dry run adds no row), not shown. Nothing on a run on a view. For proofs only; no module of the
program imports this file.


-/
import OnBytes.Flat.BlocksKeep
import OnBytes.Proof.File
import OnBytes.Model.Verify

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- Closes `Blk.Keeps b` by the walk. -/
local macro "keeps_blk" : tactic => `(tactic| (show Over.K (m := Blk) _; keeps))

/-! ## The second chain -/

/-- Two values that the first part of the test on the table passes on have the same four numbers:
the number of W, of the split's mask message, of the group, and of the first fold's mask. Nothing is
asked of the claim. -/
def LinFirst.Alike (f f' : LinFirst) : Prop :=
  f.w = f'.w ∧ f.split = f'.split ∧ f.own = f'.own ∧ f.mask = f'.mask

/-- Then the second is the first with another claim. -/
theorem LinFirst.Alike.eq {f f' : LinFirst} (a : LinFirst.Alike f f') :
    f' = { f with claim := f'.claim } := by
  obtain ⟨h1, h2, h3, h4⟩ := a
  cases f
  cases f'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- The second part of the test on the table gives the same result at every dry context, whatever
the claim of the first part. -/
theorem dryEq_linSecondVerify (S : Params.LinShape) (first : LinFirst) (c' : LinClaim)
    (sharedSt : Statement) (sharedBook : TreeBook) (shared : LinShared) :
    Blk.DryEq (linSecondVerify S first sharedSt sharedBook shared)
      (linSecondVerify S { first with claim := c' } sharedSt sharedBook shared) := by
  unfold linSecondVerify
  apply Blk.dryEq_bind
  · keeps_blk
  intro omega
  by_cases hS : S.ownSplitNeeded = true <;> simp only [hS, ↓reduceIte]
  all_goals
    iterate 4
      apply Blk.dryEq_bind
      · keeps_blk
      intro _
    exact Blk.dryEq_bind2 (Blk.keeps_getOnView _ _ _) (Blk.dryEq_getOnView _ _ _ _) fun row =>
      Blk.DryEq.refl _

/-- **The block of a second chain gives the same result at every dry context, whatever the claim of
the first part.** -/
theorem dryEq_secondBlock (S : Params.LinShape) (first : LinFirst) (c' : LinClaim)
    (shared : Proof.SharedEnd) :
    Blk.DryEq (Proof.secondBlock S first shared)
      (Proof.secondBlock S { first with claim := c' } shared) := by
  unfold Proof.secondBlock
  apply Blk.dryEq_bind2 _ (dryEq_linSecondVerify S first c' _ _ _) fun x => Blk.DryEq.refl _
  keeps_blk

/-- Two blocks that give the same result at every dry context state the same rounds. -/
theorem rounds_of_dryEq {α : Type} {b b' : Blk α} (h : Blk.DryEq b b') (st : Start) :
    b.rounds st = b'.rounds st := by
  unfold Blk.rounds Blk.dryRun
  rw [h.dryRunNamed st]

/-- **The rounds of a second chain's block hang on four numbers of what the first part passes on.**
-/
theorem secondBlock_rounds_alike (S : Params.LinShape) {f f' : LinFirst}
    (a : LinFirst.Alike f f') (shared : Proof.SharedEnd) (st : Start) :
    (Proof.secondBlock S f shared).rounds st = (Proof.secondBlock S f' shared).rounds st := by
  rw [a.eq]
  exact rounds_of_dryEq (dryEq_secondBlock S f f'.claim shared) st

/-! ## The first chain: the hypothesis by name -/

/-- Two values that a first chain's block returns: the same statement, the same book of trees, and
the same four numbers of `lin`. -/
def FirstEnd.Alike (e e' : Proof.FirstEnd) : Prop :=
  e.st = e'.st ∧ e.book = e'.book ∧ LinFirst.Alike e.lin e'.lin

/-- Two dry runs of first blocks: both fail, or both return, with the same rounds and with values
that are alike. -/
def DryAlike : Option (List (Fmt.Round × List Fmt.Stored) × Proof.FirstEnd) →
    Option (List (Fmt.Round × List Fmt.Stored) × Proof.FirstEnd) → Prop
  | none, none => True
  | some x, some x' => x.1 = x'.1 ∧ FirstEnd.Alike x.2 x'.2
  | _, _ => False

/-- What is asked of the blocks of the links of two requests: at all replies and every start the dry
runs of the first chain's block are alike. A hypothesis by name; nothing here shows it of the
model's links. -/
def FirstFree (p : Params.First) (links links' : Blk Proof.LinksResult) : Prop :=
  ∀ (reply reply' : E) (st : Start),
    DryAlike ((Proof.firstBlock p links reply).dryRun st)
      ((Proof.firstBlock p links' reply').dryRun st)

/-- The same of the program's links: at any two requests that `Head.coveredOf` takes. p: what
`Verify.planned` returns at the three public files. -/
def PlannedFirstFree (p : Verify.Planned) : Prop :=
  ∀ (so so' : Head.StOwn) (cov cov' : Head.Covered) (links links' : Array Stages.LinkH),
    Head.coveredOf so p.X.T p.X.P.h.V = .ok cov → Head.coveredOf so' p.X.T p.X.P.h.V = .ok cov' →
    Verify.linksOf p.X cov = .ok links → Verify.linksOf p.X cov' = .ok links' →
    FirstFree p.chains.proof.first
      (Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
        p.chains.proof.first p.X.layers.wsLay)
      (Stages.runLinksH (p.built.links.zipWith (fun b l => { b with run := l.run }) links')
        p.chains.proof.first p.X.layers.wsLay)

/-! ## What follows from it -/

/-- The first chain's rounds are the same at the two requests and at any two replies. -/
theorem first_rounds_free {p : Params.First} {links links' : Blk Proof.LinksResult}
    (h : FirstFree p links links') (reply reply' : E) (st : Start) :
    (Proof.firstBlock p links reply).rounds st = (Proof.firstBlock p links' reply').rounds st := by
  have a := h reply reply' st
  unfold Blk.rounds
  revert a
  cases (Proof.firstBlock p links reply).dryRun st <;>
    cases (Proof.firstBlock p links' reply').dryRun st <;> intro a
  · rfl
  · exact a.elim
  · exact a.elim
  · exact congrArg some a.1

/-- The second chain's rounds are the same: the block at what the first dry run has passed on, from
the start that is made of what it has returned. -/
theorem second_rounds_free {p : Params.First} {links links' : Blk Proof.LinksResult}
    (h : FirstFree p links links') {reply reply' : E} {st : Start}
    {x x' : List (Fmt.Round × List Fmt.Stored) × Proof.FirstEnd}
    (h1 : (Proof.firstBlock p links reply).dryRun st = some x)
    (h2 : (Proof.firstBlock p links' reply').dryRun st = some x')
    (t : Proof.TailPublic) (shared : Proof.SharedEnd) (first : ChainRead) :
    x.1 = x'.1 ∧
    (Proof.secondBlock t.lin x.2.lin shared).rounds (Proof.secondStart t x.2 first) =
      (Proof.secondBlock t.lin x'.2.lin shared).rounds (Proof.secondStart t x'.2 first) := by
  have a := h reply reply' st
  rw [h1, h2] at a
  obtain ⟨a1, a2, a3, a4⟩ := a
  refine ⟨a1, ?_⟩
  have e : Proof.secondStart t x.2 first = Proof.secondStart t x'.2 first := by
    unfold Proof.secondStart
    rw [a2, a3]
  rw [e]
  exact secondBlock_rounds_alike t.lin a4 shared _

end OnBytes.Flat
