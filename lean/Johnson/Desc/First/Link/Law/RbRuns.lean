-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/RbRuns.lean: WHAT THE FOUR BOOLS OF THE TABLE's PROMISE READ OF THE
RECORD IS LEFT AS IT WAS BY ALL THAT A LINK's RUNS AND THE BATCHING KIND's LENS WRITE: one relation
`Rb` between the record in front and the record behind. Definitions and theorems at the first
chain's record: the stuff for «the record's half of the promise is handed on» at the link's blocks
whose rows close and open no class of rows and no pin.

What is said.
  `Rq`, `Rb`, `Rb.refl`, `Rb.trans`, `Rb.rq`, `rb_putTl`, `rb_putFork`, `rb_putLink`,
    `rb_head` LIE IN THE LIGHT FILE RbDef.lean. Here: `rb_wrote`: what a run of
    the layers' own kind writes stands in Rb. `rests_rb`: **`RelRests Rb`** (RelRuns.lean): so every
    known run of a link's two orders stands in Rb. `part_reads`. `rb_set`: the lens's writing of a
    part with the statement and the link's number that it has read.

Limits. The rows that are owed a count are NOT in Rb: the draw lays them, the one equation pays them
(OwedRides.lean, OwedPaid.lean). Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.RbDef
import Johnson.Desc.First.Link.Law.RelRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S standOf)

theorem rb_wrote {e e₁ : S} {a : First.LayOwn} {G : Fork} (hw : Wrote e a G e₁) : Rb e e₁ := by
  obtain ⟨h1, rfl⟩ := hw
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · unfold standOf
    rw [h1]
  · unfold S.link?
    rw [h1]

/-- **Every known writing of a link's runs stands in Rb.** -/
theorem rests_rb : RelRests Rb where
  refl := Rb.refl
  wrote _ _ _ _ hw := rb_wrote hw
  head := rb_head
  eq n e c e₁ h := by
    obtain ⟨G, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok n e e₁ c h
    exact (rb_putTl e tl').trans (rb_putFork _ F1)
  ls e e₁ h := by
    obtain ⟨G, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
    exact rb_putTl e _
  tests nU e e₁ h := by
    obtain ⟨G, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
    exact (rb_putTl e tl).trans (rb_putFork _ _)

/-- What the lens reads of the record. -/
theorem part_reads (e : S) (q : K9.Part) (hq : atS.get? e = some q) :
    e.link? = some q.L ∧ q.d.st = e.st := by
  unfold atS at hq
  simp only [Option.bind_eq_bind, Option.pure_def] at hq
  obtain ⟨L, hL, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
  rw [← Option.some.inj hq]
  exact ⟨hL, rfl⟩

/-- The lens's writing of a part with the statement and the link's number that it has read. -/
theorem rb_set (e : S) (q q' : K9.Part) (hq : atS.get? e = some q) (hd : q'.d.st = q.d.st)
    (hl : q'.L.link = q.L.link) : Rb e (atS.set e q') := by
  obtain ⟨hL, hst⟩ := part_reads e q hq
  have h1 := (rb_putLink e q.L q'.L hL hl).trans (rb_putFork _ q'.F)
  exact ⟨h1.failed, by show q'.d.st = e.st; rw [hd, hst], h1.book, h1.roots, h1.stand, h1.num⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_rb
#print axioms VerifiableInference.Desc.LinkJoin.rb_set
