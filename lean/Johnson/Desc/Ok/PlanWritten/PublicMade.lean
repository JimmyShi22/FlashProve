-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/PublicMade.lean: two predicates that say "made of the three public
files" without naming a hash: `PublicMade` of a public part, `PlannedMade` of a planner's value.

Why. The library's laws on the public part and on the planner's value have a premise of the form
"`publicOf` returns X" or "`planned` returns p", and these two texts name the second hash function
and the format's hash. A description that takes the second hash function as an argument o runs
`publicOfO o` and `plannedAtO o` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean). A law that is stated
under one of the two predicates here can be used from either side.

The statements are tools: they hold of all public files, and no description of the protocol is
named.

  `PublicMade pol KL layout X`: at some o, `publicOfO o pol KL layout` returns X. It follows from
    the text at an argument (`PublicMade.of_at`), from the library's text (`PublicMade.of_publicOf`)
    and from `PlannedMade` (`PlannedMade.public`). `PublicMade.scan`: the scan in X is the scan of
    the parameter file. `PublicMade.two`: two such values on the same files differ at most in the
    three digests of the lists of lookup calls.
  `PlannedMade pol KL layout p`: p.X is made of the files; p.chains is what `chainsOf` returns on
    p.X at the digest p.cfg; p.built is what `builtOf` returns on p.X and p.chains, but for the
    checks in the links (`blankRun`, `SameButRun`; `SameButRun.refl`: a list of links is so related
    to itself). It follows from the planner's text at an argument (`PlannedMade.of_at`), from the
    library's text with the digest as an argument (`PlannedMade.of_plannedAt`), both with p.cfg = c,
    and from the library's planner (`PlannedMade.of_planned`).

Why the checks are left out. A link holds the check of its sub-proof as a routine in the field
`run`. A maker that lays another routine there returns other links, though every public number in
them is the same. In the library one routine alone applies that field (`runLinkH`,
OnBytes/Model/StagesLinks.lean), by a search.

What of OnBytes/Model/ is used: `Verify.Public`, `Verify.Planned`, `Verify.publicOf`,
`Verify.planned`, `Verify.chainsOf`, `Verify.builtOf`, `Stages.LinkH`, `Stages.LinksH`, `polScan`,
by name, in the statements.

Limits. The predicates hide o: from `PublicMade` nothing follows on X.digests, nor on which tables'
digests were compared with what. `PlannedMade` does not say that p.cfg is the digest of the files.
Nothing says that a value is made at any files. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import Johnson.Desc.Ok.PlanWritten.PublicAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-! ## 1. The public part -/

/-- X is what the text of the public part returns on the three files at some argument o. -/
def PublicMade (pol KL : ByteArray) (layout : Option ByteArray) (X : Public) : Prop :=
  ∃ o : Nat → ByteArray → ByteArray, publicOfO o pol KL layout = .ok X

/-- From the text at an argument o. -/
theorem PublicMade.of_at {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    PublicMade pol KL layout X := ⟨o, h⟩

/-- From the library's text. -/
theorem PublicMade.of_publicOf {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOf pol KL layout = .ok X) : PublicMade pol KL layout X :=
  ⟨secondHashFunction, (publicOfO_older pol KL layout).trans h⟩

/-- The scan in X is the scan of the parameter file. -/
theorem PublicMade.scan {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : PublicMade pol KL layout X) : polScan pol = .ok X.P := by
  obtain ⟨o, h⟩ := h
  exact publicOfO_scan h

/-- Two such values on the same files differ at most in the three digests of the lists of lookup
calls. -/
theorem PublicMade.two {pol KL : ByteArray} {layout : Option ByteArray} {X X' : Public}
    (h : PublicMade pol KL layout X) (h' : PublicMade pol KL layout X') :
    X' = { X with digests := X'.digests } := by
  obtain ⟨o, h⟩ := h
  obtain ⟨o', h'⟩ := h'
  exact publicOfO_two h h'

/-! ## 2. The planner's value -/

/-- A link with its check, the field `run`, replaced by one that does nothing. -/
def blankRun (L : Stages.LinkH) : Stages.LinkH := { L with run := pure none }

/-- Two lists of links are the same but for the checks in them. -/
def SameButRun (b b' : Stages.LinksH) : Prop := b.links.map blankRun = b'.links.map blankRun

theorem SameButRun.refl (b : Stages.LinksH) : SameButRun b b := rfl

/-- p is a planner's value on the three files: its public part is made of the files; its chains are
what the library's maker returns on that public part at p's digest; its links are what the library's
maker returns, but for the checks in them. -/
def PlannedMade (pol KL : ByteArray) (layout : Option ByteArray) (p : Planned) : Prop :=
  PublicMade pol KL layout p.X ∧ chainsOf p.X layout p.cfg = .ok p.chains ∧
    ∃ b, builtOf p.X p.chains = .ok b ∧ SameButRun b p.built

/-- From the planner's text at an argument o; and p's digest is the one that was handed in. -/
theorem PlannedMade.of_at {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {c : ByteArray} {p : Planned}
    (h : plannedAtO o pol KL layout c = .ok p) : PlannedMade pol KL layout p ∧ p.cfg = c := by
  unfold plannedAtO at h
  obtain ⟨X, eX, h⟩ := exc_bind h
  obtain ⟨ch, ec, h⟩ := exc_bind h
  obtain ⟨b, eb, h⟩ := exc_bind h
  cases h
  exact ⟨⟨⟨o, eX⟩, ec, b, eb, rfl⟩, rfl⟩

/-- From the library's text with the digest as an argument. -/
theorem PlannedMade.of_plannedAt {pol KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {p : Planned} (h : OnBytes.Tie.plannedAt pol KL layout c = .ok p) :
    PlannedMade pol KL layout p ∧ p.cfg = c :=
  PlannedMade.of_at ((plannedAtO_older pol KL layout c).trans h)

/-- From the library's planner. -/
theorem PlannedMade.of_planned {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) : PlannedMade pol KL layout p :=
  (PlannedMade.of_plannedAt ((OnBytes.Tie.planned_eq pol KL layout).symm.trans h)).1

/-- Its public part is made of the files. -/
theorem PlannedMade.public {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : PlannedMade pol KL layout p) : PublicMade pol KL layout p.X := h.1

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.PublicMade.of_at
#print axioms VerifiableInference.PlanWritten.PublicMade.of_publicOf
#print axioms VerifiableInference.PlanWritten.PublicMade.scan
#print axioms VerifiableInference.PlanWritten.PublicMade.two
#print axioms VerifiableInference.PlanWritten.SameButRun.refl
#print axioms VerifiableInference.PlanWritten.PlannedMade.of_at
#print axioms VerifiableInference.PlanWritten.PlannedMade.of_plannedAt
#print axioms VerifiableInference.PlanWritten.PlannedMade.of_planned
#print axioms VerifiableInference.PlanWritten.PlannedMade.public
