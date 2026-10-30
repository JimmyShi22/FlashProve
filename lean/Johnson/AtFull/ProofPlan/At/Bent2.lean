-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/Bent2.lean: THE WRITTEN DESCRIPTION `WP`
(Johnson/AtFull/ProofPlan/WP.lean) WITH ONE THING TURNED, FIFTEEN TIMES MORE: for the negative lines
of the tests on the plan that Johnson/AtFull/ProofPlan/At/Bent.lean does not serve. Definitions
alone.

Each differs from `WP` in one thing, chosen so that one named test must say no. The files under
At/No/ ask Lean's kernel, each alone. Where the things stand: the first chain's third row ("G0:1")
tells two trees; the first has four tenants, three of them sampled, each in the group 0. The
distinct declared round number 38 ("LOC") is the first that opens trees: the chain's own trees 0, 2
and 3, of the depth 23. Number 1 is "SEND answer".

  `wpFile`: fileOk is false. AT `WP` fileOk IS A LITERAL: this one shows only that the field is
    read.
  `wpPlans₂`, `wpPlans₃`: the plan's second, third list is empty. `wpShaped₂`, `wpShaped₃`: the
    shared, the second chain's first row says that its oracles have one member more than it has
    rounds.
  `wpRows`: the first tenant's mask has 4 words for 3. `wpTold`: the third row tells nothing.
    `wpAlike`: the second tenant is in the group 1. `wpOneGroup`: the first tenant is in two groups.
  `wpRange`: round 38 draws positions below 2 ^ 22. `wpOnce`: it opens its first tree twice.
    `wpInTime`: its first tree's source is the chain's own tree 82. `wpInOrder`: its openings stand
    in the reverse order. `wpAnswered`: round 1 holds 5 answers for 4.
  `wpBefore`: the first chain's fourth row ("G0:2") names the message 82 of its own chain too.

Limits. Made-up values: none is any description's. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (declRecsFull cutFirstFull cutSharedFull cutSecondFull)

/-- `WP` with one row of the first chain's cut turned. -/
def wpRow (i : Nat) (f : Row → Row) : FileDescription Unit :=
  wOf (cutFirstFull.modify i f) cutSharedFull cutSecondFull declProofFull 32

/-- `WP` with one of the distinct declared rounds turned. -/
def wpRec (i : Nat) (f : Fmt.DeclaredRound → Fmt.DeclaredRound) : FileDescription Unit :=
  wOf cutFirstFull cutSharedFull cutSecondFull (declOfRecs (declRecsFull.modify i f)) 32

/-- A row with the first tree that it tells turned. -/
def turnTree (f : Oracle → Oracle) (r : Row) : Row :=
  (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1.modify 0 fun t => (t.1, t.2.modify 0 f),
    r.2.2.2.2.2)

/-- A tree with its tenant number k turned. -/
def turnTenant (k : Nat) (f : SymbolComponent → SymbolComponent) (o : Oracle) : Oracle :=
  { o with tenants := o.tenants.modify k f }

/-- A row whose oracles are said to have one member more. -/
def longer (r : Row) : Row := (r.1, r.2.1, r.2.2.1, r.2.2.2.1 + 1, r.2.2.2.2)

def wpFile : FileDescription Unit := { WP with fileOk := false }

def wpPlans₂ : FileDescription Unit := { WP with plans := (WP.plans.1, [], WP.plans.2.2) }

def wpPlans₃ : FileDescription Unit := { WP with plans := (WP.plans.1, WP.plans.2.1, []) }

def wpShaped₂ : FileDescription Unit :=
  wOf cutFirstFull (cutSharedFull.modify 0 longer) cutSecondFull declProofFull 32

def wpShaped₃ : FileDescription Unit :=
  wOf cutFirstFull cutSharedFull (cutSecondFull.modify 0 longer) declProofFull 32

def wpRows : FileDescription Unit :=
  wpRow 2 (turnTree (turnTenant 0 fun t => { t with mask := t.mask + 1 }))

def wpTold : FileDescription Unit :=
  wpRow 2 fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, [], r.2.2.2.2.2)

def wpAlike : FileDescription Unit := wpRow 2 (turnTree (turnTenant 1 fun t => { t with groups := [1] }))

def wpOneGroup : FileDescription Unit :=
  wpRow 2 (turnTree (turnTenant 0 fun t => { t with groups := [0, 1] }))

def wpRange : FileDescription Unit := wpRec 38 fun r => { r with entry := { r.entry with logN := 22 } }

def wpOnce : FileDescription Unit := wpRec 38 fun r => { r with opens := r.opens.take 1 ++ r.opens }

def wpInTime : FileDescription Unit :=
  wpRec 38 fun r => { r with opens := r.opens.modify 0 fun o => (o.1, .own 82) }

def wpInOrder : FileDescription Unit := wpRec 38 fun r => { r with opens := r.opens.reverse }

def wpAnswered : FileDescription Unit :=
  wpRec 1 fun r => { r with entry := { r.entry with answers := r.entry.answers + 1 } }

def wpBefore : FileDescription Unit :=
  wpRow 3 fun r => (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1, (1, 82) :: r.2.2.2.2.2)

end P2Law.ProofPlan
