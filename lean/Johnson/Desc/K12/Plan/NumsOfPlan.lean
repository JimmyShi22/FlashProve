-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Plan/NumsOfPlan.lean: two numbers of a proximity test's place, off the plan, for
each of a proof file's four tests: `first`: the trees of the test's group, and of a mask that came
earlier, each with its source (the chain's own number, or "taken" with a chain and a number);
`firstTree`: the number in the leaves' hashes of the chain's own tree number 0. Definitions only,
all computable; nothing is proved here.

How made. By calls of the rule Johnson/G/RoundsOfPlan.lean: `treesSent`, `ownMasks`,
`frameOpens`, `sharedOpens`, `switchOpens`, `secondOpens`. No rule is typed here: only which of the
rule's lists is which test's first round of positions.
  L (the first chain's last test): `frameOpens`' list behind the links' "LOC"s; firstTree 0.
  U (the folded row's test): `sharedOpens`' list number 1, behind the stored table's "LOC";
    firstTree 0.
  O (Omega's test): `sharedOpens`' list behind the folded row's test's code switches, less its last
    tree (the mask that the first fold sends itself: `TestNums` lays that one); firstTree 0.
  W (the request's own test): `secondOpens`' first list: the trees that are taken over: the first
    chain's input and W, and the shared chain's Omega; firstTree: the first chain's number of trees
    + 1, as `secondOpens` hands it to `switchOpens`.

Why the sources matter. The own test's declared rounds must say of Omega's tree that it is taken
from the shared chain, and which message it is. A decision on views cannot hold that (a view has no
root); the compiler does, out of the declared rounds.

Limits. The rule's own: which trees a test's first round of positions opens was read off
written dry lists at two examples; there is no theorem. Without a split of the shared chain O has no
test: nothing is returned for it. The namespace is H2U, under which the files that stand on this one
name it. Nothing on soundness.
Where the shared chain needs a split and the rule has no list at O's index, `firstsOfPlan` returns
`none` for O too, without an error: the value that also means «no split». For L, U and W a missing
list is an error.
Terms: lean/GLOSSARY.md.

-/
import Johnson.G.RoundsOfPlan
import Johnson.Desc.K12.TestEntries

set_option autoImplicit false
namespace H2U
open OnBytes OnBytes.Params Johnson.G.OfPlan

/-- first and firstTree of one place. -/
abbrev FirstAt : Type := List (Fmt.Shape × Fmt.TreeSource) × Nat

/-- The four places' first and firstTree. O: nothing where the shared chain has no split. -/
structure Firsts where
  L : FirstAt
  U : FirstAt
  O : Option FirstAt
  W : FirstAt

/-- **From what the planner and sendsOf make of the three public files.** -/
def firstsOfPlan (m : Made) : Except String Firsts := do
  let z := m.p.chains.made.sized.proof
  let S := z.batch.shape
  let P0 := m.p.chains.proof.first.given.plan
  let P1 := m.p.chains.proof.shared.given.plan
  let P2 := m.p.chains.proof.second.given.plan
  let t0 ← treesSent "proof file, first chain" m.proof.1 P0 []
  let t1 ← treesSent "proof file, shared chain" m.proof.2.1 P1
    (ownMasks m.proof.2.1.codes S P1.rounds)
  let t2 ← treesSent "proof file, second chain" m.proof.2.2 P2 []
  let riders := z.request.atStart.map (·.leafClass)
  let locs := (P0.rounds.filter fun e => e.name == "LOC").length
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some a => pure a
    | none => throw ("firstsOfPlan: the rule has no list for " ++ what)
  let l ← get "the last test" (frameOpens riders t0 locs)[locs]?
  let sh := sharedOpens S t1
  let u ← get "the folded row's test" (sh[1]?)
  let o :=
    if S.sharedSplitNeeded then
      (sh[2 + (switchOpens 0 .folded t1).length]?).map fun x => (x.1.dropLast, 0)
    else none
  let w ← get "the own test"
    (secondOpens S (fun t => t.tag == .link 0 0 && riders.contains t.cls) t0 t1 t2).head?
  pure { L := (l, 0), U := (u.1, 0), O := o, W := (w, t0.length + 1) }

end H2U
