-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/TestOracles.lean: two fields of the proximity test's block, made from the numbers
of its place (`H2U.TestNums`, Johnson/Desc/K12/TestEntries.lean): what the block says of the oracle
messages that it sends, and which messages must have been sent before its first draw. Definitions
only, all computable; nothing is proved here.

  `testOracles5 N firstGroup`  for `Block.oracles`: for each round, for each root that it sends: the
                               oracle message beneath it: log-length, the words of a symbol, and who
                               shares a symbol (the tenants). (`testOracles` in TestEntries.lean
                               gives the shapes alone. The 5 in the name has no meaning.)
  `beforeOf chain N`           for `Block.before`.

The trees that a test sends, and their tenants.
  The mask that the first fold sends itself (only where `N.ownMask`): a tree of its own, with one
    tenant: no main word; 3 · 2 ^ h mask words.
  At each code switch, the tree of the stage s that is entered: two tenants, since the masks ride.
    (1) The stage's message: 3 · 2 ^ k main words (2 ^ k rows over the extension field); 3 · 2 ^ h
        mask words; sampled; a member of the group that the switch makes.
    (2) At a stage but the last: the mask of that stage's own fold: no main word; 3 · 2 ^ h mask
        words; not sampled; in no group. At the last stage: the masking word of the base case: as
        many main and mask words as the stage's message; not sampled; in no group. (The verifier
        program announces that word with one main row and one mask row, 3 and 3 words. Ours are that
        only at k = h = 0, which the block's test on the plan asks of the last stage.)
  Log-length and words are `TestNums.sent`'s. The tenants' words add up to them for every k and h.
  degree: of the main rows: 3 where a tenant has main rows; 1 at a tenant without.
  groups: the number of the group in the running record: the j-th switch of the test makes the group
    firstGroup + j. firstGroup is a number of the place that `TestNums` does not hold: an argument.
  `beforeOf`: the trees of `N.first` (the test's group's, and a mask's that came earlier): an own
    tree number n gives (chain, n); one taken over from the chain c, from 0, gives (c + 1, n):
    Block.lean counts chains from 1 and messages by their roots' order of sending.

Limits. Those of TestEntries.lean: one answer to a sample; masks that ride; a mask at every stage.
That the tenants told here are those that the verifier program lays in its trees has been held in
runs, not proved. Nothing on soundness.
`testOracles5` deals the trees to the rounds by `take` and `drop`. It asks neither that they suffice
nor that none is left: a round may get fewer oracle messages than it has roots, and what is left
over is dropped without an error.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.Desc.K12.TestEntries

set_option autoImplicit false
namespace H2U
open VerifiableInference.Desc (Oracle SymbolComponent)

/-- A tenant that is a mask alone. -/
def maskTenant (h : Nat) : SymbolComponent :=
  { main := 0, mask := 3 * 2 ^ h, degree := 1, sampled := false, groups := [] }

/-- The trees that the test sends, in order, each with its tenants. -/
def TestNums.sentOracles (N : TestNums) (firstGroup : Nat) : List Oracle :=
  (match N.ownMask, N.stages with
    | true, s :: _ => [{ logLength := s.Z.a, words := 3 * 2 ^ s.h, tenants := [maskTenant s.h] }]
    | _, _ => []) ++
  (N.stages.drop 1).zipIdx.map fun s =>
    let last := s.2 + 2 == N.stages.length
    { logLength := s.1.C.a
      words := if last then Fmt.M1.wLast s.1 else Fmt.M1.wMid s.1
      tenants :=
        [{ main := 3 * 2 ^ s.1.k, mask := 3 * 2 ^ s.1.h, degree := 3, sampled := true,
           groups := [firstGroup + s.2] },
         if last then
           { main := 3 * 2 ^ s.1.k, mask := 3 * 2 ^ s.1.h, degree := 3, sampled := false,
             groups := [] }
         else maskTenant s.1.h] }

/-- **For each round, for each root that it sends: the oracle message beneath it.** -/
def testOracles5 (N : TestNums) (firstGroup : Nat) : Option (List (List Oracle)) :=
  (roundsOfNums N).map fun l =>
    (l.foldl (fun (acc : List (List Oracle) × List Oracle) r =>
      (acc.2.take r.entry.roots :: acc.1, acc.2.drop r.entry.roots))
      ([], N.sentOracles firstGroup)).1.reverse

/-- **What must have been sent before the test's first draw.** chain: 1, 2 or 3. -/
def beforeOf (chain : Nat) (N : TestNums) : List (Nat × Nat) :=
  N.first.map fun o => match o.2 with
    | .own n => (chain, n)
    | .taken c n => (c + 1, n)

end H2U
