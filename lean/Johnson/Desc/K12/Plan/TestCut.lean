-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Plan/TestCut.lean: the cut of each of a proof file's four proximity tests out of
the made plans, as a function of the planner's answer `C : Configured`: on which chain it stands;
where its "BAT" stands; its entries from "BAT" to "BASE"; the roots that the rounds in front
receive; the verifier program's stages. Definitions only, all computable; nothing is proved here. It
imports the planner (OnBytes/Params/Configure.lean) and nothing that stands over Mathlib, so it can
be compiled with the running code.

How made.
  The entries are a slice of the made plan's own list of rounds (`C.proof`: the first chain, the
    shared chain, the second chain, in the order of the file).
  The stages are those that the verifier program runs: the request's shape's `last`; the table's
    shape's `testU`, `testOmega`, `testOwn`.
  How long: by the stages' numbers of row variables: "BAT"; at each stage but the last: one round, k
    rounds, two rounds; at the last: two.
  Where: at a round named "BAT": the first chain's last; the shared chain's first and second; the
    second chain's first. The names are read, and the whole stretch is held against the names that
    the stages ask (`towerNames`): nothing where one parts.

Main names.
  `TestCut`: chain, start, entries, roots, stages. `towerLen`, `towerNames`, `batPlaces`,
    `testCutAt`.
  `cutTestL`, `cutTestU`, `cutTestO`, `cutTestW`: the first chain's last test; the folded row's;
    Omega's; the request's own.
  An Option, with no default. Nothing: where the chain or that "BAT" is not there; where the stretch
  runs over the end; where a name parts; where there are fewer than two stages.

Limits. Which "BAT" is a test's was laid by reading the planner's routines (`reqPlanFrom`,
`firstPlan`, OnBytes/Params/DeriveReq.lean; `linSharedTests`, `secondChainList`,
OnBytes/Params/PlanListsChains.lean). That no round named "BAT" stands behind the first chain's last
test is not held at the texts: where one did, the names would part and the cut would be nothing, not
a wrong cut. Nothing on trees, groups, members, masks. The namespace is H2U, under which the files
that stand on this one name it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Params.Configure

set_option autoImplicit false

namespace H2U
open OnBytes OnBytes.Params

/-- The cut of a proximity test out of a made plan. -/
structure TestCut where
  /-- 0: the first chain; 1: the shared chain; 2: the second chain -/
  chain : Nat
  /-- the place of the test's "BAT" on the chain, from 0 -/
  start : Nat
  /-- the plan's entries from "BAT" to "BASE" -/
  entries : List Fmt.Entry
  /-- the sum of the roots of the entries in front -/
  roots : Nat
  /-- the program's stages -/
  stages : List IoppStage
  deriving Repr

/-- The rounds behind "BAT". -/
def towerLen : List IoppStage → Nat
  | [] => 0
  | [_] => 2
  | c :: r => 1 + c.k + 2 + towerLen r

/-- Their names. -/
def towerNames : List IoppStage → List String
  | [] => []
  | [_] => ["BASE lambda", "BASE"]
  | c :: r =>
    "FOLD epsilon" :: List.replicate c.k "FOLD round" ++ ["SEND seed", "CS"] ++ towerNames r

/-- The places of the rounds named "BAT". -/
def batPlaces (es : List Fmt.Entry) : List Nat :=
  (es.zipIdx.filter fun p => p.1.name == "BAT").map (·.2)

/-- The cut at the place i of the chain number ch. -/
def testCutAt (C : Configured) (ch i : Nat) (st : List IoppStage) : Option TestCut := do
  let P ← C.proof[ch]?
  let es := P.rounds.map (·.entry)
  let cut := (es.drop i).take (1 + towerLen st)
  if st.length < 2 || cut.map (·.name) != "BAT" :: towerNames st then none
  pure ⟨ch, i, cut, ((es.take i).map (·.roots)).foldl (· + ·) 0, st⟩

/-- The places of "BAT" on the chain number ch. -/
def batsOn (C : Configured) (ch : Nat) : Option (List Nat) :=
  (C.proof[ch]?).map fun P => batPlaces (P.rounds.map (·.entry))

/-- The first chain's last test. -/
def cutTestL (C : Configured) : Option TestCut := do
  testCutAt C 0 (← (← batsOn C 0).getLast?) C.sized.proof.request.last

/-- The folded row's test. -/
def cutTestU (C : Configured) : Option TestCut := do
  testCutAt C 1 (← (← batsOn C 1)[0]?) C.sized.proof.batch.shape.testU

/-- The test on Omega's group. -/
def cutTestO (C : Configured) : Option TestCut := do
  testCutAt C 1 (← (← batsOn C 1)[1]?) C.sized.proof.batch.shape.testOmega

/-- The request's own test. -/
def cutTestW (C : Configured) : Option TestCut := do
  testCutAt C 2 (← (← batsOn C 2)[0]?) C.sized.proof.batch.shape.testOwn

end H2U
