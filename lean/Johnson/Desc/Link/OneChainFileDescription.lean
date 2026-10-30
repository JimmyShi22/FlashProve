-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/OneChainFileDescription.lean: a file of ONE chain as a description in blocks: the one-chain
sibling of `FileDescription` (Johnson/Desc/Block.lean), over
the same `Block`, `Chain`, `Block.step` and `chainAt`.
Definitions with code; no theorem.

Why. An entry file holds one chain (the link), without a sealing round. `FileDescription.run` folds three
chains, puts a sealing
round back behind the first view and refuses a chain without a block: so it does not fit.
  OneChainFileDescription Xi     S, Cl · plan (the plan's DECLARED ROUNDS of the chain, whole: as FileDescription.plans
  in Block.lean) · tableDepth · tables · fileOk · okStart · start · chain · fin
  asFile         the same description as a FileDescription whose two later chains are idle: NEVER RUN:
  by it
  planOk         IS `FileDescription.planOkCore` ITSELF, whole, at asFile (in Block.lean:
  planOk := planOkCore && sealLast: fileOk ·
                 every block's own test and `shaped` · THE BLOCKS' DECLARED ROUNDS IN A ROW ARE THE
                 PLAN's, WHOLE · every stored part has
                 the stored tables' depth · labelsOk, by which the first chain takes no tree over ·
                 placesOk · beforeOk · treeSharingOk ·
                 readsOk, by which the stored parts tile the round's draws and stand in the tables'
                 order, none twice · sent and opened
                 agree): NO GENERAL FUNCTION IS COPIED. sealLast IS
                 NOT ASKED, AND NOT FORCED: an entry file's
                 chain is unsealed: its last block, the chain's end, has no round. AND ONE CLAUSE OF
                 ITS OWN: storedOk: a stored part
                 names a table that the file has
  runEnd | run | say   the tests on the plan · the test on the instance · every word of the view is
  below the prime (viewWordsBelowPrime) ·
                 the chain's fold (chainAt) from `start x`, with nothing left over, AT THE VIEW AS
                 IT IS (no sealing round is put
                 back) · the last test


WHAT PARTS FROM FileDescription, ALL OF IT: one state, one view; no XiPub (the instance is handed whole to
start: an entry file's
instance is public); no start₃; no sealing round.
Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- **A one-chain file's description.** Xi: the instance. -/
structure OneChainFileDescription (Xi : Type) where
  S : Type
  Cl : Type
  /-- the plan's declared rounds of the chain, whole -/
  plan : List Fmt.DeclaredRound
  /-- the stored tables' depth -/
  tableDepth : Nat
  /-- how many stored tables the file's statement holds: its items 0, 1, … -/
  tables : Nat
  /-- the file's own tests on the plan -/
  fileOk : Bool
  /-- the test on the instance -/
  okStart : Xi → Bool
  start : Xi → S
  chain : Chain S Cl
  /-- the last test -/
  fin : Xi → S → Bool

variable {Xi : Type}

/-- A chain that does nothing: a chain has a first and a last block: two
quiet ones. -/
def roundlessChain {Cl : Type} (n : Nat) : Chain Unit Cl :=
  { first := roundlessBlock "idle: first" n none 0 fun s => .ok s, front := [], links := [], back := []
    last := roundlessBlock "idle: last" n none 1 fun s => .ok s }

/-- **The same description as a file of three chains, the two later ones idle**: so that
every test on the plan is
`FileDescription`'s own, called as it lies: no general function is written a second time. IT IS NEVER RUN:
`FileDescription.run` would put a
sealing round back and refuse a chain without a block. -/
def OneChainFileDescription.asFile (F : OneChainFileDescription Xi) : FileDescription Xi :=
  { S₁ := F.S, S₂ := Unit, S₃ := Unit, Cl := F.Cl, plans := (F.plan, [], []), tableDepth :=
      F.tableDepth
    fileOk := F.fileOk, okStart := F.okStart, XiPub := Xi, pub := id, start₁ := F.start
    start₂ := fun _ => (), start₃ := fun _ _ _ => .ok (), first := F.chain
    wanted := [], owed := []
    shared := roundlessChain 2, second := roundlessChain 3, fin := fun x s _ _ => F.fin x s }

/-- The chain's declared rounds: what a compiler takes. -/
def OneChainFileDescription.roundsDeclaredByBlocks (F : OneChainFileDescription Xi) : List Fmt.DeclaredRound := F.chain.blocksInOrder.flatMap (·.rounds)

/-- The table of places. -/
def OneChainFileDescription.places (F : OneChainFileDescription Xi) : List (String × Place × Nat) := placesOf F.chain.blocksInOrder

/-- **Which stored table a round's part reads**: each part names a table that the file has. (That
the parts stand in the tables' order,
no table twice, is `readsFit`'s, Johnson/Desc/Block.lean.) -/
def OneChainFileDescription.storedOk (F : OneChainFileDescription Xi) : Bool :=
  F.roundsDeclaredByBlocks.all fun r => r.stored.all fun s => decide (s.item < F.tables)

/-- The clauses of the tests on the plan that have a name, and the whole: for a print and for a
refusal's words. -/
def OneChainFileDescription.planClauses (F : OneChainFileDescription Xi) : List (String × Bool) :=
  let G := F.asFile
  [("fileOk", G.fileOk), ("the blocks' own tests, and shaped", blocksOk G.first.blocksInOrder),
   ("the blocks' declared rounds in a row are the plan's, whole", G.roundsDeclaredByBlocks.1 == G.plans.1),
   ("labelsOk", G.labelsOk), ("placesOk", G.placesOk), ("beforeOk", G.beforeOk),
       ("bookOk", G.treeSharingOk),
   ("readsOk", G.readsOk),
   ("FileDesc.planOkCore, whole", G.planOkCore),
   ("storedOk", F.storedOk)]

/-- **The tests on the plan**: `FileDescription.planOkCore`, whole, and `storedOk`. -/
def OneChainFileDescription.planOk (F : OneChainFileDescription Xi) : Bool := F.asFile.planOkCore && F.storedOk

/-- The words of the refusal on the plan; `none` where the tests pass. -/
def OneChainFileDescription.planWord (F : OneChainFileDescription Xi) : Option String :=
  if F.planOk then none else
    some ("the tests on the plan" ++
      match firstBad F.chain.blocksInOrder with
      | some n => ": " ++ n
      | none => ": the file's: " ++ ((F.planClauses.find? (!·.2)).map (·.1)).getD "")

/-- **The decision, with the chain's end.** -/
def OneChainFileDescription.runEnd (F : OneChainFileDescription Xi) (x : Xi) (v : Fmt.View) : Except String F.S := do
  if let some w := F.planWord then throw w
  need "the test on the instance" (F.okStart x)
  need "a word of the view is not below the prime" (viewWordsBelowPrime v)
  let e ← chainAt "the chain" 0 F.chain.blocksInOrder (F.start x) v
  need "the end fails the last test" (F.fin x e)
  pure e

/-- **The decision.** -/
def OneChainFileDescription.run (F : OneChainFileDescription Xi) (x : Xi) (v : Fmt.View) : Bool := (F.runEnd x v).isOk

/-- The same in words. -/
def OneChainFileDescription.say (F : OneChainFileDescription Xi) (x : Xi) (v : Fmt.View) : String := sayOf (F.runEnd x v)

end VerifiableInference.Desc
