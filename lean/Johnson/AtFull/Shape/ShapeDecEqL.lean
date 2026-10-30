-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ShapeDecEqL.lean: A SECOND DECIDER FOR THE EQUALITY OF TWO WHOLE SHAPES OF THE
FIRST CHAIN's STATE (`ShA`, FrameForm.lean), WHICH COMPARES TWO ARRAYS AS LISTS. Instances alone, in
a namespace of their own (Johnson.AtFull.Shape.ByLists): one for arrays and six by instance search,
these seven `scoped`; 53 derived by Lean's own handler, global. No statement but the one that the
first instance spends (Array.toList_inj, Lean's own); nothing is evaluated. It stands beside
Johnson/AtFull/Shape/ShapeDecEq.lean and does not import it.

  decArray        DecidableEq (Array α) by "a.toList = b.toList".
  struck, in this file alone: Lean's own instance for arrays, and the 14 instances that the search
                  finds, over this file's imports, for a type of ours that ShA reaches and that
                  reaches Array (through a String too): these have Lean's own comparison of arrays
                  built in.
  the 53          these 14 types anew, and every type of ours that ShA reaches and that has no
                  decider over this file's imports; dependencies in front: lists and order are a
                  program's.
  **decShAL**     THE DECIDER.

Why. In a scratch line ShapeDecEq's decider, under Lean's kernel, ran out of memory at a shape
inside a link (7.75 million nodes, the lookup's record with its calls' tables in it); at shapes
between links it had taken seconds. The arrays are a guess at the cause: how Lean's own instance
for arrays walks them was not opened, and no line has told the arrays apart from the rest.

Limits. THAT THE SEARCH TOOK THE NEW INSTANCES IS NOT SEEN BY THIS FILE's PASSING.
It wants a
walk of the constants that decShAL reaches. What this decider costs Lean's kernel is not measured
here. WHAT AN IMPORTER INHERITS. The seven typed instances (decArray, decLedTailL, decLedShL,
decChainTail₁L, decChainTail₂L, decChainShL, decShAL) are `scoped`: the search sees them only where
this namespace is open; so an importer's search for DecidableEq (Array α) still finds Lean's own,
and whoever wants decShAL names it. THE 53 DERIVED INSTANCES ARE GLOBAL (Lean's `deriving instance`
has no scoped form): every importer inherits them. For 39 of the 53 types no other decider is in
sight over this file's imports. 14 STAND BESIDE AN ELDER INSTANCE (the 14 that this file strikes for
itself; a strike holds in its own file alone), AND DOWNSTREAM THE SEARCH FINDS THE ONE OF THIS FILE
FIRST. For Model.Call and Forest.Shape a second pair stands in the import closure, derived in
Johnson/Desc/First/FillK4.lean and not struck here: the search found PublicB's pair in front of it.
Each instance carries its proof, so nothing false follows; a `decide` typed under the one is not,
sign for sign, that under the other: name the decider where it matters. Strings are compared by
Lean's own instance. A decider says nothing on what any shape is. Nothing on soundness, completeness
or hiding.
-/
import Johnson.AtFull.Shape.FrameForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000

namespace Johnson.AtFull.Shape.ByLists
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape

attribute [-instance] Array.instDecidableEq
attribute [-instance] OnBytes.Model.instDecidableEqT2Foreign
attribute [-instance] VerifiableInference.Desc.First.Att.P.PublicB.instDecidableEqCall_johnson
attribute [-instance] VerifiableInference.Desc.First.Att.P.PublicB.instDecidableEqShape_johnson
attribute [-instance] OnBytes.Model.instDecidableEqT2Map
attribute [-instance] OnBytes.Model.instDecidableEqTMat
attribute [-instance] OnBytes.Params.instDecidableEqReqArray
attribute [-instance] OnBytes.Params.instDecidableEqReqLayout
attribute [-instance] OnBytes.instDecidableEqSwitchTarget
attribute [-instance] OnBytes.instDecidableEqCodes
attribute [-instance] VerifiableInference.Desc.Ground.Sh.instDecidableEqStSh
attribute [-instance] OnBytes.instDecidableEqTreeShape
attribute [-instance] VerifiableInference.Desc.Ground.Sh.instDecidableEqTreeSh
attribute [-instance] VerifiableInference.Desc.Ground.Sh.instDecidableEqBookSh
attribute [-instance] VerifiableInference.Desc.Ground.Sh.instDecidableEqCoreSh

/-- Two arrays are equal just if their lists are. -/
scoped instance decArray {α : Type} [DecidableEq α] : DecidableEq (Array α) :=
  fun a b => decidable_of_iff (a.toList = b.toList) Array.toList_inj

deriving instance DecidableEq for OnBytes.Model.T2Foreign
deriving instance DecidableEq for OnBytes.Model.Piece
deriving instance DecidableEq for OnBytes.Model.Call
deriving instance DecidableEq for OnBytes.Model.CallZ
deriving instance DecidableEq for OnBytes.Model.Forest.Shape
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.HeardAll
deriving instance DecidableEq for OnBytes.Model.T2Map
deriving instance DecidableEq for OnBytes.Model.TMat
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.TailSh
deriving instance DecidableEq for OnBytes.Params.ReqArray
deriving instance DecidableEq for OnBytes.Params.ReqLayout
deriving instance DecidableEq for OnBytes.ReqRows
deriving instance DecidableEq for OnBytes.GroupLayout
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.TensorSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.FormSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.SingleSh
deriving instance DecidableEq for OnBytes.SwitchTarget
deriving instance DecidableEq for OnBytes.ReqGroup
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.FrameSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.CheckSh

/-- The ledger's shape, thirteen factors: its last eight. -/
scoped instance decLedTailL : DecidableEq
    (Nat × List TreeSh × Nat × Nat × Nat × Bool × List Bool × Bool) := inferInstance

scoped instance decLedShL : DecidableEq LedSh :=
  inferInstanceAs (DecidableEq (Nat × Nat × Nat × List Bool × List Bool ×
    (Nat × List TreeSh × Nat × Nat × Nat × Bool × List Bool × Bool)))

deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.SwSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.GroupMk
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.FinSh
deriving instance DecidableEq for VerifiableInference.Desc.K13.Honest.ClaimSh
deriving instance DecidableEq for VerifiableInference.Desc.K13.Honest.LaidSh
deriving instance DecidableEq for OnBytes.Codes
deriving instance DecidableEq for VerifiableInference.Desc.Ground.Sh.StSh
deriving instance DecidableEq for OnBytes.TreeShape
deriving instance DecidableEq for VerifiableInference.Desc.Ground.Sh.TreeSh
deriving instance DecidableEq for VerifiableInference.Desc.Ground.Sh.BookSh
deriving instance DecidableEq for VerifiableInference.Desc.Ground.Sh.CoreSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.LevelSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.TscSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.NormsSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.RecSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.MergeSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.StackSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.OwnSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.WsClaimSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.HeadHeardSh
deriving instance DecidableEq for OnBytes.Model.Tail2
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.LinkSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.ShutSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.HeadSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.SumSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.Heard5Sh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.AttOwnSh
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.RunMk
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.MainMk
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.UnitMk
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.TermMk
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.RowMk
deriving instance DecidableEq for VerifiableInference.Desc.First.Shape.FormsSh

/-- The chain's shape, nineteen factors: its last seven. -/
scoped instance decChainTail₁L : DecidableEq
    (Option LinkSh × Option HeardAll × Option HeardAll × Option OwnSh × Option HeadSh ×
      Option AttOwnSh × Option FinSh) := inferInstance

/-- The six in front of these. -/
scoped instance decChainTail₂L : DecidableEq
    (Ground.Sh.CoreSh × Bool × Nat × List K13.Honest.RowSh × Option EndSh × CheckSh ×
      (Option LinkSh × Option HeardAll × Option HeardAll × Option OwnSh × Option HeadSh ×
        Option AttOwnSh × Option FinSh)) := inferInstance

scoped instance decChainShL : DecidableEq ChainSh :=
  inferInstanceAs (DecidableEq (Bool × Nat × Option TailSh × Option LedSh × Option (List FunSh) ×
    Option Nat × (Ground.Sh.CoreSh × Bool × Nat × List K13.Honest.RowSh × Option EndSh × CheckSh ×
      (Option LinkSh × Option HeardAll × Option HeardAll × Option OwnSh × Option HeadSh ×
        Option AttOwnSh × Option FinSh))))

/-- **THE DECIDER, arrays as lists.** -/
scoped instance decShAL : DecidableEq ShA := inferInstanceAs (DecidableEq (ChainSh × FormsSh))

end Johnson.AtFull.Shape.ByLists

#print axioms Johnson.AtFull.Shape.ByLists.decArray
#print axioms Johnson.AtFull.Shape.ByLists.decLedTailL
#print axioms Johnson.AtFull.Shape.ByLists.decLedShL
#print axioms Johnson.AtFull.Shape.ByLists.decChainTail₁L
#print axioms Johnson.AtFull.Shape.ByLists.decChainTail₂L
#print axioms Johnson.AtFull.Shape.ByLists.decChainShL
#print axioms Johnson.AtFull.Shape.ByLists.decShAL
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqT2Foreign_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqPiece_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqCall_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqCallZ_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqShape_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqHeardAll
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqT2Map_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTMat_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTailSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqReqArray_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqReqLayout_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqReqRows_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqGroupLayout_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTensorSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqFormSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqSingleSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqSwitchTarget_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqReqGroup_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqFrameSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqCheckSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqSwSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqGroupMk
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqFinSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqClaimSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqLaidSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqCodes_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqStSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTreeShape_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTreeSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqBookSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqCoreSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqLevelSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTscSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqNormsSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqRecSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqMergeSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqStackSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqOwnSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqWsClaimSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqHeadHeardSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTail2_johnson
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqLinkSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqShutSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqHeadSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqSumSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqHeard5Sh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqAttOwnSh
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqRunMk
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqMainMk
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqUnitMk
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqTermMk
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqRowMk
#print axioms Johnson.AtFull.Shape.ByLists.instDecidableEqFormsSh
