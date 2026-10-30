-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyOpensGuards.lean

What the rounds of the key file's shared chain open against what is in hand, at a border, as closed
numbers, by Lean's evaluator. It is `Thread.opensAvailable` (Honest/Thread/OneState.lean) with the
thread taken away: that test reads of a thread its list of sub-protocols, and only their rounds and
how many oracle messages each declares, and `taken`, which is empty on the shared chain.
KeyOpensKernel.lean imports this file; KeyOpensLaw.lean ties it to the thread.

  `ro`        of a block: its rounds and the number of its oracle messages
  `opensR`    the test, on a list of such pairs, at a border
  `keyR`      the list at the written values `QK`, `PF`: the front, the eight, the two tests, the end
  `srcNum`    a source as a number, to print
  `bentHand`  a control: in member 9's stead the rounds of member 10: a round opens what the hand lacks
  `bentTrees` a control: member 9 sends no tree

Limits. Evaluations outside the kernel: no theorem. Nothing on completeness, on soundness or on what
is hidden.
-/
import E2E.KeyShapeSharedFull
import Johnson.Desc.K12.Law.SitsKeyChains

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyOpens
open AtPublicFiles.AtFiles.Full (PF QK)
open VerifiableInference.Desc (Block)
open _root_.Desc.K14 (blocksOr)

/-- Of a block: its rounds, and how many oracle messages it declares. -/
def ro {S Cl : Type} (b : Block S Cl) : List Fmt.DeclaredRound × Nat :=
  (b.rounds, (b.oracles.flatMap id).length)

/-- `Thread.opensAvailable` at a list of these, where no tree is taken over. -/
def opensR (R : List (List Fmt.DeclaredRound × Nat)) (n : Nat) : Bool :=
  ((R.take n).flatMap (·.1)).all fun d => d.opens.all fun o =>
    decide (o.2 ∈ (List.range ((R.take n).map (·.2)).sum).map Fmt.TreeSource.own)

/-- The list at the written values. -/
def keyR : List (List Fmt.DeclaredRound × Nat) :=
  ((([], 0) :: (blocksOr QK).map ro) ++ [ro (H2K.JointK.keyGu PF)]) ++
    ro (H2K.JointK.keyOmega (PF.O.getD PF.U)) ::
      [([VerifiableInference.Desc.ChainEnd.sealRound], 0)]

/-- A source as a number, to print: an own tree's number; a taken tree's far above. -/
def srcNum : Fmt.TreeSource → Nat
  | .own n => n
  | .taken c k => 100000 + 1000 * c + k

/-- Control: member 10's rounds in member 9's stead, with member 9's count. -/
def bentHand : List (List Fmt.DeclaredRound × Nat) :=
  keyR.set 9 ((keyR.getD 10 ([], 0)).1, (keyR.getD 9 ([], 0)).2)

/-- Control: member 9 sends no tree. -/
def bentTrees : List (List Fmt.DeclaredRound × Nat) := keyR.set 9 ((keyR.getD 9 ([], 0)).1, 0)

-- Member by member: rounds, trees, and what its rounds open.
#eval keyR.map fun x => (x.1.length, x.2, (x.1.flatMap (·.opens)).map fun o => srcNum o.2)
-- The test at each border.
#eval (List.range 13).map (opensR keyR)

-- Foretold: yes at 10, 11, 12.
#guard keyR.length == 12
#guard opensR keyR 10 && opensR keyR 11 && opensR keyR 12
-- Controls. Foretold: no.
#guard !opensR bentHand 10
#guard !opensR bentTrees 10

end AtPublicFiles.KeyOpens

#print axioms AtPublicFiles.KeyOpens.ro
#print axioms AtPublicFiles.KeyOpens.opensR
#print axioms AtPublicFiles.KeyOpens.keyR
#print axioms AtPublicFiles.KeyOpens.srcNum
#print axioms AtPublicFiles.KeyOpens.bentHand
#print axioms AtPublicFiles.KeyOpens.bentTrees
