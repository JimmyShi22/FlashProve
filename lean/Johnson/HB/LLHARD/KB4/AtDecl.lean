-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/AtDecl.lean: the tests on the plan that read a description's declared rounds,
as functions of three lists of rounds. General in the description: no value is treated.

A description's declared rounds (FileDescription.roundsDeclaredByBlocks, Johnson/Desc/Block.lean) are its blocks' rounds in a
row. Where these are shown to be a written value, a test that reads them is to be asked at that
value. Here each such test's text stands with the three lists as a letter, and is the test at the
description's own lists: by unfolding.

Main names: labelsAt, readsAt, depthAt, sentAt; labelsOk_at, readsOk_at, depth_at, sentFit_at.
Limits. The twins copy the tests' texts; the equations hold the copies against the originals.
Nothing on soundness.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc

/-- Three lists of declared rounds. -/
abbrev D3 : Type := List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound

/-- FileDescription.labelsOk's text at three lists. -/
def labelsAt (D : D3) : Bool :=
  [D.1, D.2.1, D.2.2].zipIdx.all fun c => (c.1.flatMap (·.opens)).all fun o =>
    match o.2 with
    | .own n =>
      o.1.tree == (if c.2 == 2 then D.1.foldl (fun n r => n + r.entry.roots) 0 + 1 + n else n)
    | .taken ch sent => c.2 == 2 && decide (ch < 2) && o.1.tree == sent

theorem labelsOk_at {Xi : Type} (F : FileDescription Xi) : F.labelsOk = labelsAt F.roundsDeclaredByBlocks := rfl

/-- FileDescription.readsOk's text at three lists. -/
def readsAt (D : D3) : Bool := (D.1 ++ D.2.1 ++ D.2.2).all readsFit

theorem readsOk_at {Xi : Type} (F : FileDescription Xi) : F.readsOk = readsAt F.roundsDeclaredByBlocks := rfl

/-- The eighth conjunct of planOkCore at three lists and a depth. -/
def depthAt (D : D3) (a : Nat) : Bool :=
  (D.1 ++ D.2.1 ++ D.2.2).all fun r => r.stored.all (·.sh.a == a)

theorem depth_at {Xi : Type} (F : FileDescription Xi) :
    (F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2).all (fun r => r.stored.all (·.sh.a == F.tableDepth)) =
      depthAt F.roundsDeclaredByBlocks F.tableDepth := rfl

/-- FileDescription.sentFit's text at three lists of rounds and what the three chains' blocks say of the
trees that they send. -/
def sentAt (D : D3) (s₁ s₂ s₃ : List (Nat × Nat)) : Bool :=
  [s₁, s₂, s₃].zipIdx.all fun c =>
    let opened := openedOwn D c.2
    opened.all (fun o => c.1[o.1]? == some (o.2.1, o.2.2)) &&
      (List.range c.1.length).all fun n => opened.any fun o => o.1 == n

theorem sentFit_at {Xi : Type} (F : FileDescription Xi) :
    F.sentFit = sentAt F.roundsDeclaredByBlocks (sentOf F.first.blocksInOrder) (sentOf F.shared.blocksInOrder) (sentOf F.second.blocksInOrder) :=
  rfl

end Johnson.KB4

#print axioms Johnson.KB4.labelsOk_at
#print axioms Johnson.KB4.readsOk_at
#print axioms Johnson.KB4.depth_at
#print axioms Johnson.KB4.sentFit_at
