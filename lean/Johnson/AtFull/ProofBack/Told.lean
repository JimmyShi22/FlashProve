-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofBack/Told.lean: the value of `ProofFile.toldChain` (Johnson/Desc/ProofFile/Told.lean)
at the proof file's three chains of the full size, at the written sendings, for every plan whose
rounds are the written rounds' entries and which has no entry that is no round, AT EVERY NAME: so
the three lines of `ProofFile.toldOf`.

Definitions.
  `maskW`: the one message that each of the shared chain's own masks holds.
  `tl0`, `tl1`, `tl2`: what `toldAt` returns at a chain's sendings.
Statements.
  `some_of_isSome`: what is there is `some` of what it holds.
  `told_some0`, `told_some1`, `told_some2`: BY THE KERNEL, behind `Johnson.Unfolds.mergeSort_eq`:
    the `mapM` of `toldAt` returns.
  `cmp0`, `cmp1`, `cmp2`: BY THE KERNEL, behind the laws of Johnson/Unfolds/ on Lean's library: the
    trees with their tenants agree in depth and width with `treesSent`'s.
  **`told0`**, **`told1`**, **`told2`**: from (e) the plan's rounds are the chain's written entries
    and (o) it has as many entries as rounds: `toldChain` returns `mineW`
    (Johnson/Unfolds/ToldLaw.lean) at `tl0`, `tl1`, `tl2`. By `Johnson.Unfolds.toldChain_of` and the
    chains' trees (Johnson/AtFull/ProofBack/Trees.lean).
  Negative test, BY THE KERNEL: `cmp2_no`: with every width raised by one the comparison rejects.

Limits. The full size alone. THE TWO EQUATIONS ON THE PLAN ARE PREMISES. IT SPEAKS OF WRITTEN
VALUES: that the written sendings, rounds and sizes are what `sendsOf` and the planner make of any
public files is not said here. The trees with their tenants stand as terms, not as a written list.
Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.ProofBack.Decl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofBack
open OnBytes OnBytes.Params Johnson.G Johnson.G.OfPlan Johnson.Unfolds

/-- What is there is `some` of what it holds. -/
theorem some_of_isSome {α : Type} {x : Option α} (d : α) (h : x.isSome = true) :
    x = some (x.getD d) := by
  cases x with
  | none => cases h
  | some a => rfl

/-- The one message that each of the shared chain's own masks holds. -/
def maskW : Option OracleNotice :=
  shapeW.testOmega.head?.map fun st => foldMaskNotice (ioppFoldShape st {})

/-- What `toldAt` returns at the second chain's sendings. -/
def tl2 : List (List (Nat × ProofFile.Root)) :=
  (proofSends2.sends.mapM (ProofFile.toldAt proofSends2.codes 0)).getD []

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the `mapM` of `toldAt` returns at the second chain's sendings. -/
theorem told_some2 : (proofSends2.sends.mapM (ProofFile.toldAt proofSends2.codes 0)).isSome = true := by
  unfold ProofFile.toldAt ProofFile.rootsOfSent
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the second chain's trees with their tenants agree in depth and width with
`treesSent`'s. -/
theorem cmp2 :
    ((mineW tl2 extra2 none).map (fun r => (r.logLength, r.words)) !=
      t2.map fun t => (t.1.a, t.1.W)) = false := by
  unfold mineW tl2 t2 sortedW sentsOf extra2 ProofFile.toldAt ProofFile.rootsOfSent sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **For a plan whose rounds are the second chain's written entries and which has no other entry:
`toldChain` returns the second chain's trees with their tenants**, at every name. -/
theorem told2 {P : Fmt.Plan} (e : P.rounds = es2) (o : P.entries.length - P.rounds.length = 0)
    (at_ : String) :
    ProofFile.toldChain at_ proofSends2 P extra2 none = .ok (mineW tl2 extra2 none) := by
  refine toldChain_of (l := tl2) (theirs := t2) ?_ ?_ cmp2
  · rw [o]
    exact some_of_isSome [] told_some2
  · rw [treesSent_eq, o, e]
    exact trees2 _

/-- What `toldAt` returns at the shared chain's sendings. -/
def tl1 : List (List (Nat × ProofFile.Root)) :=
  (proofSends1.sends.mapM (ProofFile.toldAt proofSends1.codes 0)).getD []

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the `mapM` of `toldAt` returns at the shared chain's sendings. -/
theorem told_some1 : (proofSends1.sends.mapM (ProofFile.toldAt proofSends1.codes 0)).isSome = true := by
  unfold ProofFile.toldAt ProofFile.rootsOfSent
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the shared chain's trees with their tenants agree in depth and width with
`treesSent`'s. -/
theorem cmp1 :
    ((mineW tl1 extra1 maskW).map (fun r => (r.logLength, r.words)) !=
      t1.map fun t => (t.1.a, t.1.W)) = false := by
  unfold mineW tl1 t1 sortedW sentsOf extra1 ProofFile.toldAt ProofFile.rootsOfSent sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **For a plan whose rounds are the shared chain's written entries and which has no other entry:
`toldChain` returns the shared chain's trees with their tenants**, at every name. -/
theorem told1 {P : Fmt.Plan} (e : P.rounds = es1) (o : P.entries.length - P.rounds.length = 0)
    (at_ : String) :
    ProofFile.toldChain at_ proofSends1 P extra1 maskW = .ok (mineW tl1 extra1 maskW) := by
  refine toldChain_of (l := tl1) (theirs := t1) ?_ ?_ cmp1
  · rw [o]
    exact some_of_isSome [] told_some1
  · rw [treesSent_eq, o, e]
    exact trees1 _

/-- What `toldAt` returns at the first chain's sendings. -/
def tl0 : List (List (Nat × ProofFile.Root)) :=
  (proofSends0.sends.mapM (ProofFile.toldAt proofSends0.codes 0)).getD []

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the `mapM` of `toldAt` returns at the first chain's sendings. -/
theorem told_some0 : (proofSends0.sends.mapM (ProofFile.toldAt proofSends0.codes 0)).isSome = true := by
  unfold ProofFile.toldAt ProofFile.rootsOfSent
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: the first chain's trees with their tenants agree in depth and width with
`treesSent`'s. -/
theorem cmp0 :
    ((mineW tl0 extra0 none).map (fun r => (r.logLength, r.words)) !=
      t0.map fun t => (t.1.a, t.1.W)) = false := by
  unfold mineW tl0 t0 sortedW sentsOf extra0 ProofFile.toldAt ProofFile.rootsOfSent sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **For a plan whose rounds are the first chain's written entries and which has no other entry:
`toldChain` returns the first chain's trees with their tenants**, at every name. -/
theorem told0 {P : Fmt.Plan} (e : P.rounds = es0) (o : P.entries.length - P.rounds.length = 0)
    (at_ : String) :
    ProofFile.toldChain at_ proofSends0 P extra0 none = .ok (mineW tl0 extra0 none) := by
  refine toldChain_of (l := tl0) (theirs := t0) ?_ ?_ cmp0
  · rw [o]
    exact some_of_isSome [] told_some0
  · rw [treesSent_eq, o, e]
    exact trees0 _

/-! ## A negative test, stated positively -/

set_option maxHeartbeats 0 in
/-- BY THE KERNEL: with every width of `treesSent`'s four trees raised by one, the second chain's
trees with their tenants do not agree with them (four against four). -/
theorem cmp2_no :
    ((mineW tl2 extra2 none).map (fun r => (r.logLength, r.words)) !=
      t2.map fun t => (t.1.a, t.1.W + 1)) = true := by
  unfold mineW tl2 t2 sortedW sentsOf extra2 ProofFile.toldAt ProofFile.rootsOfSent sentAt sendTag
  simp only [Johnson.Unfolds.mergeSort_eq, Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end Johnson.AtFull.ProofBack

#print axioms Johnson.AtFull.ProofBack.some_of_isSome
#print axioms Johnson.AtFull.ProofBack.told_some2
#print axioms Johnson.AtFull.ProofBack.cmp2
#print axioms Johnson.AtFull.ProofBack.told2
#print axioms Johnson.AtFull.ProofBack.told_some1
#print axioms Johnson.AtFull.ProofBack.cmp1
#print axioms Johnson.AtFull.ProofBack.told1
#print axioms Johnson.AtFull.ProofBack.told_some0
#print axioms Johnson.AtFull.ProofBack.cmp0
#print axioms Johnson.AtFull.ProofBack.told0
#print axioms Johnson.AtFull.ProofBack.cmp2_no
