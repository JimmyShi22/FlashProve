-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CostFull.lean: how many questions the parser that fills whole paths asks: at most the strict
reader's number, a function of the description alone.

A counterpart of Run/CostLax.lean. The lenient reader asks nothing at an opening.
Run/ParseFull.lean's reader hashes each opened leaf and walks: at an opening of a tree of depth a
at a list of at most L positions: at most (a + 1) · L calls of the hash (Run/CostFmt.lean:
`opensN`). So its count is the strict reader's `fileN S` (Run/CostFmt.lean), in units of k, the
cost of one call of the hash. A count is a `c : CostP m`; what it says depends on the instance c:
Run/CostP.lean, the head, 4.

1. What the file contains. One statement (`Run.Spec.cost_full`) with its proof.

2. What is checked when the file compiles. Only the types and proofs.

3. Theorems. For every count c : `CostP m` and every hash h of which each call asks at most k.
   `CostP.cutStepO`, `cutFoldO`, `cutChainO`, `cutWholeO`: the fold of Run/ParseLax.lean with a
      reader of openings whose cost is opensN (number of drawn positions) (the trees) · k: roundN r
      · k; roundsN rs · k; fileN S · k.
   `cost_full`: c.le (fullWhole h S b) (fileN S · k); c.le (parseFullW h S T b) (fileN S · k).

4. What is not claimed. These are upper bounds. What Run/CostFmt.lean's head says is not counted
there is not counted here.

Terms: lean/GLOSSARY.md.
-/
import Run.CostLax
import Run.ParseFull

set_option autoImplicit false

namespace Run
open _root_.Fmt (Plan Spec St Round Shape Src firstBlock wordsAtMost drawRound rowOf listOf)

open Iop Compile.Batch in
def Spec.cost_full : Prop :=
  ∀ (m : Type → Type) [Monad m] (c : CostP m)
      (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat),
    (∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True) →
    ∀ (S : _root_.Fmt.Spec) (b : ByteArray),
      c.le (fullWhole h S b) (fileN S * k) (fun _ => True) ∧
      ∀ (Y : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof Y E) (T : Typing Q),
        c.le (parseFullW h S T b) (fileN S * k) fun _ => True

namespace CostP
variable {m : Type → Type} [Monad m] (c : CostP m)
  (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (k : Nat)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem cutStepO (ops : OpsW m)
    (ho : ∀ run roots poss os i,
      c.le (ops run roots poss os i) (opensN poss.length os * k) fun _ => True)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St) (r : Round) :
    c.le (Run.cutStep h ops P run b s r) (roundN r * k) fun _ => True := by
  unfold Run.cutStep
  split
  · exact c.pureLe _ _ _ trivial
  · split
    · exact c.pureLe _ _ _ trivial
    · split
      · exact c.pureLe _ _ _ trivial
      · refine c.le_mono _
          ((firstBlock r.entry.work + (wordsAtMost r.entry r.kind + 3) / 4 + 1) / 2 * k +
            opensN r.entry.poss r.opens * k)
          _ _ _ (c.le_bind _ _ _ _ _ _ (c.laxQueryW h k hk _ _ _ _ _ _) fun q _ => ?_)
          (by simp only [roundN, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
        cases q with
        | none => exact c.pureLe _ _ _ trivial
        | some cv =>
          simp only []
          split
          · exact c.pureLe _ _ _ trivial
          · refine c.le_mono _ (opensN r.entry.poss r.opens * k + 0) _ _ _
              (c.le_bind _ _ _ 0 (fun _ => True) _ ?_ fun q _ => ?_) (Nat.le_refl _) fun _ h => h
            · have key : ∀ (roots : Array ByteArray) (i : Nat),
                  c.le
                    (ops run roots (drawRound P.field r.entry r.kind (rowOf cv.2)).poss r.opens i)
                    (opensN r.entry.poss r.opens * k) fun _ => True := fun roots i => by
                have := ho run roots (drawRound P.field r.entry r.kind (rowOf cv.2)).poss r.opens i
                rw [drawRound_poss] at this
                exact this
              exact key _ _
            · cases q <;> exact c.le_pure _ _ trivial

theorem cutFoldO (ops : OpsW m)
    (ho : ∀ run roots poss os i,
      c.le (ops run roots poss os i) (opensN poss.length os * k) fun _ => True)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    ∀ (rs : List Round) (s : St),
      c.le (Run.cutFold h ops P run b rs s) (roundsN rs * k) fun _ => True
  | [], _ => c.pureLe _ _ _ trivial
  | r :: rs, s => by
    simp only [Run.cutFold]
    refine c.le_mono _ (roundN r * k + roundsN rs * k) _ _ _
      (c.le_bind _ _ _ _ _ _ (c.cutStepO h k hk ops ho P run b s r) fun q _ => ?_)
      (by simp only [roundsN, Nat.add_mul]; exact Nat.le_refl _) fun _ h => h
    cases q with
    | none => exact c.pureLe _ _ _ trivial
    | some s' => exact cutFoldO ops ho P run b rs s'

theorem cutChainO (ops : ByteArray → OpsW m)
    (ho : ∀ b run roots poss os i,
      c.le (ops b run roots poss os i) (opensN poss.length os * k) fun _ => True)
    (S : Spec) (b : ByteArray) (i : Nat) :
    c.le (Run.cutChain h ops S b i) (fileN S * k) fun _ => True := by
  unfold Run.cutChain
  split
  · exact c.pureLe _ _ _ trivial
  · simp only []
    split
    · exact c.pureLe _ _ _ trivial
    · refine c.le_mono _ (k + (2 * k + (roundsN S.rounds * k + 0))) _ _ _
        (c.le_bind _ _ k _ _ _ (hk _ _ _ _ _) fun pd _ =>
          c.le_bind _ _ _ _ _ _ (c.startChainW h k hk _ _ _ _) fun q _ => ?_)
        (by simp only [fileN, Nat.add_mul]; omega) fun _ h => h
      cases q with
      | none => exact c.pureLe _ _ _ trivial
      | some hd =>
        refine c.le_bind _ _ _ 0 _ _ (c.cutFoldO h k hk (ops b) (ho b) _ _ _ _ _) fun q _ => ?_
        cases q <;> exact c.le_pure _ _ trivial

theorem cutWholeO (ops : ByteArray → OpsW m)
    (ho : ∀ b run roots poss os i,
      c.le (ops b run roots poss os i) (opensN poss.length os * k) fun _ => True)
    (S : Spec) (b : ByteArray) :
    c.le (Run.cutWhole h ops S b) (fileN S * k) fun _ => True := by
  simp only [Run.cutWhole]
  refine c.le_bind _ _ _ 0 _ _ (c.cutChainO h k hk ops ho S b 0) fun q _ => ?_
  cases q <;> exact c.le_pure _ _ trivial

theorem fullOpens (cfg : ByteArray) (P : Plan) (b : ByteArray) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) :
    ∀ (os : List (Shape × Src)) (i : Nat),
      c.le (Run.fullOpens h cfg P b run roots poss os i) (opensN poss.length os * k) fun _ => True
  | [], _ => c.pureLe _ _ _ trivial
  | (sh, src) :: os, i => by
    unfold Run.fullOpens
    simp only []
    split
    · exact c.pureLe _ _ _ trivial
    · have hl : (listOf (poss.map (· % 2 ^ sh.a))).length ≤ poss.length :=
        Nat.le_trans (listOf_len _) (Nat.le_of_eq (List.length_map _))
      refine c.le_mono _ ((sh.a + 1) * (poss.length * k) + opensN poss.length os * k) _ _ _
        (c.le_bind _ _ _ _ _ _
          (c.le_mono _ _ _ _ _ (c.readOpeningW h k hk cfg P.field P.salt sh _ _ b i)
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hl)) fun _ h => h) fun r _ => ?_)
        (by simp only [opensN, Nat.add_mul, Nat.mul_assoc]; exact Nat.le_refl _) fun _ h => h
      cases r with
      | none => exact c.pureLe _ _ _ trivial
      | some o =>
        simp only []
        refine c.le_mono _ (opensN poss.length os * k + 0) _ _ _
          (c.le_bind _ _ _ 0 _ _ (fullOpens cfg P b run roots poss os _) fun r _ => ?_)
          (Nat.le_refl _) fun _ h => h
        cases r <;> exact c.le_pure _ _ trivial

theorem fullWhole (S : Spec) (b : ByteArray) :
    c.le (Run.fullWhole h S b) (fileN S * k) fun _ => True := by
  unfold Run.fullWhole
  exact c.cutWholeO h k hk _
    (fun b' run roots poss os i => c.fullOpens h k hk S.cfg S.plan b' run roots poss os i) S b

open Iop Compile.Batch in
theorem parseFullW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (b : ByteArray) :
    c.le (Run.parseFullW h S T b) (fileN S * k) fun _ => True := by
  simp only [Run.parseFullW]
  exact c.bindPure _ _ _ _ _ (c.fullWhole h k hk S b) fun _ _ => trivial

end CostP

theorem cost_full : Spec.cost_full := fun _ _ c h k hk S b =>
  ⟨c.fullWhole h k hk S b, fun _ _ _ T => c.parseFullW h k hk S T b⟩

end Run
