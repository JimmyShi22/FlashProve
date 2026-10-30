-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TailLight.lean: THE SMALLNESS TEST: THE PREMISES OF `TailReady`
(Johnson/Desc/K8/Honest/EqTailReturns.lean) WITHOUT THE THREE THAT SPEAK OF THE READS' MARKS, AND A
TEST FOR THEM THAT LAYS NO MARK. Two definitions, and two statements, each as a definition of a
proposition; no proof stands here. Lemmas; none of the library's goals.

  `TailLight …`      fourteen of the seventeen premises, to the letter (`four` · `drawn` · `plan` ·
                     `one` · `fresh` · `fits` · `table` · `reads` · `inList` · `tile1` · `tile3` ·
                     `kinds` · `sum` · `apart`), and one new: `parts`: there are at most two parts.
                     Left out: `marks` · `allSet` · `count`
  `tailLightB …`     the test: `tailReadyB` (Johnson/Desc/K8/Honest/EqTailToy.lean) without its
                     call of `marksOf`, without "every mark is set" and without the count, and with
                     the number of parts
  `Spec.tailReady_of_light`    the fifteen give the seventeen, at some marks
  `Spec.tailReadyB_of_light`   a yes of the lighter test is a yes of `tailReadyB`
What the lighter test still walks: the list of reads, once (`readB` at each read): as many steps as
the tables have segments. What it no longer does: lay a mark for each entry of the vectors' parts.
NEITHER TEST HAS BEEN MEASURED AT A LARGE PLAN.
Limits. One way: a no of the lighter test does not deny the seventeen (three parts, the third
empty). The lighter test calls the tiling test twice, which sorts the tables by `List.mergeSort`;
the toy lines of Johnson/Desc/First/TailClaims/MarksOfTiles.lean evaluate that test by
`decide +kernel`. The five tests that it shares with `tailReadyB` stand in a file of tests, which
this file therefore imports. Nothing says that the premises hold at any state of a run.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- Fourteen of `TailReady`'s premises, to the letter, and the number of parts. -/
structure TailLight (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork)
    (cs : Array Claim) (s1 s3 : Nat) : Prop where
  four : front + cs.size - before = 4
  drawn : F.thetaDrawnF = true
  plan : F.planClaimsF ≠ 0
  one : oneRow tl = true
  fresh : ∀ mu, mu < tl.NM → (takenOf tl).getD mu true = false
  fits : ∀ mu, mu < tl.NM →
    (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k ∧ 0 < (tl.mats.getD mu {}).m
  table : ∀ Fn ∈ funs.toList, Fn.mat < tl.NM → (Fn.tree = 0 ∨ Fn.tree = 2) →
    (tl.ix.U.getD Fn.tree none).isSome = true ∧ Fn.len ≠ 0 ∧
      (tl.mats.getD Fn.mat {}).m % Fn.len = 0 ∧ Fn.phi.size = Fn.len
  reads : ∀ x ∈ readsList tl funs, ∃ tU, ReadReady tl F x.1 x.2 tU
  inList : (funs.all fun Fn =>
    decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) = true
  tile1 : tl.tablesTile funs 0 = some s1
  tile3 : tl.tablesTile funs 2 = some s3
  kinds : ((List.range F.trees.size).all fun t =>
    (tiesOnOf tl F.trees.size).getD t 0 ==
      (if (F.trees.map (·.kind)).getD t .table == .symbols then 1 else 0)) = true
  sum : (tiesOnOf tl F.trees.size).foldl (· + ·) 0 = tl.NM
  apart : allDistinct tl.gtTree.toList = true
  /-- there are at most two parts that hold tables -/
  parts : tl.tabLen.size ≤ 2

/-- The test for the fifteen: it lays no mark. -/
def tailLightB (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork)
    (cs : Array Claim) : Bool :=
  match tl.tablesTile funs 0, tl.tablesTile funs 2 with
  | some _, some _ =>
    front + cs.size - before == 4 && F.thetaDrawnF && F.planClaimsF != 0 && oneRow tl &&
      freshB tl && fitsB tl && tableB tl funs && (readsList tl funs).all (readB tl F) &&
      (funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) &&
      ((List.range F.trees.size).all fun t =>
        (tiesOnOf tl F.trees.size).getD t 0 ==
          (if (F.trees.map (·.kind)).getD t .table == .symbols then 1 else 0)) &&
      (tiesOnOf tl F.trees.size).foldl (· + ·) 0 == tl.NM && allDistinct tl.gtTree.toList &&
      decide (tl.tabLen.size ≤ 2)
  | _, _ => false

namespace Spec

/-- States: the fifteen premises give the seventeen, at some marks. -/
def tailReady_of_light : Prop :=
  ∀ (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim)
    (s1 s3 : Nat), TailLight before front tl funs F cs s1 s3 →
    ∃ rd, TailReady before front tl funs F cs rd s1 s3

/-- States: a yes of the lighter test is a yes of the test for the seventeen. -/
def tailReadyB_of_light : Prop :=
  ∀ (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim),
    tailLightB before front tl funs F cs = true → tailReadyB before front tl funs F cs = true

end Spec

end VerifiableInference.Desc.First.K8.Honest
