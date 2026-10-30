-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedCostTree.lean: what the Merkle trees of the honest committer and prover cost
  over one hash function, if only the marked blocks are queried. One small lemma for each term of
  Compile/Batch/TokTree.lean (words of this library: lean/GLOSSARY.md).

  The weight of a typed query is the number of its marked blocks (`needOf nb m`,
  Compile/Batch/NeedTable.lean; `num_le_blk`, Compile/Batch/NeedCost.lean). For `Std m`
  (Compile/Batch/NeedTable.lean) the oracles of trees have one block, so each query to them costs at
  most one, whatever nb. The bounds are stated with `SWA` (Compile/CostAt.lean).
    `tr d`                        2^d + (2^d − 1): the leaves and the inner nodes of a tree of depth
                                  d; `tr_le`: at most 2 · 2^d
    `swa_pairUp`, `swa_levelsM`   for any node function that costs one: the levels over a list of n
                                  entries cost at most n − 1, whatever n and the number of levels
    `swa_commitT`, `swa_commitE`  a tree over a prover message, a tree over an encoded index: tr d
    `swa_reqT`                    a request tree over n slot values: n + (n − 1)
    `swa_reqTU`                   the request tree in which the leaf of an empty slot is sampled
                                  (Compile/Batch/ProverU.lean): one for each slot value, and (number
                                  of slots) − 1 inner nodes
    `swa_openT`, `swa_showT`, `swa_openE`, `swa_drawT`
                                  opening, showing and sampling cost nothing
  Limits: nothing on rounds, chains and schemes. All are upper bounds on every path.
-/
import Compile.CostAt
import Compile.Batch.NeedCost
import Compile.Batch.ProverU

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.CostP (SWA)

/-- the leaves and the inner nodes of a tree of depth d -/
def tr (d : ℕ) : ℕ := 2 ^ d + (2 ^ d - 1)

theorem tr_le (d : ℕ) : tr d ≤ 2 * 2 ^ d := by
  unfold tr
  omega

section Trees
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam}

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam K L) (sp := split lam K L) (Rom.Need.num (needOf nb m))

/-! ### What costs nothing -/

theorem swa_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    SWo (openT (lam := lam) (K := K) (L := L) t j a) 0 T1 := fun _ => trivial

theorem swa_showT (t : Tok) : SWo (showT (lam := lam) (K := K) (L := L) t) 0 T1 := fun _ => trivial

theorem swa_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    SWo (openE (K := K) (L := L) t j a) 0 T1 := by
  unfold openE
  split
  · exact fun _ => trivial
  · exact trivial

theorem swa_drawT {β : Type} (e : Enum β) : SWo (drawT (lam := lam) (K := K) (L := L) e) 0 T1 :=
  fun _ => trivial

/-! ### Levels, for any node function that costs one -/

theorem swa_pairUp {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, SWo (node a b) 1 T1) :
    ∀ l : List D, SWo (pairUp node l) (l.length / 2) fun u => u.length = (l.length + 1) / 2
  | [] => show ([] : List D).length = (0 + 1) / 2 from rfl
  | [a] => show [a].length = (1 + 1) / 2 from rfl
  | a :: b :: t =>
      SWA.bind' (hn a b) (m' := t.length / 2) (fun c _ => SWA.bind' (swa_pairUp hn t) (m' := 0) (fun r hr => by
        show (c :: r).length = ((a :: b :: t).length + 1) / 2
        simp only [List.length_cons]
        omega) (Nat.le_refl _)) (by simp only [List.length_cons]; omega)

/-- If a call of the node function costs at most one (`hn`): the levels over n entries cost at most
n − 1: each call of the node function makes one entry of two. -/
theorem swa_levelsM {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, SWo (node a b) 1 T1) :
    ∀ (d : ℕ) (l : List D), SWo (levelsM node d l) (l.length - 1) T1
  | 0, _ => trivial
  | d + 1, l =>
      SWA.bind' (swa_pairUp nb hn l) (m' := (l.length + 1) / 2 - 1)
        (fun u hu =>
          SWA.bind' (hu ▸ swa_levelsM hn d u) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
        (by omega)

variable (hm : Std m)
include hm

/-! ### Trees over prover messages -/

theorem swa_leafT (sMT : ℕ) (b : Body L) : SWo (leafT (lam := lam) (K := K) sMT b) 1 T1 :=
  fun _ => ⟨1, 0, fun _ _ => num_le_blk nb hm OracleName.leaf _, rfl, fun _ _ => trivial⟩

theorem swa_nodeT (a b : Tok) : SWo (nodeT (lam := lam) (K := K) (L := L) a b) 1 T1 :=
  ⟨1, 0, fun _ _ => num_le_blk nb hm OracleName.node _, rfl, fun _ _ => trivial⟩

theorem swa_leavesT (sMT : ℕ) :
    ∀ l : List (Body L),
      SWo (leavesT (lam := lam) (K := K) sMT l) l.length fun o => o.1.length = l.length
  | [] => rfl
  | b :: t =>
      SWA.bind' (swa_leafT nb hm sMT b) (m' := t.length) (fun x _ => SWA.bind' (swa_leavesT sMT t) (m' := 0) (fun r hr => by
        show (x.2 :: r.1).length = (b :: t).length
        rw [List.length_cons, List.length_cons, hr]) (Nat.le_refl _)) (by rw [List.length_cons]; omega)

/-- A tree of depth d over a prover message. -/
theorem swa_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    SWo (commitT (lam := lam) (K := K) sMT d leaf) (tr d) T1 :=
  SWA.bind' (swa_leavesT nb hm sMT _) (m' := 2 ^ d - 1)
    (fun x hx =>
      SWA.bind' (swa_levelsM nb (swa_nodeT nb hm) d x.1) (m' := 0) (fun _ _ => trivial)
        (by rw [hx, List.length_map, List.length_range]; omega))
    (by rw [List.length_map, List.length_range]; exact Nat.le_refl _)

/-! ### Request trees -/

theorem swa_rleafT (c : Tok) : SWo (rleafT (lam := lam) (K := K) (L := L) c) 1 T1 :=
  ⟨1, 0, fun _ _ => num_le_blk nb hm OracleName.rleaf _, rfl, fun _ _ => trivial⟩

theorem swa_rnodeT (a b : Tok) : SWo (rnodeT (lam := lam) (K := K) (L := L) a b) 1 T1 :=
  ⟨1, 0, fun _ _ => num_le_blk nb hm OracleName.rnode _, rfl, fun _ _ => trivial⟩

theorem swa_rleavesT :
    ∀ l : List Tok,
      SWo (rleavesT (lam := lam) (K := K) (L := L) l) l.length fun r => r.length = l.length
  | [] => rfl
  | c :: t =>
      SWA.bind' (swa_rleafT nb hm c) (m' := t.length) (fun d _ => SWA.bind' (swa_rleavesT t) (m' := 0) (fun r hr => by
        show (d :: r).length = (c :: t).length
        rw [List.length_cons, List.length_cons, hr]) (Nat.le_refl _)) (by rw [List.length_cons]; omega)

/-- a request tree over n slot values -/
theorem swa_reqT (depthReq : ℕ) (cs : List Tok) :
    SWo (reqT (lam := lam) (K := K) (L := L) depthReq cs) (cs.length + (cs.length - 1)) T1 :=
  SWA.bind' (swa_rleavesT nb hm cs) (m' := cs.length - 1)
    (fun ls hl =>
      SWA.bind' (swa_levelsM nb (swa_rnodeT nb hm) depthReq ls) (m' := 0)
        (fun _ _ => trivial) (by rw [hl]; omega)) (Nat.le_refl _)

/-- For `Std m`: the leaves of the request tree `reqTU` (an empty slot's leaf is sampled) cost at
most one query for each slot value. -/
theorem swa_rleavesTU :
    ∀ l : List (Option Tok),
      SWo (rleavesTU (lam := lam) (K := K) (L := L) l)
        ((l.map Option.isSome).count true) fun r => r.length = l.length
  | [] => rfl
  | some c :: t =>
      SWA.bind' (swa_rleafT nb hm c) (m' := (t.map Option.isSome).count true) (fun d _ => SWA.bind' (swa_rleavesTU t) (m' := 0) (fun r hr => by
        show (d :: r).length = (some c :: t).length
        rw [List.length_cons, List.length_cons, hr]) (Nat.le_refl _)) (by simp only [List.map_cons, Option.isSome_some, List.count_cons_self]; omega)
  | none :: t => fun d =>
      SWA.bind' (swa_rleavesTU t) (m' := 0) (fun r hr => by
        show (d :: r).length = (none :: t).length
        rw [List.length_cons, List.length_cons, hr]) (by simp)

/-- For `Std m`: the request tree `reqTU` costs at most a leaf query for each slot value, and one
inner node less than there are slots. -/
theorem swa_reqTU (depthReq : ℕ) (cs : List (Option Tok)) :
    SWo (reqTU (lam := lam) (K := K) (L := L) depthReq cs)
      ((cs.map Option.isSome).count true + (cs.length - 1)) T1 :=
  SWA.bind' (swa_rleavesTU nb hm cs) (m' := cs.length - 1)
    (fun ls hl =>
      SWA.bind' (swa_levelsM nb (swa_rnodeT nb hm) depthReq ls) (m' := 0)
        (fun _ _ => trivial) (by rw [hl]; omega)) (Nat.le_refl _)

/-! ### Trees over encoded indices -/

theorem swa_leafE (sMT : ℕ) (b : Body L) (bl : Bool) :
    SWo (leafE (lam := lam) (K := K) sMT b bl) 1 T1 := by
  unfold leafE
  cases bl with
  | true =>
    exact SWA.bind' (swa_leafT nb hm sMT b) (m' := 0)
      (fun x _ => SWA.bind' (swa_showT nb x.2) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
      (Nat.le_refl _)
  | false => exact ⟨1, 0, num_le_blk nb hm OracleName.leaf _, rfl, fun _ => trivial⟩

theorem swa_nodeE (a b : Dig lam) : SWo (nodeE (K := K) (L := L) a b) 1 T1 :=
  ⟨1, 0, num_le_blk nb hm OracleName.node _, rfl, fun _ => trivial⟩

theorem swa_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool),
      SWo (leavesE (lam := lam) (K := K) sMT l) l.length fun o => o.1.length = l.length
  | [] => rfl
  | (b, bl) :: t =>
      SWA.bind' (swa_leafE nb hm sMT b bl) (m' := t.length) (fun x _ => SWA.bind' (swa_leavesE sMT t) (m' := 0) (fun r hr => by
        show (x.1 :: r.1).length = ((b, bl) :: t).length
        rw [List.length_cons, List.length_cons, hr]) (Nat.le_refl _)) (by rw [List.length_cons]; omega)

/-- A tree of depth d over an encoded index. -/
theorem swa_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    SWo (commitE (lam := lam) (K := K) sMT d leaf) (tr d) T1 :=
  SWA.bind' (swa_leavesE nb hm sMT _) (m' := 2 ^ d - 1)
    (fun x hx =>
      SWA.bind' (swa_levelsM nb (swa_nodeE nb hm) d x.1) (m' := 0) (fun _ _ => trivial)
        (by rw [hx, List.length_map, List.length_range]; omega))
    (by rw [List.length_map, List.length_range]; exact Nat.le_refl _)

end Trees

end Need
end Compile.Batch
