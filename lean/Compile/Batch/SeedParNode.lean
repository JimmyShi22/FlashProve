-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedParNode.lean: the program that makes a `Node` of the compiled scheme does not look
at the numbers of its tokens. Used in Compile/Batch/SeedReplay.lean. (Words of this library:
lean/GLOSSARY.md.)

A `Node` is the randomness of one encoding of the index with its salted Merkle tree; `nodeP'` of
Compile/Batch/Star.lean makes a fresh one (a tree over an encoded index, `commitE` of
Compile/Batch/TokTree.lean). A token is the number of a secret string in the store on which a token
program runs.

  Part 1  run on a store, and run on the store without the δ strings after the first N₀, the program
          makes the same queries and takes the same samples; the digests in its result are the same,
          and the tokens in its result are related by `Life2.up` (Compile/Step1_life2_Virt.lean: a
          number below N₀ stays, any other grows by δ) (`Compile.Seed.Par`, Compile/SeedKit.lean)
  Part 2  all tokens of the result are below the length of the store after the run

Limits: nothing about distributions, and nothing about the prover of a batch.
-/
import Compile.Batch.SeedStar

noncomputable section

open Rom Iop

namespace Compile.Batch
namespace Seed

open Life2 (up)
open Compile.Seed (Par upS upTree All SaltsLt all_prefix)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {N₀ δ : ℕ}

/-! ## Part 1. On two stores -/

/-- a salted leaf: its salt and its digest are new tokens -/
theorem par_leafT (sMT : ℕ) (b : Body L) :
    Par N₀ δ (fun a a' => a = (up N₀ δ a'.1, up N₀ δ a'.2) ∧ N₀ ≤ a'.1 ∧ N₀ ≤ a'.2)
      (leafT (lam := lam) (K := K) sMT b) (leafT sMT b) := by
  unfold leafT
  exact Par.fresh sMT fun t ht =>
    Par.marked (S := spec lam K L) (sp := split lam K L) (t := t) (us := [])
      (k := fun _ d => Step.pure (up N₀ δ t, d)) (k' := fun _ d => Step.pure (t, d)) OracleName.leaf
      (fun v _ => (⟨b, v⟩ : LeafIn L)) _ fun _ t' ht' => Par.pure ⟨rfl, ht, ht'⟩

theorem par_showT (t : Tok) :
    Par N₀ δ Eq (showT (lam := lam) (K := K) (L := L) (up N₀ δ t)) (showT t) :=
  Par.reveal (ts := [t]) fun _ => Par.pure rfl

theorem par_leafE (sMT : ℕ) (b : Body L) (bl : Bool) :
    Par N₀ δ (fun a a' => a = (a'.1, upS N₀ δ a'.2))
      (leafE (lam := lam) (K := K) sMT b bl) (leafE sMT b bl) := by
  unfold leafE
  cases bl with
  | true =>
    simp only [if_true]
    refine (par_leafT sMT b).bind fun x x' h => ?_
    obtain ⟨rfl, -, -⟩ := h
    refine (par_showT x'.2).bind fun d d' h' => ?_
    subst h'
    exact Par.pure rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact Par.plain _ _ fun d => Par.pure rfl

theorem par_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool), Par N₀ δ (fun a a' => a = (a'.1, a'.2.map (upS N₀ δ)))
      (leavesE (lam := lam) (K := K) sMT l) (leavesE sMT l)
  | [] => Par.pure rfl
  | (b, bl) :: t => by
    show Par N₀ δ _
      ((leafE sMT b bl).bind fun x =>
        (leavesE sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2))
      ((leafE sMT b bl).bind fun x =>
        (leavesE sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2))
    refine (par_leafE sMT b bl).bind fun a a' h => (par_leavesE sMT t).bind fun c c' h' => ?_
    subst h h'
    exact Par.pure rfl

theorem par_pairUpE :
    ∀ l : List (Dig lam), Par N₀ δ Eq (pairUp (nodeE (K := K) (L := L)) l) (pairUp nodeE l)
  | a :: b :: t => by
    show Par N₀ δ _ ((nodeE a b).bind fun c => (pairUp nodeE t).bind fun r => Step.pure (c :: r))
      ((nodeE a b).bind fun c => (pairUp nodeE t).bind fun r => Step.pure (c :: r))
    refine Par.bind (r := Eq) (Par.plain _ _ fun d => Par.pure rfl) fun c c' h =>
      (par_pairUpE t).bind fun r r' h' => ?_
    subst h h'
    exact Par.pure rfl
  | [] => Par.pure rfl
  | [_] => Par.pure rfl

theorem par_levelsE :
    ∀ (d : ℕ) (l : List (Dig lam)),
      Par N₀ δ Eq (levelsM (nodeE (K := K) (L := L)) d l) (levelsM nodeE d l)
  | 0, _ => Par.pure rfl
  | d + 1, l => by
    show Par N₀ δ _
      ((pairUp nodeE l).bind fun u => (levelsM nodeE d u).bind fun r => Step.pure (l :: r))
      ((pairUp nodeE l).bind fun u => (levelsM nodeE d u).bind fun r => Step.pure (l :: r))
    refine (par_pairUpE l).bind fun u u' h => ?_
    subst h
    refine (par_levelsE d u).bind fun r r' h' => ?_
    subst h'
    exact Par.pure rfl

/-- A tree over an encoded index: the same digests; the tokens of its salts are related by up. -/
theorem par_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    Par N₀ δ (fun a a' => a = upTree N₀ δ a')
      (commitE (lam := lam) (K := K) sMT d leaf) (commitE sMT d leaf) := by
  show Par N₀ δ _
    ((leavesE sMT ((List.range (2 ^ d)).map leaf)).bind fun x =>
      (levelsM nodeE d x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TreeH lam))
    ((leavesE sMT ((List.range (2 ^ d)).map leaf)).bind fun x =>
      (levelsM nodeE d x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TreeH lam))
  refine (par_leavesE sMT _).bind fun x x' h => ?_
  subst h
  refine (par_levelsE d x'.1).bind fun lv lv' h' => ?_
  subst h'
  exact Par.pure rfl

theorem par_drawT {β : Type} (e : Enum β) :
    Par N₀ δ Eq (drawT (lam := lam) (K := K) (L := L) e) (drawT e) :=
  Par.sample _ fun _ => Par.pure rfl

/-- A `Node`. -/
theorem par_nodeP' (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I) :
    Par N₀ δ (fun a a' => a = upNode N₀ δ a') (nodeP' W WP p i) (nodeP' W WP p i) := by
  unfold nodeP'
  refine Par.bind (par_drawT WP.ri) fun r r' h => ?_
  subst h
  refine Par.bind (par_commitE p.sMT W.depth _) fun t t' h => ?_
  subst h
  exact Par.pure rfl

/-! ## Part 2. The tokens of the result -/

theorem all_leafE_lt (sMT : ℕ) (b : Body L) (bl : Bool) (vs : List Bits) :
    All (fun o => SaltsLt o.2.length [o.1.2])
      (erase (leafE (lam := lam) (K := K) sMT b bl) vs) := by
  unfold leafE
  cases bl
  · intro r y hy
    simp at hy
  · intro r r' y hy
    have e : y = (vs.length, (vs ++ [List.ofFn fun i : Fin sMT => r.val.testBit i]).length) := by
      have := List.mem_singleton.1 hy
      exact (Option.some.inj this)
    subst e
    constructor
    · show vs.length < ((vs ++ [_]) ++ [_]).length
      simp only [List.length_append, List.length_singleton]
      omega
    · show (vs ++ [_]).length < ((vs ++ [_]) ++ [_]).length
      simp only [List.length_append, List.length_singleton]
      omega

theorem all_leavesE_lt (sMT : ℕ) :
    ∀ (l : List (Body L × Bool)) (vs : List Bits),
      All (fun o => SaltsLt o.2.length o.1.2) (erase (leavesE (lam := lam) (K := K) sMT l) vs)
  | [], _ => fun y hy => by simp at hy
  | (b, bl) :: t, vs => by
      show All _
        (erase ((leafE sMT b bl).bind fun x =>
            (leavesE sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2)) vs)
      rw [erase_bind]
      refine (all_leafE_lt sMT b bl vs).bind fun a ha => ?_
      rw [erase_bind]
      refine ((all_leavesE_lt sMT t a.2).and (all_prefix _ a.2)).bind fun r hr => ?_
      intro y hy
      rcases List.mem_cons.1 hy with e | e
      · exact (ha.mono hr.2.length_le) y (by rw [e]; exact List.mem_singleton.2 rfl)
      · exact hr.1 y e

theorem all_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) (vs : List Bits) :
    All (fun o => SaltsLt o.2.length o.1.salts)
      (erase (commitE (lam := lam) (K := K) sMT d leaf) vs) := by
  show All _
    (erase ((leavesE sMT ((List.range (2 ^ d)).map leaf)).bind fun x =>
        (levelsM nodeE d x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TreeH lam)) vs)
  rw [erase_bind]
  refine (all_leavesE_lt sMT _ vs).bind fun a ha => ?_
  rw [erase_bind]
  exact (all_prefix _ a.2).bind fun r hr => ha.mono hr.length_le

/-- All tokens of a `Node` are below the length of the store after it. -/
theorem all_nodeP' (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I) (vs : List Bits) :
    All (fun o => SaltsLt o.2.length o.1.tree.salts) (erase (nodeP' W WP p i) vs) := by
  unfold nodeP'
  rw [erase_bind]
  refine All.bind (Q := fun _ => True) ((all_prefix _ vs).mono fun _ _ => trivial) fun a _ => ?_
  rw [erase_bind]
  exact (all_commitE p.sMT W.depth _ a.2).bind fun t ht => ht

end Seed
end Compile.Batch
