-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/StoredItemZeroDeclared.lean: at every description F of a file (FileDescription,
Johnson/Desc/Block.lean) that has data (F.data file = .ok D), no declared round of the first chain
(F.roundsDeclaredByBlocks.1) or the third (F.roundsDeclaredByBlocks.2.2, the field second) names a stored table, and every stored table
that a declared round of the second chain (F.roundsDeclaredByBlocks.2.1, the field shared) names has the item 0
(declared_stored). So every read of a stored table by readsOf, the reader in the frame of the honest
side (Johnson/Desc/ProofFile/Honest/Frame.lean), at any list of such declared rounds and at any list
of verifier challenges, is at the item 0 (read_item_zero_rounds).
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
A file has three chains of rounds. A declared round (Fmt.DeclaredRound, Decl/Declared.lean) is a round
as the public plan states it: its entry, the stored tables and the trees that it opens. F.roundsDeclaredByBlocks holds
the three chains' lists. A written round is the pair that writtenOf (Johnson/G/RoundsOfPlan.lean)
makes of a declared one. The item of a stored table (Fmt.Stored.item, Fmt/Rules8X.lean) is the
number, from 0, of the statement's item that holds the table's root. Here "description" is a file's
description, FileDescription.
  declared_stored   FileDescription.data (Johnson/Desc/BlockSlot.lean) returns data only where the
      library's tests okAt accept the written rounds (OnBytes/Maker/Files.lean). One of these tests
      is storedFit (OnBytes/Maker/WholeOf.lean): only the second chain opens a stored table, and
      each that it opens has the stated depth and the item 0. This theorem brings the parts on who
      opens and on the item back to the declared rounds, all of them: the first chain's last round,
      in which the chain is sealed, is among them. The depth is not needed here.
  wantsDecl_item, read_item_zero_rounds   Every stored table that such declared rounds ask for
      (wantsDecl, Johnson/Desc/BlockSlot.lean) has the item 0. Every read q of readsOf
      (Johnson/Desc/ProofFile/Honest/Frame.lean) with q.item = some i has i = 0, by read_table
      (Johnson/Desc/ProofFile/Honest/Law/WantsReads.lean). A read of a tree has the field item none
      (by readsOf's definition; by inspection, not proved).
  read_item_zero_declared, rounds_in_decl   Two cases of the list. A whole chain's declared rounds:
      at these the function run (Johnson/Desc/ProofFile/Honest/Frame.lean) calls readsOf. One
      block's rounds, which are among its chain's: at these ChainProgress.settle
      (Johnson/Desc/ProofFile/Honest/Walk.lean) calls it, through which the two strategies of
      honestBatchProverOfFile read. Where the two functions call readsOf is by inspection, not proved.
  read_item_zero_laid   The case of the proof file's description F0T o Zp Np cF
      (Johnson/P5J/AtTerm.lean) under LaidAt (Johnson/P5J/LaidOpens.lean), whose field data is the
      premise.
  zip_stored, mem_of_forall₂   The data of a written round keep the list of stored tables of the
      declared round that it is made of. mem_of_forall₂ is a lemma on lists.

How it fits. Committer.prover (Johnson/Desc/ProofFile/Honest/Committer.lean) lays the committer's
stored table into a prover of that frame's type, and answers every item with that table: it ignores
the item. By this file no declared round of a description that has data names an item other than 0.
At the library's explicit full-size data, storedFit_proofFull (Johnson/G/DryProofTestsFull.lean)
proves by evaluation in Lean's kernel that the test accepts. This file evaluates nothing: it takes
from its premise F.data file = .ok D that the test accepts, and so it holds at every size at which a
description has data. This is a lemma on descriptions. It is not one of the release's goal
statements.

Limits.
  It speaks of a description with three chains whose data FileDescription.data makes. The description of a
      copy's file is a OneChainFileDescription (Johnson/Desc/Link/OneChainFileDescription.lean), not a FileDescription, and names two
      items, 0 and 1 (readsAtLink, Johnson/Desc/K15/K15.lean; by inspection, not proved). The key
      file's description is a FileDescription (Johnson/Desc/Key/Desc.lean): the theorems hold of it too,
      where it has data.
  It speaks of declared rounds and of readsOf. That a run or a strategy reads stored tables through
      readsOf alone is not proved here. Nor is it proved that two values of the argument stored that
      agree at the item 0 give the same reads (a read's words are stored s.item x,
      Johnson/Desc/ProofFile/Honest/Frame.lean; by inspection, not proved).
  At rounds of the first and the third chain the theorems on reads are vacuous: no read there is of
      a stored table.
  That the format puts the index's root at the item 0 is not proved here (p14Of,
      Johnson/Desc/K14/Blocks.lean; by inspection, not proved).
  That any description has data is not proved here. Under LaidAt the proof file's has, by that
      structure's field data; that LaidAt holds of any files is not proved here.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.Desc.BlockSlotProofs
import Johnson.Desc.ProofFile.Honest.Law.WantsReads
import Johnson.P5J.LaidOpens

set_option autoImplicit false

namespace OnBytes.FrontRoad
open OnBytes.Maker (WholeD Want storedFit okAt_parts wholeAt)
open OnBytes.Three (rdOf)
open VerifiableInference.Desc (FileDescription Written data_ok writtenOf_ok wantsDecl Place)
open ProofFile.Honest (Read readsOf read_table Table)
open P5J

/-- A written round's data keep the declared round's list of stored tables. -/
theorem zip_stored (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : OnBytes.Params.Rounds}
    (hw : List.Forall₂ (Written e) l R) : ∀ L : List ℕ, L.length = R.length →
    List.Forall₂ (fun (d : OnBytes.Three.RDL) (z : Fmt.DeclaredRound) => d.stored = z.stored)
      (List.zipWith (rdOf all t₁ t₂ here base first) R L) l := by
  induction hw with
  | nil =>
    intro L _
    rw [List.zipWith_nil_left]
    exact .nil
  | @cons r x l R hd _ ih =>
    intro L hL
    cases L with
    | nil => cases hL
    | cons n L =>
      rw [List.zipWith_cons_cons]
      obtain ⟨y, -, rfl⟩ := hd
      exact .cons rfl (ih L (Nat.succ.inj hL))

/-- Each member of the second of two lists that are related member by member has a partner in the
first. -/
theorem mem_of_forall₂ {α β : Type} {P : α → β → Prop} : ∀ {A : List α} {B : List β},
    List.Forall₂ P A B → ∀ b ∈ B, ∃ a ∈ A, P a b
  | _, _, .nil, _, h => absurd h (List.not_mem_nil)
  | _, _, .cons hd tl, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hd⟩
    · obtain ⟨a, ha, hp⟩ := mem_of_forall₂ tl b h
      exact ⟨a, List.mem_cons_of_mem _ ha, hp⟩

/-- **At a description that has data: no declared round of the first chain (F.roundsDeclaredByBlocks.1) or the third
(F.roundsDeclaredByBlocks.2.2) names a stored table, and every stored table that a declared round of the second chain
(F.roundsDeclaredByBlocks.2.1) names has the item 0.** -/
theorem declared_stored {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) :
    (∀ z ∈ F.roundsDeclaredByBlocks.1, z.stored = []) ∧ (∀ z ∈ F.roundsDeclaredByBlocks.2.1, ∀ s ∈ z.stored, s.item = 0) ∧
      ∀ z ∈ F.roundsDeclaredByBlocks.2.2, z.stored = [] := by
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, -⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have hs : storedFit F.tableDepth (OnBytes.Three.Whole.of R₁ R₂ R₃) = true :=
    (okAt_parts hk).stored
  unfold storedFit at hs
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hs
  have k₁ : List.Forall₂ (fun (d : OnBytes.Three.RDL) (z : Fmt.DeclaredRound) => d.stored = z.stored)
      (OnBytes.Three.Whole.of R₁ R₂ R₃).ds₁ F.roundsDeclaredByBlocks.1 :=
    zip_stored _ _ _ _ _ _ w₁ _ (OnBytes.Maker.sentBefore_length R₁)
  have k₂ : List.Forall₂ (fun (d : OnBytes.Three.RDL) (z : Fmt.DeclaredRound) => d.stored = z.stored)
      (OnBytes.Three.Whole.of R₁ R₂ R₃).ds₂ F.roundsDeclaredByBlocks.2.1 :=
    zip_stored _ _ _ _ _ _ w₂ _ (OnBytes.Maker.sentBefore_length R₂)
  have k₃ : List.Forall₂ (fun (d : OnBytes.Three.RDL) (z : Fmt.DeclaredRound) => d.stored = z.stored)
      (OnBytes.Three.Whole.of R₁ R₂ R₃).ds₃ F.roundsDeclaredByBlocks.2.2 :=
    zip_stored _ _ _ _ _ _ w₃ _ (OnBytes.Maker.sentBefore_length R₃)
  refine ⟨fun z hz => ?_, fun z hz s hs' => ?_, fun z hz => ?_⟩
  · obtain ⟨d, hd, e⟩ := mem_of_forall₂ k₁ z hz
    rw [← e]
    exact List.isEmpty_iff.1 (hs.1 d (List.mem_append_left _ hd))
  · obtain ⟨d, hd, e⟩ := mem_of_forall₂ k₂ z hz
    rw [← e] at hs'
    have g := List.all_eq_true.1 (hs.2 d hd) s hs'
    rw [Bool.and_eq_true] at g
    exact beq_iff_eq.1 g.2
  · obtain ⟨d, hd, e⟩ := mem_of_forall₂ k₃ z hz
    rw [← e]
    exact List.isEmpty_iff.1 (hs.1 d (List.mem_append_right _ hd))

/-- Where every stored table that declared rounds name has the item 0, every stored table that they
ask for has the item 0. -/
theorem wantsDecl_item (num : Fmt.TreeSource → ℕ) : ∀ (l : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ l, ∀ s ∈ d.stored, s.item = 0) →
    ∀ item x, Want.table item x ∈ wantsDecl num l Rs → item = 0
  | [], _, _, _, _, hw => by
    unfold wantsDecl at hw
    exact absurd hw (List.not_mem_nil)
  | _ :: _, [], _, _, _, hw => by
    unfold wantsDecl at hw
    exact absurd hw (List.not_mem_nil)
  | d :: ds, R :: Rs, h, item, x, hw => by
    unfold wantsDecl at hw
    rcases List.mem_append.1 hw with hw | hw
    · rcases List.mem_append.1 hw with hw | hw
      · obtain ⟨s, hs, hm⟩ := List.mem_flatMap.1 hw
        obtain ⟨y, -, e⟩ := List.mem_map.1 hm
        injection e with e1 _
        rw [← e1]
        exact h d (List.mem_cons_self) s hs
      · obtain ⟨o, -, hm⟩ := List.mem_flatMap.1 hw
        obtain ⟨y, -, e⟩ := List.mem_map.1 hm
        cases e
    · exact wantsDecl_item num ds Rs (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) item x hw

/-- **At a description that has data: every read of a stored table by readsOf, at any list of
declared rounds of its three chains and at any list of verifier challenges, is at the item 0**; for
all other arguments of the reader. The list may be a whole chain's or one block's. -/
theorem read_item_zero_rounds {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) (chain ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Rs : List Fmt.Drawn) (q : Read) (i : ℕ)
    (hi : q.item = some i) (l : List Fmt.DeclaredRound)
    (hl : ∀ d ∈ l, d ∈ F.roundsDeclaredByBlocks.1 ∨ d ∈ F.roundsDeclaredByBlocks.2.1 ∨ d ∈ F.roundsDeclaredByBlocks.2.2)
    (hq : q ∈ readsOf chain ft stored tree l Rs) : i = 0 := by
  obtain ⟨d₁, d₂, d₃⟩ := declared_stored h
  refine wantsDecl_item (fun _ => 0) l Rs (fun d hd s hs => ?_) i q.pos
    (read_table (fun _ => 0) chain ft stored tree l Rs q hq i hi).1
  rcases hl d hd with g | g | g
  · rw [d₁ d g] at hs
    exact absurd hs (List.not_mem_nil)
  · exact d₂ d g s hs
  · rw [d₃ d g] at hs
    exact absurd hs (List.not_mem_nil)

/-- The case of a whole chain's declared rounds. (At these three lists the function run calls
readsOf: by inspection, not proved.) -/
theorem read_item_zero_declared {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) (chain ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Rs : List Fmt.Drawn) (q : Read) (i : ℕ)
    (hi : q.item = some i) (l : List Fmt.DeclaredRound)
    (hl : l = F.roundsDeclaredByBlocks.1 ∨ l = F.roundsDeclaredByBlocks.2.1 ∨ l = F.roundsDeclaredByBlocks.2.2)
    (hq : q ∈ readsOf chain ft stored tree l Rs) : i = 0 :=
  read_item_zero_rounds h chain ft stored tree Rs q i hi l
    (fun d hd => by
      rcases hl with rfl | rfl | rfl
      · exact Or.inl hd
      · exact Or.inr (Or.inl hd)
      · exact Or.inr (Or.inr hd)) hq

/-- The rounds of a block of a chain are among that chain's declared rounds. -/
theorem rounds_in_decl {Xi : Type} (F : FileDescription Xi) :
    (∀ b ∈ F.first.blocksInOrder, ∀ d ∈ b.rounds, d ∈ F.roundsDeclaredByBlocks.1) ∧
      (∀ b ∈ F.shared.blocksInOrder, ∀ d ∈ b.rounds, d ∈ F.roundsDeclaredByBlocks.2.1) ∧
      ∀ b ∈ F.second.blocksInOrder, ∀ d ∈ b.rounds, d ∈ F.roundsDeclaredByBlocks.2.2 :=
  ⟨fun b hb d hd => List.mem_flatMap.2 ⟨b, hb, hd⟩, fun b hb d hd => List.mem_flatMap.2 ⟨b, hb, hd⟩,
    fun b hb d hd => List.mem_flatMap.2 ⟨b, hb, hd⟩⟩

/-- **Under LaidAt, every read of a stored table by readsOf, at any list of declared rounds of the
three chains of the proof file's description F0T o Zp Np cF, is at the item 0.** The premise of
read_item_zero_rounds is LaidAt's field data. -/
theorem read_item_zero_laid {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (L : LaidAt o pol lay KL D r Zp Np cF)
    (chain ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (Rs : List Fmt.Drawn) (q : Read) (i : ℕ)
    (hi : q.item = some i) (l : List Fmt.DeclaredRound)
    (hl : ∀ d ∈ l, d ∈ (F0T o Zp Np cF).roundsDeclaredByBlocks.1 ∨ d ∈ (F0T o Zp Np cF).roundsDeclaredByBlocks.2.1 ∨
      d ∈ (F0T o Zp Np cF).roundsDeclaredByBlocks.2.2)
    (hq : q ∈ readsOf chain ft stored tree l Rs) : i = 0 :=
  read_item_zero_rounds L.data chain ft stored tree Rs q i hi l hl hq

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.zip_stored
#print axioms OnBytes.FrontRoad.mem_of_forall₂
#print axioms OnBytes.FrontRoad.declared_stored
#print axioms OnBytes.FrontRoad.wantsDecl_item
#print axioms OnBytes.FrontRoad.read_item_zero_rounds
#print axioms OnBytes.FrontRoad.read_item_zero_declared
#print axioms OnBytes.FrontRoad.rounds_in_decl
#print axioms OnBytes.FrontRoad.read_item_zero_laid
