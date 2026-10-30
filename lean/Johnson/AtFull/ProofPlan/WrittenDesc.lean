-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/WrittenDesc.lean: A written description out of the rows of a cut and lists
of declared rounds (`wOf`), and when a file's description is alike to it (`planAlike_of_cut`).
General in the rows, the rounds, the depth and the description. Definitions, statements and proofs.

Why. The tests on the plan (`FileDescription.planOk`, Johnson/Desc/Block.lean) are to be asked of Lean's
kernel at a closed description and carried to the proof file's by `FileDescription.planOk_alike₂`
(Johnson/AtFull/ProofPlan/PlanAlike.lean). A row of a cut (`cutOf`,
Johnson/Desc/Ok/PlanWritten/CutTest.lean) holds of a block its name, place, number of rounds, the
length of its oracles, the rounds that tell a tree, and before. With the declared rounds in a row
that is all that the tests read of a block, but for its own test.

  `unsparse`, `piecesBy`, `initOf`, `lastOf`: four small functions on lists. `blockOfRow`,
    `blocksOfRows`, `chainOfBlocks`, `wOf`: the written description.
  `sparse_ge`, `unsparse_sparse`, `unsparse_told`: a list of lists comes back from its length and
    its non-empty members. `pieces_flat`: a list cut by its pieces' lengths gives the pieces.
    `init_last`, `flat_of_blocks`, `flat_of_two`, `flat_len`: the chain's flat list.
  `blocks_of_cut`, `chain_alike`: the blocks that a list's own cut and rounds spell are alike to the
    list.
  `planAlike_of_cut`: main. `planWord_of_cut`: at the proof file's written cut.

What `planWord_of_cut` carries, and what it does not. To the closed premise hW go: the depth of the
stored parts, `labelsOk`, `placesOk`, `beforeOk`, `treeSharingOk`, `readsOk`, `sentFit`, `sealLast`, and
`shaped` in `blocksOk`. The three tests `roundsDeclaredByBlocks.i == plans.i` come back in another dress: hD and hP
ask that F's declared rounds and its plans are the written rounds: more than `planOk` says: a fact
on the public files (of the declared rounds: what the first of the proof file's entry tests,
`seatPinnedProof`, compares). Outright stay: each block's own test (b₁, b₂, b₃) and fileOk (hF). hC
is the tenth of these entry tests (`cutRow`). So it moves the plan view; it does not prove it.

Limits. `wOf` is faithful to rows that a `cutOf` has made, and to no others: `unsparse` drops a
member whose number is out of order or out of range, in silence. No description is named but in
`planWord_of_cut`, where the rows are the written ones; that any description has these rows is not
said. Nothing on soundness.

Sources. The idea is public. Three small functions and one lemma here follow declarations of two
public libraries, each in the same steps; all four are small:




  `initOf`: `List.dropLast`; `lastOf`: `List.getLast`, with a default in the place of its proof, as
    `List.getLastD` has one (Lean 4's core library, toolchain v4.29.1,
    src/lean/Init/Data/List/Basic.lean, lines 1043, 304 and 341);
  `piecesBy`: `List.splitLengths` (Mathlib/Data/List/SplitLengths.lean, line 26);
  `init_last`: `List.dropLast_append_getLast` (Mathlib/Data/List/Basic.lean, lines 314 to 320).
What is theirs: the three routines' cases and steps, and of the lemma the statement's form, the
three cases with their bound names, and the first two cases' proofs. What differs here: the names;
`piecesBy` takes and drops where theirs splits; the third case of `init_last` is one rewriting.
Mathlib: at the commit that this library pins, 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
Licence of the text that is followed, from each package's own file LICENSE:
Lean's toolchain (71 lines; sha256
8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e): its first lines are "Apache
License 2.0 (Apache)", "Apache License", "Version 2.0, January 2004"; Mathlib (201 lines; sha256
b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1): "Apache License", "Version 2.0,
January 2004".
The three files' own headers, from the sources:
  src/lean/Init/Data/List/Basic.lean (2557 lines, sha256
  a949215c6d4cf4538c2748a620d1d86f5f55c60cada26711d8bc3d6aee8a5eb0):
    Copyright (c) 2016 Microsoft Corporation. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Author: Leonardo de Moura
  Mathlib/Data/List/SplitLengths.lean (107 lines, sha256
  9553272f51b29fa4b8ca542c1c288e98dabeed36cc0404b6125aaf75d3f5ed14):
    Copyright (c) 2024 Daniel Weber. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Daniel Weber
  Mathlib/Data/List/Basic.lean (1253 lines, sha256
  06575ba156e40e3bee2092e47aa94d98a3c9401172f98f45fa894bdddf4e8bea):
    Copyright (c) 2014 Parikshit Khanna. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.PlanAlike
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open VerifiableInference.PlanWritten (toldRounds cutOf cutIs cutIs_eq cutFirstFull cutSharedFull
  cutSecondFull)

variable {S Cl : Type}

/-! ### four small functions on lists -/

/-- A row of a cut: name · place · how many rounds · the length of oracles · the rounds that tell a
tree · before. -/
abbrev Row : Type := String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)

/-- A list of n lists, from its non-empty members with their numbers, which count from k. A member
whose number is out of order or out of range is dropped. -/
def unsparse {α : Type} : Nat → Nat → List (Nat × List α) → List (List α)
  | _, 0, _ => []
  | k, n + 1, [] => [] :: unsparse (k + 1) n []
  | k, n + 1, (i, x) :: t =>
    if i == k then x :: unsparse (k + 1) n t else [] :: unsparse (k + 1) n ((i, x) :: t)

/-- A list, cut into pieces of the given lengths. -/
def piecesBy {α : Type} : List Nat → List α → List (List α)
  | [], _ => []
  | n :: ns, l => l.take n :: piecesBy ns (l.drop n)

/-- All but the last. -/
def initOf {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | a :: b :: l => a :: initOf (b :: l)

/-- The last; d at the empty list. -/
def lastOf {α : Type} (d : α) : List α → α
  | [] => d
  | [a] => a
  | _ :: b :: l => lastOf d (b :: l)

/-! ### the written description -/

/-- The block that a row and its rounds spell. It decides nothing and states no claim. ITS OWN TEST
IS true. -/
def blockOfRow (r : Row) (rounds : List Fmt.DeclaredRound) : Block Unit Unit :=
  { name := r.1, place := r.2.1, planOk := true, rounds := rounds
    oracles := unsparse 0 r.2.2.2.1 r.2.2.2.2.1, before := r.2.2.2.2.2
    decide := fun _ _ _ => .ok (), claims := [], after := [] }

/-- The blocks that rows spell, their rounds cut out of one list by the rows' numbers of rounds. -/
def blocksOfRows (rows : List Row) (R : List Fmt.DeclaredRound) : List (Block Unit Unit) :=
  List.zipWith blockOfRow rows (piecesBy (rows.map (·.2.2.1)) R)

/-- A chain without links. Of two blocks or more its flat list is the given list, block by block,
each block's own test joined with `hasNoClaimsAndNothingAfter`. Of one block: that block twice. Of none: two quiet
blocks. -/
def chainOfBlocks : List (Block Unit Unit) → Chain Unit Unit
  | [] =>
    { first := roundlessBlock "" 0 none 0 fun s => .ok s, front := [], links := [], back := []
      last := roundlessBlock "" 0 none 0 fun s => .ok s }
  | a :: t => { first := a, front := initOf t, links := [], back := [], last := lastOf a t }

/-- **The written description**: of three lists of rows, three lists of declared rounds and a depth.
fileOk IS true; the plans ARE the rounds. It is never run. -/
def wOf (c₁ c₂ c₃ : List Row) (R : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (d : Nat) : FileDescription Unit :=
  { S₁ := Unit, S₂ := Unit, S₃ := Unit, Cl := Unit, plans := R, tableDepth := d, wanted := []
    owed := [], fileOk := true, okStart := fun _ => true, XiPub := Unit, pub := id, start₁ := id
    start₂ := id, start₃ := fun _ _ _ => .ok (), first := chainOfBlocks (blocksOfRows c₁ R.1)
    shared := chainOfBlocks (blocksOfRows c₂ R.2.1), second := chainOfBlocks (blocksOfRows c₃ R.2.2)
    fin := fun _ _ _ _ => true }

/-! ### a list of lists comes back from its length and its non-empty members -/

/-- The non-empty members of a list of lists, each with its number, which counts from k. -/
def sparseFrom {α : Type} (l : List (List α)) (k : Nat) : List (Nat × List α) :=
  ((l.zipIdx k).filter fun x => !x.1.isEmpty).map fun x => (x.2, x.1)

theorem sparse_ge {α : Type} : ∀ (l : List (List α)) (k : Nat) (p : Nat × List α),
    p ∈ sparseFrom l k → k ≤ p.1
  | [], _, _, h => by simp [sparseFrom] at h
  | a :: l, k, p, h => by
    unfold sparseFrom at h
    rw [List.zipIdx_cons] at h
    cases a with
    | nil =>
      rw [List.filter_cons_of_neg (by simp)] at h
      exact Nat.le_of_succ_le (sparse_ge l (k + 1) p h)
    | cons y a =>
      rw [List.filter_cons_of_pos (by simp), List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (sparse_ge l (k + 1) p h)

theorem unsparse_sparse {α : Type} : ∀ (l : List (List α)) (k : Nat),
    unsparse k l.length (sparseFrom l k) = l
  | [], _ => by simp [unsparse]
  | a :: l, k => by
    have ih := unsparse_sparse l (k + 1)
    have ge := sparse_ge l (k + 1)
    unfold sparseFrom
    rw [List.zipIdx_cons, List.length_cons]
    cases a with
    | nil =>
      rw [List.filter_cons_of_neg (by simp)]
      change unsparse k (l.length + 1) (sparseFrom l (k + 1)) = [] :: l
      cases hs : sparseFrom l (k + 1) with
      | nil =>
        rw [hs] at ih
        rw [unsparse, ih]
      | cons p t =>
        obtain ⟨i, x⟩ := p
        have hi : k + 1 ≤ i := ge (i, x) (by rw [hs]; simp)
        rw [hs] at ih
        rw [unsparse, if_neg (by rw [beq_iff_eq]; omega), ih]
    | cons y a =>
      rw [List.filter_cons_of_pos (by simp), List.map_cons]
      change unsparse k (l.length + 1) ((k, y :: a) :: sparseFrom l (k + 1)) = (y :: a) :: l
      rw [unsparse, if_pos (by simp), ih]

/-- A block's oracles come back from its row. -/
theorem unsparse_told (b : Block S Cl) : unsparse 0 b.oracles.length (toldRounds b) = b.oracles :=
  unsparse_sparse b.oracles 0

/-! ### a list cut by its pieces' lengths gives the pieces -/

theorem pieces_flat {α β : Type} (f : β → List α) : ∀ bs : List β,
    piecesBy (bs.map fun b => (f b).length) (bs.flatMap f) = bs.map f
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.flatMap_cons, piecesBy, List.take_left, List.drop_left,
      pieces_flat f bs]

/-! ### the chain's flat list -/

theorem init_last {α : Type} (d : α) : ∀ l : List α, l ≠ [] → initOf l ++ [lastOf d l] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | a :: b :: l, _ => by
    rw [initOf, lastOf, List.cons_append, init_last d (b :: l) (by simp)]

/-- A block, its own test joined with `hasNoClaimsAndNothingAfter`: what `Chain.blocksInOrder` lays outside the links. -/
def bareOf (b : Block S Cl) : Block S Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

theorem flat_of_blocks (a b : Block Unit Unit) (l : List (Block Unit Unit)) :
    (chainOfBlocks (a :: b :: l)).blocksInOrder = (a :: b :: l).map bareOf := by
  have e := init_last a (b :: l) (by simp)
  unfold chainOfBlocks Chain.blocksInOrder
  simp only [List.flatMap_nil, List.map_nil, List.append_nil]
  rw [List.map_cons]
  conv_rhs => rw [← e]
  rw [List.map_append, List.map_cons, List.map_nil, List.cons_append]
  rfl

/-- The like at every list of two blocks or more. -/
theorem flat_of_two : ∀ ws : List (Block Unit Unit), 2 ≤ ws.length →
    (chainOfBlocks ws).blocksInOrder = ws.map bareOf
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: b :: l, _ => flat_of_blocks a b l

/-- A chain's flat list has two blocks or more. -/
theorem flat_len (c : Chain S Cl) : 2 ≤ c.blocksInOrder.length := by
  unfold Chain.blocksInOrder
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ### the blocks that a list's own cut and rounds spell -/

theorem blocks_of_cut : ∀ bs : List (Block S Cl),
    blocksOfRows (cutOf bs) (bs.flatMap (·.rounds)) = bs.map fun b =>
      blockOfRow (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before)
        b.rounds := by
  intro bs
  unfold blocksOfRows cutOf
  rw [List.map_map]
  have e : piecesBy (bs.map ((fun r : Row => r.2.2.1) ∘ fun b =>
      (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before)))
      (bs.flatMap (·.rounds)) = bs.map (·.rounds) :=
    pieces_flat (fun b : Block S Cl => b.rounds) bs
  rw [e, List.zipWith_map_left, List.zipWith_map_right, List.zipWith_self]

theorem map_alike {β : Type} (g : β → Block Unit Unit) (f : β → Block S Cl) :
    ∀ bs : List β, (∀ b ∈ bs, Alike₂ (g b) (f b)) → List.Forall₂ Alike₂ (bs.map g) (bs.map f)
  | [], _ => .nil
  | b :: bs, h =>
    .cons (h b (by simp)) (map_alike g f bs fun c hc => h c (by simp [hc]))

/-- **The blocks that a list's own cut and rounds spell, laid as a chain, are alike to the
list.** -/
theorem chain_alike (bs : List (Block S Cl)) (h2 : 2 ≤ bs.length)
    (hB : ∀ b ∈ bs, b.planOk = true) :
    List.Forall₂ Alike₂ (chainOfBlocks (blocksOfRows (cutOf bs) (bs.flatMap (·.rounds)))).blocksInOrder
      bs := by
  rw [blocks_of_cut, flat_of_two _ (by rw [List.length_map]; exact h2), List.map_map]
  have k := map_alike (S := S) (Cl := Cl)
    (bareOf ∘ fun b : Block S Cl =>
      blockOfRow (b.name, b.place, b.rounds.length, b.oracles.length, toldRounds b, b.before)
        b.rounds) id bs
    (fun c hc => ⟨rfl, rfl, unsparse_told c, rfl, fun _ => hB c hc⟩)
  rw [List.map_id] at k
  exact k

/-! ### the joining -/

/-- **F is alike to the written description** where: its three cuts are the rows; its declared
rounds, its plans and its depth are the written ones; each of its blocks passes its own test; its
fileOk passes. -/
theorem planAlike_of_cut {Xi : Type} {F : FileDescription Xi} {c₁ c₂ c₃ : List Row}
    {R : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound} {d : Nat}
    (h₁ : cutOf F.first.blocksInOrder = c₁) (h₂ : cutOf F.shared.blocksInOrder = c₂) (h₃ : cutOf F.second.blocksInOrder = c₃)
    (hD : F.roundsDeclaredByBlocks = R) (hP : F.plans = R) (hd : F.tableDepth = d)
    (b₁ : ∀ b ∈ F.first.blocksInOrder, b.planOk = true) (b₂ : ∀ b ∈ F.shared.blocksInOrder, b.planOk = true)
    (b₃ : ∀ b ∈ F.second.blocksInOrder, b.planOk = true) (hF : F.fileOk = true) :
    PlanAlike (wOf c₁ c₂ c₃ R d) F := by
  subst h₁ h₂ h₃ hD
  exact ⟨fun _ => hF, hP.symm, hd.symm, chain_alike _ (flat_len _) b₁,
    chain_alike _ (flat_len _) b₂, chain_alike _ (flat_len _) b₃⟩

/-- **So the refusal's words on the plan are none**, at the proof file's written cut. -/
theorem planWord_of_cut {Xi : Type} {F : FileDescription Xi}
    {R : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound} {d : Nat}
    (hW : (wOf cutFirstFull cutSharedFull cutSecondFull R d).planOk = true) (hC : cutIs F = true)
    (hD : F.roundsDeclaredByBlocks = R) (hP : F.plans = R) (hd : F.tableDepth = d)
    (b₁ : ∀ b ∈ F.first.blocksInOrder, b.planOk = true) (b₂ : ∀ b ∈ F.shared.blocksInOrder, b.planOk = true)
    (b₃ : ∀ b ∈ F.second.blocksInOrder, b.planOk = true) (hF : F.fileOk = true) : F.planWord = none :=
  FileDescription.planWord_alike₂
    (planAlike_of_cut (cutIs_eq hC).1 (cutIs_eq hC).2.1 (cutIs_eq hC).2.2 hD hP hd b₁ b₂ b₃ hF) hW

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.sparse_ge
#print axioms P2Law.ProofPlan.unsparse_sparse
#print axioms P2Law.ProofPlan.unsparse_told
#print axioms P2Law.ProofPlan.pieces_flat
#print axioms P2Law.ProofPlan.init_last
#print axioms P2Law.ProofPlan.flat_of_blocks
#print axioms P2Law.ProofPlan.flat_of_two
#print axioms P2Law.ProofPlan.flat_len
#print axioms P2Law.ProofPlan.blocks_of_cut
#print axioms P2Law.ProofPlan.map_alike
#print axioms P2Law.ProofPlan.chain_alike
#print axioms P2Law.ProofPlan.planAlike_of_cut
#print axioms P2Law.ProofPlan.planWord_of_cut
