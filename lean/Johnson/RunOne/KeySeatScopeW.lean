-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatScopeW.lean: THEOREMS. **The trees that the first n blocks of a description tell are the trees of the data's first ‹rounds in front› rounds** (general in the description); and that count at the key file's written data, by the kernel.
OBJECT: oraclesOf (F.first.blocksInOrder.take n) · Johnson.G.writtenKFull. USER: Johnson/RunOne/KeySeatScopeW2.lean (the key file's third sampled message's seat); meant too for the ranges' test's «free».
THE ROAD. What a shaped block tells is, round by round, as many trees as the round's entry has roots (the description's own test on the plan) · the first n blocks' rounds are the declared rounds' first ‹rounds in front› (a list fact in another file, Johnson/RunOne/Law/RoundsInFront.lean) · the declared rounds' roots are the data's trees (roundsOfData, Johnson/Desc/Sound/DataRounds.lean) · at the written data the count is a numeral, by the kernel.
  told_len | told_eq_roots   what shaped blocks tell, counted by the rounds' roots
  roots_data                 the declared rounds' roots against the data's trees
  roots_in_front | told_in_front   **the first n blocks of any description**
  len_written | one_written | five_written | six_written | two_written   by the kernel: 18850 rounds; 1 tree in the first 2, 5 in the first 18848, 6 in 18849 (the border bites), 2 in 18805
THE KEY FILE's OWN PART (the first chain's tail; the third seat; the three seats' trees) stands in Johnson/RunOne/KeySeatScopeW2.lean.
What is not claimed. That any description's data are the written data. Anything on what is sent. Nothing on soundness.

-/
import Johnson.RunOne.KeySeatScope
import Johnson.Desc.Sound.DataRounds
import Johnson.RunOne.Law.RoundsInFront

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Sound (nTrees)
open Johnson.RunOne.Law.RoundsInFront (inFront decl₁_take)
open Johnson.Top.H (csKey)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq sum_eq_sumE)
open Lk6.AtPlan (keyFull)

section general
variable {S Cl : Type}

/-- Lists of lists whose lengths are given, one for one. -/
theorem flat_len_of {α β : Type} (f : α → ℕ) : ∀ (rs : List α) (os : List (List β)), os.length = rs.length →
    (∀ x ∈ rs.zip os, x.2.length = f x.1) → (os.flatMap id).length = (rs.map f).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, o :: os, h, H => by
    have h' : os.length = rs.length := by simpa using h
    have e := flat_len_of f rs os h' fun x hx => H x (List.mem_cons_of_mem _ hx)
    have e0 : o.length = f r := H (r, o) (List.mem_cons_self ..)
    simp only [List.flatMap_cons, id, List.length_append, List.map_cons, List.sum_cons, e, e0]

/-- What a shaped block tells, counted by its rounds' roots. -/
theorem told_len (b : Block S Cl) (h : b.shaped = true) : (b.oracles.flatMap id).length = (b.rounds.map (·.entry.roots)).sum := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true] at h
  refine flat_len_of (·.entry.roots) b.rounds b.oracles (by simpa using h.1) fun x hx => ?_
  have := List.all_eq_true.1 h.2 x hx
  rw [Bool.and_eq_true] at this
  simpa using this.1

/-- What a list of shaped blocks tells. -/
theorem told_eq_roots : ∀ (bs : List (Block S Cl)), blocksOk bs = true →
    (oraclesOf bs).length = ((bs.flatMap (·.rounds)).map (·.entry.roots)).sum
  | [], _ => rfl
  | b :: bs, h => by
    unfold blocksOk at h
    rw [List.all_cons, Bool.and_eq_true, Bool.and_eq_true] at h
    have e := told_eq_roots bs h.2
    unfold oraclesOf at e ⊢
    simp only [List.flatMap_cons, List.length_append, List.map_append, List.sum_append, e, told_len b h.1.2]

theorem blocksOk_take (bs : List (Block S Cl)) (n : ℕ) (h : blocksOk bs = true) : blocksOk (bs.take n) = true := by
  unfold blocksOk at h ⊢
  exact List.all_eq_true.2 fun b hb => List.all_eq_true.1 h b (List.mem_of_mem_take hb)

end general

/-- Round by round the same number: so the sums over the first k. -/
theorem sum_take_of {α β : Type} (f : α → ℕ) (g : β → ℕ) : ∀ (l : List α) (m : List β), List.Forall₂ (fun a b => f a = g b) l m →
    ∀ k, ((m.take k).map g).sum = ((l.take k).map f).sum
  | _, _, .nil, k => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, h, sum_take_of f g _ _ t k]

/-- **The declared rounds' roots against the data's trees.** -/
theorem roots_data {XI : Type} (F : FileDescription XI) (file : String) (D : WholeD) (h : F.data file = .ok D) (k : ℕ) (hk : k ≤ D.ds₁.length) :
    ((F.roundsDeclaredByBlocks.1.take k).map (·.entry.roots)).sum = nTrees (D.ds₁.take k) := by
  have H := (roundsOfData F file D h).1
  have hl : D.ds₁.length = F.roundsDeclaredByBlocks.1.dropLast.length := H.length_eq
  have e : F.roundsDeclaredByBlocks.1.take k = F.roundsDeclaredByBlocks.1.dropLast.take k := by
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left]
    rw [List.length_dropLast] at hl
    omega
  rw [e]
  exact sum_take_of (·.trees.length) (·.entry.roots) _ _ (H.imp fun _ _ x => x.2.2.2.1) k

/-- The roots of the rounds that the first n blocks declare. -/
theorem roots_in_front {XI : Type} (F : FileDescription XI) (file : String) (D : WholeD) (h : F.data file = .ok D) (n : ℕ)
    (hk : inFront F.first.blocksInOrder n ≤ D.ds₁.length) :
    (((F.first.blocksInOrder.take n).flatMap (·.rounds)).map (·.entry.roots)).sum = nTrees (D.ds₁.take (inFront F.first.blocksInOrder n)) := by
  rw [decl₁_take]
  exact roots_data F file D h _ hk

/-- **The trees that the first n blocks tell are the trees of the data's first ‹rounds in front› rounds.** -/
theorem told_in_front {XI : Type} (F : FileDescription XI) (file : String) (D : WholeD) (hp : F.planOk = true) (h : F.data file = .ok D) (n : ℕ)
    (hk : inFront F.first.blocksInOrder n ≤ D.ds₁.length) :
    (oraclesOf (F.first.blocksInOrder.take n)).length = nTrees (D.ds₁.take (inFront F.first.blocksInOrder n)) := by
  have hb : blocksOk F.first.blocksInOrder = true := by
    unfold FileDescription.planOk FileDescription.planOkCore at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  rw [told_eq_roots _ (blocksOk_take _ n hb)]
  exact roots_in_front F file D h n hk

/-! ## At the written data, by the kernel -/

theorem len_written : writtenKFull.ds₁.length = 18850 := by
  rw [writtenKFull_eq]
  exact Johnson.G.length_of_lenE Johnson.G.len_keyFull.1

set_option maxRecDepth 1000000 in
theorem five_d : nTrees (dKeyFull.ds₁.take 18848) = 5 := by
  show ((dKeyFull.ds₁.take 18848).map (·.trees.length)).sum = 5
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem six_d : nTrees (dKeyFull.ds₁.take 18849) = 6 := by
  show ((dKeyFull.ds₁.take 18849).map (·.trees.length)).sum = 6
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem two_d : nTrees (dKeyFull.ds₁.take 18805) = 2 := by
  show ((dKeyFull.ds₁.take 18805).map (·.trees.length)).sum = 2
  rw [sum_eq_sumE]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem one_d : nTrees (dKeyFull.ds₁.take 2) = 1 := by
  show ((dKeyFull.ds₁.take 2).map (·.trees.length)).sum = 1
  rw [sum_eq_sumE]
  decide +kernel

theorem one_written : nTrees (writtenKFull.ds₁.take 2) = 1 := by rw [writtenKFull_eq]; exact one_d
theorem five_written : nTrees (writtenKFull.ds₁.take 18848) = 5 := by rw [writtenKFull_eq]; exact five_d
theorem six_written : nTrees (writtenKFull.ds₁.take 18849) = 6 := by rw [writtenKFull_eq]; exact six_d
theorem two_written : nTrees (writtenKFull.ds₁.take 18805) = 2 := by rw [writtenKFull_eq]; exact two_d

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.told_len
#print axioms Johnson.RunOne.KeyLetters.told_eq_roots
#print axioms Johnson.RunOne.KeyLetters.roots_data
#print axioms Johnson.RunOne.KeyLetters.roots_in_front
#print axioms Johnson.RunOne.KeyLetters.told_in_front
#print axioms Johnson.RunOne.KeyLetters.len_written
#print axioms Johnson.RunOne.KeyLetters.one_written
#print axioms Johnson.RunOne.KeyLetters.five_written
#print axioms Johnson.RunOne.KeyLetters.six_written
#print axioms Johnson.RunOne.KeyLetters.two_written
