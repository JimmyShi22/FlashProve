-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreeInFront.lean: at a description that passes the library's tests
on the plan (`FileDescription.planOk`, Johnson/Desc/Block.lean), and at a block of its shared chain's flat
list: how many trees the chain states in front of the block, counted in three ways; that the block's
first stated oracle message is told under that number; that the list can be cut at the block's place
in one way alone; and so, where that first message has a tenant that is not sampled and the block
itself opens its tree, a bound on the frame's list of the positions read of it. General in the
description. Counting lemmas on public data. It imports Mathlib.

  `planOk_book`, `planOk_places`, `planOk_shaped`   three of the tests, out of `planOk`
  `rows_len`, `rows_sum`, `told_len`   over shaped blocks: `rowsOfChain`
                 (Johnson/Desc/ProofFile/Honest/Law/StratWords.lean) has as many rows as the blocks
                 have rounds; its rows' oracle messages are as many as `oraclesOf` lists; and these
                 as many as the rounds' entries count roots
  `trees_in_front`   the number in the frame's letters: the oracle messages of the rows in front of
                 a block are as many as the roots that the rounds in front send
  `told_at`      the block's first stated message is `oraclesOf`'s member of that number
  `cut_unique`, `cut_at_place`   a list in which a value is taken once can be cut at it in one way;
                 so the shared list at a block's place, by `placesOk`
  `openedOf_append`, `opened_mem`   a block's openings are among the file's
  `asks_at_block`   the bound

Limits. The shared chain alone. "At most": nothing says that a position is read. Nothing on
completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ReadsOfTree
import Johnson.Desc.ProofFile.Honest.Law.StratWords
import Johnson.Desc.Sound.BaseOfBookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block Place Oracle oraclesOf blocksOk)
open VerifiableInference.Desc.Sound (shaped_told sum_flat)
open Johnson.G.OfPlan (rootsOf)

variable {Xi S Cl : Type}

/-! ## 1 Three tests out of `planOk` -/

theorem planOk_book {F : FileDescription Xi} (h : F.planOk = true) : F.treeSharingOk = true := by
  cases hb : F.treeSharingOk with
  | true => rfl
  | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h

theorem planOk_places {F : FileDescription Xi} (h : F.planOk = true) : F.placesOk = true := by
  cases hb : F.placesOk with
  | true => rfl
  | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h

theorem planOk_shaped {F : FileDescription Xi} (h : F.planOk = true) :
    ∀ b ∈ F.shared.blocksInOrder, b.shaped = true := by
  have hb : blocksOk F.shared.blocksInOrder = true := by
    cases hb : blocksOk F.shared.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  intro b hm
  have := List.all_eq_true.1 hb b hm
  rw [Bool.and_eq_true] at this
  exact this.2

/-! ## 2 Counting over shaped blocks -/

theorem shaped_len (b : Block S Cl) (h : b.shaped = true) : b.oracles.length = b.rounds.length := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem rows_len : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    (rowsOfChain bs).length = (bs.flatMap (·.rounds)).length
  | [], _ => rfl
  | b :: bs, h => by
    have ih := rows_len bs fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold rowsOfChain at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append, ih,
      List.length_zip, shaped_len b (h b List.mem_cons_self), Nat.min_self]

theorem sum_lengths {α : Type} : ∀ l : List (List α), (l.map (·.length)).sum = (l.flatMap id).length
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, sum_lengths l]
    rfl

theorem rows_sum : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    ((rowsOfChain bs).map (·.2.length)).sum = (oraclesOf bs).length
  | [], _ => rfl
  | b :: bs, h => by
    have ih := rows_sum bs fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hz : (b.rounds.zip b.oracles).map (·.2) = b.oracles :=
      List.map_snd_zip (Nat.le_of_eq (shaped_len b (h b List.mem_cons_self)))
    have h1 : ((b.rounds.zip b.oracles).map (·.2.length)).sum = (b.oracles.flatMap id).length := by
      rw [← sum_lengths, ← hz, List.map_map, hz]
      rfl
    unfold rowsOfChain oraclesOf at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.sum_append,
      List.length_append, ih, h1]

theorem told_len : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    (oraclesOf bs).length = rootsOf (bs.flatMap (·.rounds))
  | [], _ => rfl
  | b :: bs, h => by
    have ih := told_len bs fun x hx => h x (List.mem_cons_of_mem _ hx)
    unfold oraclesOf rootsOf at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.map_append,
      List.sum_append, ih, shaped_told b (h b List.mem_cons_self)]

/-- **The number in the frame's letters.** -/
theorem trees_in_front (pre t : List (Block S Cl)) (b : Block S Cl)
    (h : ∀ x ∈ pre, x.shaped = true) :
    (((rowsOfChain (pre ++ b :: t)).take (pre.flatMap (·.rounds)).length).map
      (·.2.length)).sum = rootsOf (pre.flatMap (·.rounds)) := by
  have e : rowsOfChain (pre ++ b :: t) = rowsOfChain pre ++ rowsOfChain (b :: t) := by
    unfold rowsOfChain
    rw [List.flatMap_append]
  rw [e, ← rows_len pre h, List.take_left', rows_sum pre h, told_len pre h]
  rfl

/-- **The block's first stated message is told under that number.** -/
theorem told_at (pre t : List (Block S Cl)) (b : Block S Cl) (h : ∀ x ∈ pre, x.shaped = true)
    (X : Oracle) (rest : List Oracle) (hX : b.oracles.flatMap id = X :: rest) :
    (oraclesOf (pre ++ b :: t))[rootsOf (pre.flatMap (·.rounds))]? = some X := by
  have e : oraclesOf (pre ++ b :: t) = oraclesOf pre ++ (X :: (rest ++ oraclesOf t)) := by
    unfold oraclesOf
    rw [List.flatMap_append, List.flatMap_cons, hX]
    rfl
  rw [e, ← told_len pre h, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-! ## 3 One cut -/

theorem cut_unique {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) (v : β) :
    ∀ (p p' : List α) (b b' : α) (t t' : List α), p ++ b :: t = p' ++ b' :: t' → f b = v →
      f b' = v → ((p ++ b :: t).map f).count v ≤ 1 → p = p'
  | [], [], _, _, _, _, _, _, _, _ => rfl
  | [], y :: p', b, b', t, t', e, hb, hb', hc => by
    exfalso
    rw [e] at hc
    obtain ⟨rfl, -⟩ := List.cons.inj e
    simp only [List.cons_append, List.map_cons, List.map_append, List.count_cons,
      List.count_append, hb, hb', beq_self_eq_true, if_true] at hc
    omega
  | x :: p, [], b, b', t, t', e, hb, hb', hc => by
    exfalso
    obtain ⟨rfl, -⟩ := List.cons.inj e
    simp only [List.cons_append, List.map_cons, List.map_append, List.count_cons,
      List.count_append, hb, hb', beq_self_eq_true, if_true] at hc
    omega
  | x :: p, y :: p', b, b', t, t', e, hb, hb', hc => by
    obtain ⟨rfl, e'⟩ := List.cons.inj e
    rw [cut_unique f v p p' b b' t t' e' hb hb' ?_]
    refine Nat.le_trans ?_ hc
    rw [List.cons_append, List.map_cons, List.count_cons]
    exact Nat.le_add_right _ _

/-- **The shared list can be cut at a block's place in one way.** -/
theorem cut_at_place {F : FileDescription Xi} (h : F.planOk = true) (p p' t t' : List (Block F.S₂ F.Cl))
    (b b' : Block F.S₂ F.Cl) (e : F.shared.blocksInOrder = p ++ b :: t) (e' : F.shared.blocksInOrder = p' ++ b' :: t')
    (hp : b.place = b'.place) : p = p' := by
  have hq := planOk_places h
  unfold FileDescription.placesOk at hq
  simp only [Bool.and_eq_true] at hq
  have hall := List.all_eq_true.1 hq.2
  refine cut_unique (fun x : Block F.S₂ F.Cl => (x.place.chain, x.place.link, x.place.piece))
    (b.place.chain, b.place.link, b.place.piece) p p' b b' t t' (e.symm.trans e') rfl
    (by rw [hp]) ?_
  rw [← e]
  have hm : (b.place.chain, b.place.link, b.place.piece) ∈
      F.places.map fun q => (q.2.1.chain, q.2.1.link, q.2.1.piece) := by
    refine List.mem_map.2 ⟨(b.name, b.place, b.rounds.length), ?_, rfl⟩
    unfold FileDescription.places
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    refine List.mem_map.2 ⟨b, ?_, rfl⟩
    rw [e]
    exact List.mem_append_right _ List.mem_cons_self
  have h1 := beq_iff_eq.1 (hall _ hm)
  refine Nat.le_trans ?_ (Nat.le_of_eq h1)
  unfold FileDescription.places VerifiableInference.Desc.placesOf
  rw [List.map_append, List.map_append, List.count_append, List.count_append]
  simp only [List.map_map]
  have hle : ∀ x y z : ℕ, y ≤ x + y + z := fun x y z => by omega
  have e2 : F.shared.blocksInOrder.map (fun x => (x.place.chain, x.place.link, x.place.piece)) =
      F.shared.blocksInOrder.map ((fun q : String × Place × ℕ => (q.2.1.chain, q.2.1.link, q.2.1.piece)) ∘
                 fun x => (x.name, x.place, x.rounds.length)) := rfl
  rw [e2]
  exact hle _ _ _

/-! ## 4 The bound -/

theorem openedOf_append (c : ℕ) (a b : List Fmt.DeclaredRound) :
    openedOf c (a ++ b) = openedOf c a ++ openedOf c b := by
  unfold openedOf
  rw [List.flatMap_append]

theorem opened_mem {F : FileDescription Xi} (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl)
    (e : F.shared.blocksInOrder = pre ++ b :: t) (x : (ℕ × ℕ) × ℕ × ℕ) (hx : x ∈ openedOf 1 b.rounds) :
    x ∈ openedAll F.roundsDeclaredByBlocks := by
  unfold openedAll
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  show x ∈ openedOf 1 (F.shared.blocksInOrder.flatMap (·.rounds))
  rw [e, List.flatMap_append, List.flatMap_cons, openedOf_append, openedOf_append]
  exact List.mem_append_right _ (List.mem_append_left _ hx)

/-- **Where a block's first stated message has a tenant that is not sampled, and the block itself
opens that tree in a round that samples P positions, at the depth a.** -/
theorem asks_at_block {F : FileDescription Xi} (h : F.planOk = true) (pre t : List (Block F.S₂ F.Cl))
    (b : Block F.S₂ F.Cl) (e : F.shared.blocksInOrder = pre ++ b :: t) (X : Oracle) (rest : List Oracle)
    (hX : b.oracles.flatMap id = X :: rest) (hs : X.tenants.all (·.sampled) = false) (P a : ℕ)
    (he : ((1, rootsOf (pre.flatMap (·.rounds))), P, a) ∈ openedOf 1 b.rounds) (ρ : Draws)
    (hρ : ρ.due F = true) :
    (treeAsks F ρ 1 (rootsOf (pre.flatMap (·.rounds)))).length ≤ P ∧
      ∀ x ∈ treeAsks F ρ 1 (rootsOf (pre.flatMap (·.rounds))), x < 2 ^ a := by
  have hsh : ∀ x ∈ pre, x.shaped = true := fun x hx =>
    planOk_shaped h x (by rw [e]; exact List.mem_append_left _ hx)
  refine asks_of_one F (planOk_book h) ρ hρ 1 _ P a X ?_ hs (opened_mem pre t b e _ he)
  show (some (oraclesOf F.shared.blocksInOrder)).bind (·[rootsOf (pre.flatMap (·.rounds))]?) = some X
  rw [e]
  exact told_at pre t b hsh X rest hX

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.planOk_book
#print axioms ProofFile.Honest.K12.Light.planOk_places
#print axioms ProofFile.Honest.K12.Light.planOk_shaped
#print axioms ProofFile.Honest.K12.Light.shaped_len
#print axioms ProofFile.Honest.K12.Light.rows_len
#print axioms ProofFile.Honest.K12.Light.sum_lengths
#print axioms ProofFile.Honest.K12.Light.rows_sum
#print axioms ProofFile.Honest.K12.Light.told_len
#print axioms ProofFile.Honest.K12.Light.trees_in_front
#print axioms ProofFile.Honest.K12.Light.told_at
#print axioms ProofFile.Honest.K12.Light.cut_unique
#print axioms ProofFile.Honest.K12.Light.cut_at_place
#print axioms ProofFile.Honest.K12.Light.openedOf_append
#print axioms ProofFile.Honest.K12.Light.opened_mem
#print axioms ProofFile.Honest.K12.Light.asks_at_block
