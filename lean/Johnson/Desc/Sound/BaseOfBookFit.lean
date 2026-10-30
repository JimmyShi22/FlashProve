-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/BaseOfBookFit.lean: THE TREES
THAT A FILE's DATA SEND IN FRONT OF BLOCK k ARE AS MANY AS THE TABLE OF JOINTS' NUMBER
Numbers.treesAt SAYS AT THAT BLOCK's PLACE. Statements with their proofs; no kind is named.
Why. A piece of the maker's row has the base nTrees (ds₁.take n), n the rounds that the blocks in
front declare (Desc.K14.Law.cutRow_at). A kind's tie speaks of the plan's number N.treesAt ps[k]?
("every open sampled tenant's tree is below the base"). This is the joint between the two: the row
N8 of K01_law; it serves every kind's like premise.
Letters: those of Johnson/Desc/Sound/StretchTags.lean: the data dataOf a R₁ R₂ R₃ of three lists of
written rounds; WrittenAs e (bs.flatMap (·.rounds)) R₁. N, ps: the table's numbers and places.
  toldBy bs        for each block, in order, the oracles beneath the roots that it sends: the list
                   that First.bookFit (Johnson/Desc/First/BookFit.lean) is meant for.
  data_trees       round by round the first chain's data send as many trees as the written round
                   has roots among its items, but for the last round (the seal).
  written_roots    the written rounds' entries count the roots that the declared rounds' entries
                   count.
  take_flat        the declared rounds in a row, cut in front of block k by the blocks' own counts.
  shaped_told      a block that passes Block.shaped tells as many oracles as its rounds' entries
                   count roots.
  nTrees_front     **the data's side**: nTrees (ds₁.take (roundsIn (bs.take k))) is what the first k
                   blocks tell.
  base_of_bookFit  **the joint**: so it is N.treesAt ps[k]?, where the test bookFit says yes.
  base_at_flat     the same at a chain's flat list, the rounds in front counted in plain text.
  bookFit_withTold the test has a member: Numbers.withTold, where each place stands once.
PREMISES THAT STAY. hW: the framework's own WrittenAs. hroots: each written round has as many roots
among its items as its entry counts (fits_roots, Johnson/Desc/Sound/ReadsOfData.lean, has it from
the maker's test Three.Whole.fits). hsh: every block passes Block.shaped (a clause of blocksOk,
Johnson/Desc/Block.lean). hfit: the test bookFit at N, ps and toldBy bs. hroom: a round is declared
at or behind block k.
What is not claimed. That bookFit says yes at the numbers of any filling of the table but
Numbers.withTold. Nothing on the second or the third
chain's data. Nothing on soundness.

-/
import Johnson.Desc.Sound.StretchTags
import Johnson.Desc.First.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes OnBytes.Maker OnBytes.Flat
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (Block Chain Place Oracle)
open VerifiableInference.Desc.K13.Law (tagD tagW written_tags length_flat roundsIn_cons)
open _root_.Desc.K14.Law (roundsIn)

variable {T Cl : Type}

/-- For each block, in order, the oracles beneath the roots that it sends, all rounds together. -/
def toldBy (bs : List (Block T Cl)) : List (List Oracle) := bs.map fun b => b.oracles.flatMap id

/-- **The first chain's data: how many trees a round sends.** -/
theorem data_trees (a : ℕ) (R₁ R₂ R₃ : Rounds) :
    (dataOf a R₁ R₂ R₃).ds₁.map (·.trees.length) =
      (R₁.map fun r => r.1.items.countP (· == .root)).dropLast := by
  show (((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast).map rdtOf).map (·.trees.length) = _
  rw [List.map_map, List.map_dropLast]
  exact congrArg List.dropLast (rdsFromL_map _ _ _ _ _ _ ((·.trees.length) ∘ rdtOf)
    (fun r => r.1.items.countP (· == .root)) (fun _ _ => by simp [rdtOf, Three.rdOf]) R₁)

/-- The written rounds' entries count the declared rounds' roots. -/
theorem written_roots {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : Rounds}
    (h : WrittenAs e l R) : R.map (·.1.entry.roots) = l.map (·.entry.roots) := by
  have h1 := congrArg (List.map fun t : K13.Law.Tag => t.1.roots) (written_tags h)
  rw [List.map_map, List.map_map] at h1
  exact h1

/-- The declared rounds in front of block k. -/
theorem take_flat : ∀ (bs : List (Block T Cl)) (k : ℕ),
    (bs.flatMap (·.rounds)).take (roundsIn (bs.take k)) = (bs.take k).flatMap (·.rounds)
  | [], k => by simp [roundsIn]
  | b :: l, 0 => by
    have h0 : roundsIn ((b :: l).take 0) = 0 := rfl
    rw [h0]
    rfl
  | b :: l, k + 1 => by
    rw [List.take_succ_cons, roundsIn_cons, List.flatMap_cons, List.flatMap_cons,
      List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      take_flat l k]

theorem zip_told : ∀ (rs : List Fmt.DeclaredRound) (os : List (List Oracle)),
    os.length = rs.length → (∀ x ∈ rs.zip os, x.2.length = x.1.entry.roots) →
    (os.flatMap id).length = (rs.map (·.entry.roots)).sum
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | r :: rs, o :: os, h, q => by
    have h1 := q (r, o) (by simp)
    have ih := zip_told rs os (by simpa using h) fun x hx => q x (by
      rw [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ hx)
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, ih]
    show o.length + _ = _
    rw [h1]

/-- A block that passes the test on its shape tells as many oracles as its entries count roots. -/
theorem shaped_told (b : Block T Cl) (h : b.shaped = true) :
    (b.oracles.flatMap id).length = (b.rounds.map (·.entry.roots)).sum := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine zip_told b.rounds b.oracles h.1 fun x hx => ?_
  have h2 := h.2 x hx
  rw [Bool.and_eq_true, beq_iff_eq] at h2
  exact h2.1

theorem sum_flat : ∀ bs : List (Block T Cl),
    ((bs.flatMap (·.rounds)).map (·.entry.roots)).sum =
      (bs.map fun b => (b.rounds.map (·.entry.roots)).sum).sum
  | [] => rfl
  | b :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_flat l]

/-- **THE DATA's SIDE.** -/
theorem nTrees_front (a : ℕ) (R₁ R₂ R₃ : Rounds) {e : List (List ByteArray × ByteArray)}
    (bs : List (Block T Cl)) (hW : WrittenAs e (bs.flatMap (·.rounds)) R₁)
    (hroots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hsh : ∀ b ∈ bs, b.shaped = true) (k : ℕ) (hroom : roundsIn (bs.take k) < roundsIn bs) :
    nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (roundsIn (bs.take k))) =
      First.treesTold (toldBy bs) k := by
  have e1 : (R₁.map fun r => r.1.items.countP (· == .root)) = R₁.map (·.1.entry.roots) :=
    List.map_congr_left hroots
  unfold nTrees First.treesTold toldBy
  rw [List.map_take, data_trees, e1, written_roots hW, List.dropLast_eq_take, List.take_take,
    List.length_map, length_flat, Nat.min_eq_left (by omega), ← List.map_take, take_flat, sum_flat,
    ← List.map_take, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  exact (shaped_told b (hsh b (List.mem_of_mem_take hb))).symm

/-- **THE JOINT.** -/
theorem base_of_bookFit (a : ℕ) (R₁ R₂ R₃ : Rounds) {e : List (List ByteArray × ByteArray)}
    (bs : List (Block T Cl)) (hW : WrittenAs e (bs.flatMap (·.rounds)) R₁)
    (hroots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hsh : ∀ b ∈ bs, b.shaped = true) (N : First.Numbers) (ps : List Place)
    (hfit : First.bookFit N ps (toldBy bs) = true) (k : ℕ) (hk : k ≤ ps.length)
    (hroom : roundsIn (bs.take k) < roundsIn bs) :
    nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (roundsIn (bs.take k))) = N.treesAt ps[k]? := by
  rw [nTrees_front a R₁ R₂ R₃ bs hW hroots hsh k hroom,
    (First.bookFit_at N ps (toldBy bs) hfit k hk).1]

/-- The joint at a chain's flat list, the rounds in front counted in plain text. -/
theorem base_at_flat {S : Type} (a : ℕ) (R₁ R₂ R₃ : Rounds)
    {e : List (List ByteArray × ByteArray)} (c : Chain S Cl)
    (hW : WrittenAs e (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hroots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hsh : ∀ b ∈ c.blocksInOrder, b.shaped = true) (N : First.Numbers) (ps : List Place)
    (hfit : First.bookFit N ps (toldBy c.blocksInOrder) = true) (k : ℕ) (hk : k ≤ ps.length)
    (hroom : roundsIn (c.blocksInOrder.take k) < roundsIn c.blocksInOrder) :
    nTrees ((dataOf a R₁ R₂ R₃).ds₁.take ((c.blocksInOrder.take k).map (·.rounds.length)).sum) =
      N.treesAt ps[k]? :=
  base_of_bookFit a R₁ R₂ R₃ c.blocksInOrder hW hroots hsh N ps hfit k hk hroom

/-- **The test has a member**: the numbers filled off what the blocks tell
(Johnson/Desc/First/BookNumbers.lean) pass it, where each place stands once in the list. -/
theorem bookFit_withTold (N : First.Numbers) (ps : List Place) (told : List (List Oracle))
    (hnd : ps.Nodup) : First.bookFit (N.withTold ps told) ps told = true := by
  unfold First.bookFit
  rw [List.all_eq_true]
  intro k hk
  have hk' : k ≤ ps.length := Nat.le_of_lt_succ (List.mem_range.1 hk)
  have hb : First.borderOf ps ps[k]? = k := by
    rcases Nat.lt_or_eq_of_le hk' with h | h
    · rw [List.getElem?_eq_getElem h]
      show ps.idxOf ps[k] = k
      exact hnd.idxOf_getElem k h
    · subst h
      rw [List.getElem?_eq_none (Nat.le_refl _)]
      rfl
  show (First.treesTold told (First.borderOf ps ps[k]?) == First.treesTold told k &&
    First.msgsTold told (First.borderOf ps ps[k]?) == First.msgsTold told k) = true
  rw [hb]
  simp

end VerifiableInference.Desc.Sound
