-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/WalkTieProofs.lean: the format page's walk through a Merkle opening is, under the hypotheses
below, the library's pruned walk: theorems.

The format page (docs/format/FORMAT.md, which comes with the programs, the C++ implementation that
comes with this Lean code) says in its section 7 how a reader walks from opened leaves and given
digests to a root; Fmt/Rules7.lean renders it. The library's pruned walk is in Hash/Octopus.lean.
This file holds definitions, statements as theorems, and proofs. They hold for every list of
numbers, every inhabited type of digests (`[Inhabited D]`) and every vertex function
hN : D → D → D. The tests at the page's own cases are in Run/WalkTie.lean.

A pruned walk recomputes the root of a Merkle tree from several opened leaves and one shared list
of sibling digests, level by level. In Hash/Octopus.lean js is the list of the vertices' numbers on
a level, v the list of their values, and s the list of given digests, called the message; `up js`
is the list of the parents' numbers, `upN d js` the numbers after d levels, `need1 js` and
`need d js` the numbers of digests that one level and d levels take from the message.

All is stated at the monad Id, that is, for hashes that are functions. In a general monad one
cannot say of a level's result that it has as many values as there are parents, which the next
level needs. A text over a monad is carried to Id by a morphism of monads: that is other files'
matter (Run/Hom.lean, Run/HomFmt.lean).

1. What the file contains (definitions).
   `sibs1 d js`, `sibs d js`: the vertices whose values one level, and d levels, take from the
     message, as (depth, place), in the walk's order. Written after Octopus's own case distinction.
     That is the case distinction of `need1` and `stepC` in Hash/Octopus.lean.
   `leafV`: the reader's own hash calls on an opening's columns and salts.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems.
   `length_stepF`, `length_octF`: the library's walk at a function (`stepF`, `octF`:
     Hash/OctopusFacts.lean): lengths. One level gives as many values as `up js` has numbers; d
     levels, if there are as many values as numbers, as many as `upN d js` has.
   `level_id`: one level. If there are as many values as numbers and the message has at least need1
     js digests, `Fmt.walkLevelW`, taking given values by `Fmt.takeGiven`, on (numbers with values)
     gives the parents' numbers (`Octopus.up`) with the values of `Octopus.stepC`, and leaves the
     message without its first need1 js digests. Auxiliary: `note1`, `lone_id`.
   `walk_id`: d levels. If there are as many values as numbers, the d levels bring js to one vertex
     and the message has at least need d js digests, `Fmt.walkW` ends in the one value of
     `Octopus.octC`, and leaves the message without its first need d js digests.
   `places_eq`, `places_length`: if a levels bring xs to one vertex, Fmt.walkPlaces a xs =
     sibs a xs; it has Octopus.need a xs members.
   `need_le_mul`: need d js ≤ d · |js|.
   `listOK_spec`, `listOK_one`: a list that `Fmt.listOK` accepts is not empty, strictly increasing
     and below 2^a; a levels bring it to one vertex.
   `reader_id`: the reader. Whatever the hash function h and the vertices' start cfg: if
     `Fmt.readOpeningW` at Id returns o, then o has one column and one salt for each position and
     exactly need a xs given digests, and o.root is the one value in which `Octopus.octC` ends at
     hN l r := h 166 0 0 cfg (l ++ r), on the leaves' digests (`leafV` on o.cols, o.salts) and
     o.given.

Notation:
  `h 166 0 0 cfg (l ++ r)`: the hash h at number, tree, index, start, bytes (`Fmt.vertexW`,
    Fmt/Rules7.lean);
  `166`: the number under which the format hashes an inner vertex (`Fmt.vertexW`);
  `a`: the tree's depth (`sh.a`, `Fmt.Shape`, Fmt/Plan.lean);
  `xs`: the list of opened positions (`Fmt.readOpeningW`);
  `o`: an `Fmt.OpenOut`, what the reader of an opening hands on;
  `met`: the vertices passed so far, as depth, place, value (`Fmt.walkW`);
  `verifyOneProtocol`: the compiled verifier of one slot (Compile/Batch/Verifier.lean).

4. What is not claimed.
   Nothing on the order or number of hash calls. Nothing on o.seen. Nothing on leaves beyond "the
   reader hashes them itself". Nothing on `verifyOneProtocol`.
   Where the message is too short, Octopus reads it as if it were filled up and the page's walk
   refuses: no statement is made on that case.

Sources. Section 7 of the format page, rules R7.6 to R7.10 on the walk; this file has not been held
against the page as it ships, and may differ from it.

-/
import Fmt.Rules7
import Hash.OctopusFacts

namespace Run.WalkTie
open Octopus

/-- the vertices whose values one level takes from the message, as (depth, place), in the walk's
order -/
def sibs1 (d : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | [i] => [(d, sibOf i)]
  | i :: j :: l => if sib i j then sibs1 d l else (d, sibOf i) :: sibs1 d (j :: l)

/-- the same for d levels: from depth d up to depth 1 -/
def sibs : ℕ → List ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | d + 1, js => sibs1 (d + 1) js ++ sibs d (up js)

theorem length_sibs1 (d : ℕ) : ∀ js : List ℕ, (sibs1 d js).length = need1 js
  | [] => rfl
  | [_] => rfl
  | i :: j :: l => by
    unfold sibs1 need1
    split
    · exact length_sibs1 d l
    · simp [length_sibs1 d (j :: l), Nat.add_comm]

theorem length_sibs : ∀ (d : ℕ) (js : List ℕ), (sibs d js).length = need d js
  | 0, _ => rfl
  | d + 1, js => by simp [sibs, need, length_sibs1, length_sibs d]

section
variable {D : Type} [Inhabited D] (hN : D → D → D)

theorem length_stepF : ∀ (js : List ℕ) (v s : List D), (stepF hN js v s).length = (up js).length
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | i :: j :: l, v, s => by
    unfold stepF stepC up
    split
    · exact congrArg (· + 1) (length_stepF l v.tail.tail s)
    · exact congrArg (· + 1) (length_stepF (j :: l) v.tail s.tail)

/-- what one level notes of the message: for which vertex each digest stands -/
def note1 (d : ℕ) : List ℕ → List D → List (ℕ × ℕ × D)
  | [], _ => []
  | [i], s => [(d, sibOf i, s.headD default)]
  | i :: j :: l, s =>
    if sib i j then note1 d l s else (d, sibOf i, s.headD default) :: note1 d (j :: l) s.tail

omit [Inhabited D] in
theorem lone_id (d i : ℕ) (a x : D) (g : List D) (acc : List (ℕ × ℕ × D)) :
    Fmt.walkLoneW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d i a (x :: g, acc) =
      some ((i / 2, loneF hN i a x), (g, (d, sibOf i, x) :: acc)) := by
  unfold Fmt.walkLoneW Fmt.takeGiven loneF sibOf
  by_cases h : i % 2 = 0 <;> simp [h] <;> rfl

/-- One level (in words: the head, `level_id`). -/
theorem level_id (d : ℕ) :
    ∀ (js : List ℕ) (v s : List D) (acc : List (ℕ × ℕ × D)), v.length = js.length →
      need1 js ≤ s.length →
      Fmt.walkLevelW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d (js.zip v) (s, acc) =
        some ((up js).zip (stepF hN js v s), (s.drop (need1 js), (note1 d js s).reverse ++ acc))
  | [], v, s, acc, _, _ => by simp [Fmt.walkLevelW, up, need1, note1]; rfl
  | [i], [a], x :: g, acc, _, _ => by
    simp only [List.zip_cons_cons, List.zip_nil_right, Fmt.walkLevelW]
    show Option.map _
        (Fmt.walkLoneW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d i a (x :: g, acc)) = _
    rw [lone_id]
    rfl
  | i :: j :: l, a :: b :: v, s, acc, hv, hs => by
    have hv' : v.length = l.length := by simpa using hv
    by_cases h : sib i j
    · have hs' : need1 l ≤ s.length := by
        have e : need1 (i :: j :: l) = need1 l := by rw [need1, if_pos h]
        exact e ▸ hs
      have hc : (i % 2 == 0 && j == i + 1) = true := by simp [h.1, h.2]
      simp only [List.zip_cons_cons, Fmt.walkLevelW, hc, if_true]
      show Option.map _
          (Fmt.walkLevelW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d (l.zip v) (s, acc)) = _
      rw [level_id d l v s acc hv' hs']
      simp only [up, need1, note1, stepF, stepC, if_pos h]
      rfl
    · have hn : need1 (i :: j :: l) = 1 + need1 (j :: l) := by rw [need1, if_neg h]
      obtain ⟨x, g, rfl⟩ : ∃ x g, s = x :: g := by
        cases s with
        | nil => simp [hn] at hs
        | cons x g => exact ⟨x, g, rfl⟩
      have hs' : need1 (j :: l) ≤ g.length := by
        rw [hn] at hs
        simp only [List.length_cons] at hs
        omega
      have hc : (i % 2 == 0 && j == i + 1) = false := by
        by_contra hh
        simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hh
        exact h hh
      simp only [List.zip_cons_cons, Fmt.walkLevelW, hc, Bool.false_eq_true, if_false]
      rw [lone_id]
      show Option.map _
          (Fmt.walkLevelW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d
            ((j :: l).zip (b :: v)) (g, (d, sibOf i, x) :: acc)) = _
      rw [level_id d (j :: l) (b :: v) g _ (by simpa using hv') hs']
      simp only [up, note1, stepF, stepC, if_neg h, hn, List.reverse_cons, List.append_assoc]
      rw [Nat.add_comm 1 (need1 (j :: l)), List.drop_succ_cons]
      rfl

theorem length_octF :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D),
      v.length = js.length → (octF hN d js v s).length = (upN d js).length
  | 0, _, _, _, h => h
  | d + 1, js, v, s, _ =>
    length_octF d (up js) (stepF hN js v s) (s.drop (need1 js)) (length_stepF hN js v s)

/-- The whole walk: the root and what is left of the message (in words: the head, `walk_id`). -/
theorem walk_id :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D) (acc met : List (ℕ × ℕ × D)), v.length = js.length →
      need d js ≤ s.length → (upN d js).length = 1 →
      (Fmt.walkW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d (js.zip v) (s, acc) met).map
          (fun x => (x.1, x.2.1.1)) =
        some ((octF hN d js v s).headD default, s.drop (need d js))
  | 0, [i], [r], s, acc, met, _, _, _ => rfl
  | d + 1, js, v, s, acc, met, hv, hs, hu => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hs
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hs
      omega
    simp only [Fmt.walkW]
    rw [level_id hN (d + 1) js v s acc hv h1]
    show (Fmt.walkW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d
        ((up js).zip (stepF hN js v s)) (s.drop (need1 js), _) _).map _ = _
    rw [walk_id d (up js) (stepF hN js v s) (s.drop (need1 js)) _ _ (length_stepF hN js v s) h2 hu,
      List.drop_drop]
    rfl

end

/-- The places: one level of the walk on places alone notes the places `sibs1 d js`. -/
theorem level_places (d : ℕ) :
    ∀ (js : List ℕ) (acc : List (ℕ × ℕ)),
      Fmt.walkLevelW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
          (fun d i acc => some ((), (d, i) :: acc)) d (js.map fun x => (x, ())) acc =
        some ((up js).map (fun x => (x, ())), (sibs1 d js).reverse ++ acc)
  | [], acc => rfl
  | [i], acc => by
    simp only [List.map_cons, List.map_nil, Fmt.walkLevelW, Fmt.walkLoneW, up, sibs1, sibOf]
    by_cases h : i % 2 = 0 <;> simp [h] <;> rfl
  | i :: j :: l, acc => by
    by_cases h : sib i j
    · have hc : (i % 2 == 0 && j == i + 1) = true := by simp [h.1, h.2]
      simp only [List.map_cons, Fmt.walkLevelW, hc, if_true]
      show Option.map _
          (Fmt.walkLevelW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
            (fun d i acc => some ((), (d, i) :: acc)) d (l.map fun x => (x, ())) acc) = _
      rw [level_places d l acc]
      simp only [up, sibs1, if_pos h]
      rfl
    · have hc : (i % 2 == 0 && j == i + 1) = false := by
        by_contra hh
        simp only [Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hh
        exact h hh
      have hl : Fmt.walkLoneW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
            (fun d i (acc : List (ℕ × ℕ)) => some ((), (d, i) :: acc)) d i () acc =
          some ((i / 2, ()), (d, sibOf i) :: acc) := by
        unfold Fmt.walkLoneW sibOf
        by_cases h2 : i % 2 = 0 <;> simp [h2] <;> rfl
      simp only [List.map_cons, Fmt.walkLevelW, hc, Bool.false_eq_true, if_false]
      rw [hl]
      show Option.map _
          (Fmt.walkLevelW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
            (fun d i acc => some ((), (d, i) :: acc)) d
            ((j :: l).map fun x => (x, ())) ((d, sibOf i) :: acc)) = _
      rw [level_places d (j :: l) _]
      simp only [up, sibs1, if_neg h, List.reverse_cons, List.append_assoc]
      rfl

theorem walk_places :
    ∀ (d : ℕ) (js : List ℕ) (acc : List (ℕ × ℕ)) (met : List (ℕ × ℕ × Unit)), (upN d js).length =
        1 →
      (Fmt.walkW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
            (fun d i acc => some ((), (d, i) :: acc)) d (js.map fun x => (x, ())) acc met).map
          (fun x => x.2.1) =
        some ((sibs d js).reverse ++ acc)
  | 0, [i], acc, met, _ => rfl
  | d + 1, js, acc, met, hu => by
    simp only [Fmt.walkW]
    rw [level_places (d + 1) js acc]
    show (Fmt.walkW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
        (fun d i acc => some ((), (d, i) :: acc)) d ((up js).map fun x => (x, ())) _ _).map _ = _
    rw [walk_places d (up js) _ _ hu]
    simp only [sibs, List.reverse_append, List.append_assoc]

/-- Whose values an opening gives: if a levels bring xs to one vertex (`hu`), the page's walk and
the library's case distinction name the same vertices in the same order. -/
theorem places_eq (a : ℕ) (xs : List ℕ) (hu : (upN a xs).length = 1) :
    Fmt.walkPlaces a xs = sibs a xs := by
  have h := walk_places a xs [] [] hu
  unfold Fmt.walkPlaces
  revert h
  generalize Fmt.walkW (m := Id) (α := Unit) (fun _ _ _ _ => pure ())
      (fun d i (acc : List (ℕ × ℕ)) => some ((), (d, i) :: acc)) a (xs.map fun x => (x, ())) [] [] =
    w
  intro h
  cases w with
  | none => simp at h
  | some p =>
    obtain ⟨u, acc, met⟩ := p
    simp only [Option.map_some, Option.some.injEq, List.append_nil] at h
    show (match Id.run (some (u, acc, met)) with
      | some (_, acc, _) => acc.reverse
      | none => []) = _
    show acc.reverse = _
    rw [h, List.reverse_reverse]

theorem places_length (a : ℕ) (xs : List ℕ) (hu : (upN a xs).length = 1) :
    (Fmt.walkPlaces a xs).length = need a xs := by
  rw [places_eq a xs hu, length_sibs]

/-- the cost: at most one given digest for each opened position on each level -/
theorem need_le_mul : ∀ (d : ℕ) (js : List ℕ), need d js ≤ d * js.length
  | 0, _ => by simp [need]
  | d + 1, js => by
    have h1 : need1 js ≤ js.length := le_trans (need1_le js) (length_up_le js)
    have h2 : need d (up js) ≤ d * js.length :=
      le_trans (need_le_mul d (up js)) (Nat.mul_le_mul_left d (length_up_le js))
    calc need (d + 1) js = need1 js + need d (up js) := rfl
      _ ≤ js.length + d * js.length := Nat.add_le_add h1 h2
      _ = (d + 1) * js.length := by ring

/-! ### A list that `Fmt.listOK` accepts comes to one vertex -/

theorem listOK_spec (a : ℕ) :
    ∀ xs : List ℕ, Fmt.listOK a xs = true → xs ≠ [] ∧ xs.Pairwise (· < ·) ∧ ∀ x ∈ xs, x < 2 ^ a
  | [x], h => ⟨by simp, by simp, by simpa [Fmt.listOK] using h⟩
  | x :: y :: tl, h => by
    simp only [Fmt.listOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, hp, hb⟩ := listOK_spec a (y :: tl) h.2
    have hy : ∀ z ∈ y :: tl, x < z := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h.1
      · exact lt_trans h.1 ((List.pairwise_cons.1 hp).1 z hz)
    refine ⟨by simp, List.pairwise_cons.2 ⟨hy, hp⟩, ?_⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact lt_trans h.1 (hb y (by simp))
    · exact hb z hz

theorem up_ne_nil : ∀ js : List ℕ, js ≠ [] → up js ≠ []
  | [_], _ => by simp [up]
  | i :: j :: l, _ => by
    unfold up
    split <;> simp

theorem upN_one :
    ∀ (a : ℕ) (xs : List ℕ),
      xs ≠ [] → xs.Pairwise (· < ·) → (∀ x ∈ xs, x < 2 ^ a) → (upN a xs).length = 1
  | 0, xs, hn, hp, hb => by
    have h1 : xs.length ≤ 1 := length_le_of_pairwise hp (by simpa using hb)
    have h0 : 0 < xs.length := List.length_pos_iff.2 hn
    show xs.length = 1
    omega
  | a + 1, xs, hn, hp, hb => by
    refine upN_one a (up xs) (up_ne_nil xs hn) (pairwise_up xs hp) ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_up xs x hx
    have := hb k hk
    rw [pow_succ] at this
    omega

theorem listOK_one (a : ℕ) (xs : List ℕ) (h : Fmt.listOK a xs = true) : (upN a xs).length = 1 :=
  upN_one a xs (listOK_spec a xs h).1 (listOK_spec a xs h).2.1 (listOK_spec a xs h).2.2

/-! ### The reader -/

theorem rdMany_length {α : Type} (r : Fmt.Rd α) :
    ∀ (n : ℕ) (b : ByteArray) (i : ℕ) (l : List α) (k : ℕ),
      Fmt.rdMany r n b i = some (l, k) → l.length = n
  | 0, _, _, l, k, h => by
    simp only [Fmt.rdMany, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | n + 1, b, i, l, k, h => by
    simp only [Fmt.rdMany] at h
    split at h
    · rename_i x j _
      split at h
      · rename_i l' k' e'
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, rdMany_length r n b j l' k' e']
      · cases h
    · cases h

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- the opened leaves' digests: the reader's own hash calls -/
def leafV (sh : Fmt.Shape) (start : ByteArray) :
    List ℕ → List (List UInt64 × ByteArray) → List ByteArray
  | x :: xs, c :: cs =>
    h (Fmt.leafNo sh.stored) (Fmt.leafPlace sh.tree c.1.length (c.2.size / 8)) (2 ^ sh.a + x)
        start (Fmt.leafBytes c.1 c.2) ::
      leafV sh start xs cs
  | _, _ => []

theorem length_leafV (sh : Fmt.Shape) (start : ByteArray) :
    ∀ (xs : List ℕ) (cs : List (List UInt64 × ByteArray)),
      cs.length = xs.length → (leafV h sh start xs cs).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: cs, e => congrArg (· + 1) (length_leafV sh start xs cs (by simpa using e))

theorem leaves_id (sh : Fmt.Shape) (start : ByteArray) :
    ∀ (xs : List ℕ) (cs : List (List UInt64 × ByteArray)), cs.length = xs.length →
      Fmt.leavesW (m := Id) h sh start xs cs = xs.zip (leafV h sh start xs cs)
  | [], [], _ => rfl
  | x :: xs, (col, salt) :: cs, e => by
    simp only [Fmt.leavesW]
    show (x, _) :: Fmt.leavesW (m := Id) h sh start xs cs = _
    rw [leaves_id sh start xs cs (by simpa using e)]
    rfl

theorem zip_fst_snd {α β : Type} : ∀ l : List (α × β), (l.map (·.1)).zip (l.map (·.2)) = l
  | [] => rfl
  | x :: l => by simp [zip_fst_snd l]

/-- If the reader returns o (`e`), the reader's root is the library's (in words: the head,
`reader_id`). -/
theorem reader_id (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ) (sh : Fmt.Shape) (start : ByteArray)
    (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : Fmt.OpenOut)
    (e : Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i = some o) :
    o.cols.length = xs.length ∧
    o.salts.length = xs.length ∧
    o.given.length = need sh.a xs ∧
    o.root = (octF (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs
          (leafV h sh start xs (o.cols.zip o.salts)) o.given).headD default := by
  unfold Fmt.readOpeningW at e
  split at e
  · rename_i hok
    have hl : Fmt.listOK sh.a xs = true := (Bool.and_eq_true _ _ ▸ hok : _ ∧ _).1
    have hu := listOK_one sh.a xs hl
    split at e
    · cases e
    · rename_i cs given next ep
      have hlen : cs.length = xs.length ∧ given.length = need sh.a xs := by
        unfold Fmt.rdOpening Fmt.rdPair at ep
        split at ep
        · rename_i cs' j e1
          split at ep
          · rename_i g' k e2
            simp only [Option.some.injEq, Prod.mk.injEq] at ep
            obtain ⟨⟨rfl, rfl⟩, -⟩ := ep
            exact ⟨rdMany_length _ _ _ _ _ _ e1,
              (rdMany_length _ _ _ _ _ _ e2).trans (places_length sh.a xs hu)⟩
          · cases ep
        · cases ep
      have hw := walk_id (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs (leafV h sh start xs cs) given
        [] [] (length_leafV h sh start xs cs hlen.1) (le_of_eq hlen.2.symm) hu
      have e' : (Fmt.walkW (m := Id) (fun _ _ l r => h 166 0 0 cfg (l ++ r)) Fmt.takeGiven sh.a
              (Fmt.leavesW (m := Id) h sh start xs cs) (given, []) []).map
            (fun r =>
              (⟨cs.map (·.1), cs.map (·.2), given, r.1, r.2.2 ++ r.2.1.2, next⟩ : Fmt.OpenOut)) =
          some o := e
      rw [leaves_id h sh start xs cs hlen.1] at e'
      revert hw e'
      generalize Fmt.walkW (m := Id) (fun _ _ l r => h 166 0 0 cfg (l ++ r)) Fmt.takeGiven sh.a
          (xs.zip (leafV h sh start xs cs)) (given, []) [] = w
      intro hw e'
      cases w with
      | none => cases e'
      | some p =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw e'
        subst e'
        refine ⟨by simp [hlen.1], by simp [hlen.1], hlen.2, ?_⟩
        show p.1 = _
        rw [zip_fst_snd]
        exact hw.1
  · cases e

end

end Run.WalkTie
