-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Sound/KeyMapAtFK.lean: It stands on Johnson/Desc/Key/Desc.lean.
WHICH BLOCK SITS AT WHICH SEAT OF THE KEY FILE'S FIRST CHAIN: facts on
the description's own text.

What is said. L := the number of the plan's lookups (`Key.lookupsOf`).
  `getElem?_flatMap_const`: a law on lists: where every part has n members, member n · l + j of the
    parts in a row is member j of part l.
  `fk_first_flat`: the first chain's flat list: the two sendings in front; six blocks a lookup; the
    back.
  `fk_link_at`: seat 2 + (6 · l + j), for j < 6, holds member j of lookup l's link's flat list.
  `fk_caller_at` (j = 1), `fk_K3_at` (2), `fk_layer_at` (3): these three by name: AT SEAT
    2 + (6 · l + 2) SITS THE KIND'S OWN BLOCK
    `lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace X.set l x)`.

  `fk_idx_at`, `fk_msg_at`: seats 0 and 1. `fk_back_at`: seat 2 + 6 · L + j holds member j of the
    chain's back; `fk_rows_at` (j = 0), `fk_rng_at` (j = 1).

Limits. The first chain alone. Nothing on any block's law.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Sound
open VerifiableInference.Desc
open VerifiableInference.Desc.Key (descriptionFromSource Source FirstState Claim firstChain lookupLink lookupsOf
  caller layer lookupSeat lookupPlace)
open VerifiableInference.Desc.K3 (lookupKind)

/-- Where every part has n members, member n · l + j of the parts in a row is member j of part l. -/
theorem getElem?_flatMap_const {α β : Type} (f : α → List β) (n : ℕ) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).length = n) → ∀ (l j : ℕ), j < n →
      (xs.flatMap f)[n * l + j]? = (xs[l]?).bind fun x => (f x)[j]?
  | [], _, _, _, _ => by simp
  | x :: xs, h, 0, j, hj => by
    have hx : j < (f x).length := by rw [h x List.mem_cons_self]; exact hj
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem?_append_left hx]
    rfl
  | x :: xs, h, l + 1, j, hj => by
    have hx : (f x).length = n := h x List.mem_cons_self
    have hle : (f x).length ≤ n * (l + 1) + j := by
      rw [hx, Nat.mul_succ]
      omega
    have e : n * (l + 1) + j - (f x).length = n * l + j := by
      rw [hx, Nat.mul_succ]
      omega
    rw [List.flatMap_cons, List.getElem?_append_right hle, e,
      getElem?_flatMap_const f n xs (fun y hy => h y (List.mem_cons_of_mem x hy)) l j hj]
    rfl

theorem length_flatMap_const {α β : Type} (f : α → List β) (n : ℕ) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).length = n) → (xs.flatMap f).length = n * xs.length
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatMap_cons, List.length_append, h x List.mem_cons_self,
      length_flatMap_const f n xs (fun y hy => h y (List.mem_cons_of_mem x hy)), List.length_cons,
      Nat.mul_succ, Nat.add_comm]

theorem getElem?_append_at {α : Type} (a b : List α) (n j : ℕ) (h : a.length = n) :
    (a ++ b)[n + j]? = b[j]? := by
  subst h
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- The links of the first chain. -/
abbrev fkLinks : List (Link Key.FirstState Key.Claim) :=
  (Key.lookupsOf X.Y.k.oneTime).zipIdx.map fun x => Key.lookupLink X.Y.k.oneTime X.set x.2 x.1

/-- A block of a chain outside its links as the flat list lays it. -/
abbrev bareB {S Cl : Type} (b : Block S Cl) : Block S Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- The first chain, at its own types. -/
abbrev fkFirst : Chain Key.FirstState Key.Claim :=
  Key.firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N

/-- What stands behind the links: the chain's back and its last block. -/
abbrev fkTail : List (Block Key.FirstState Key.Claim) :=
  (fkFirst X N).back.map bareB ++ [bareB (fkFirst X N).last]

/-- **The first chain's flat list, in three parts**: the first block and the front; the links' flat
lists; the back and the last block. -/
theorem fk_flat_eq : (FK X N P).first.blocksInOrder =
    (bareB (fkFirst X N).first :: (fkFirst X N).front.map bareB ++
      (fkLinks X).flatMap Link.blocksInOrder) ++ fkTail X N :=
  List.append_assoc (bareB (fkFirst X N).first :: (fkFirst X N).front.map bareB ++
    (fkLinks X).flatMap Link.blocksInOrder) ((fkFirst X N).back.map bareB) [bareB (fkFirst X N).last]

/-- **The first chain's flat list**: two blocks in front; the links' flat lists; the rest. -/
theorem fk_first_flat : ∃ (i m : Block Key.FirstState Key.Claim)
    (back : List (Block Key.FirstState Key.Claim)),
    (FK X N P).first.blocksInOrder = [i, m] ++ (fkLinks X).flatMap Link.blocksInOrder ++ back :=
  ⟨_, _, _, fk_flat_eq X N P⟩

theorem link_six (L : Link Key.FirstState Key.Claim) (h : L ∈ fkLinks X) : L.blocksInOrder.length = 6 := by
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 h
  rfl

/-- **Seat 2 + (6 · l + j) holds member j of lookup l's link's flat list.** -/
theorem fk_link_at (l j : ℕ) (hj : j < 6) (x : Key.Lookup)
    (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x) :
    (FK X N P).first.blocksInOrder[2 + (6 * l + j)]? =
      (Key.lookupLink X.Y.k.oneTime X.set l x).blocksInOrder[j]? := by
  obtain ⟨i, m, back, e⟩ := fk_first_flat X N P
  have hl : l < (Key.lookupsOf X.Y.k.oneTime).length := (List.getElem?_eq_some_iff.1 hx).1
  have hlen : ((fkLinks X).flatMap Link.blocksInOrder).length =
      6 * (Key.lookupsOf X.Y.k.oneTime).length := by
    rw [length_flatMap_const Link.blocksInOrder 6 _ (link_six X)]
    simp [fkLinks]
  have hk : (fkLinks X)[l]? = some (Key.lookupLink X.Y.k.oneTime X.set l x) := by
    simp [fkLinks, List.getElem?_map, List.getElem?_zipIdx, hx]
  have h1 : 2 + (6 * l + j) < ([i, m] ++ (fkLinks X).flatMap Link.blocksInOrder).length := by
    rw [List.length_append, hlen]
    show 2 + (6 * l + j) < 2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length
    omega
  rw [e]
  refine (List.getElem?_append_left h1).trans ?_
  refine (List.getElem?_append_right
    (show [i, m].length ≤ 2 + (6 * l + j) from Nat.le_add_right 2 _)).trans ?_
  rw [show 2 + (6 * l + j) - [i, m].length = 6 * l + j from Nat.add_sub_cancel_left 2 _,
    getElem?_flatMap_const Link.blocksInOrder 6 _ (link_six X) l j hj, hk]
  rfl

/-- **At seat 2 + (6 · l + 2) sits the kind's own block.** -/
theorem fk_K3_at (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x) :
    (FK X N P).first.blocksInOrder[2 + (6 * l + 2)]? =
      some (lookupKind Key.lookupSeat [(1, 0), (1, 1)] 0 [] (Key.lookupPlace X.set l x)) :=
  fk_link_at X N P l 2 (by decide) x hx

theorem fk_caller_at (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x) :
    (FK X N P).first.blocksInOrder[2 + (6 * l + 1)]? = some (Key.caller X.Y.k.oneTime l x) :=
  fk_link_at X N P l 1 (by decide) x hx

theorem fk_layer_at (l : ℕ) (x : Key.Lookup) (hx : (Key.lookupsOf X.Y.k.oneTime)[l]? = some x) :
    (FK X N P).first.blocksInOrder[2 + (6 * l + 3)]? =
      some (Key.layer X.Y.k.oneTime X.set l x
        (claimsIn (Key.lookupLink X.Y.k.oneTime X.set l x).hear
          (Key.lookupLink X.Y.k.oneTime X.set l x).order)) :=
  fk_link_at X N P l 3 (by decide) x hx

/-- **Seats 0 and 1: the two sendings in front.** -/
theorem fk_idx_at : ∃ g, (FK X N P).first.blocksInOrder[0]? =
    some (bareB (Key.sendIndexMasks X.Y.k.oneTime Key.pieces g)) := ⟨_, rfl⟩

theorem fk_msg_at : ∃ g, (FK X N P).first.blocksInOrder[1]? =
    some (bareB (Key.sendOwnMessage X.Y.k.oneTime Key.pieces g)) := ⟨_, rfl⟩

/-- **Seat 2 + 6 · L + j holds member j of what stands behind the links.** -/
theorem fk_back_at (j : ℕ) :
    (FK X N P).first.blocksInOrder[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + j]? =
      (fkTail X N)[j]? := by
  have e := fk_flat_eq X N P
  have hlen : (bareB (fkFirst X N).first :: (fkFirst X N).front.map bareB ++
      (fkLinks X).flatMap Link.blocksInOrder).length =
      2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length := by
    show ([bareB (fkFirst X N).first, _] ++ (fkLinks X).flatMap Link.blocksInOrder).length = _
    rw [List.length_append, length_flatMap_const Link.blocksInOrder 6 _ (link_six X)]
    simp [fkLinks]
  exact (congrArg (fun l => l[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + j]?) e).trans
    (getElem?_append_at _ _ _ j hlen)

/-- **Behind the links: the rows onto the ranges' group; the ranges' test; the batching.** -/
theorem fk_rows_at : (FK X N P).first.blocksInOrder[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 0]? =
    some (bareB (Key.layRows X.Y.k.oneTime)) := fk_back_at X N P 0

theorem fk_rng_at :
    (FK X N P).first.blocksInOrder[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 1]? =
      some (bareB (Key.rangesTest (Key.enterRanges X.Y.k.oneTime) Key.leaveRanges N)) := by
  exact fk_back_at X N P 1

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.fk_idx_at
#print axioms Johnson.RunOne.Sound.fk_msg_at
#print axioms Johnson.RunOne.Sound.fk_back_at
#print axioms Johnson.RunOne.Sound.fk_rows_at
#print axioms Johnson.RunOne.Sound.fk_rng_at
#print axioms Johnson.RunOne.Sound.getElem?_flatMap_const
#print axioms Johnson.RunOne.Sound.fk_link_at
#print axioms Johnson.RunOne.Sound.fk_K3_at
#print axioms Johnson.RunOne.Sound.fk_caller_at
#print axioms Johnson.RunOne.Sound.fk_layer_at
#print axioms Johnson.RunOne.Sound.length_flatMap_const
#print axioms Johnson.RunOne.Sound.getElem?_append_at
#print axioms Johnson.RunOne.Sound.fk_flat_eq
#print axioms Johnson.RunOne.Sound.fk_first_flat
#print axioms Johnson.RunOne.Sound.link_six
