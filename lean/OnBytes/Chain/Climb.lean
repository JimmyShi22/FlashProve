-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Climb.lean: the walk from the opened leaves of a tree to its root, as loops.

Fmt/ states one level of the walk (format page, R7.9) by recursion on the result, once for each
vertex of the level, and likewise the hashing of the opened leaves. A compiled program then needs
stack in proportion to the number of opened positions. Here both collect their results in an
array. Each is proved equal to the function of Fmt/ at the identity monad.
C++ counterpart: tree_walk in blocks/tree/tree.h.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `loneT`, `levelT`, `walkT`, `walkPlacesT`, `leavesT`.
Main theorems: `levelT_eq`, `walkT_eq`, `walkPlacesT_eq`, `leavesT_eq`.
-/
import Fmt.Rules8Fast

namespace OnBytes

section
variable {α σ : Type} (comb : Nat → Nat → α → α → α) (give : Nat → Nat → σ → Option (α × σ))

/-- A vertex (d, i) whose sibling has no opened leaf below it: the sibling's value is given.
`comb d' i' l r` makes the value of the vertex (d', i') from its children's values l and r.
`give d' i' s` hands out the next given value from the state s, as the value of the vertex
(d', i'); if it returns none, so does `loneT`. Returns the parent's place and value, and the new
state. -/
def loneT (d i : Nat) (x : α) (s : σ) : Option ((Nat × α) × σ) :=
  match give d (if i % 2 == 0 then i + 1 else i - 1) s with
  | none => none
  | some (o, s') =>
    some ((i / 2, if i % 2 == 0 then comb (d - 1) (i / 2) x o else comb (d - 1) (i / 2) o x), s')

/-- `loneT` equals `Fmt.walkLoneW` at the identity monad. -/
theorem loneT_eq (d i : Nat) (x : α) (s : σ) :
    loneT comb give d i x s = Fmt.walkLoneW (m := Id) comb give d i x s := by
  unfold loneT Fmt.walkLoneW
  cases give d (if i % 2 == 0 then i + 1 else i - 1) s with
  | none => rfl
  | some r =>
    obtain ⟨o, s'⟩ := r
    by_cases hb : (i % 2 == 0) = true
    · simp only [if_pos hb]
      rfl
    · simp only [if_neg hb]
      rfl

/-- One depth of the walk (format page, R7.9). The list holds (place, value) for the vertices of
depth d that lie above an opened leaf. The caller gives them by increasing place, which is not
tested here. Their parents are appended to acc. -/
def levelLoop (d : Nat) : List (Nat × α) → σ → Array (Nat × α) → Option (List (Nat × α) × σ)
  | [], s, acc => some (acc.toList, s)
  | [(i, x)], s, acc =>
    match loneT comb give d i x s with
    | none => none
    | some (p, s') => some ((acc.push p).toList, s')
  | (i, x) :: (i', x') :: rest, s, acc =>
    if i % 2 == 0 && i' == i + 1 then
      levelLoop d rest s (acc.push (i / 2, comb (d - 1) (i / 2) x x'))
    else
      match loneT comb give d i x s with
      | none => none
      | some (p, s') => levelLoop d ((i', x') :: rest) s' (acc.push p)

/-- `levelLoop` returns the members of acc followed by what `Fmt.walkLevelW` returns. -/
theorem levelLoop_eq (d : Nat) : ∀ (l : List (Nat × α)) (s : σ) (acc : Array (Nat × α)),
    levelLoop comb give d l s acc =
      (Fmt.walkLevelW (m := Id) comb give d l s).map fun r => (acc.toList ++ r.1, r.2)
  | [], s, acc => by
    show some (acc.toList, s) = some (acc.toList ++ [], s)
    rw [List.append_nil]
  | [(i, x)], s, acc => by
    rw [levelLoop, loneT_eq]
    show _ = Option.map _
      ((Fmt.walkLoneW (m := Id) comb give d i x s).map fun r => ([r.1], r.2))
    cases Fmt.walkLoneW (m := Id) comb give d i x s with
    | none => rfl
    | some r =>
      obtain ⟨p, s'⟩ := r
      simp
  | (i, x) :: (i', x') :: rest, s, acc => by
    rw [levelLoop]
    by_cases hc : (i % 2 == 0 && i' == i + 1) = true
    · rw [if_pos hc, levelLoop_eq d rest s]
      show _ = Option.map _ (if (i % 2 == 0 && i' == i + 1) = true then
        (Fmt.walkLevelW (m := Id) comb give d rest s).map fun r =>
          ((i / 2, comb (d - 1) (i / 2) x x') :: r.1, r.2) else _)
      rw [if_pos hc]
      cases Fmt.walkLevelW (m := Id) comb give d rest s with
      | none => rfl
      | some r => simp
    · rw [if_neg hc, loneT_eq]
      show _ = Option.map _ (if (i % 2 == 0 && i' == i + 1) = true then _ else
        (match Fmt.walkLoneW (m := Id) comb give d i x s with
        | none => none
        | some (p, s') =>
          (Fmt.walkLevelW (m := Id) comb give d ((i', x') :: rest) s').map fun r =>
            (p :: r.1, r.2)))
      rw [if_neg hc]
      cases Fmt.walkLoneW (m := Id) comb give d i x s with
      | none => rfl
      | some r =>
        obtain ⟨p, s'⟩ := r
        dsimp only
        rw [levelLoop_eq d ((i', x') :: rest) s']
        cases Fmt.walkLevelW (m := Id) comb give d ((i', x') :: rest) s' with
        | none => rfl
        | some r => simp

/-- One depth of the walk: `Fmt.walkLevelW` as a loop. -/
def levelT (d : Nat) (l : List (Nat × α)) (s : σ) : Option (List (Nat × α) × σ) :=
  levelLoop comb give d l s #[]

/-- `levelT` equals `Fmt.walkLevelW` at the identity monad. -/
theorem levelT_eq (d : Nat) (l : List (Nat × α)) (s : σ) :
    levelT comb give d l s = Fmt.walkLevelW (m := Id) comb give d l s := by
  unfold levelT
  rw [levelLoop_eq]
  cases Fmt.walkLevelW (m := Id) comb give d l s with
  | none => rfl
  | some r => rfl

/-- From depth d to the root: `Fmt.walkW` with each depth walked by the loop. Returns the root's
value, the last state of `give` and the vertices met. Returns none if `give` does, or if the walk
does not end in exactly one vertex, as for an empty list. `met` holds the vertices passed so far
as (depth, place, value); those of the present depth are put in front. The given values are not
among them. Counterpart: tree_walk in blocks/tree/tree.h. -/
def walkT : Nat → List (Nat × α) → σ → List (Nat × Nat × α) →
    Option (α × σ × List (Nat × Nat × α))
  | 0, [(i, r)], s, met => some (r, s, (0, i, r) :: met)
  | 0, _, _, _ => none
  | d + 1, now, s, met =>
    match levelT comb give (d + 1) now s with
    | none => none
    | some (nxt, s') => walkT d nxt s' (now.map (fun v => (d + 1, v.1, v.2)) ++ met)

/-- `walkT` equals `Fmt.walkW` at the identity monad. -/
theorem walkT_eq : ∀ (d : Nat) (now : List (Nat × α)) (s : σ) (met : List (Nat × Nat × α)),
    walkT comb give d now s met = Fmt.walkW (m := Id) comb give d now s met
  | 0, [], _, _ => rfl
  | 0, [_], _, _ => rfl
  | 0, _ :: _ :: _, _, _ => rfl
  | d + 1, now, s, met => by
    rw [walkT, levelT_eq]
    show _ = (match Fmt.walkLevelW (m := Id) comb give (d + 1) now s with
      | none => none
      | some (nxt, s') =>
        Fmt.walkW (m := Id) comb give d nxt s'
          (now.map (fun (v : Nat × α) => (d + 1, v.1, v.2)) ++ met))
    cases Fmt.walkLevelW (m := Id) comb give (d + 1) now s with
    | none => rfl
    | some r => exact walkT_eq d r.1 r.2 _

end

/-- The vertices whose values an opening gives, for a tree of depth a opened at the list xs, in
the opening's order, as (depth, place): `Fmt.walkPlaces` with the loops. The empty list if the
walk does not end in exactly one vertex, as for an empty xs. -/
def walkPlacesT (a : Nat) (xs : List Nat) : List (Nat × Nat) :=
  match walkT (α := Unit) (σ := List (Nat × Nat)) (fun _ _ _ _ => ())
      (fun d i acc => some ((), (d, i) :: acc)) a (xs.map fun x => (x, ())) [] [] with
  | some (_, acc, _) => acc.reverse
  | none => []

/-- `walkPlacesT` equals `Fmt.walkPlaces`. -/
theorem walkPlacesT_eq (a : Nat) (xs : List Nat) : walkPlacesT a xs = Fmt.walkPlaces a xs := by
  unfold walkPlacesT Fmt.walkPlaces
  rw [walkT_eq]
  rfl

/-- Appends the digests of the opened leaves, each with its place, to acc. -/
def leavesLoop (h : Fmt.Hash) (sh : Fmt.Shape) (start : ByteArray) :
    List Nat → List (List UInt64 × ByteArray) → Array (Nat × ByteArray) → List (Nat × ByteArray)
  | x :: xs, (col, salt) :: cs, acc =>
    leavesLoop h sh start xs cs
      (acc.push (x, Fmt.leafW (m := Id) h (Fmt.leafNo sh.stored) sh.tree sh.a x start col salt))
  | _, _, acc => acc.toList

/-- `Fmt.leavesW` at the identity monad, as a plain list. -/
def leavesId (h : Fmt.Hash) (sh : Fmt.Shape) (start : ByteArray) (xs : List Nat)
    (cs : List (List UInt64 × ByteArray)) : List (Nat × ByteArray) :=
  Fmt.leavesW (m := Id) h sh start xs cs

/-- `leavesLoop` returns the members of acc followed by what `Fmt.leavesW` returns. -/
theorem leavesLoop_eq (h : Fmt.Hash) (sh : Fmt.Shape) (start : ByteArray) :
    ∀ (xs : List Nat) (cs : List (List UInt64 × ByteArray)) (acc : Array (Nat × ByteArray)),
    leavesLoop h sh start xs cs acc =
      acc.toList ++ leavesId h sh start xs cs
  | [], _, acc => by
    show acc.toList = acc.toList ++ []
    rw [List.append_nil]
  | _ :: _, [], acc => by
    show acc.toList = acc.toList ++ []
    rw [List.append_nil]
  | x :: xs, (col, salt) :: cs, acc => by
    rw [leavesLoop, leavesLoop_eq h sh start xs cs]
    show _ = acc.toList ++ (((x, Fmt.leafW (m := Id) h (Fmt.leafNo sh.stored) sh.tree sh.a x start
      col salt) : Nat × ByteArray) :: leavesId h sh start xs cs)
    simp

/-- The opened leaves' digests, in the list's order, each with its place: `Fmt.leavesW` as a
loop. xs are the places, cs the columns with their salts. If one of the two lists is longer, its
further members are dropped: that the lengths agree is not tested here. -/
def leavesT (h : Fmt.Hash) (sh : Fmt.Shape) (start : ByteArray) (xs : List Nat)
    (cs : List (List UInt64 × ByteArray)) : List (Nat × ByteArray) :=
  leavesLoop h sh start xs cs #[]

/-- `leavesT` equals `Fmt.leavesW` at the identity monad. -/
theorem leavesT_eq (h : Fmt.Hash) (sh : Fmt.Shape) (start : ByteArray) (xs : List Nat)
    (cs : List (List UInt64 × ByteArray)) :
    leavesT h sh start xs cs = Fmt.leavesW (m := Id) h sh start xs cs := by
  unfold leavesT
  rw [leavesLoop_eq]
  rfl

end OnBytes
