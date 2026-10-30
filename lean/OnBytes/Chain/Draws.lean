-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/Draws.lean: a round's long draws as loops.

A round can draw the entries of a matrix over {-1, 0, 1}, 32 from each word of the round's row
(format page, R6.7). Fmt/ states that draw by recursion on the result, once for each word. A
compiled program then needs stack in proportion to the number of words, and a round of a large
model draws millions of entries. Here the words are taken by a map over their numbers, and the
entries are collected in an array. The draw is proved equal to the draw of Fmt/.

The positions of a round are taken from the words in the same way. The list that is made from
them (their set, increasing) is made by sorting: see `listOfT`. A public file sets how many
positions a round draws, and the steps of Fmt/'s function grow with the square of that number.
The elements of a round are drawn by loops too.
C++ counterparts: AlgebraicDraw, SeedDraw, PositionsDraw::positions and BitsDraw::trits in
blocks/chain/rounds.h; PositionList::from_draws in blocks/tree/positions.h.
The format page is docs/format/FORMAT.md. A number such as R7.14 is a rule of that page.

Main definitions: `wordsT`, `timesT`, `drawElemsT`, `drawPossT`, `listOfT`, `tritsT`, `drawTritsT`,
`drawRoundT`.
Main theorems: `timesT_eq`, `drawElemsT_eq`, `drawPossT_eq`, `listOfT_eq`, `drawTritsT_eq`,
`drawRoundT_eq`.
-/
import Fmt.Rules6Round
import Fmt.Rules6Laws

namespace OnBytes

open Fmt (Row Dr Fld Entry Kind Drawn)

/-- The n words of the row from place c on. -/
def wordsT (row : Row) (c n : Nat) : List UInt64 := (List.range n).map fun j => row (c + j)

/-- Taking the next word n times gives `wordsT row c n` and moves the place from c to c + n. -/
theorem times_word : ∀ (n : Nat) (row : Row) (c : Nat),
    Dr.word.times n row c = (wordsT row c n, c + n)
  | 0, _, _ => rfl
  | n + 1, row, c => by
    have ih := times_word n row (c + 1)
    show (row c :: (Dr.word.times n row (c + 1)).1, (Dr.word.times n row (c + 1)).2) = _
    rw [ih]
    unfold wordsT
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    refine Prod.ext ?_ (by show c + 1 + n = c + (n + 1); omega)
    show row c :: _ = row c :: _
    congr 1
    refine List.map_congr_left fun j _ => ?_
    show row (c + 1 + j) = row (c + (j + 1))
    rw [Nat.add_assoc, Nat.add_comm 1 j]

/-- The loop of `timesT`. acc: what was drawn so far. -/
def timesLoop {α : Type} (x : Dr α) (row : Row) : Nat → Nat → Array α → List α × Nat
  | 0, c, acc => (acc.toList, c)
  | n + 1, c, acc => timesLoop x row n (x row c).2 (acc.push (x row c).1)

/-- A draw, n times: `Fmt.Dr.times` as a loop. -/
def timesT {α : Type} (x : Dr α) (n : Nat) : Dr (List α) := fun row c => timesLoop x row n c #[]

/-- The loop gives what `Fmt.Dr.times` gives, after what was drawn before. -/
theorem timesLoop_eq {α : Type} (x : Dr α) (row : Row) : ∀ (n c : Nat) (acc : Array α),
    timesLoop x row n c acc = (acc.toList ++ (x.times n row c).1, (x.times n row c).2)
  | 0, c, acc => by
    show (acc.toList, c) = (acc.toList ++ [], c)
    rw [List.append_nil]
  | n + 1, c, acc => by
    show timesLoop x row n (x row c).2 (acc.push (x row c).1) =
      (acc.toList ++ (x row c).1 :: (x.times n row (x row c).2).1, (x.times n row (x row c).2).2)
    rw [timesLoop_eq x row n, Array.toList_push, List.append_assoc]
    rfl

/-- `timesT` equals `Fmt.Dr.times`. -/
theorem timesT_eq {α : Type} (x : Dr α) (n : Nat) : timesT x n = x.times n := by
  funext row c
  rw [timesT, timesLoop_eq]
  rfl

/-- The elements of a round: `Fmt.drawElems` with the four functions that it calls written out
(`drawSeeds`, `drawSeedL`, `drawSeed`, `drawPlainNZ` of Fmt/) and every "n times" as a loop. -/
def drawElemsT (f : Fld) (e : Entry) (k : Kind) : Dr (List Fmt.Ext) :=
  if k = .seeds then
    (timesT ((((timesT (Fmt.drawE f) ((e.drawE - e.drawNZ) / e.drawNZ)).bind fun pt =>
        (Fmt.drawNZ f).bind fun s => Dr.pure (pt, s)) : Dr (List Fmt.Ext × Fmt.Ext)).bind fun s =>
          Dr.pure (s.1 ++ [s.2])) e.drawNZ).bind fun x =>
      (timesT (Fmt.drawE f) ((e.drawE - e.drawNZ) % e.drawNZ)).bind fun y =>
        Dr.pure (x.flatten ++ y)
  else
    (timesT (Fmt.drawE f) (e.drawE - e.drawNZ)).bind fun x =>
      (timesT (Fmt.drawNZ f) e.drawNZ).bind fun y => Dr.pure (x ++ y)

/-- `drawElemsT` equals `Fmt.drawElems`. -/
theorem drawElemsT_eq (f : Fld) (e : Entry) (k : Kind) :
    drawElemsT f e k = Fmt.drawElems f e k := by
  unfold drawElemsT
  simp only [timesT_eq]
  rfl

/-- The seal, in a round of that kind: `Fmt.drawDigest`, its four words taken by `wordsT`. -/
def drawDigestT (k : Kind) : Dr (Option ByteArray) := fun row c =>
  if k = .sealed then (some (Fmt.cat ((wordsT row c 4).map Fmt.u64)), c + 4) else (none, c)

/-- `drawDigestT` equals `Fmt.drawDigest`. -/
theorem drawDigestT_eq (k : Kind) : drawDigestT k = Fmt.drawDigest k := by
  funext row c
  unfold drawDigestT Fmt.drawDigest
  by_cases h : k = .sealed
  · rw [if_pos h, if_pos h]
    show _ = (some (Fmt.cat ((Dr.word.times 4 row c).1.map Fmt.u64)), (Dr.word.times 4 row c).2)
    rw [times_word]
  · rw [if_neg h, if_neg h]
    rfl

/-- The draws of a round: n positions below 2 ^ k in the order drawn, repeats kept (format page,
R6.6). Each is the low k bits of the next word. `Fmt.drawPoss` without deep recursion. -/
def drawPossT (k n : Nat) : Dr (List Nat) := fun row c =>
  ((wordsT row c n).map fun w => w.toNat % 2 ^ k, c + n)

/-- Drawing a position n times gives the low bits of the next n words. -/
theorem times_pos (k : Nat) : ∀ (n : Nat) (row : Row) (c : Nat),
    (Fmt.drawPos k).times n row c = ((wordsT row c n).map fun w => w.toNat % 2 ^ k, c + n)
  | 0, _, _ => rfl
  | n + 1, row, c => by
    have ih := times_pos k n row (c + 1)
    have hw := times_word (n + 1) row c
    have hw' := times_word n row (c + 1)
    have e : wordsT row c (n + 1) = row c :: wordsT row (c + 1) n := by
      have h1 : (Dr.word.times (n + 1) row c).1 = row c :: (Dr.word.times n row (c + 1)).1 := rfl
      rw [hw, hw'] at h1
      exact h1
    show ((row c).toNat % 2 ^ k :: ((Fmt.drawPos k).times n row (c + 1)).1,
      ((Fmt.drawPos k).times n row (c + 1)).2) = _
    rw [ih, e, List.map_cons]
    refine Prod.ext rfl ?_
    show c + 1 + n = c + (n + 1)
    omega

/-- `drawPossT` equals `Fmt.drawPoss`. -/
theorem drawPossT_eq (k n : Nat) : drawPossT k n = Fmt.drawPoss k n := by
  funext row c
  exact (times_pos k n row c).symm

/-- Puts a number into an increasing list without repeats: `Fmt.insertIntoIncreasingList` without deep
recursion. -/
def insertT (x : Nat) (l : List Nat) : List Nat :=
  l.takeWhile (· < x) ++
    match l.dropWhile (· < x) with
    | [] => [x]
    | y :: t => if x = y then y :: t else x :: y :: t

/-- `insertT` equals `Fmt.insertIntoIncreasingList`. -/
theorem insertT_eq (x : Nat) : ∀ l : List Nat, insertT x l = Fmt.insertIntoIncreasingList x l
  | [] => rfl
  | y :: l => by
    have ih := insertT_eq x l
    unfold insertT at ih ⊢
    rw [Fmt.insertIntoIncreasingList]
    by_cases h1 : x < y
    · have h2 : ¬ y < x := by omega
      have h3 : ¬ x = y := by omega
      simp [h1, h2, h3]
    · by_cases h3 : x = y
      · simp [h3]
      · have h2 : y < x := by omega
        simp only [List.takeWhile_cons, List.dropWhile_cons, h2, decide_true, if_true, if_neg h1,
          if_neg h3, List.cons_append]
        rw [ih]

/-- The set of a list's members, increasing, by insertion: `Fmt.listOf` without deep recursion. Its
steps grow with the square of the length. The sort below calls it only if a bound on the sort's
own steps is too small. The bounds that `listOfT` gives are meant to be large enough. No theorem
says so, and none is needed: the result is the same. -/
def slowList (l : List Nat) : List Nat := l.foldr insertT []

/-- `slowList` equals `Fmt.listOf`. -/
theorem slowList_eq (l : List Nat) : slowList l = Fmt.listOf l := by
  have e : insertT = Fmt.insertIntoIncreasingList := by
    funext x l
    exact insertT_eq x l
  unfold slowList Fmt.listOf
  rw [e]

/-- x stands before y: x < y if `up`, and y < x otherwise. -/
def Bef (up : Bool) (x y : Nat) : Prop := if up then x < y else y < x

/-- The test for `Bef`. -/
def bef (up : Bool) (x y : Nat) : Bool := if up then decide (x < y) else decide (y < x)

/-- The test says what `Bef` says. -/
theorem bef_iff (up : Bool) (x y : Nat) : bef up x y = true ↔ Bef up x y := by
  cases up <;> simp [bef, Bef]

/-- x stands before y one way exactly if y stands before x the other way. -/
theorem Bef.flip {up : Bool} {x y : Nat} : Bef (!up) x y ↔ Bef up y x := by
  cases up <;> simp [Bef]

/-- `Bef up` is transitive. -/
theorem Bef.trans {up : Bool} {x y z : Nat} (h1 : Bef up x y) (h2 : Bef up y z) : Bef up x z := by
  cases up <;> simp only [Bef] at h1 h2 ⊢ <;> simp at h1 h2 ⊢ <;> omega

/-- Of two different numbers one stands before the other. -/
theorem Bef.other {up : Bool} {x y : Nat} (h1 : x ≠ y) (h2 : ¬ Bef up x y) : Bef up y x := by
  cases up <;> simp only [Bef] at h2 ⊢ <;> simp at h2 ⊢ <;> omega

/-- Let a be sorted one way, and acc the other way, with all its members before those of a. Then a
reversed onto acc is sorted the other way and has the members of both. -/
theorem reverseAux_sorted (up : Bool) : ∀ (a acc : List Nat), a.Pairwise (Bef up) →
    acc.Pairwise (Bef (!up)) → (∀ c ∈ acc, ∀ x ∈ a, Bef up c x) →
    (a.reverseAux acc).Pairwise (Bef (!up)) ∧ ∀ z, z ∈ a.reverseAux acc ↔ z ∈ acc ∨ z ∈ a
  | [], acc, _, hc, _ => ⟨hc, fun z => by simp [List.reverseAux]⟩
  | x :: a, acc, ha, hc, hb => by
    have ha' := List.pairwise_cons.1 ha
    obtain ⟨p, m⟩ := reverseAux_sorted up a (x :: acc) ha'.2
      (List.pairwise_cons.2 ⟨fun c h => Bef.flip.2 (hb c h x List.mem_cons_self), hc⟩)
      (fun c h w hw => by
        rcases List.mem_cons.1 h with e | h'
        · rw [e]
          exact ha'.1 w hw
        · exact hb c h' w (List.mem_cons_of_mem _ hw))
    refine ⟨p, fun z => ?_⟩
    show z ∈ a.reverseAux (x :: acc) ↔ _
    rw [m, List.mem_cons, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

/-- An increasing list as it is if `up`, and reversed otherwise. -/
def orient (up : Bool) (l : List Nat) : List Nat := if up then l else l.reverse

/-- An increasing list, oriented, is sorted that way and has the same members. -/
theorem orient_sorted (up : Bool) (l : List Nat) (h : l.Pairwise (· < ·)) :
    (orient up l).Pairwise (Bef up) ∧ ∀ z, z ∈ orient up l ↔ z ∈ l := by
  cases up
  · refine ⟨?_, fun z => by simp [orient]⟩
    show l.reverse.Pairwise (Bef false)
    rw [List.pairwise_reverse]
    exact h.imp fun h' => by simpa [Bef] using h'
  · exact ⟨h.imp fun h' => by simpa [Bef] using h', fun z => by simp [orient]⟩

/-- Merges two lists that are sorted one way (increasing if `up`), drops repeats, and puts each
member in front of acc. acc is to be sorted the other way, with all its members before those of
both lists; then so is the result. The number bounds the steps. If it is too small, `slowList` does
the rest: slowly, with the same result. -/
def mergeRev (up : Bool) : Nat → List Nat → List Nat → List Nat → List Nat
  | 0, a, b, acc => orient (!up) (slowList (a ++ (b ++ acc)))
  | _ + 1, [], b, acc => b.reverseAux acc
  | _ + 1, x :: a, [], acc => (x :: a).reverseAux acc
  | f + 1, x :: a, y :: b, acc =>
    if x = y then mergeRev up f a b (x :: acc)
    else if bef up x y then mergeRev up f a (y :: b) (x :: acc)
    else mergeRev up f (x :: a) b (y :: acc)

/-- What `mergeRev` gives is sorted the other way and has the members of all three lists. -/
theorem mergeRev_sorted (up : Bool) : ∀ (f : Nat) (a b acc : List Nat),
    a.Pairwise (Bef up) → b.Pairwise (Bef up) → acc.Pairwise (Bef (!up)) →
    (∀ c ∈ acc, ∀ x ∈ a, Bef up c x) → (∀ c ∈ acc, ∀ x ∈ b, Bef up c x) →
    (mergeRev up f a b acc).Pairwise (Bef (!up)) ∧
      ∀ z, z ∈ mergeRev up f a b acc ↔ z ∈ acc ∨ z ∈ a ∨ z ∈ b
  | 0, a, b, acc, _, _, _, _, _ => by
    obtain ⟨p, m⟩ := orient_sorted (!up) _ (Fmt.listOf_incr (a ++ (b ++ acc)))
    rw [mergeRev, slowList_eq]
    refine ⟨p, fun z => ?_⟩
    rw [m, Fmt.listOf_mem, List.mem_append, List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  | f + 1, [], b, acc, _, hb, hc, _, hcb => by
    obtain ⟨p, m⟩ := reverseAux_sorted up b acc hb hc hcb
    exact ⟨p, fun z => by rw [mergeRev, m]; simp⟩
  | f + 1, x :: a, [], acc, ha, _, hc, hca, _ => by
    obtain ⟨p, m⟩ := reverseAux_sorted up (x :: a) acc ha hc hca
    exact ⟨p, fun z => by rw [mergeRev, m]; simp⟩
  | f + 1, x :: a, y :: b, acc, ha, hb, hc, hca, hcb => by
    have ha' := List.pairwise_cons.1 ha
    have hb' := List.pairwise_cons.1 hb
    have accX : (x :: acc).Pairwise (Bef (!up)) :=
      List.pairwise_cons.2 ⟨fun c h => Bef.flip.2 (hca c h x List.mem_cons_self), hc⟩
    have accY : (y :: acc).Pairwise (Bef (!up)) :=
      List.pairwise_cons.2 ⟨fun c h => Bef.flip.2 (hcb c h y List.mem_cons_self), hc⟩
    have xa : ∀ c ∈ x :: acc, ∀ w ∈ a, Bef up c w := fun c h w hw => by
      rcases List.mem_cons.1 h with e | h'
      · rw [e]
        exact ha'.1 w hw
      · exact hca c h' w (List.mem_cons_of_mem _ hw)
    have yb : ∀ c ∈ y :: acc, ∀ w ∈ b, Bef up c w := fun c h w hw => by
      rcases List.mem_cons.1 h with e | h'
      · rw [e]
        exact hb'.1 w hw
      · exact hcb c h' w (List.mem_cons_of_mem _ hw)
    rw [mergeRev]
    by_cases h0 : x = y
    · rw [if_pos h0]
      obtain ⟨p, m⟩ := mergeRev_sorted up f a b (x :: acc) ha'.2 hb'.2 accX xa
        (fun c h w hw => by
          rcases List.mem_cons.1 h with e | h'
          · rw [e, h0]
            exact hb'.1 w hw
          · exact hcb c h' w (List.mem_cons_of_mem _ hw))
      refine ⟨p, fun z => ?_⟩
      rw [m]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | h | h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inl h
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rintro (h | (h | h) | (h | h))
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl (Or.inl (by rw [h, h0]))
        · exact Or.inr (Or.inr h)
    · rw [if_neg h0]
      by_cases h1 : bef up x y = true
      · rw [if_pos h1]
        have hxy := (bef_iff up x y).1 h1
        obtain ⟨p, m⟩ := mergeRev_sorted up f a (y :: b) (x :: acc) ha'.2 hb accX xa
          (fun c h w hw => by
            rcases List.mem_cons.1 h with e | h'
            · rw [e]
              rcases List.mem_cons.1 hw with e' | hw'
              · rw [e']
                exact hxy
              · exact hxy.trans (hb'.1 w hw')
            · exact hcb c h' w hw)
        refine ⟨p, fun z => ?_⟩
        rw [m]
        simp only [List.mem_cons]
        constructor
        · rintro ((h | h) | h | h)
          · exact Or.inr (Or.inl (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inr h))
          · exact Or.inr (Or.inr h)
        · rintro (h | (h | h) | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · rw [if_neg h1]
        have hyx : Bef up y x := Bef.other h0 fun h => h1 ((bef_iff up x y).2 h)
        obtain ⟨p, m⟩ := mergeRev_sorted up f (x :: a) b (y :: acc) ha hb'.2 accY
          (fun c h w hw => by
            rcases List.mem_cons.1 h with e | h'
            · rw [e]
              rcases List.mem_cons.1 hw with e' | hw'
              · rw [e']
                exact hyx
              · exact hyx.trans (ha'.1 w hw')
            · exact hca c h' w hw) yb
        refine ⟨p, fun z => ?_⟩
        rw [m]
        simp only [List.mem_cons]
        constructor
        · rintro ((h | h) | h | h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inr h))
        · rintro (h | h | (h | h))
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inr h)

/-- Unites the lists of a list two by two and puts the unions in front of acc. The lists are sorted
one way, the unions the other way. A last list without a partner is reversed. n bounds the steps
of each union. -/
def pairLoop (up : Bool) (n : Nat) : List (List Nat) → List (List Nat) → List (List Nat)
  | a :: b :: rest, acc => pairLoop up n rest (mergeRev up n a b [] :: acc)
  | [a], acc => a.reverseAux [] :: acc
  | [], acc => acc

/-- If all lists are sorted one way and those of acc the other way, all that `pairLoop` gives are
sorted the other way, and they have the same members. -/
theorem pairLoop_sorted (up : Bool) (n : Nat) : ∀ (runs acc : List (List Nat)),
    (∀ r ∈ runs, r.Pairwise (Bef up)) → (∀ r ∈ acc, r.Pairwise (Bef (!up))) →
    (∀ r ∈ pairLoop up n runs acc, r.Pairwise (Bef (!up))) ∧
      ∀ z, (∃ r ∈ pairLoop up n runs acc, z ∈ r) ↔ (∃ r ∈ runs, z ∈ r) ∨ ∃ r ∈ acc, z ∈ r
  | [], acc, _, ha => ⟨ha, fun z => by simp [pairLoop]⟩
  | [a], acc, hr, ha => by
    obtain ⟨p, m⟩ := reverseAux_sorted up a [] (hr a List.mem_cons_self) List.Pairwise.nil
      fun _ h => by cases h
    refine ⟨fun r h => ?_, fun z => ?_⟩
    · rcases List.mem_cons.1 h with e | h'
      · rw [e]
        exact p
      · exact ha r h'
    · simp [pairLoop]
  | a :: b :: rest, acc, hr, ha => by
    obtain ⟨pu, mu⟩ := mergeRev_sorted up n a b [] (hr a List.mem_cons_self)
      (hr b (List.mem_cons_of_mem _ List.mem_cons_self)) List.Pairwise.nil
      (fun _ h => by cases h) (fun _ h => by cases h)
    obtain ⟨p, m⟩ := pairLoop_sorted up n rest (mergeRev up n a b [] :: acc)
      (fun r h => hr r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
      (fun r h => by
        rcases List.mem_cons.1 h with e | h'
        · rw [e]
          exact pu
        · exact ha r h')
    refine ⟨p, fun z => ?_⟩
    rw [pairLoop, m]
    simp only [List.mem_cons, exists_eq_or_imp, mu, List.not_mem_nil, false_or]
    constructor
    · rintro (h | (h | h) | h)
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inr h
    · rintro ((h | h | h) | h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- Unites the lists of a list into one increasing list: two by two, again and again. `up` says
which way the lists are sorted, and it turns at each pass. n bounds the steps of each union. The
second number bounds the passes; the number of the lists is more than enough. If it were too small,
`slowList` would do the rest. -/
def sortLoop (n : Nat) : Nat → Bool → List (List Nat) → List Nat
  | _, _, [] => []
  | _, up, [a] => if up then a else a.reverseAux []
  | 0, _, a :: b :: rest => slowList (a :: b :: rest).flatten
  | f + 1, up, a :: b :: rest => sortLoop n f (!up) (pairLoop up n (a :: b :: rest) [])

/-- The union of lists that are sorted one way increases and has all their members. -/
theorem sortLoop_incr (n : Nat) : ∀ (f : Nat) (up : Bool) (runs : List (List Nat)),
    (∀ r ∈ runs, r.Pairwise (Bef up)) →
    (sortLoop n f up runs).Pairwise (· < ·) ∧ ∀ z, z ∈ sortLoop n f up runs ↔ ∃ r ∈ runs, z ∈ r
  | 0, _, [], _ => ⟨List.Pairwise.nil, fun z => by simp [sortLoop]⟩
  | _ + 1, _, [], _ => ⟨List.Pairwise.nil, fun z => by simp [sortLoop]⟩
  | 0, up, [a], hr => one up a (hr a List.mem_cons_self) 0
  | f + 1, up, [a], hr => one up a (hr a List.mem_cons_self) (f + 1)
  | 0, _, a :: b :: rest, _ => by
    rw [sortLoop, slowList_eq]
    refine ⟨Fmt.listOf_incr _, fun z => ?_⟩
    rw [Fmt.listOf_mem, List.mem_flatten]
  | f + 1, up, a :: b :: rest, hr => by
    obtain ⟨pp, mp⟩ := pairLoop_sorted up n (a :: b :: rest) [] hr fun _ h => by cases h
    obtain ⟨p, m⟩ := sortLoop_incr n f (!up) (pairLoop up n (a :: b :: rest) []) pp
    exact ⟨p, fun z => by rw [sortLoop, m, mp]; simp⟩
where
  /-- The case of one list. -/
  one (up : Bool) (a : List Nat) (h : a.Pairwise (Bef up)) (f : Nat) :
      (sortLoop n f up [a]).Pairwise (· < ·) ∧ ∀ z, z ∈ sortLoop n f up [a] ↔ ∃ r ∈ [a], z ∈ r := by
    have e : sortLoop n f up [a] = if up then a else a.reverseAux [] := by
      cases f <;> rfl
    rw [e]
    cases up
    · obtain ⟨p, m⟩ := reverseAux_sorted false a [] h List.Pairwise.nil fun _ h' => by cases h'
      refine ⟨p.imp fun h' => by simpa [Bef] using h', fun z => ?_⟩
      simp
    · exact ⟨h.imp fun h' => by simpa [Bef] using h', fun z => by simp⟩

/-- An increasing list is determined by its members. -/
theorem eq_of_incr : ∀ (l1 l2 : List Nat), l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ z, z ∈ l1 ↔ z ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).2 List.mem_cons_self) List.not_mem_nil
  | x :: _, [], _, _, h => absurd ((h x).1 List.mem_cons_self) List.not_mem_nil
  | x :: t1, y :: t2, h1, h2, h => by
    have p1 := List.pairwise_cons.1 h1
    have p2 := List.pairwise_cons.1 h2
    have hxy : x = y := by
      rcases List.mem_cons.1 ((h x).1 List.mem_cons_self) with e | a'
      · exact e
      · rcases List.mem_cons.1 ((h y).2 List.mem_cons_self) with e | b'
        · exact e.symm
        · have u := p2.1 x a'
          have v := p1.1 y b'
          omega
    subst hxy
    have ht : t1 = t2 := eq_of_incr t1 t2 p1.2 p2.2 fun z => by
      constructor
      · intro hz
        rcases List.mem_cons.1 ((h z).1 (List.mem_cons_of_mem _ hz)) with e | h'
        · have u := p1.1 z hz
          omega
        · exact h'
      · intro hz
        rcases List.mem_cons.1 ((h z).2 (List.mem_cons_of_mem _ hz)) with e | h'
        · have u := p2.1 z hz
          omega
        · exact h'
    rw [ht]

/-- The list of a round: the set of the drawn positions, increasing (format page, R6.6). Openings
go by this list: a position that is drawn twice is opened once. What is done once for each draw
goes by the draws themselves. `Fmt.listOf` puts each draw into its place in an increasing list, so
its steps grow with the square of the number of draws. Here each draw is a list of one member, and
the lists are united two by two until one is left: a merge sort that drops repeats. All its
functions call themselves last, so the compiled program needs little stack. All are defined by
recursion on a list or on a number, so Lean's kernel can evaluate them in a proof by `decide`.
Counterpart: PositionList::from_draws in blocks/tree/positions.h. -/
def listOfT (l : List Nat) : List Nat :=
  sortLoop l.length l.length true (l.map fun x => [x])

/-- `listOfT` equals `Fmt.listOf`: both are increasing and have the draws as their members. -/
theorem listOfT_eq (l : List Nat) : listOfT l = Fmt.listOf l := by
  obtain ⟨p, m⟩ := sortLoop_incr l.length l.length true (l.map fun x => [x]) fun r h => by
    obtain ⟨x, _, e⟩ := List.mem_map.1 h
    rw [← e]
    exact List.pairwise_singleton _ _
  refine eq_of_incr _ _ p (Fmt.listOf_incr l) fun z => ?_
  rw [listOfT, m, Fmt.listOf_mem l z]
  constructor
  · rintro ⟨r, hr, hz⟩
    obtain ⟨x, hx, e⟩ := List.mem_map.1 hr
    rw [← e] at hz
    rw [List.mem_singleton.1 hz]
    exact hx
  · intro hz
    exact ⟨[z], List.mem_map.2 ⟨z, hz, rfl⟩, List.mem_singleton.2 rfl⟩

/-- Appends n entries from the words ws to acc, 32 from each word; what is left of the last word
that is used is dropped. If ws has too few words for n entries, fewer are appended. -/
def tritsLoop : List UInt64 → Nat → Array Int → List Int
  | [], _, acc => acc.toList
  | w :: ws, n, acc =>
    tritsLoop ws (n - 32) (acc ++ (List.range (min n 32)).map (Fmt.tritAt w))

/-- `tritsLoop` returns the members of acc followed by what `Fmt.tritsOf` returns. -/
theorem tritsLoop_eq : ∀ (ws : List UInt64) (n : Nat) (acc : Array Int),
    tritsLoop ws n acc = acc.toList ++ Fmt.tritsOf ws n
  | [], _, acc => by simp [tritsLoop, Fmt.tritsOf]
  | w :: ws, n, acc => by
    rw [tritsLoop, tritsLoop_eq ws, Fmt.tritsOf]
    simp [List.append_assoc]

/-- n entries from a list of words: `Fmt.tritsOf` as a loop. -/
def tritsT (ws : List UInt64) (n : Nat) : List Int := tritsLoop ws n #[]

/-- `tritsT` equals `Fmt.tritsOf`. -/
theorem tritsT_eq (ws : List UInt64) (n : Nat) : tritsT ws n = Fmt.tritsOf ws n := by
  unfold tritsT
  rw [tritsLoop_eq]
  rfl

/-- n entries of a matrix over {-1, 0, 1}: `Fmt.drawTrits` without deep recursion. -/
def drawTritsT (n : Nat) : Dr (List Int) := fun row c =>
  (tritsT (wordsT row c ((n + 31) / 32)) n, c + (n + 31) / 32)

/-- `drawTritsT` equals `Fmt.drawTrits`. -/
theorem drawTritsT_eq (n : Nat) : drawTritsT n = Fmt.drawTrits n := by
  funext row c
  show _ = (Fmt.tritsOf (Dr.word.times ((n + 31) / 32) row c).1 n,
    (Dr.word.times ((n + 31) / 32) row c).2)
  rw [times_word]
  unfold drawTritsT
  rw [tritsT_eq]

/-- The verifier's message of a round: `Fmt.drawRound` with the positions drawn by `drawPossT`, the
elements by `drawElemsT`, the matrix entries by `drawTritsT` and the seal by `drawDigestT`. The
order is that of `Fmt.drawRoundD`: positions, elements, matrix entries, seal. -/
def drawRoundT (f : Fld) (e : Entry) (k : Kind) (row : Row) : Drawn :=
  (((drawPossT e.logN e.poss).bind fun ps => (drawElemsT f e k).bind fun es =>
    (drawTritsT e.trits).bind fun ts => (drawDigestT k).bind fun d =>
      Dr.pure ⟨es, ps, ts, d⟩) row 0).1

/-- `drawRoundT` equals `Fmt.drawRound`. -/
theorem drawRoundT_eq (f : Fld) (e : Entry) (k : Kind) (row : Row) :
    drawRoundT f e k row = Fmt.drawRound f e k row := by
  unfold drawRoundT
  rw [drawTritsT_eq, drawPossT_eq, drawElemsT_eq, drawDigestT_eq]
  rfl

end OnBytes
