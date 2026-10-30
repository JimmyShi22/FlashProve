-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/WalkPaths.lean: the whole paths that the whole-path parser (Run/ParseFull.lean: `pathFrom`,
`seenAt`) reads off the record of vertices of a pruned walk, climbed one by one, lead to the root to
which the pruned walk leads, under the hypotheses below.

Definitions, lemmas with their proofs; no Spec. The first part is generic in the type of digests and
the node function (it uses `level_id`, Run/WalkTieProofs.lean, and Hash/Octopus.lean); the second is
at byte strings and the format's reader of an opening (`readOpeningW`, Fmt/Rules7.lean).
The file is about openings of several leaves of one Merkle tree. A pruned walk computes a root from
the opened leaves' digests and one list of sibling digests (the message), level by level (`octF`,
Hash/OctopusFacts.lean). A whole path is the authentication path of one leaf.

Main names:
  `opening_paths`: readOpeningW h cfg f salt sh start xs b i = some o, h's answers of the right
    length, the given digests of 32 bytes ⇒ for every listed position x with its leaf's digest:
    pathFrom sh.a o.seen x = some (p as digests); p has sh.a entries of 32 bytes; octF (the vertex
    hash) sh.a [x] [the leaf's digest] p = [o.root].
Limits: this file says nothing on a root that was sent: o.root is the computed one. It says nothing
on soundness (index binding included), what a root fixes, opening-form binding, no two openings of
a commitment, correctness of extraction or whatever else names a committer or a prover: these are
identities of computations. -/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.WalkTieProofs
import Run.ParseFull
import Run.Toy1TieTree

set_option autoImplicit false

namespace Run.WalkTie
open Octopus

section
variable {D : Type} [Inhabited D] (hN : D → D → D)

/-- The table of one level of the pruned walk: the vertices that have an opened leaf below them,
with their values; then the vertices whose values the message gives. -/
def lvTab (js : List ℕ) (v s : List D) : List (ℕ × D) :=
  js.zip v ++ (note1 0 js s).map fun n => (n.2.1, n.2.2)

omit [Inhabited D] in
theorem sibOf_half (i : ℕ) : sibOf i / 2 = i / 2 := by
  unfold sibOf
  split <;> omega

omit [Inhabited D] in
theorem sibOf_ne (i : ℕ) : sibOf i ≠ i := by
  unfold sibOf
  split <;> omega

/-- Every key of a level's table is a vertex of the level or the sibling of one (the two have one
parent). -/
theorem lvTab_block : ∀ (js : List ℕ) (v s : List D), ∀ e ∈ lvTab js v s, ∃ j ∈ js, e.1 / 2 = j / 2
  | [], v, s, e, he => by simp [lvTab, note1] at he
  | [i], v, s, e, he => by
    simp only [lvTab, note1, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact ⟨e.1, (List.of_mem_zip he).1, rfl⟩
    · exact ⟨i, List.mem_singleton.2 rfl, sibOf_half i⟩
  | i :: j :: l, v, s, e, he => by
    simp only [lvTab, List.mem_append, List.mem_map] at he
    rcases he with he | ⟨n, hn, rfl⟩
    · exact ⟨e.1, (List.of_mem_zip he).1, rfl⟩
    · by_cases hs : sib i j
      · rw [note1, if_pos hs] at hn
        obtain ⟨k, hk, h2⟩ := lvTab_block l v.tail.tail s (n.2.1, n.2.2)
          (by simp only [lvTab, List.mem_append, List.mem_map]; exact Or.inr ⟨n, hn, rfl⟩)
        exact ⟨k, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk), h2⟩
      · rw [note1, if_neg hs] at hn
        rcases List.mem_cons.1 hn with rfl | hn
        · exact ⟨i, List.mem_cons_self .., sibOf_half i⟩
        · obtain ⟨k, hk, h2⟩ := lvTab_block (j :: l) v.tail s.tail (n.2.1, n.2.2)
            (by simp only [lvTab, List.mem_append, List.mem_map]; exact Or.inr ⟨n, hn, rfl⟩)
          exact ⟨k, List.mem_cons_of_mem _ hk, h2⟩


theorem mem_lvTab_sib (i j : ℕ) (l : List ℕ) (a b : D) (v s : List D) (hs : sib i j) (e : ℕ × D) :
    e ∈ lvTab (i :: j :: l) (a :: b :: v) s ↔ e = (i, a) ∨ e = (j, b) ∨ e ∈ lvTab l v s := by
  simp only [lvTab, note1, if_pos hs, List.zip_cons_cons, List.cons_append, List.mem_cons]

theorem mem_lvTab_lone (i j : ℕ) (l : List ℕ) (a x : D) (v g : List D)
    (hs : ¬ sib i j) (e : ℕ × D) :
    e ∈ lvTab (i :: j :: l) (a :: v) (x :: g) ↔
    e = (i, a) ∨ e = (sibOf i, x) ∨ e ∈ lvTab (j :: l) v g := by
  simp only [lvTab, note1, if_neg hs, List.zip_cons_cons, List.cons_append, List.mem_cons,
    List.mem_append, List.map_cons, List.headD_cons, List.tail_cons]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

/-- One level of the pruned walk, for js strictly increasing, v of js's length and s long enough: no
vertex has two values in the level's table; each vertex of the level has its sibling in the table,
and the two make the parent's value in the next level. -/
theorem level_ok :
    ∀ (js : List ℕ) (v s : List D), js.Pairwise (· < ·) →
      v.length = js.length → need1 js ≤ s.length →
      (∀ e ∈ lvTab js v s, ∀ e' ∈ lvTab js v s, e.1 = e'.1 → e.2 = e'.2) ∧
      ∀ e ∈ js.zip v, ∃ b,
        (sibOf e.1, b) ∈ lvTab js v s ∧
        (e.1 / 2, loneF hN e.1 e.2 b) ∈ (up js).zip (stepF hN js v s)
  | [], _, _, _, _, _ => ⟨fun e he => by simp [lvTab, note1] at he, fun e he => by simp at he⟩
  | [i], [a], x :: g, _, _, _ => by
    have hm : ∀ e, e ∈ lvTab [i] [a] (x :: g) ↔ e = (i, a) ∨ e = (sibOf i, x) :=
      fun e => by simp [lvTab, note1]
    refine ⟨fun e he e' he' hk => ?_, fun e he => ?_⟩
    · rcases (hm e).1 he with rfl | rfl <;> rcases (hm e').1 he' with rfl | rfl
      · rfl
      · exact absurd hk.symm (sibOf_ne i)
      · exact absurd hk (sibOf_ne i)
      · rfl
    · have : e = (i, a) := by simpa using he
      subst this
      exact ⟨x, (hm _).2 (Or.inr rfl),
        by show _ ∈ [(i / 2, loneF hN i a x)]; exact List.mem_singleton.2 rfl⟩
  | i :: j :: l, a :: b :: v, s, hp, hv, hn => by
    have hij : i < j := (List.pairwise_cons.1 hp).1 j (List.mem_cons_self ..)
    have hpj : (j :: l).Pairwise (· < ·) := (List.pairwise_cons.1 hp).2
    by_cases hs : sib i j
    · obtain ⟨he2, rfl⟩ := hs
      have hs : sib i (i + 1) := ⟨he2, rfl⟩
      have hpl : l.Pairwise (· < ·) := (List.pairwise_cons.1 hpj).2
      have hbig : ∀ k ∈ l, i / 2 < k / 2 :=
        fun k hk => by have := (List.pairwise_cons.1 hpj).1 k hk; omega
      obtain ⟨U, P⟩ := level_ok l v s hpl (by simpa using hv) (by simpa [need1, if_pos hs] using hn)
      have hblk : ∀ e ∈ lvTab l v s, i / 2 < e.1 / 2 :=
        fun e he => by obtain ⟨k, hk, h2⟩ := lvTab_block l v s e he; rw [h2]; exact hbig k hk
      have hup : (up (i :: (i + 1) :: l)).zip (stepF hN (i :: (i + 1) :: l) (a :: b :: v) s) =
          (i / 2, hN a b) :: (up l).zip (stepF hN l v s) := by
        simp only [up, if_pos hs, stepF, stepC]
        rfl
      refine ⟨fun e he e' he' hk => ?_, fun e he => ?_⟩
      · rcases (mem_lvTab_sib i (i + 1) l a b v s hs e).1 he with rfl | rfl | he
          <;> rcases (mem_lvTab_sib i (i + 1) l a b v s hs e').1 he' with rfl | rfl | he'
        · rfl
        · exact absurd hk (by show i ≠ i + 1; omega)
        · have := hblk e' he'; rw [← hk] at this; exact absurd this (lt_irrefl _)
        · exact absurd hk (by show i + 1 ≠ i; omega)
        · rfl
        · have := hblk e' he'; rw [← hk] at this; exact absurd this (by show ¬ (i / 2 < (i + 1) / 2); omega)
        · have := hblk e he; rw [hk] at this; exact absurd this (lt_irrefl _)
        · have := hblk e he; rw [hk] at this; exact absurd this (by show ¬ (i / 2 < (i + 1) / 2); omega)
        · exact U e he e' he' hk
      · rw [hup]
        rcases List.mem_cons.1
          (by simpa using he : e ∈ (i, a) :: (i + 1, b) :: l.zip v) with rfl | he
        · refine ⟨b,
            (mem_lvTab_sib i (i + 1) l a b v s hs _).2
              (Or.inr (Or.inl (by show (sibOf i, b) = (i + 1, b); rw [sibOf, if_pos he2]))),
            List.mem_cons.2 (Or.inl ?_)⟩
          show (i / 2, loneF hN i a b) = _
          rw [loneF, if_pos he2]
        · rcases List.mem_cons.1 he with rfl | he
          · have ho : ¬ ((i + 1) % 2 = 0) := by omega
            refine ⟨a,
              (mem_lvTab_sib i (i + 1) l a b v s hs _).2
                (Or.inl (by show (sibOf (i + 1), a) = (i, a); rw [sibOf, if_neg ho]; rfl)),
              List.mem_cons.2 (Or.inl ?_)⟩
            show ((i + 1) / 2, loneF hN (i + 1) b a) = _
            rw [loneF, if_neg ho, show (i + 1) / 2 = i / 2 by omega]
          · obtain ⟨c, h1, h2⟩ := P e he
            exact ⟨c, (mem_lvTab_sib i (i + 1) l a b v s hs _).2 (Or.inr (Or.inr h1)),
              List.mem_cons_of_mem _ h2⟩
    · cases s with
      | nil => simp [need1, if_neg hs] at hn
      | cons x g =>
        have hbig : ∀ k ∈ j :: l, i / 2 < k / 2 := fun k hk => by
          have h1 : i < k := (List.pairwise_cons.1 hp).1 k hk
          have h2 : j ≤ k := by
            rcases List.mem_cons.1 hk with rfl | hk
            · exact le_refl _
            · exact le_of_lt ((List.pairwise_cons.1 hpj).1 k hk)
          have h3 : ¬ (i % 2 = 0 ∧ j = i + 1) := hs
          omega
        obtain ⟨U, P⟩ := level_ok (j :: l) (b :: v) g hpj (by simpa using hv)
          (by simp only [need1, if_neg hs, List.length_cons] at hn; omega)
        have hblk : ∀ e ∈ lvTab (j :: l) (b :: v) g, i / 2 < e.1 / 2 :=
          fun e he => by
            obtain ⟨k, hk, h2⟩ := lvTab_block (j :: l) (b :: v) g e he; rw [h2]; exact hbig k hk
        have hup : (up (i :: j :: l)).zip (stepF hN (i :: j :: l) (a :: b :: v) (x :: g)) =
            (i / 2, loneF hN i a x) :: (up (j :: l)).zip (stepF hN (j :: l) (b :: v) g) := by
          simp only [up, if_neg hs, stepF, stepC]
          rfl
        refine ⟨fun e he e' he' hk => ?_, fun e he => ?_⟩
        · rcases (mem_lvTab_lone i j l a x (b :: v) g hs e).1 he with rfl | rfl | he
            <;> rcases (mem_lvTab_lone i j l a x (b :: v) g hs e').1 he' with rfl | rfl | he'
          · rfl
          · exact absurd hk.symm (sibOf_ne i)
          · have := hblk e' he'; rw [← hk] at this; exact absurd this (lt_irrefl _)
          · exact absurd hk (sibOf_ne i)
          · rfl
          · have := hblk e' he'; rw [← hk] at this; exact absurd this (by show ¬ (i / 2 < sibOf i / 2); rw [sibOf_half]; exact lt_irrefl _)
          · have := hblk e he; rw [hk] at this; exact absurd this (lt_irrefl _)
          · have := hblk e he; rw [hk] at this; exact absurd this (by show ¬ (i / 2 < sibOf i / 2); rw [sibOf_half]; exact lt_irrefl _)
          · exact U e he e' he' hk
        · rw [hup]
          rcases List.mem_cons.1
            (by simpa using he : e ∈ (i, a) :: (j :: l).zip (b :: v)) with rfl | he
          · exact ⟨x, (mem_lvTab_lone i j l a x (b :: v) g hs _).2 (Or.inr (Or.inl rfl)),
              List.mem_cons_self ..⟩
          · obtain ⟨c, h1, h2⟩ := P e he
            exact ⟨c, (mem_lvTab_lone i j l a x (b :: v) g hs _).2 (Or.inr (Or.inr h1)),
              List.mem_cons_of_mem _ h2⟩


/-! ### The walk's whole output -/

/-- The vertices passed, as the walk lists them: the levels nearer the root in front. -/
def metAll : ℕ → List ℕ → List D → List D → List (ℕ × ℕ × D)
  | 0, js, v, _ => (js.zip v).map fun e => (0, e.1, e.2)
  | d + 1, js, v, s =>
    metAll d (up js) (stepF hN js v s) (s.drop (need1 js)) ++
      (js.zip v).map fun e => (d + 1, e.1, e.2)

/-- The given vertices, as the walk notes them. -/
def noteAll : ℕ → List ℕ → List D → List (ℕ × ℕ × D)
  | 0, _, _ => []
  | d + 1, js, s => noteAll d (up js) (s.drop (need1 js)) ++ (note1 (d + 1) js s).reverse

/-- The whole walk: all that `Fmt.walkW` hands out: the root, what is left of the message, the given
vertices noted, the vertices passed (Run/WalkTieProofs.lean's `walk_id` has the first two). -/
theorem walk_full :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D) (acc met : List (ℕ × ℕ × D)), v.length = js.length →
      need d js ≤ s.length → (upN d js).length = 1 →
      Fmt.walkW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d (js.zip v) (s, acc) met =
        some ((octF hN d js v s).headD default,
            (s.drop (need d js), noteAll d js s ++ acc),
            metAll hN d js v s ++ met)
  | 0, [i], [r], s, acc, met, _, _, _ => rfl
  | d + 1, js, v, s, acc, met, hv, hs, hu => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hs
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hs
      omega
    simp only [Fmt.walkW]
    rw [level_id hN (d + 1) js v s acc hv h1]
    show Fmt.walkW (m := Id) (fun _ _ l r => hN l r) Fmt.takeGiven d ((up js).zip (stepF hN js v s))
        (s.drop (need1 js), _) _ = _
    rw [walk_full d (up js) (stepF hN js v s) (s.drop (need1 js)) _ _
          (length_stepF hN js v s) h2 hu, List.drop_drop]
    simp only [metAll, noteAll, List.append_assoc]
    rfl

/-- The depth in a level's notes is a tag. -/
theorem note1_tag (d : ℕ) :
    ∀ (js : List ℕ) (s : List D), note1 d js s = (note1 0 js s).map fun n => (d, n.2.1, n.2.2)
  | [], _ => rfl
  | [_], _ => rfl
  | i :: j :: l, s => by
    by_cases hs : sib i j
    · simp only [note1, if_pos hs]
      exact note1_tag d l s
    · simp only [note1, if_neg hs, List.map_cons]
      rw [note1_tag d (j :: l) s.tail]

/-- A vertex with its value is in the table of the level d' of the walk that starts at depth d.
-/
def InLv : ℕ → List ℕ → List D → List D → ℕ → ℕ × D → Prop
  | 0, js, v, _, d', e => d' = 0 ∧ e ∈ js.zip v
  | d + 1, js, v, s, d', e =>
    (d' = d + 1 ∧ e ∈ lvTab js v s) ∨ InLv d (up js) (stepF hN js v s) (s.drop (need1 js)) d' e

theorem InLv_le :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D) (d' : ℕ) (e : ℕ × D), InLv hN d js v s d' e → d' ≤ d
  | 0, _, _, _, _, _, h => le_of_eq h.1
  | d + 1, js, v, s, d', e, h => by
    rcases h with ⟨h, -⟩ | h
    · exact le_of_eq h
    · exact le_trans (InLv_le d _ _ _ d' e h) (Nat.le_succ d)

/-- What the walk hands out as passed and noted is what is in the levels' tables. -/
theorem mem_seen_iff :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D) (x : ℕ × ℕ × D),
      x ∈ metAll hN d js v s ++ noteAll d js s ↔ InLv hN d js v s x.1 (x.2.1, x.2.2)
  | 0, js, v, s, x => by
    simp only [metAll, noteAll, List.append_nil, List.mem_map, InLv]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨rfl, he⟩
    · rintro ⟨h0, he⟩
      exact ⟨_, he, by obtain ⟨a, b, c⟩ := x; cases h0; rfl⟩
  | d + 1, js, v, s, x => by
    have ih := mem_seen_iff d (up js) (stepF hN js v s) (s.drop (need1 js)) x
    simp only [List.mem_append] at ih
    simp only [metAll, noteAll, List.mem_append, List.mem_map, List.mem_reverse, InLv, lvTab, ← ih]
    rw [note1_tag (d + 1) js s]
    simp only [List.mem_map]
    constructor
    · rintro ((h | ⟨e, he, rfl⟩) | (h | ⟨n, hn, rfl⟩))
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨rfl, Or.inl he⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inl ⟨rfl, Or.inr ⟨n, hn, rfl⟩⟩
    · rintro (⟨h0, he | ⟨n, hn, he⟩⟩ | h | h)
      · exact Or.inl (Or.inr ⟨_, he, by obtain ⟨a, b, c⟩ := x; cases h0; rfl⟩)
      · exact Or.inr (Or.inr ⟨n, hn, by obtain ⟨a, b, c⟩ := x; cases h0; cases he; rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)


/-- Under the hypotheses of its statement, no vertex has two values in what the walk hands out. -/
theorem InLv_unique :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D), js.Pairwise (· < ·) → v.length = js.length →
      need d js ≤ s.length → (upN d js).length = 1 →
      ∀ (d' : ℕ) (e e' : ℕ × D),
        InLv hN d js v s d' e → InLv hN d js v s d' e' → e.1 = e'.1 → e.2 = e'.2
  | 0, [i], [r], s, _, _, _, _, d', e, e', h, h', _ => by
    have h1 : e = (i, r) := by simpa using h.2
    have h2 : e' = (i, r) := by simpa using h'.2
    rw [h1, h2]
  | d + 1, js, v, s, hp, hv, hs, hu, d', e, e', h, h', hk => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hs
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hs
      omega
    rcases h with ⟨hd, he⟩ | h <;> rcases h' with ⟨hd', he'⟩ | h'
    · exact (level_ok hN js v s hp hv h1).1 e he e' he' hk
    · have := InLv_le hN d _ _ _ d' e' h'; omega
    · have := InLv_le hN d _ _ _ d' e h; omega
    · exact InLv_unique d (up js) (stepF hN js v s) (s.drop (need1 js)) (pairwise_up js hp)
        (length_stepF hN js v s) h2 hu d' e e' h h' hk

/-- A whole path for the vertex k of the level d: at each level the value that the level's table has
for the sibling. -/
def PathOK : ℕ → List ℕ → List D → List D → ℕ → List D → Prop
  | 0, _, _, _, _, p => p = []
  | d + 1, js, v, s, k, p =>
    ∃ b p',
      p = b :: p' ∧
      (sibOf k, b) ∈ lvTab js v s ∧
      PathOK d (up js) (stepF hN js v s) (s.drop (need1 js)) (k / 2) p'

/-- Under the hypotheses of its statement: climbed alone along such a path, a vertex of the pruned
walk reaches the root to which the pruned walk leads. -/
theorem climb_ok :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D), js.Pairwise (· < ·) → v.length = js.length →
      need d js ≤ s.length → (upN d js).length = 1 →
      ∀ (k : ℕ) (a : D) (p : List D), (k, a) ∈ js.zip v → PathOK hN d js v s k p →
        octF hN d [k] [a] p = [(octF hN d js v s).headD default]
  | 0, [i], [r], s, _, _, _, _, k, a, p, hm, _ => by
    have h1 : (k, a) = (i, r) := by simpa using hm
    cases h1
    rfl
  | d + 1, js, v, s, hp, hv, hs, hu, k, a, p, hm, hpath => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hs
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hs
      omega
    obtain ⟨b, p', rfl, hb, hp'⟩ := hpath
    obtain ⟨U, P⟩ := level_ok hN js v s hp hv h1
    obtain ⟨b0, hb0, hpar⟩ := P (k, a) hm
    have hbb : b0 = b := U _ hb0 _ hb rfl
    subst hbb
    show octF hN d [k / 2] [loneF hN k a b0] p' =
      [(octF hN d (up js) (stepF hN js v s) (s.drop (need1 js))).headD default]
    exact climb_ok d (up js) (stepF hN js v s) (s.drop (need1 js)) (pairwise_up js hp)
      (length_stepF hN js v s) h2 hu (k / 2) _ p' hpar hp'

end
end Run.WalkTie


namespace Run.WalkTie
open Octopus

/-- The value that the record has at a vertex, if the vertex is in it and has one value there.
-/
theorem seenAt_of_mem (seen : List (ℕ × ℕ × ByteArray)) (d p : ℕ) (val : ByteArray)
    (hm : (d, p, val) ∈ seen) (hu : ∀ y ∈ seen, y.1 = d → y.2.1 = p → y.2.2 = val) :
    seenAt seen d p = some val := by
  unfold seenAt
  cases hf : seen.find? (fun v => v.1 == d && v.2.1 == p) with
  | none =>
    have := List.find?_eq_none.1 hf (d, p, val) hm
    simp at this
  | some y =>
    have h1 := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    rw [Option.map_some, hu y (List.mem_of_find?_eq_some hf) h1.1 h1.2]

theorem xor_one (n : ℕ) : n ^^^ 1 = sibOf n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero =>
    unfold sibOf
    by_cases h : n % 2 = 0
    · have h1 : (n + 1) % 2 = 1 := by omega
      simp [Nat.testBit_zero, h, h1]
    · have h1 : n % 2 = 1 := by omega
      have h2 : (n - 1) % 2 = 0 := by omega
      simp [Nat.testBit_zero, h1, h2]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, sibOf_half]
    simp

/-- The whole paths that are read off the record of a pruned walk: for a part of the walk (from
depth d on) all of whose tables stand in the record, and a record in which no vertex has two values;
js strictly increasing, v of js's length, s long enough: the parser's look-ups in the record give
such a path. -/
theorem paths_ind (hN : ByteArray → ByteArray → ByteArray) (seen : List (ℕ × ℕ × ByteArray))
    (hu : ∀ y ∈ seen, ∀ y' ∈ seen, y.1 = y'.1 → y.2.1 = y'.2.1 → y.2.2 = y'.2.2) :
    ∀ (d : ℕ) (js : List ℕ) (v s : List ByteArray), js.Pairwise (· < ·) → v.length = js.length →
      need d js ≤ s.length → (∀ d' e, InLv hN d js v s d' e → (d', e.1, e.2) ∈ seen) →
      ∀ e ∈ js.zip v, ∃ p : List ByteArray,
        (List.range d).mapM (fun t => (seenAt seen (d - t) ((e.1 / 2 ^ t) ^^^ 1)).map bytesToDig) =
          some (p.map bytesToDig) ∧
        PathOK hN d js v s e.1 p ∧
        ∀ q ∈ p, ∃ d' k, (d', k, q) ∈ seen
  | 0, _, _, _, _, _, _, _, _, _ => ⟨[], rfl, rfl, fun q hq => absurd hq (List.not_mem_nil)⟩
  | d + 1, js, v, s, hp, hv, hs, hin, e, he => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hs
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hs
      omega
    obtain ⟨b, hb, hpar⟩ := (level_ok hN js v s hp hv h1).2 e he
    obtain ⟨p', hm, hpk, hq⟩ :=
      paths_ind hN seen hu d (up js) (stepF hN js v s) (s.drop (need1 js)) (pairwise_up js hp)
        (length_stepF hN js v s) h2 (fun d' e' h => hin d' e' (Or.inr h)) _ hpar
    have hbs : (d + 1, sibOf e.1, b) ∈ seen := hin (d + 1) (sibOf e.1, b) (Or.inl ⟨rfl, hb⟩)
    refine ⟨b :: p', ?_, ⟨b, p', rfl, hb, hpk⟩, fun q hq' => ?_⟩
    · rw [List.range_succ_eq_map, List.mapM_cons, List.mapM_map]
      have e0 : seenAt seen (d + 1 - 0) ((e.1 / 2 ^ 0) ^^^ 1) = some b := by
        rw [Nat.sub_zero, Nat.pow_zero, Nat.div_one, xor_one]
        exact seenAt_of_mem seen _ _ b hbs fun y hy h1 h2 => hu y hy _ hbs h1 h2
      have e1 : (fun t =>
            (seenAt seen (d + 1 - (t + 1)) ((e.1 / 2 ^ (t + 1)) ^^^ 1)).map bytesToDig) =
          fun t => (seenAt seen (d - t) (((e.1 / 2) / 2 ^ t) ^^^ 1)).map bytesToDig := by
        funext t
        rw [Nat.add_sub_add_right, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
      rw [e0]
      show (do let y ← some (bytesToDig b); let ys ← (List.range d).mapM ((fun t => (seenAt seen (d + 1 - t) ((e.1 / 2 ^ t) ^^^ 1)).map bytesToDig) ∘ Nat.succ); pure (y :: ys)) = _
      have e2 : ((fun t => (seenAt seen (d + 1 - t) ((e.1 / 2 ^ t) ^^^ 1)).map bytesToDig) ∘
            Nat.succ) =
          fun t => (seenAt seen (d - t) (((e.1 / 2) / 2 ^ t) ^^^ 1)).map bytesToDig := e1
      rw [e2, hm]
      rfl
    · rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨_, _, hbs⟩
      · exact hq q hq'


section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- The root and the record of vertices that the reader of an opening hands out, where it hands out
o (`e`): the root by `octF`, the record by `metAll` and `noteAll`. -/
theorem reader_seen (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ) (sh : Fmt.Shape) (start : ByteArray)
    (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : Fmt.OpenOut)
    (e : Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i = some o) :
    Fmt.listOK sh.a xs = true ∧
    o.cols.length = xs.length ∧
    o.salts.length = xs.length ∧
    o.given.length = need sh.a xs ∧
    o.root = (octF (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs
        (leafV h sh start xs (o.cols.zip o.salts)) o.given).headD default ∧
    o.seen = metAll (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs
          (leafV h sh start xs (o.cols.zip o.salts)) o.given ++
        noteAll sh.a xs o.given := by
  obtain ⟨r1, r2, r3, r4⟩ := reader_id h cfg f salt sh start xs b i o e
  unfold Fmt.readOpeningW at e
  split at e
  · rename_i hok
    have hl : Fmt.listOK sh.a xs = true := (Bool.and_eq_true _ _ ▸ hok : _ ∧ _).1
    have hu := listOK_one sh.a xs hl
    refine ⟨hl, r1, r2, r3, r4, ?_⟩
    split at e
    · cases e
    · rename_i cs given next ep
      have e' : (Fmt.walkW (m := Id) (fun _ _ l r => h 166 0 0 cfg (l ++ r)) Fmt.takeGiven sh.a
              (Fmt.leavesW (m := Id) h sh start xs cs) (given, []) []).map
            (fun r =>
              (⟨cs.map (·.1), cs.map (·.2), given, r.1, r.2.2 ++ r.2.1.2, next⟩ : Fmt.OpenOut)) =
          some o := e
      cases hw0 : Fmt.walkW (m := Id) (fun _ _ l r => h 166 0 0 cfg (l ++ r)) Fmt.takeGiven sh.a
          (Fmt.leavesW (m := Id) h sh start xs cs) (given, []) [] with
      | none => rw [hw0] at e'; cases e'
      | some p =>
        rw [hw0] at e'
        simp only [Option.map_some, Option.some.injEq] at e'
        subst e'
        have hc : cs.length = xs.length := by simpa using r1
        have hg : given.length = need sh.a xs := r3
        rw [leaves_id h sh start xs cs hc,
          walk_full (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs (leafV h sh start xs cs) given [] []
            (length_leafV h sh start xs cs hc) (le_of_eq hg.symm) hu] at hw0
        have hp := Option.some.inj hw0
        show p.2.2 ++ p.2.1.2 = _
        rw [← hp, zip_fst_snd]
        simp only [List.append_nil]
  · cases e

end


section
variable {D : Type} [Inhabited D] (hN : D → D → D)

theorem PathOK_length :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D) (k : ℕ) (p : List D),
      PathOK hN d js v s k p → p.length = d
  | 0, _, _, _, _, _, h => by rw [show _ = [] from h]; rfl
  | d + 1, js, v, s, k, p, h => by
    obtain ⟨b, p', rfl, -, hp⟩ := h
    rw [List.length_cons, PathOK_length d _ _ _ _ p' hp]

/-- What a level notes of the message is in the message, if the message is long enough. -/
theorem note1_mem (d : ℕ) :
    ∀ (js : List ℕ) (s : List D), need1 js ≤ s.length → ∀ n ∈ note1 d js s, n.2.2 ∈ s
  | [], _, _, n, hn => by simp [note1] at hn
  | [i], x :: g, _, n, hn => by
    have : n = (d, sibOf i, x) := by simpa [note1] using hn
    subst this
    exact List.mem_cons_self ..
  | i :: j :: l, s, h, n, hn => by
    by_cases hs : sib i j
    · rw [note1, if_pos hs] at hn
      exact note1_mem d l s (by simpa [need1, if_pos hs] using h) n hn
    · cases s with
      | nil => simp [need1, if_neg hs] at h
      | cons x g =>
        rw [note1, if_neg hs] at hn
        rcases List.mem_cons.1 hn with rfl | hn
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _
            (note1_mem d (j :: l) g
              (by simp only [need1, if_neg hs, List.length_cons] at h; omega) n hn)

/-- A property of the leaves' values, of the message's digests, of every value of the node function
(`hP`) and of every value of `stepF` (`hstep`) holds of all that is in the tables, if the
message is long enough. -/
theorem InLv_all (Pr : D → Prop) (hP : ∀ a b, Pr (hN a b))
    (hstep : ∀ (js : List ℕ) (v s : List D), ∀ x ∈ stepF hN js v s, Pr x) :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D), need d js ≤ s.length → (∀ x ∈ v, Pr x) →
      (∀ x ∈ s, Pr x) → ∀ (d' : ℕ) (e : ℕ × D), InLv hN d js v s d' e → Pr e.2
  | 0, js, v, s, _, hv, _, d', e, h => hv _ (List.of_mem_zip h.2).2
  | d + 1, js, v, s, hn, hv, hs, d', e, h => by
    have h1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hn
    have h2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hn
      omega
    rcases h with ⟨-, he⟩ | h
    · simp only [lvTab, List.mem_append, List.mem_map] at he
      rcases he with he | ⟨n, hn', rfl⟩
      · exact hv _ (List.of_mem_zip he).2
      · exact hs _ (note1_mem 0 js s h1 n hn')
    · exact InLv_all Pr hP hstep d (up js) (stepF hN js v s) (s.drop (need1 js)) h2 (hstep js v s)
        (fun x hx => hs x (List.mem_of_mem_drop hx)) d' e h

end

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

theorem leafV_size (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = Fmt.dlen n)
    (sh : Fmt.Shape) (start : ByteArray) :
    ∀ (xs : List ℕ) (cs : List (List UInt64 × ByteArray)), ∀ x ∈ leafV h sh start xs cs, x.size = 32
  | [], _, x, hx => by simp [leafV] at hx
  | _ :: _, [], x, hx => by simp [leafV] at hx
  | y :: xs, c :: cs, x, hx => by
    rcases List.mem_cons.1 (show x ∈ _ :: leafV h sh start xs cs from hx) with rfl | hx
    · rw [hz]
      unfold Fmt.dlen Fmt.leafNo
      cases sh.stored <;> rfl
    · exact leafV_size hz sh start xs cs x hx

/-- The whole paths that the parser reads off an opening's record, where the reader hands out o
(`e`), h's answers have the right length (`hz`) and the given digests 32 bytes (`hg`): there is one
for every listed position; it has the tree's depth; its digests have 32 bytes; climbed alone along
it, the position's leaf reaches the root that the reader computed. -/
theorem opening_paths (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = Fmt.dlen n)
    (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ) (sh : Fmt.Shape) (start : ByteArray) (xs : List ℕ)
    (b : ByteArray) (i : ℕ) (o : Fmt.OpenOut)
    (e : Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i = some o)
    (hg : ∀ g ∈ o.given, g.size = 32) :
    ∀ c ∈ xs.zip (leafV h sh start xs (o.cols.zip o.salts)), ∃ p : List ByteArray,
      pathFrom sh.a o.seen c.1 = some (p.map bytesToDig) ∧
      p.length = sh.a ∧
      (∀ q ∈ p, q.size = 32) ∧
      octF (fun l r => h 166 0 0 cfg (l ++ r)) sh.a [c.1] [c.2] p = [o.root] := by
  obtain ⟨hl, r1, r2, r3, r4, r5⟩ := reader_seen h cfg f salt sh start xs b i o e
  obtain ⟨-, hp, -⟩ := listOK_spec sh.a xs hl
  have hu1 := listOK_one sh.a xs hl
  have hlen : (leafV h sh start xs (o.cols.zip o.salts)).length = xs.length :=
    length_leafV h sh start xs _ (by rw [List.length_zip, r1, r2, Nat.min_self])
  have hn : need sh.a xs ≤ o.given.length := le_of_eq r3.symm
  intro c hc
  have hmem : ∀ x,
      x ∈ o.seen ↔
      InLv (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs (leafV h sh start xs (o.cols.zip o.salts))
        o.given x.1 (x.2.1, x.2.2) :=
    fun x => by rw [r5]; exact mem_seen_iff _ _ _ _ _ x
  obtain ⟨p, h1, h2, h3⟩ := paths_ind (fun l r => h 166 0 0 cfg (l ++ r)) o.seen
    (fun y hy y' hy' e1 e2 =>
      InLv_unique _ sh.a xs _ o.given hp hlen hn hu1 y.1 (y.2.1, y.2.2) (y'.2.1, y'.2.2)
        ((hmem y).1 hy) (by rw [e1]; exact (hmem y').1 hy') e2)
    sh.a xs _ o.given hp hlen hn (fun d' e' hi => (hmem (d', e'.1, e'.2)).2 hi) c hc
  refine ⟨p, h1, PathOK_length _ _ _ _ _ _ p h2, fun q hq => ?_, ?_⟩
  · obtain ⟨d', k, hk⟩ := h3 q hq
    exact InLv_all (fun l r => h 166 0 0 cfg (l ++ r)) (fun x => x.size = 32)
      (fun a b => hz 166 0 0 cfg (a ++ b))
      (TieTree.size_stepF _ (fun a b => hz 166 0 0 cfg (a ++ b))) sh.a xs _ o.given hn
      (leafV_size h hz sh start xs _) hg d' (k, q) ((hmem (d', k, q)).1 hk)
  · rw [climb_ok _ sh.a xs _ o.given hp hlen hn hu1 c.1 c.2 p hc h2, r4]

end

end Run.WalkTie
