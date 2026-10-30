-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadNodes.lean: the vertices that the reader of an opening has met fit together: where
both children of a vertex are among them, the vertex is among them with the hash of the two; the
opened leaves stand at the bottom, the root at the top.

Statements and proofs. The first part is generic in the type of digests and the node function and
goes by the levels' tables of Run/WalkPaths.lean (`lvTab`, `InLv`, `level_ok`). The second is at
the format's reader of an opening, in the letters of the look-up by which whole paths are read off
the record (`Run.seenAt`, Run/ParseFull.lean).

Main names:
  `level_node`, `InLv_node`: in a level's table, and in all levels' tables of a walk.
  `opening_nodes`: of an opening o that the reader has handed out, with seen := o.seen:
    (1) seenAt seen (d + 1) (2 * k) = some l and seenAt seen (d + 1) (2 * k + 1) = some r give
    seenAt seen d k = some (the vertex hash of l and r); (2) at each listed position the bottom
    level holds the leaf's digest; (3) seenAt seen 0 0 = some o.root.
  `walked_nodes`: (1) and (3) of an opening that is `Walked` (OnBytes/Maker/ReadWalks.lean).
Limits: the root is the one to which the reader's walk led. These are identities of computations:
nothing on soundness (index binding included), what a root fixes, opening-form binding, no two
openings of a commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.Maker.ReadWalks

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.WalkTie Octopus

section
variable {D : Type} [Inhabited D] (hN : D → D → D)

/-- Both children in a level's table: the parent, with the node function's value, in the next
level. -/
theorem level_node (js : List ℕ) (v s : List D) (hp : js.Pairwise (· < ·))
    (hv : v.length = js.length) (hs : need1 js ≤ s.length) (k : ℕ) (l r : D)
    (h1 : (2 * k, l) ∈ lvTab js v s) (h2 : (2 * k + 1, r) ∈ lvTab js v s) :
    (k, hN l r) ∈ (up js).zip (stepF hN js v s) := by
  obtain ⟨j, hj, hjk⟩ := lvTab_block js v s (2 * k, l) h1
  obtain ⟨a, ha⟩ := mem_zip_left js v hv.symm j hj
  obtain ⟨U, P⟩ := level_ok hN js v s hp hv hs
  obtain ⟨b, hb, hpar⟩ := P (j, a) ha
  have hja : (j, a) ∈ lvTab js v s := List.mem_append_left _ ha
  have hk : j / 2 = k := by
    have : (2 * k) / 2 = j / 2 := hjk
    omega
  by_cases he : j % 2 = 0
  · have ej : j = 2 * k := by omega
    have es : sibOf j = 2 * k + 1 := by unfold sibOf; rw [if_pos he]; omega
    have ea : a = l := U (j, a) hja (2 * k, l) h1 ej
    have eb : b = r := U (sibOf j, b) hb (2 * k + 1, r) h2 es
    have e3 : loneF hN j a b = hN l r := by unfold loneF; rw [if_pos he, ea, eb]
    have hpar' : (j / 2, loneF hN j a b) ∈ (up js).zip (stepF hN js v s) := hpar
    rw [hk, e3] at hpar'
    exact hpar'
  · have ej : j = 2 * k + 1 := by omega
    have es : sibOf j = 2 * k := by unfold sibOf; rw [if_neg he]; omega
    have ea : a = r := U (j, a) hja (2 * k + 1, r) h2 ej
    have eb : b = l := U (sibOf j, b) hb (2 * k, l) h1 es
    have e3 : loneF hN j a b = hN l r := by unfold loneF; rw [if_neg he, ea, eb]
    have hpar' : (j / 2, loneF hN j a b) ∈ (up js).zip (stepF hN js v s) := hpar
    rw [hk, e3] at hpar'
    exact hpar'

/-- A vertex of the level at which a walk starts is in that level's table. -/
theorem InLv_start : ∀ (d : ℕ) (js : List ℕ) (v s : List D) (e : ℕ × D), e ∈ js.zip v →
    InLv hN d js v s d e
  | 0, _, _, _, _, he => ⟨rfl, he⟩
  | _ + 1, _, _, _, _, he => Or.inl ⟨rfl, List.mem_append_left _ he⟩

/-- **Both children in the tables of a walk: the parent too, with the node function's value.** -/
theorem InLv_node : ∀ (d : ℕ) (js : List ℕ) (v s : List D), js.Pairwise (· < ·) →
    v.length = js.length → need d js ≤ s.length → ∀ (d' k : ℕ) (l r : D),
    InLv hN d js v s (d' + 1) (2 * k, l) → InLv hN d js v s (d' + 1) (2 * k + 1, r) →
    InLv hN d js v s d' (k, hN l r)
  | 0, _, _, _, _, _, _, d', _, _, _, h1, _ => by
    have := h1.1
    omega
  | d + 1, js, v, s, hp, hv, hs, d', k, l, r, h1, h2 => by
    have g1 : need1 js ≤ s.length := le_trans (Nat.le_add_right _ _) hs
    have g2 : need d (up js) ≤ (s.drop (need1 js)).length := by
      rw [List.length_drop]
      have : need1 js + need d (up js) ≤ s.length := hs
      omega
    rcases h1 with ⟨e1, m1⟩ | h1 <;> rcases h2 with ⟨e2, m2⟩ | h2
    · have ed : d' = d := by omega
      rw [ed]
      exact Or.inr (InLv_start hN d _ _ _ _ (level_node hN js v s hp hv g1 k l r m1 m2))
    · have := InLv_le hN d _ _ _ _ _ h2
      omega
    · have := InLv_le hN d _ _ _ _ _ h1
      omega
    · exact Or.inr (InLv_node d (up js) (stepF hN js v s) (s.drop (need1 js)) (pairwise_up js hp)
        (length_stepF hN js v s) g2 d' k l r h1 h2)

/-- The top level's table is what the walk ends in. -/
theorem InLv_top : ∀ (d : ℕ) (js : List ℕ) (v s : List D) (e : ℕ × D),
    e ∈ (upN d js).zip (octF hN d js v s) → InLv hN d js v s 0 e
  | 0, _, _, _, _, he => ⟨rfl, he⟩
  | d + 1, js, v, s, e, he =>
    Or.inr (InLv_top d (up js) (stepF hN js v s) (s.drop (need1 js)) e he)

end

/-- The numbers after d levels are the numbers' parts above 2 ^ d. -/
theorem mem_upN : ∀ (d : ℕ) (js : List ℕ) (x : ℕ), x ∈ upN d js → ∃ j ∈ js, x = j / 2 ^ d
  | 0, _, x, hx => ⟨x, hx, by simp⟩
  | d + 1, js, x, hx => by
    obtain ⟨j, hj, e⟩ := mem_upN d (up js) x hx
    obtain ⟨i, hi, e'⟩ := mem_up js j hj
    exact ⟨i, hi, by rw [e, e', Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]⟩

/-- What the look-up finds is in the record. -/
theorem seenAt_mem {seen : List (ℕ × ℕ × ByteArray)} {d p : ℕ} {val : ByteArray}
    (h : seenAt seen d p = some val) : (d, p, val) ∈ seen := by
  unfold seenAt at h
  cases hf : seen.find? (fun v => v.1 == d && v.2.1 == p) with
  | none => rw [hf] at h; cases h
  | some y =>
    rw [hf] at h
    have h1 := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    have h2 : y.2.2 = val := Option.some.inj h
    have hy := List.mem_of_find?_eq_some hf
    obtain ⟨a, b, c⟩ := y
    obtain ⟨rfl, rfl⟩ := h1
    obtain rfl := h2
    exact hy

section
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → ByteArray)

/-- **The record of vertices of one opening.** -/
theorem opening_nodes (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ) (sh : Fmt.Shape)
    (start : ByteArray) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : Fmt.OpenOut)
    (e : Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i = some o) :
    (∀ d k l r, seenAt o.seen (d + 1) (2 * k) = some l →
      seenAt o.seen (d + 1) (2 * k + 1) = some r →
      seenAt o.seen d k = some (h 166 0 0 cfg (l ++ r))) ∧
    (∀ c ∈ xs.zip (leafV h sh start xs (o.cols.zip o.salts)), seenAt o.seen sh.a c.1 = some c.2) ∧
    seenAt o.seen 0 0 = some o.root := by
  obtain ⟨hl, r1, r2, r3, r4, r5⟩ := reader_seen h cfg f salt sh start xs b i o e
  obtain ⟨-, hp, hb⟩ := listOK_spec sh.a xs hl
  have hu1 := listOK_one sh.a xs hl
  have hlen : (leafV h sh start xs (o.cols.zip o.salts)).length = xs.length :=
    length_leafV h sh start xs _ (by rw [List.length_zip, r1, r2, Nat.min_self])
  have hn : need sh.a xs ≤ o.given.length := le_of_eq r3.symm
  have hmem : ∀ x,
      x ∈ o.seen ↔
      InLv (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs (leafV h sh start xs (o.cols.zip o.salts))
        o.given x.1 (x.2.1, x.2.2) :=
    fun x => by rw [r5]; exact mem_seen_iff _ _ _ _ _ x
  have hone : ∀ u ∈ o.seen, ∀ v ∈ o.seen, u.1 = v.1 → u.2.1 = v.2.1 → u.2.2 = v.2.2 :=
    fun u hu v hv e1 e2 =>
      InLv_unique _ sh.a xs _ o.given hp hlen hn hu1 u.1 (u.2.1, u.2.2) (v.2.1, v.2.2)
        ((hmem u).1 hu) (by rw [e1]; exact (hmem v).1 hv) e2
  have back : ∀ d p val, (d, p, val) ∈ o.seen → seenAt o.seen d p = some val :=
    fun d p val hm => seenAt_of_mem o.seen d p val hm fun y hy a1 a2 => hone y hy _ hm a1 a2
  refine ⟨fun d k l r a1 a2 => ?_, fun c hc => ?_, ?_⟩
  · exact back _ _ _ ((hmem (d, k, _)).2 (InLv_node _ sh.a xs _ o.given hp hlen hn d k l r
      ((hmem _).1 (seenAt_mem a1)) ((hmem _).1 (seenAt_mem a2))))
  · exact back _ _ _ ((hmem (sh.a, c.1, c.2)).2 (InLv_start _ sh.a xs _ o.given c hc))
  · have hlo := length_octF (fun l r => h 166 0 0 cfg (l ++ r)) sh.a xs
      (leafV h sh start xs (o.cols.zip o.salts)) o.given hlen
    rw [hu1] at hlo
    obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 hu1
    obtain ⟨w, hw⟩ := List.length_eq_one_iff.1 hlo
    have ht0 : t = 0 := by
      obtain ⟨j, hj, ej⟩ := mem_upN sh.a xs t (by rw [ht]; exact List.mem_singleton.2 rfl)
      rw [ej]
      exact Nat.div_eq_of_lt (hb j hj)
    have hroot : o.root = w := by rw [r4, hw]; rfl
    refine back _ _ _ ((hmem (0, 0, o.root)).2 (InLv_top _ sh.a xs _ o.given (0, o.root) ?_))
    rw [ht, hw, ht0, hroot]
    exact List.mem_singleton.2 rfl

/-- The same of an opening that is `Walked`. -/
theorem walked_nodes (cfg : ByteArray) {y : OpenedY} (W : Walked h cfg y) :
    (∀ d k l r, seenAt y.2.2.seen (d + 1) (2 * k) = some l →
      seenAt y.2.2.seen (d + 1) (2 * k + 1) = some r →
      seenAt y.2.2.seen d k = some (h 166 0 0 cfg (l ++ r))) ∧
    seenAt y.2.2.seen 0 0 = some y.2.2.root := by
  obtain ⟨f, salt, start, b, i, e⟩ := W
  obtain ⟨a1, -, a3⟩ := opening_nodes h cfg f salt y.1 start y.2.1 b i y.2.2 e
  exact ⟨a1, a3⟩

end

end OnBytes.Maker
