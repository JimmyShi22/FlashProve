-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3Pins.lean: THE COUNTS OF THE TREES AGREE, AND A VIEW DROPS NOTHING. TWO: cut
over the sibling's RD (a list of trees a round) after a file of this project that is not in this
library: without
these nothing pins nTrees, PQ.treeSh, PQ.posAtS, PQ.colAtS, Stretches.col to one another:
plain3_local, plain3_opens, wq3_okg would build with a wrong count; it would show only as columns
silently dropped.
  AS TEXT       Ask.keyed, mem_asksL, Stretches.col_some, Stretches.shown_some,
                filterMap_map_of_some, Stretches.opened_keys
  TURNED BY MATTER   treeSh_append, colAtS_some
  NEW           posAtT_some (a round's trees: position and column's width); posAtS_some,
                Stretches.pos_some (the POSITION that is read exists too:
                a file of this project that is not in this library has the column alone)
  NOT SAID      Ask.pair, asksL_pair, carriedX … carries1_eq: the ties to Run/PlanQX.lean's
                wantedXL | symbolsCarryTheirPositions, which are not said over the sibling's RD

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop TypedOracleCompiler.Run

/-- A request's key in a view, and its position. -/
def Ask.keyed (key : ℕ → ℕ) : Ask → ℕ × ℕ
  | .stored k x => (k, x)
  | .own n x => (key n, x)

/-- A request lies inside the stored table, or inside a tree that some round of `all` sends. -/
theorem mem_asksL (a : ℕ) (all : List PQ.RD) (xs : List PQ.XO) (q : Ask) :
    ∀ (i : ℕ) (ds : List PQ.RD) (Ds : List Fmt.Drawn), q ∈ asksL a all xs i ds Ds →
      (∃ k x, q = Ask.stored k x ∧ x < 2 ^ a) ∨
        ∃ n x s, q = Ask.own n x ∧ PQ.treeSh all n = some s ∧ x < 2 ^ s.a
  | _, [], _, h => by simp [asksL] at h
  | _, _ :: _, [], h => by simp [asksL] at h
  | i, d :: ds, D :: Ds, h => by
      rw [asksL] at h
      rcases List.mem_append.1 h with hab | hr
      · rcases List.mem_append.1 hab with ha | hb
        · obtain ⟨o, _, hm⟩ := List.mem_flatMap.1 ha
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
          obtain ⟨z, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
          exact Or.inl ⟨_, _, rfl, Nat.mod_lt _ (Nat.two_pow_pos a)⟩
        · obtain ⟨n, _, hm⟩ := List.mem_flatMap.1 hb
          cases hs : PQ.treeSh all n with
          | none => rw [hs] at hm; cases hm
          | some s =>
            rw [hs] at hm
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
            obtain ⟨z, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
            exact Or.inr ⟨_, _, s, rfl, hs, Nat.mod_lt _ (Nat.two_pow_pos s.a)⟩
      · exact mem_asksL a all xs q (i + 1) ds Ds hr

/-! ## Trees, counted through -/

/-- The trees of the second list follow those of the first. -/
theorem treeSh_append : ∀ (A B : List PQ.RD) (n : ℕ),
    PQ.treeSh (A ++ B) n = if n < nTrees A then PQ.treeSh A n else PQ.treeSh B (n - nTrees A)
  | [], B, n => by
      show PQ.treeSh B n = if n < 0 then _ else PQ.treeSh B (n - 0)
      rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero]
  | d :: A, B, n => by
      show (if n < d.trees.length then d.trees[n]? else PQ.treeSh (A ++ B) (n - d.trees.length)) =
        if n < d.trees.length + nTrees A then
          (if n < d.trees.length then d.trees[n]? else PQ.treeSh A (n - d.trees.length))
        else PQ.treeSh B (n - (d.trees.length + nTrees A))
      by_cases h : n < d.trees.length
      · rw [if_pos h, if_pos (by omega), if_pos h]
      · rw [if_neg h, if_neg h, treeSh_append A B (n - d.trees.length)]
        by_cases hk : n - d.trees.length < nTrees A
        · rw [if_pos hk, if_pos (by omega)]
        · rw [if_neg hk, if_neg (by omega), Nat.sub_add_eq]

/-- TWO: among a round's trees: tree n has a position at each of its leaves, and a column there has
the tree's width. -/
theorem posAtT_some : ∀ (ts : List Fmt.Shape) (n x : ℕ) (s : Fmt.Shape),
    ts[n]? = some s → x < 2 ^ s.a →
    ∃ p, PQ.posAtT ts n x = some p ∧ ∀ c, (PQ.colT ts p c).length = s.W
  | [], _, _, _, h, _ => by simp at h
  | s' :: _, 0, x, s, h, hx => by
      obtain rfl : s' = s := by simpa using h
      exact ⟨.inl ⟨x, hx⟩, dif_pos hx, fun c => List.length_ofFn⟩
  | _ :: ts, n + 1, x, s, h, hx => by
      obtain ⟨p, hp, hc⟩ := posAtT_some ts n x s (by simpa using h) hx
      refine ⟨.inr p, ?_, hc⟩
      show (PQ.posAtT ts n x).map Sum.inr = _
      rw [hp]
      rfl

/-- A tree has a column, of the tree's width, at each of its positions. -/
theorem colAtS_some (C : PQ.CK) :
    ∀ (ds : List PQ.RD) (τ : Tr (PQ.uL C ds)) (n x : ℕ) (s : Fmt.Shape),
      PQ.treeSh ds n = some s → x < 2 ^ s.a → ∃ c, PQ.colAtS C ds τ n x = some c ∧ c.length = s.W
  | [], _, _, _, _, h, _ => by simp [PQ.treeSh] at h
  | d :: ds, (m, c0, τ), n, x, s, h, hx => by
      have h' : (if n < d.trees.length then d.trees[n]? else PQ.treeSh ds (n - d.trees.length)) =
          some s := h
      unfold PQ.colAtS
      by_cases hn : n < d.trees.length
      · rw [if_pos hn] at h' ⊢
        obtain ⟨p, hp, hc⟩ := posAtT_some d.trees n x s h' hx
        rw [hp]
        exact ⟨_, rfl, hc _⟩
      · rw [if_neg hn] at h' ⊢
        exact colAtS_some C ds τ (n - d.trees.length) x s h' hx

/-- TWO: and a position of the shape. -/
theorem posAtS_some (C : PQ.CK) :
    ∀ (ds : List PQ.RD) (n x : ℕ) (s : Fmt.Shape),
      PQ.treeSh ds n = some s → x < 2 ^ s.a → ∃ p, PQ.posAtS C ds n x = some p
  | [], _, _, _, h, _ => by simp [PQ.treeSh] at h
  | d :: ds, n, x, s, h, hx => by
      have h' : (if n < d.trees.length then d.trees[n]? else PQ.treeSh ds (n - d.trees.length)) =
          some s := h
      unfold PQ.posAtS
      by_cases hn : n < d.trees.length
      · rw [if_pos hn] at h' ⊢
        obtain ⟨p, hp, -⟩ := posAtT_some d.trees n x s h' hx
        rw [hp]
        exact ⟨_, rfl⟩
      · rw [if_neg hn] at h' ⊢
        obtain ⟨p, hp⟩ := posAtS_some C ds (n - d.trees.length) x s h' hx
        rw [hp]
        exact ⟨_, rfl⟩

namespace Stretches
variable (G : Stretches) (τ₁ : Tr (PQ.uL G.C G.ds₁)) (τ₂ : Tr (PQ.uL G.C G.ds₂))
  (τ₃ : Tr (PQ.uL G.C G.ds₃))

/-- Counted over all three stretches, a tree has a column, of the tree's width, at each of its
positions. -/
theorem col_some (n x : ℕ) (s : Fmt.Shape) (h : PQ.treeSh G.all n = some s) (hx : x < 2 ^ s.a) :
    ∃ c, G.col τ₁ τ₂ τ₃ n x = some c ∧ c.length = s.W := by
  unfold all at h
  unfold col
  rw [treeSh_append] at h
  by_cases h1 : n < nTrees G.ds₁
  · rw [if_pos h1] at h ⊢
    exact colAtS_some G.C G.ds₁ τ₁ n x s h hx
  · rw [if_neg h1, treeSh_append] at h
    rw [if_neg h1]
    by_cases h2 : n - nTrees G.ds₁ < nTrees G.ds₂
    · rw [if_pos h2] at h ⊢
      exact colAtS_some G.C G.ds₂ τ₂ _ x s h hx
    · rw [if_neg h2] at h ⊢
      exact colAtS_some G.C G.ds₃ τ₃ _ x s h hx

/-- TWO: and a position of the whole shape: what is asked of a tree is read. -/
theorem pos_some (n x : ℕ) (s : Fmt.Shape) (h : PQ.treeSh G.all n = some s) (hx : x < 2 ^ s.a) :
    ∃ p, G.pos n x = some p := by
  unfold all at h
  unfold pos
  rw [treeSh_append] at h
  by_cases h1 : n < nTrees G.ds₁
  · rw [if_pos h1] at h ⊢
    obtain ⟨p, hp⟩ := posAtS_some G.C G.ds₁ n x s h hx
    rw [hp]
    exact ⟨_, rfl⟩
  · rw [if_neg h1, treeSh_append] at h
    rw [if_neg h1]
    by_cases h2 : n - nTrees G.ds₁ < nTrees G.ds₂
    · rw [if_pos h2] at h ⊢
      obtain ⟨p, hp⟩ := posAtS_some G.C G.ds₂ _ x s h hx
      rw [hp]
      exact ⟨_, rfl⟩
    · rw [if_neg h2] at h ⊢
      obtain ⟨p, hp⟩ := posAtS_some G.C G.ds₃ _ x s h hx
      rw [hp]
      exact ⟨_, rfl⟩

/-- A view has an entry for each request, under the request's key and at its position. -/
theorem shown_some (key : ℕ → ℕ) (y : Fin (2 ^ G.a) → PQ.SgX) (xs : List PQ.XO) (i : ℕ)
    (ds : List PQ.RD) (Ds : List Fmt.Drawn) (q : Ask) (hq : q ∈ asksL G.a G.all xs i ds Ds) :
    ∃ e, Ask.shown G.a key y (G.col τ₁ τ₂ τ₃) q = some e ∧ (e.1, e.2.1) = Ask.keyed key q := by
  rcases mem_asksL G.a G.all xs q i ds Ds hq with ⟨k, x, rfl, hx⟩ | ⟨n, x, s, rfl, hs, hx⟩
  · exact ⟨(k, x, (y ⟨x, hx⟩).2), dif_pos hx, rfl⟩
  · obtain ⟨c, hc, _⟩ := G.col_some τ₁ τ₂ τ₃ n x s hs hx
    refine ⟨(key n, x, c), ?_, rfl⟩
    show (G.col τ₁ τ₂ τ₃ n x).map _ = _
    rw [hc]
    rfl

end Stretches

/-- A list of which nothing is dropped. -/
theorem filterMap_map_of_some {α β γ : Type} (f : α → Option β) (π : β → γ) (g : α → γ) :
    ∀ l : List α, (∀ q ∈ l, ∃ b, f q = some b ∧ π b = g q) → (l.filterMap f).map π = l.map g
  | [], _ => rfl
  | q :: l, h => by
      obtain ⟨b, hb, hg⟩ := h q List.mem_cons_self
      rw [List.filterMap_cons_some hb, List.map_cons, List.map_cons, hg,
        filterMap_map_of_some f π g l fun r hr => h r (List.mem_cons_of_mem _ hr)]

/-- A view drops nothing: the keys and positions of its list of opened columns, in order, are
those of the requests. So they are a function of the public data and the stretch's draws. -/
theorem Stretches.opened_keys (G : Stretches) (τ₁ : Tr (PQ.uL G.C G.ds₁))
    (τ₂ : Tr (PQ.uL G.C G.ds₂)) (τ₃ : Tr (PQ.uL G.C G.ds₃)) (key : ℕ → ℕ)
    (y : Fin (2 ^ G.a) → PQ.SgX) (ds : List PQ.RD) (xs : List PQ.XO) (τ : Tr (PQ.uL G.C ds)) :
    (viewOn G.C G.a G.all ds xs key y (G.col τ₁ τ₂ τ₃) τ).opened.map (fun e => (e.1, e.2.1)) =
      (asksL G.a G.all xs 0 ds (drOn G.C ds τ)).map (Ask.keyed key) :=
  filterMap_map_of_some _ _ _ _ fun q hq => G.shown_some τ₁ τ₂ τ₃ key y xs 0 ds _ q hq

end TypedOracleCompiler.Slice
