-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TilesOkProofs.lean: proofs of `FitOfOk`, `RowFitOfOk` and `FitsOfOk`
(Johnson/Desc/Sound/Tiles.lean): where the makers' tests (`okAt`) say yes of three lists of written
rounds, what the tiling rests on holds at the data made of them.

The road. (1) Laws on any data D: the depth of a chain's own tree; every tree with a depth stands
once in `allOf D`; `RowFit D (allOf D) (allOf D)` from its first two clauses. (2) A declared round
and its written round open trees of the same shapes (`round_shapes`); `DataFits`
(OnBytes/Maker/DataFitsOf.lean) ties a written round to the round's data, tree by tree through the
data's table; `shapesFit` ties the table to the data's depths: together `Matches`. (3) NO
ROUND OPENS A TREE THAT IS SENT LATER: from the third clause of `Three.Whole.fits` (a tree's row of
the table names the chain and the round that send it, not later than any opening), by a law on the
place of a row in the table (`rows_round`, `table_at`).
Limits: those of the statements, which stand in Johnson/Desc/Sound/Tiles.lean. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesCutProofs
import OnBytes.Maker.DataFitsOf
import OnBytes.Maker.OkOfShapes
import OnBytes.Maker.TypingViews
import OnBytes.Maker.TableChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open OnBytes.Three (rootsIn treesOfChain rdsFromL rdOf opensOf wholeNo)

/-! ## 1 Laws on any data -/

theorem depth_lt (D : WholeD) (j a' : ℕ) (h : D.depth j = some a') : j < nAll D := by
  unfold WholeD.depth at h
  unfold nAll
  by_cases h1 : j < D.t₁
  · omega
  · rw [if_neg h1] at h
    by_cases h2 : j - D.t₁ < D.t₂
    · omega
    · rw [if_neg h2] at h
      obtain ⟨sh, hsh, -⟩ := Option.map_eq_some_iff.1 h
      have := treeShT_lt _ _ _ hsh
      omega

theorem depth_own₁ (D : WholeD) (n : ℕ) (sh : Fmt.Shape) (h : treeShT D.ds₁ n = some sh) :
    D.depth (0 + n) = some sh.a := by
  have h1 : n < D.t₁ := treeShT_lt _ _ _ h
  unfold WholeD.depth
  rw [Nat.zero_add, if_pos h1, h]
  rfl

theorem depth_own₂ (D : WholeD) (n : ℕ) (sh : Fmt.Shape) (h : treeShT D.ds₂ n = some sh) :
    D.depth (D.t₁ + n) = some sh.a := by
  have h1 : n < D.t₂ := treeShT_lt _ _ _ h
  unfold WholeD.depth
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, h]
  rfl

theorem depth_own₃ (D : WholeD) (n : ℕ) (sh : Fmt.Shape) (h : treeShT D.ds₃ n = some sh) :
    D.depth (D.t₁ + D.t₂ + n) = some sh.a := by
  unfold WholeD.depth
  rw [if_neg (by omega), if_neg (by omega), show D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n by omega, h]
  rfl

theorem depth_some (D : WholeD) (j : ℕ) (h : j < nAll D) : ∃ a', D.depth j = some a' := by
  unfold nAll at h
  by_cases h1 : j < D.t₁
  · obtain ⟨sh, hsh⟩ := treeShT_some_of_lt D.ds₁ j h1
    exact ⟨_, by have t := depth_own₁ D j sh hsh; rwa [Nat.zero_add] at t⟩
  · by_cases h2 : j - D.t₁ < D.t₂
    · obtain ⟨sh, hsh⟩ := treeShT_some_of_lt D.ds₂ (j - D.t₁) h2
      exact ⟨_, by
        have t := depth_own₂ D _ sh hsh
        rwa [show D.t₁ + (j - D.t₁) = j by omega] at t⟩
    · obtain ⟨sh, hsh⟩ := treeShT_some_of_lt D.ds₃ (j - D.t₁ - D.t₂) (by omega)
      exact ⟨_, by
        have t := depth_own₃ D _ sh hsh
        rwa [show D.t₁ + D.t₂ + (j - D.t₁ - D.t₂) = j by omega] at t⟩

theorem filter_range_none (f : ℕ → ℕ) : ∀ (n j : ℕ), n ≤ j →
    ((List.range n).map fun i => (⟨i, f i⟩ : LeftT)).filter (·.no == j) = []
  | 0, _, _ => rfl
  | n + 1, j, h => by
    rw [List.range_succ, List.map_append, List.filter_append, filter_range_none f n j (by omega)]
    have e : (n == j) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp [e]

theorem filter_range_one (f : ℕ → ℕ) : ∀ (n j : ℕ), j < n →
    (((List.range n).map fun i => (⟨i, f i⟩ : LeftT)).filter (·.no == j)).map (·.a) = [f j]
  | 0, _, h => by omega
  | n + 1, j, h => by
    rw [List.range_succ, List.map_append, List.filter_append, List.map_append]
    by_cases hj : j < n
    · rw [filter_range_one f n j hj]
      have e : (n == j) = false := by
        rw [beq_eq_false_iff_ne]
        omega
      simp [e]
    · have e : j = n := by omega
      subst e
      rw [filter_range_none f j j (Nat.le_refl _)]
      simp

/-- A tree that has a depth stands once in the list of all trees, at that depth. -/
theorem allOf_listed (D : WholeD) (j a' : ℕ) (h : D.depth j = some a') :
    ((allOf D).filter (·.no == j)).map (·.a) = [a'] := by
  have t : (((List.range (nAll D)).map fun i => (⟨i, (D.depth i).getD 0⟩ : LeftT)).filter
      (·.no == j)).map (·.a) = [(D.depth j).getD 0] :=
    filter_range_one (fun i => (D.depth i).getD 0) (nAll D) j (depth_lt D j a' h)
  unfold allOf
  rw [t, h]
  rfl

/-- `RowFit` at the list of all trees, from its first two clauses. -/
theorem rowFit_all (D : WholeD) (o₁ : ∀ d ∈ D.ds₁, ∀ j ∈ d.opens, j < D.t₁)
    (o₂ : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, j < D.t₁ + D.t₂) : RowFit D (allOf D) (allOf D) := by
  refine ⟨o₁, o₂, fun d _ j _ hlt => ?_, fun d _ j _ hlt => ?_,
    fun l hl _ => ⟨l, hl, rfl, Nat.le_refl _⟩⟩
  · obtain ⟨sh, hsh⟩ := treeShT_some_of_lt D.ds₁ j hlt
    have t := depth_own₁ D j sh hsh
    rw [Nat.zero_add] at t
    rw [hsh, find_of_filter _ _ _ (allOf_listed D j _ t)]
    rfl
  · obtain ⟨a', ha⟩ := depth_some D j (by unfold nAll; omega)
    rw [ha, find_of_filter _ _ _ (allOf_listed D j _ ha)]

/-! ## 2 Lists -/

theorem mapM_forall₂ {α β : Type} (f : α → Option β) : ∀ (l : List α) (bs : List β),
    l.mapM f = some bs → List.Forall₂ (fun a b => f a = some b) l bs
  | [], bs, h => by
    rw [List.mapM_nil] at h
    cases h
    exact .nil
  | a0 :: l, bs, h => by
    rw [List.mapM_cons] at h
    cases e0 : f a0 with
    | none => rw [e0] at h; cases h
    | some b0 =>
      cases e1 : l.mapM f with
      | none => rw [e0, e1] at h; cases h
      | some bs0 =>
        rw [e0, e1] at h
        have hb : bs = b0 :: bs0 := (Option.some.inj h).symm
        subst hb
        exact .cons e0 (mapM_forall₂ f l bs0 e1)

theorem forall₂_comp {α β γ : Type} {P : α → β → Prop} {Q : β → γ → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ P l₁ l₂ → List.Forall₂ Q l₂ l₃ →
      List.Forall₂ (fun a c => ∃ b, P a b ∧ Q b c) l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons ⟨_, h, h'⟩ (forall₂_comp t t')

theorem forall₂_and_right {α β : Type} {R : α → β → Prop} {Q : β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ y ∈ l₂, Q y) →
      List.Forall₂ (fun x y => R x y ∧ Q y) l₁ l₂
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, q => .cons ⟨h, q _ List.mem_cons_self⟩
      (forall₂_and_right t fun y hy => q y (List.mem_cons_of_mem _ hy))

theorem zipWith_get {α β γ : Type} (f : α → β → γ) : ∀ (l : List α) (l' : List β) (k : ℕ) (z : γ),
    (List.zipWith f l l')[k]? = some z → ∃ x y, l[k]? = some x ∧ f x y = z
  | [], _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: _, y :: _, 0, z, h => ⟨x, y, rfl, by simpa using h⟩
  | _ :: l, _ :: l', k + 1, z, h => zipWith_get f l l' k z (by simpa using h)

theorem mem_zipIdx_get {α : Type} : ∀ (l : List α) (s k : ℕ) (x : α), l[k]? = some x →
    (x, s + k) ∈ l.zipIdx s
  | [], _, _, _, h => by simp at h
  | y :: l, s, 0, x, h => by
    rw [List.zipIdx_cons]
    have e : y = x := by simpa using h
    subst e
    exact List.mem_cons_self
  | y :: l, s, k + 1, x, h => by
    rw [List.zipIdx_cons]
    have t := mem_zipIdx_get l (s + 1) k x (by simpa using h)
    rw [show s + 1 + k = s + (k + 1) by omega] at t
    exact List.mem_cons_of_mem _ t

theorem sum_take_mono : ∀ (l : List ℕ) (m n : ℕ), m ≤ n → (l.take m).sum ≤ (l.take n).sum
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | _ :: _, _ + 1, 0, h => by omega
  | x :: l, m + 1, n + 1, h => by
    simp only [List.take_succ_cons, List.sum_cons]
    have := sum_take_mono l m n (Nat.le_of_succ_le_succ h)
    omega

/-! ## 3 Declared rounds against the data -/

theorem fst_of_forall₂ (g : Fmt.TreeSource → Option Fmt.Src) :
    ∀ {l : List (Fmt.Shape × Fmt.TreeSource)} {os : List (Fmt.Shape × Fmt.Src)},
      List.Forall₂ (fun o b => (g o.2).map (fun s => (o.1, s)) = some b) l os →
      os.map (·.1) = l.map (·.1)
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [List.map_cons, List.map_cons, fst_of_forall₂ g t]

/-- A declared round and its written round open trees of the same shapes. -/
theorem round_shapes (e : List (List ByteArray × ByteArray)) (r : Fmt.DeclaredRound) (x : Fmt.Round)
    (h : r.round e = some x) : x.opens.map (·.1) = r.opens.map (·.1) := by
  unfold Fmt.DeclaredRound.round at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨os, hos, rfl⟩ := Option.map_eq_some_iff.1 h
  exact fst_of_forall₂ (fun s => s.src e) (mapM_forall₂ _ _ _ hos)

theorem matches_of_forall₂ (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ {rs : List Fmt.DeclaredRound} {ds : List RDT}, List.Forall₂ (RoundMatch a dep) rs ds →
      Matches a dep rs ds
  | _, _, .nil => trivial
  | _, _, .cons h t => ⟨h, matches_of_forall₂ a dep t⟩

/-- Without the data's last round, if that round reads nothing. -/
theorem matches_dropLast (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT), List.Forall₂ (RoundMatch a dep) rs ds →
      (∀ d, ds.getLast? = some d → d.stored = [] ∧ d.opens = []) → Matches a dep rs ds.dropLast
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | [r], [d], h, q => by
    obtain ⟨q1, q2⟩ := q d rfl
    obtain ⟨⟨h1, -, h3⟩, -⟩ := List.forall₂_cons.1 h
    rw [q2] at h3
    show (r.stored = [] ∧ r.opens = []) ∧ True
    exact ⟨⟨by rw [← h1]; exact q1, List.forall₂_nil_right_iff.1 h3⟩, trivial⟩
  | _ :: _ :: _, [_], h, _ => by
    obtain ⟨-, t⟩ := List.forall₂_cons.1 h
    cases t
  | [_], _ :: _ :: _, h, _ => by
    obtain ⟨-, t⟩ := List.forall₂_cons.1 h
    cases t
  | r :: r' :: rs, d :: d' :: ds, h, q => by
    obtain ⟨h1, t⟩ := List.forall₂_cons.1 h
    have ih := matches_dropLast a dep (r' :: rs) (d' :: ds) t fun e he => q e (by
      rw [List.getLast?_cons_cons]
      exact he)
    rw [List.dropLast_cons₂]
    exact ⟨h1, ih⟩

section
variable {a : ℕ} {R₁ R₂ R₃ : Rounds}

/-- The depth that the data give a tree of the table is its shape's. -/
theorem depth_of_treeIs (hok : okAt a (some (R₁, R₂, R₃)) = true) (s : Fmt.Shape) (j : ℕ)
    (h : TreeIs (Three.Whole.of R₁ R₂ R₃) s j) : (dataOf a R₁ R₂ R₃).depth j = some s.a := by
  obtain ⟨t, ht, rfl⟩ := h
  have hsf : shapesFit a (Three.Whole.of R₁ R₂ R₃) = true :=
    shapesFit_of_okAt (R := (R₁, R₂, R₃)) hok
  show (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).depth j = _
  rw [WholeD.depth_shape, shapesFit_at hsf ht]
  rfl

/-- One chain: declared rounds, written as R, against the plain data that fit R. -/
theorem match_chain (hok : okAt a (some (R₁, R₂, R₃)) = true)
    (e : List (List ByteArray × ByteArray)) (dl : List Fmt.DeclaredRound) (R : Rounds)
    (ds : List Three.RDL) (w : WrittenAs e dl R) (f : DataFits (Three.Whole.of R₁ R₂ R₃) R ds)
    (st : ∀ d ∈ ds, ∀ s ∈ d.stored, s.sh.a = a) :
    List.Forall₂ (RoundMatch a (dataOf a R₁ R₂ R₃).depth) dl (ds.map rdtOf) := by
  rw [List.forall₂_map_right_iff]
  have f' : List.Forall₂ (fun x d => RoundData (Three.Whole.of R₁ R₂ R₃) (keyOf x) d) R ds :=
    List.forall₂_map_left_iff.1 f
  refine (forall₂_comp w (forall₂_and_right f' st)).imp ?_
  rintro r d ⟨x, ⟨hx, hs⟩, ⟨g1, g2⟩, g3⟩
  have g1' : x.2 = d.stored := g1
  have g2' : List.Forall₂ (TreeIs (Three.Whole.of R₁ R₂ R₃)) (x.1.opens.map (·.1)) d.opens := g2
  refine ⟨?_, ?_, ?_⟩
  · show d.stored = r.stored
    rw [← g1', hs]
  · intro s hs'
    exact g3 s (by rw [← g1', hs]; exact hs')
  · show List.Forall₂ _ r.opens d.opens
    rw [round_shapes e r x.1 hx, List.forall₂_map_left_iff] at g2'
    exact g2'.imp fun o j ho => depth_of_treeIs hok o.1 j ho

/-! ## 4 No round opens a tree that is sent later -/

theorem fits_time {m : ℕ} (h : Three.Whole.fits R₁ R₂ R₃ m = true) :
    ∀ z ∈ (Three.Whole.of R₁ R₂ R₃).opens, ∃ t, (Three.Whole.of R₁ R₂ R₃).table[z.1]? = some t ∧
      Three.Whole.notLater (t.chain, t.round) z.2.2 = true := by
  unfold Three.Whole.fits at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, c3⟩, -⟩, -⟩, -⟩ := h
  intro z hz
  have h1 := List.all_eq_true.1 c3 z hz
  cases ht : (Three.Whole.of R₁ R₂ R₃).table[z.1]? with
  | none => rw [ht] at h1; cases h1
  | some t =>
    rw [ht] at h1
    exact ⟨t, rfl, (Bool.and_eq_true _ _ ▸ h1 : _ ∧ _).1⟩

end

/-- An opening of a round's data stands in the chain's list of openings, under the round's number.
-/
theorem opened_at (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ) (R : Rounds)
    (k : ℕ) (d : Three.RDL) (hd : (rdsFromL all t₁ t₂ here base first R)[k]? = some d) (j : ℕ)
    (hj : j ∈ d.opens) : ∃ s, (j, s, here, k) ∈ opensOf t₁ t₂ here R := by
  unfold rdsFromL at hd
  obtain ⟨r, n, hr, rfl⟩ := zipWith_get _ _ _ _ _ hd
  obtain ⟨u, hu, e⟩ := List.mem_filterMap.1 hj
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 e
  refine ⟨u.1, ?_⟩
  unfold opensOf
  have hz := mem_zipIdx_get R 0 k r hr
  rw [Nat.zero_add] at hz
  refine List.mem_flatMap.2 ⟨(r, k), hz, List.mem_filterMap.2 ⟨u, hu, ?_⟩⟩
  show (OnBytes.Three.named here u.2).map _ = _
  rw [hy]
  rfl

/-- The number of trees that plain data send. -/
def nL (ds : List Three.RDL) : ℕ := (ds.map (·.trees.length)).sum

theorem nTrees_map (ds : List Three.RDL) : nTrees (ds.map rdtOf) = nL ds := by
  unfold nTrees nL
  rw [List.map_map]
  rfl

/-- The place of a row among a chain's rows: behind the trees of the earlier rounds, within those up
to its own round. -/
theorem rows_round : ∀ (ds : List Three.RDL) (s n : ℕ) (x : ℕ × ℕ × Fmt.Shape),
    ((ds.zipIdx s).flatMap fun d => d.1.trees.zipIdx.map fun u => (d.2, u.2, u.1))[n]? = some x →
      s ≤ x.1 ∧ n < nL (ds.take (x.1 - s + 1))
  | [], _, _, _, h => by simp at h
  | d :: ds, s, n, x, h => by
    rw [List.zipIdx_cons, List.flatMap_cons] at h
    try dsimp only at h
    have hl : (d.trees.zipIdx.map fun u => (s, u.2, u.1)).length = d.trees.length := by simp
    by_cases hn : n < d.trees.length
    · rw [List.getElem?_append_left (by rw [hl]; exact hn), List.getElem?_map] at h
      obtain ⟨u, -, rfl⟩ := Option.map_eq_some_iff.1 h
      refine ⟨Nat.le_refl _, ?_⟩
      show n < nL ((d :: ds).take (s - s + 1))
      rw [Nat.sub_self, List.take_succ_cons, List.take_zero]
      simpa [nL] using hn
    · rw [List.getElem?_append_right (by rw [hl]; omega), hl] at h
      obtain ⟨h1, h2⟩ := rows_round ds (s + 1) _ x h
      refine ⟨by omega, ?_⟩
      rw [show x.1 - s + 1 = (x.1 - (s + 1) + 1) + 1 by omega, List.take_succ_cons]
      unfold nL at h2 ⊢
      rw [List.map_cons, List.sum_cons]
      omega

theorem treesOfChain_round (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (here base : ℕ)
    (ds : List Three.RDL) (n : ℕ) (t : Three.Tree)
    (h : (treesOfChain all here base ds)[n]? = some t) : n < nL (ds.take (t.round + 1)) := by
  unfold treesOfChain at h
  rw [List.getElem?_map] at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [List.getElem?_zipIdx] at hx
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
  have u := (rows_round ds 0 n y hy).2
  rw [Nat.sub_zero] at u
  exact u

theorem nL_take_mono (ds : List Three.RDL) (m n : ℕ) (h : m ≤ n) :
    nL (ds.take m) ≤ nL (ds.take n) := by
  unfold nL
  rw [List.map_take, List.map_take]
  exact sum_take_mono _ m n h

/-- From the rounds' numbers to the recursive form. -/
theorem inTime_of_idx : ∀ (ds : List RDT) (B : ℕ),
    (∀ k d, ds[k]? = some d → ∀ j ∈ d.opens, j < B + nTrees (ds.take (k + 1))) → InTime B ds
  | [], _, _ => trivial
  | d :: ds, B, h => by
    refine ⟨fun j hj => ?_, inTime_of_idx ds _ fun k e he j hj => ?_⟩
    · have t := h 0 d rfl j hj
      rw [List.take_succ_cons, List.take_zero, nTrees_cons] at t
      simpa [nTrees] using t
    · have t := h (k + 1) e he j hj
      rw [List.take_succ_cons, nTrees_cons] at t
      omega

section
variable {a : ℕ} {R₁ R₂ R₃ : Rounds}

/-- Where a row of the table stands, by the chain that it names. -/
theorem table_at (j : ℕ) (t : Three.Tree) (h : (Three.Whole.of R₁ R₂ R₃).table[j]? = some t) :
    (t.chain = 0 ∧ j < rootsIn R₁ ∧ (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
        (Three.Whole.of R₁ R₂ R₃).ds₁)[j]? = some t) ∨
      (t.chain = 1 ∧ rootsIn R₁ ≤ j ∧ j < rootsIn R₁ + rootsIn R₂ ∧
        (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
          (Three.Whole.of R₁ R₂ R₃).ds₂)[j - rootsIn R₁]? = some t) ∨
      (t.chain = 2 ∧ rootsIn R₁ + rootsIn R₂ ≤ j ∧
        (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
          (Three.Whole.of R₁ R₂ R₃).ds₃)[j - (rootsIn R₁ + rootsIn R₂)]? = some t) := by
  have lA : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
      (Three.Whole.of R₁ R₂ R₃).ds₁).length = rootsIn R₁ := trees_count _ _ _ _ _ _ _ _ R₁
  have lB : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
      (Three.Whole.of R₁ R₂ R₃).ds₂).length = rootsIn R₂ := trees_count _ _ _ _ _ _ _ _ R₂
  have tab : (Three.Whole.of R₁ R₂ R₃).table =
      treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0 (Three.Whole.of R₁ R₂ R₃).ds₁ ++
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁) (Three.Whole.of R₁ R₂ R₃).ds₂ ++
      treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
        (Three.Whole.of R₁ R₂ R₃).ds₃) := rfl
  rw [tab] at h
  by_cases h1 : j < rootsIn R₁
  · rw [List.getElem?_append_left (by rw [lA]; exact h1)] at h
    exact Or.inl ⟨treesOfChain_chain _ _ _ _ t (List.mem_of_getElem? h), h1, h⟩
  · rw [List.getElem?_append_right (by rw [lA]; omega), lA] at h
    by_cases h2 : j - rootsIn R₁ < rootsIn R₂
    · rw [List.getElem?_append_left (by rw [lB]; exact h2)] at h
      exact Or.inr (Or.inl ⟨treesOfChain_chain _ _ _ _ t (List.mem_of_getElem? h), by omega,
        by omega, h⟩)
    · rw [List.getElem?_append_right (by rw [lB]; omega), lB, Nat.sub_sub] at h
      exact Or.inr (Or.inr ⟨treesOfChain_chain _ _ _ _ t (List.mem_of_getElem? h), by omega, h⟩)

/-- One chain. c: its number. B: the number of trees that the earlier chains send. -/
theorem time_chain {m : ℕ} (hf : Three.Whole.fits R₁ R₂ R₃ m = true) (c B base first : ℕ)
    (R : Rounds)
    (hmem : ∀ z ∈ opensOf (rootsIn R₁) (rootsIn R₂) c R, z ∈ (Three.Whole.of R₁ R₂ R₃).opens)
    (hseg : ∀ j t, (Three.Whole.of R₁ R₂ R₃).table[j]? = some t → t.chain < c → j < B)
    (hown : ∀ j t, (Three.Whole.of R₁ R₂ R₃).table[j]? = some t → t.chain = c → B ≤ j ∧
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens c B (rdsFromL (Three.Whole.of R₁ R₂ R₃).opens
        (rootsIn R₁) (rootsIn R₂) c base first R))[j - B]? = some t) :
    InTime B ((rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) c base first
      R).map rdtOf) := by
  refine inTime_of_idx _ _ fun k d' hd' j hj => ?_
  rw [List.getElem?_map] at hd'
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 hd'
  rw [← List.map_take, nTrees_map]
  obtain ⟨s, hs⟩ := opened_at _ _ _ _ _ _ R k d hd j hj
  obtain ⟨t, ht, hn⟩ := fits_time hf _ (hmem _ hs)
  simp only [Three.Whole.notLater, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hn
  rcases hn with h1 | ⟨h1, h2⟩
  · have := hseg j t ht h1
    omega
  · obtain ⟨hb, hg⟩ := hown j t ht h1
    have u := treesOfChain_round _ _ _ _ _ _ hg
    have v := nL_take_mono (rdsFromL (Three.Whole.of R₁ R₂ R₃).opens (rootsIn R₁) (rootsIn R₂) c
      base first R) (t.round + 1) (k + 1) (by omega)
    omega

theorem time₁ {m : ℕ} (hf : Three.Whole.fits R₁ R₂ R₃ m = true) :
    InTime 0 ((Three.Whole.of R₁ R₂ R₃).ds₁.map rdtOf) :=
  time_chain hf 0 0 0 0 R₁ (fun _ hz => List.mem_append_left _ hz)
    (fun _ _ _ h => absurd h (Nat.not_lt_zero _))
    (fun j t ht hc => by
      rcases table_at j t ht with ⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨Nat.zero_le _, h⟩
      · omega
      · omega)

theorem time₂ {m : ℕ} (hf : Three.Whole.fits R₁ R₂ R₃ m = true) :
    InTime (rootsIn R₁) ((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf) :=
  time_chain hf 1 (rootsIn R₁) (rootsIn R₁) 0 R₂
    (fun _ hz => List.mem_append_right _ (List.mem_append_left _ hz))
    (fun j t ht hc => by
      rcases table_at j t ht with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · omega
      · omega)
    (fun j t ht hc => by
      rcases table_at j t ht with ⟨h, -⟩ | ⟨-, h1, -, h⟩ | ⟨h, -⟩
      · omega
      · exact ⟨h1, h⟩
      · omega)

theorem time₃ {m : ℕ} (hf : Three.Whole.fits R₁ R₂ R₃ m = true) :
    InTime (rootsIn R₁ + rootsIn R₂) ((Three.Whole.of R₁ R₂ R₃).ds₃.map rdtOf) :=
  time_chain hf 2 (rootsIn R₁ + rootsIn R₂) (rootsIn R₁ + rootsIn R₂)
    (Three.first₃ (rootsIn R₁)) R₃
    (fun _ hz => List.mem_append_right _ (List.mem_append_right _ hz))
    (fun j t ht hc => by
      rcases table_at j t ht with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h, -⟩
      · omega
      · exact h
      · omega)
    (fun j t ht hc => by
      rcases table_at j t ht with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1, h⟩
      · omega
      · omega
      · exact ⟨h1, h⟩)

end

/-! ## 5 The statements -/

theorem rowFitOfOk : RowFitOfOk := by
  intro a R₁ R₂ R₃ hok
  have F := rowFit_of_rowFitAt (okAt_parts (R := (R₁, R₂, R₃)) hok).row
  exact rowFit_all _ F.o₁ F.o₂

theorem fitOfOk : FitOfOk := by
  intro a R₁ R₂ R₃ e₁ e₂ e₃ d₁ d₂ d₃ w₁ w₂ w₃ hok S₁ S₂ S₃ Cl b₁ l₁ b₂ l₂ b₃ l₃ r k₁ k₂ k₃
    ft₁ ft₂ ft₃ g₁ g₂ g₃ hs
  have P := okAt_parts (R := (R₁, R₂, R₃)) hok
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := P.fits
  have hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true := P.stored
  have hcn : countsFit a (Three.Whole.of R₁ R₂ R₃) = true := P.counts
  unfold countsFit at hcn
  simp only [Bool.and_eq_true, beq_iff_eq] at hcn
  have t₁ : (dataOf a R₁ R₂ R₃).t₁ = rootsIn R₁ := hcn.1
  have t₂ : (dataOf a R₁ R₂ R₃).t₂ = rootsIn R₂ := hcn.2
  unfold storedFit at hst
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, beq_iff_eq] at hst
  have st₁ : ∀ d ∈ (Three.Whole.of R₁ R₂ R₃).ds₁, ∀ s ∈ d.stored, s.sh.a = a := fun d hd s hs' => by
    rw [hst.1 d (List.mem_append_left _ hd)] at hs'
    cases hs'
  have st₂ : ∀ d ∈ (Three.Whole.of R₁ R₂ R₃).ds₂, ∀ s ∈ d.stored, s.sh.a = a :=
    fun d hd s hs' => (hst.2 d hd s hs').1
  have st₃ : ∀ d ∈ (Three.Whole.of R₁ R₂ R₃).ds₃, ∀ s ∈ d.stored, s.sh.a = a := fun d hd s hs' => by
    rw [hst.1 d (List.mem_append_right _ hd)] at hs'
    cases hs'
  have m₁ := match_chain hok e₁ d₁ R₁ _ w₁ (dataFits₁ hf) st₁
  have m₂ := match_chain hok e₂ d₂ R₂ _ w₂ (dataFits₂ hf) st₂
  have m₃ := match_chain hok e₃ d₃ R₃ _ w₃ (dataFits₃ hf) st₃
  have hsb : sealBare (Three.Whole.of R₁ R₂ R₃) = true := sealBare_of_okAt (R := (R₁, R₂, R₃)) hok
  have hsome : someFit (R₁, R₂, R₃) = true := P.rounds
  unfold someFit at hsome
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsome
  have e₁' : (dataOf a R₁ R₂ R₃).ds₁ = ((Three.Whole.of R₁ R₂ R₃).ds₁.map rdtOf).dropLast := by
    show (Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf = _
    rw [List.map_dropLast]
  refine ⟨⟨?_, ?_, hs, ?_, depth_own₁ _, allOf_listed _⟩,
    ⟨?_, ?_, Nat.zero_le _, ?_, depth_own₂ _, allOf_listed _⟩,
    ⟨?_, ?_, Nat.zero_le _, ?_, depth_own₃ _, allOf_listed _⟩⟩
  · rw [g₁, e₁']
    refine matches_dropLast a _ _ _ m₁ fun d hd => ?_
    rw [List.getLast?_map] at hd
    obtain ⟨d0, h0, rfl⟩ := Option.map_eq_some_iff.1 hd
    unfold sealBare at hsb
    rw [h0] at hsb
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hsb
    exact hsb
  · rw [g₁, e₁', List.length_dropLast, ← m₁.length_eq]
    have := List.Forall₂.length_eq w₁
    have h2 : 2 ≤ R₁.length := hsome.1
    simp only [List.length_cons, List.length_nil]
    omega
  · have u := time₁ hf
    obtain ⟨v, hv⟩ := List.dropLast_prefix ((Three.Whole.of R₁ R₂ R₃).ds₁.map rdtOf)
    rw [← hv] at u
    rw [e₁']
    exact (inTime_append _ _ _ u).1
  · rw [g₂]
    exact matches_of_forall₂ a _ m₂
  · rw [g₂, List.length_nil, Nat.add_zero]
    exact m₂.length_eq.symm
  · rw [t₁]
    exact time₂ hf
  · rw [g₃]
    exact matches_of_forall₂ a _ m₃
  · rw [g₃, List.length_nil, Nat.add_zero]
    exact m₃.length_eq.symm
  · rw [t₁, t₂]
    exact time₃ hf

theorem fitsOfOk : FitsOfOk := fitsOfOk_of fitOfOk

end VerifiableInference.Desc.Sound
