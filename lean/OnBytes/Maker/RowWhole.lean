-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RowWhole.lean: the three stages of a file in a row (OnBytes/Maker/Row.lean, `rowOf`)
decide as the reduction of the whole file (OnBytes/Maker/Whole.lean, `reductionOfWholeFile`).

Main names.
  `rowOf_of_whole`: under `RowFit` (OnBytes/Maker/RowFit.lean: what the comparison asks of a file's
    data and of the two lists of trees left behind the first and behind the second chain), and
    where the whole's test on what the three silent rounds send gives the row's three tests: where
    the whole file's verifier says yes at an instance, stored table and transcript, the row says
    yes there. The whole's run is three runs in a row (`runRow`).

Limits: of the field `out` alone, and one way: from the whole's yes to the row's. `RowFit` is a
hypothesis here. Nothing on soundness.


-/
import OnBytes.Maker.RowLaws
import OnBytes.Maker.RowFit
import Fmt.Rules6Laws

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ _root_.Compile.Joined _root_.CompileK.Joined

/-! ## Wants -/

/-- The wants hang on the depths only at the trees that the rounds open. -/
theorem wantsOf_congr (a : ℕ) (dep dep' : ℕ → Option ℕ) : ∀ (ds : List RDT) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, ∀ j ∈ d.opens, dep j = dep' j) → wantsOf a dep ds Rs = wantsOf a dep' ds Rs
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: ds, R :: Rs, h => by
      have ih := wantsOf_congr a dep dep' ds Rs fun e he => h e (List.mem_cons_of_mem _ he)
      unfold wantsOf
      rw [ih]
      congr 2
      refine List.flatMap_congr fun j hj => ?_
      rw [h d List.mem_cons_self j hj]

/-- A wanted leaf of a tree: a round opens the tree, the tree has a depth, and the leaf lies within
it. -/
theorem mem_wantsOf_tree (a : ℕ) (dep : ℕ → Option ℕ) (j x : ℕ) :
    ∀ (ds : List RDT) (Rs : List Fmt.Drawn), Want.tree j x ∈ wantsOf a dep ds Rs →
      (∃ d ∈ ds, j ∈ d.opens) ∧ ∃ b, dep j = some b ∧ x < 2 ^ b
  | [], _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, R :: Rs, h => by
      unfold wantsOf at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 h
          obtain ⟨_, _, e⟩ := List.mem_map.1 hs
          cases e
        · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.1 h
          cases hb : dep i with
          | none => rw [hb] at hs; cases hs
          | some b =>
            rw [hb] at hs
            obtain ⟨z, hz, e⟩ := List.mem_map.1 hs
            cases e
            obtain ⟨u, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hz)
            exact ⟨⟨d, List.mem_cons_self, hi⟩, b, hb, Nat.mod_lt _ (Nat.two_pow_pos b)⟩
      · obtain ⟨⟨e, he, hj⟩, hb⟩ := mem_wantsOf_tree a dep j x ds Rs h
        exact ⟨⟨e, List.mem_cons_of_mem _ he, hj⟩, hb⟩

/-! ## Positions in a list of trees left -/

/-- What `posL` finds is a leaf of a tree with the number asked for, and the leaf asked for. -/
theorem posL_spec (L : List LeftT) (j x : ℕ) (p : PosL L) (h : posL L j x = some p) :
    (L.get p.1).no = j ∧ p.2.val = x := by
  obtain ⟨i, _, hi⟩ := List.exists_of_findSome?_eq_some h
  by_cases h1 : (L.get i).no = j
  · rw [if_pos h1] at hi
    by_cases h2 : x < 2 ^ (L.get i).a
    · rw [dif_pos h2] at hi
      cases Option.some.inj hi
      exact ⟨h1, rfl⟩
    · rw [dif_neg h2] at hi
      cases hi
  · rw [if_neg h1] at hi
    cases hi

/-- `posL` finds a leaf wherever the list has the tree at a depth that holds the leaf. -/
theorem posL_isSome (L : List LeftT) (j x : ℕ) (l : LeftT) (hl : l ∈ L) (hn : l.no = j)
    (hx : x < 2 ^ l.a) : ∃ p, posL L j x = some p := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
  have : (posL L j x).isSome = true := by
    unfold posL
    rw [List.findSome?_isSome_iff]
    exact ⟨i, List.mem_finRange i, by rw [if_pos hn, dif_pos hx]; rfl⟩
  exact Option.isSome_iff_exists.1 this

/-- The same from the first entry with that number. -/
theorem posL_of_find (L : List LeftT) (j x b : ℕ)
    (hf : (L.find? (·.no == j)).map (·.a) = some b) (hx : x < 2 ^ b) :
    ∃ p, posL L j x = some p := by
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hf
  exact posL_isSome L j x l (List.mem_of_find?_eq_some hl)
    (by simpa using List.find?_some hl) hx

/-! ## A tree's column is there wherever the leaf lies within the tree -/

theorem posAtT_isSome : ∀ (ts : List Fmt.Shape) (n x : ℕ) (s : Fmt.Shape), ts[n]? = some s →
    x < 2 ^ s.a → ∃ p, posAtT ts n x = some p
  | [], _, _, _, h, _ => by cases h
  | t :: _, 0, x, s, h, hx => by
      cases Option.some.inj (show some t = some s from h)
      exact ⟨_, dif_pos hx⟩
  | _ :: ts, n + 1, x, s, h, hx => by
      obtain ⟨p, hp⟩ := posAtT_isSome ts n x s h hx
      exact ⟨.inr p, by show (posAtT ts n x).map Sum.inr = _; rw [hp]; rfl⟩

theorem colAtST_isSome (C : CK) : ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)) (n x b : ℕ),
    (treeShT ds n).map (·.a) = some b → x < 2 ^ b → ∃ c, colAtST C ds τ n x = some c
  | [], _, _, _, _, h, _ => by cases h
  | d :: ds, (m, _, τ), n, x, b, h, hx => by
      rw [treeShT_cons] at h
      rw [colAtST_cons]
      by_cases hn : n < d.trees.length
      · rw [if_pos hn] at h
        rw [if_pos hn]
        obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨p, hp⟩ := posAtT_isSome d.trees n x s hs hx
        exact ⟨_, by rw [hp]; rfl⟩
      · rw [if_neg hn] at h
        rw [if_neg hn]
        exact colAtST_isSome C ds τ _ x b h hx

/-! ## What is asked of the data and of the two lists of trees left -/

theorem sCol_tree (C : CK) (S : StageD) (yS : S.Ei.Str) (τS : Iop.Tr (uLT C S.ds)) (j x : ℕ) :
    sCol C S yS τS (.tree j x) =
      if j < S.base then (posL S.Lin j x).map yS.2 else colAtST C S.ds τS (j - S.base) x := rfl

/-- A column of a tree at hand is the column of its source, where the list has the leaf and the
source has the column. -/
theorem sCol_through (C : CK) (S : StageD) (yS : S.Ei.Str) (τS : Iop.Tr (uLT C S.ds)) (j x : ℕ)
    (hj : j < S.base) (src : ℕ → ℕ → Option (List UInt64))
    (hy : ∀ p : PosL S.Lin, yS.2 p = (src (S.Lin.get p.1).no p.2.val).getD [])
    (hp : ∃ p, posL S.Lin j x = some p) (hc : ∃ c, src j x = some c) :
    sCol C S yS τS (.tree j x) = src j x := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨c, hc⟩ := hc
  obtain ⟨h1, h2⟩ := posL_spec _ _ _ _ hp
  rw [sCol_tree, if_pos hj, hp]
  show some (yS.2 p) = _
  rw [hy p, h1, h2, hc]
  rfl

section
variable (C : CK) (D : WholeD) (L₁ L₂ : List LeftT) (y : (oneExternalString (2 ^ D.a) SgX).Str)
  (τ₁ : Iop.Tr (uLT C D.ds₁)) (τ₂ : Iop.Tr (uLT C D.ds₂)) (τ₃ : Iop.Tr (uLT C D.ds₃))

/-- The three stages' implicit instances, as the row hands them on. -/
def imp₁ : (D.st₁ L₁).Ei.Str := (y, fun p => p.1.elim0)
def imp₂ : (D.st₂ L₁ L₂).Ei.Str := (y, sLeft C (D.st₁ L₁) (imp₁ D L₁ y) τ₁)
def imp₃ : (D.st₃ L₂).Ei.Str := (y, sLeft C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂)

/-! ### Depths -/

theorem depth₁ (F : RowFit D L₁ L₂) :
    ∀ d ∈ D.ds₁, ∀ j ∈ d.opens, (D.st₁ L₁).depth j = D.depth j := by
  intro d hd j hj
  show (if j < 0 then (([] : List LeftT).find? (·.no == j)).map (·.a)
    else (treeShT D.ds₁ (j - 0)).map (·.a)) = _
  unfold WholeD.depth
  rw [if_neg (Nat.not_lt_zero j), Nat.sub_zero, if_pos (F.o₁ d hd j hj)]

theorem depth₂ (F : RowFit D L₁ L₂) :
    ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, (D.st₂ L₁ L₂).depth j = D.depth j := by
  intro d hd j hj
  show (if j < D.t₁ then (L₁.find? (·.no == j)).map (·.a)
    else (treeShT D.ds₂ (j - D.t₁)).map (·.a)) = _
  unfold WholeD.depth
  by_cases h : j < D.t₁
  · rw [if_pos h, if_pos h, F.l₁ d hd j hj h]
  · have := F.o₂ d hd j hj
    rw [if_neg h, if_neg h, if_pos (by omega)]

theorem depth₃ (F : RowFit D L₁ L₂) :
    ∀ d ∈ D.ds₃, ∀ j ∈ d.opens, (D.st₃ L₂).depth j = D.depth j := by
  intro d hd j hj
  show (if j < D.t₁ + D.t₂ then (L₂.find? (·.no == j)).map (·.a)
    else (treeShT D.ds₃ (j - (D.t₁ + D.t₂))).map (·.a)) = _
  by_cases h : j < D.t₁ + D.t₂
  · rw [if_pos h, F.l₂ d hd j hj h]
  · unfold WholeD.depth
    rw [if_neg h, if_neg (by omega), if_neg (by omega), Nat.sub_sub]

/-! ### Columns -/

theorem col₁ (j x : ℕ) :
    sCol C (D.st₁ L₁) (imp₁ D L₁ y) τ₁ (.tree j x) = colAtST C D.ds₁ τ₁ j x := by
  rw [sCol_tree, if_neg (show ¬ j < (D.st₁ L₁).base from Nat.not_lt_zero j)]
  show colAtST C D.ds₁ τ₁ (j - 0) x = _
  rw [Nat.sub_zero]

theorem col₂_left (j x : ℕ) (hj : j < D.t₁) (hp : ∃ p, posL L₁ j x = some p)
    (hc : ∃ c, colAtST C D.ds₁ τ₁ j x = some c) :
    sCol C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ (.tree j x) = colAtST C D.ds₁ τ₁ j x :=
  sCol_through C (D.st₂ L₁ L₂) _ τ₂ j x hj (fun n z => colAtST C D.ds₁ τ₁ n z)
    (fun p => by
      show (sCol C (D.st₁ L₁) (imp₁ D L₁ y) τ₁ (.tree _ _)).getD [] = _
      rw [col₁]
      rfl) hp hc

theorem col₂_own (j x : ℕ) (hj : ¬ j < D.t₁) :
    sCol C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ (.tree j x) =
      colAtST C D.ds₂ τ₂ (j - D.t₁) x := by
  rw [sCol_tree, if_neg (show ¬ j < (D.st₂ L₁ L₂).base from hj)]
  rfl

theorem colOf_tree_eq (j x : ℕ) : colOf C D y τ₁ τ₂ τ₃ (.tree j x) =
    if j < D.t₁ then colAtST C D.ds₁ τ₁ j x
    else if j - D.t₁ < D.t₂ then colAtST C D.ds₂ τ₂ (j - D.t₁) x
    else colAtST C D.ds₃ τ₃ (j - D.t₁ - D.t₂) x := rfl

/-- A tree of the first two chains, at a leaf within its depth: the second stage has the whole's
column, and there is one. L: that the first list has the leaf, where the tree is the first
chain's. -/
theorem col₂_whole (j x b : ℕ) (hj : j < D.t₁ + D.t₂) (hb : D.depth j = some b) (hx : x < 2 ^ b)
    (hL : j < D.t₁ → ∃ p, posL L₁ j x = some p) :
    sCol C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ (.tree j x) = colOf C D y τ₁ τ₂ τ₃ (.tree j x) ∧
      ∃ c, colOf C D y τ₁ τ₂ τ₃ (.tree j x) = some c := by
  unfold WholeD.depth at hb
  rw [colOf_tree_eq]
  by_cases h : j < D.t₁
  · rw [if_pos h] at hb
    rw [if_pos h]
    have hc := colAtST_isSome C D.ds₁ τ₁ j x b hb hx
    exact ⟨col₂_left C D L₁ L₂ y τ₁ τ₂ j x h (hL h) hc, hc⟩
  · have h2 : j - D.t₁ < D.t₂ := by omega
    rw [if_neg h, if_pos h2] at hb
    rw [if_neg h, if_pos h2]
    exact ⟨col₂_own C D L₁ L₂ y τ₁ τ₂ j x h, colAtST_isSome C D.ds₂ τ₂ _ x b hb hx⟩

variable (F : RowFit D L₁ L₂)
include F

theorem stage₁_col (Rs : List Fmt.Drawn) : ∀ w ∈ wantsOf D.a D.depth D.ds₁ Rs,
    sCol C (D.st₁ L₁) (imp₁ D L₁ y) τ₁ w = colOf C D y τ₁ τ₂ τ₃ w := by
  intro w hw
  cases w with
  | table item x => rfl
  | tree j x =>
    obtain ⟨⟨d, hd, hj⟩, _⟩ := mem_wantsOf_tree _ _ j x _ _ hw
    rw [col₁, colOf_tree_eq, if_pos (F.o₁ d hd j hj)]

theorem stage₂_col (Rs : List Fmt.Drawn) : ∀ w ∈ wantsOf D.a D.depth D.ds₂ Rs,
    sCol C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ w = colOf C D y τ₁ τ₂ τ₃ w := by
  intro w hw
  cases w with
  | table item x => rfl
  | tree j x =>
    obtain ⟨⟨d, hd, hj⟩, b, hb, hx⟩ := mem_wantsOf_tree _ _ j x _ _ hw
    refine (col₂_whole C D L₁ L₂ y τ₁ τ₂ τ₃ j x b (F.o₂ d hd j hj) hb hx fun h => ?_).1
    refine posL_of_find L₁ j x b ?_ hx
    rw [F.l₁ d hd j hj h]
    unfold WholeD.depth at hb
    rwa [if_pos h] at hb

theorem stage₃_col (Rs : List Fmt.Drawn) : ∀ w ∈ wantsOf D.a D.depth D.ds₃ Rs,
    sCol C (D.st₃ L₂) (imp₃ C D L₁ L₂ y τ₁ τ₂) τ₃ w = colOf C D y τ₁ τ₂ τ₃ w := by
  intro w hw
  cases w with
  | table item x => rfl
  | tree j x =>
    obtain ⟨⟨d, hd, hj⟩, b, hb, hx⟩ := mem_wantsOf_tree _ _ j x _ _ hw
    by_cases h : j < D.t₁ + D.t₂
    · have hf : (L₂.find? (·.no == j)).map (·.a) = some b := by rw [F.l₂ d hd j hj h, hb]
      obtain ⟨e, c, hc⟩ := col₂_whole C D L₁ L₂ y τ₁ τ₂ τ₃ j x b h hb hx fun h1 => by
        obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hf
        have hn : l.no = j := by simpa using List.find?_some hl
        obtain ⟨l', hl', hn', ha⟩ := F.l₂₁ l (List.mem_of_find?_eq_some hl) (by rw [hn]; exact h1)
        exact posL_isSome L₁ j x l' hl' (by rw [hn', hn])
          (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) ha))
      rw [← e]
      exact sCol_through C (D.st₃ L₂) _ τ₃ j x h
        (fun n z => sCol C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ (.tree n z)) (fun _ => rfl)
        (posL_of_find L₂ j x b hf hx) ⟨c, e.trans hc⟩
    · rw [sCol_tree, if_neg (show ¬ j < (D.st₃ L₂).base from h), colOf_tree_eq, if_neg (by omega),
        if_neg (by omega), Nat.sub_sub]
      rfl

end

/-! ## Views and tests -/

section
variable (C : CK) (D : WholeD)

/-- A stage's view is the whole's, where its wants and its columns are. -/
theorem sView_whole (S : StageD) (yS : S.Ei.Str) (τS : Iop.Tr (uLT C S.ds))
    (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ₁ : Iop.Tr (uLT C D.ds₁)) (τ₂ : Iop.Tr (uLT C D.ds₂))
    (τ₃ : Iop.Tr (uLT C D.ds₃)) (ws : List Want) (hw : sWants C S (rhoT C S.ds τS) = ws)
    (hc : ∀ w ∈ ws, sCol C S yS τS w = colOf C D y τ₁ τ₂ τ₃ w) :
    sView C S yS τS = viewOf C D y τ₁ τ₂ τ₃ (rvT C S.ds τS) S.key ws := by
  unfold sView viewOf
  rw [hw]
  congr 1
  refine List.filterMap_congr fun w hm => ?_
  rw [hc w hm]
  cases w <;> rfl

/-- The test on the stored table's symbols is the whole's, where the table is. -/
theorem sCarries_whole (S : StageD) (ha : S.a = D.a) (yS : S.Ei.Str)
    (y : (oneExternalString (2 ^ D.a) SgX).Str) (hy : ∀ x (h : x < 2 ^ S.a) (h' : x < 2 ^ D.a),
                   yS.1 ⟨x, h⟩ = y ⟨x, h'⟩) (ws : List Want) : sCarries S yS ws = carriesOf D y ws := by
  unfold sCarries carriesOf
  refine List.all_congr rfl fun w => ?_
  cases w with
  | table item x =>
    by_cases h : x < 2 ^ D.a
    · have h' : x < 2 ^ S.a := by rw [ha]; exact h
      simp only [dif_pos h, dif_pos h', hy x h' h]
    · have h' : ¬ x < 2 ^ S.a := by rw [ha]; exact h
      simp only [dif_neg h, dif_neg h']
  | tree j x => rfl

end

/-! ## The row's output, written out -/

/-- The three runs in a row, as one run on three views. -/
def runRow {Y X₁ X₂ : Type} (run₁ : Y → View → Option X₁) (run₂ : X₁ → View → Option X₂)
    (run₃ : X₂ → View → Bool) (x : Y) (v₁ v₂ v₃ : View) : Bool :=
  match run₁ x v₁ with
  | none => false
  | some x₁ =>
    match run₂ x₁ v₂ with
    | none => false
    | some x₂ => run₃ x₂ v₃

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (L₁ L₂ : List LeftT) {Y X₁ X₂ : Type} (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
  (ok3 : X₂ → T3 → Bool) (run₁ : Y → View → Option X₁) (run₂ : X₁ → View → Option X₂)
  (run₃ : X₂ → View → Bool)

/-- The row's output, by unfolding. -/
theorem rowOf_out_eq (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf C D tF tJ t3).sh) :
    (rowOf C D tF tJ t3 L₁ L₂ okF okJ ok3 run₁ run₂ run₃).ior.out x y τ =
      (if okF x ((chainsOf C D tF tJ t3).msgF τ).2 then
        (if sTests C (D.st₁ L₁) (imp₁ D L₁ y) ((chainsOf C D tF tJ t3).tr₁ τ) then
          run₁ x (sView C (D.st₁ L₁) (imp₁ D L₁ y) ((chainsOf C D tF tJ t3).tr₁ τ)) else none)
        else none).bind fun x₁ =>
      (if okJ x₁ ((chainsOf C D tF tJ t3).msgJ τ).2 then
        (if sTests C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y ((chainsOf C D tF tJ t3).tr₁ τ))
            ((chainsOf C D tF tJ t3).tr₂ τ) then
          run₂ x₁ (sView C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y ((chainsOf C D tF tJ t3).tr₁ τ))
            ((chainsOf C D tF tJ t3).tr₂ τ)) else none)
        else none).bind fun x₂ =>
      if ok3 x₂ ((chainsOf C D tF tJ t3).msg3 τ).2 then
        (if (sTests C (D.st₃ L₂) (imp₃ C D L₁ L₂ y ((chainsOf C D tF tJ t3).tr₁ τ)
              ((chainsOf C D tF tJ t3).tr₂ τ)) ((chainsOf C D tF tJ t3).tr₃ τ) &&
            run₃ x₂ (sView C (D.st₃ L₂) (imp₃ C D L₁ L₂ y ((chainsOf C D tF tJ t3).tr₁ τ)
              ((chainsOf C D tF tJ t3).tr₂ τ)) ((chainsOf C D tF tJ t3).tr₃ τ))) = true
          then some () else none)
        else none := rfl

end

/-! ## The comparison -/

theorem carriesOf_append_eq (D : WholeD) (y : (oneExternalString (2 ^ D.a) SgX).Str) (u v : List Want) :
    carriesOf D y (u ++ v) = (carriesOf D y u && carriesOf D y v) := by
  unfold carriesOf
  rw [List.all_append]

theorem runRow_true {Y X₁ X₂ : Type} {run₁ : Y → View → Option X₁} {run₂ : X₁ → View → Option X₂}
    {run₃ : X₂ → View → Bool} {x : Y} {v₁ v₂ v₃ : View}
    (h : runRow run₁ run₂ run₃ x v₁ v₂ v₃ = true) :
    ∃ x₁ x₂, run₁ x v₁ = some x₁ ∧ run₂ x₁ v₂ = some x₂ ∧ run₃ x₂ v₃ = true := by
  unfold runRow at h
  cases h1 : run₁ x v₁ with
  | none => rw [h1] at h; cases h
  | some x₁ =>
    rw [h1] at h
    have h' : (match run₂ x₁ v₂ with
      | none => false
      | some x₂ => run₃ x₂ v₃) = true := h
    cases h2 : run₂ x₁ v₂ with
    | none => rw [h2] at h'; cases h'
    | some x₂ =>
      rw [h2] at h'
      exact ⟨x₁, x₂, rfl, h2, h'⟩

section
variable (C : CK) (D : WholeD) (L₁ L₂ : List LeftT) (y : (oneExternalString (2 ^ D.a) SgX).Str)
  (τ₁ : Iop.Tr (uLT C D.ds₁)) (τ₂ : Iop.Tr (uLT C D.ds₂)) (τ₃ : Iop.Tr (uLT C D.ds₃))

/-- the three chains' wants, from their parts of a transcript -/
def w₁Of : List Want := wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ τ₁))
def w₂Of : List Want := wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ τ₂))
def w₃Of : List Want := wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ τ₃))

variable (F : RowFit D L₁ L₂)
include F

theorem sWants₁ : sWants C (D.st₁ L₁) (rhoT C D.ds₁ τ₁) = w₁Of C D τ₁ :=
  wantsOf_congr _ _ _ _ _ (depth₁ D L₁ L₂ F)

theorem sWants₂ : sWants C (D.st₂ L₁ L₂) (rhoT C D.ds₂ τ₂) = w₂Of C D τ₂ :=
  wantsOf_congr _ _ _ _ _ (depth₂ D L₁ L₂ F)

theorem sWants₃ : sWants C (D.st₃ L₂) (rhoT C D.ds₃ τ₃) = w₃Of C D τ₃ :=
  wantsOf_congr _ _ _ _ _ (depth₃ D L₁ L₂ F)

theorem sView₁ : sView C (D.st₁ L₁) (imp₁ D L₁ y) τ₁ =
    viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₁ τ₁) D.key₁ (w₁Of C D τ₁) :=
  sView_whole C D (D.st₁ L₁) _ τ₁ y τ₁ τ₂ τ₃ _ (sWants₁ C D L₁ L₂ τ₁ F)
    (stage₁_col C D L₁ L₂ y τ₁ τ₂ τ₃ F _)

theorem sView₂ : sView C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ =
    viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₂ τ₂) D.key₂ (w₂Of C D τ₂) :=
  sView_whole C D (D.st₂ L₁ L₂) _ τ₂ y τ₁ τ₂ τ₃ _ (sWants₂ C D L₁ L₂ τ₂ F)
    (stage₂_col C D L₁ L₂ y τ₁ τ₂ τ₃ F _)

theorem sView₃ : sView C (D.st₃ L₂) (imp₃ C D L₁ L₂ y τ₁ τ₂) τ₃ =
    viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₃ τ₃) D.key₃ (w₃Of C D τ₃) :=
  sView_whole C D (D.st₃ L₂) _ τ₃ y τ₁ τ₂ τ₃ _ (sWants₃ C D L₁ L₂ τ₃ F)
    (stage₃_col C D L₁ L₂ y τ₁ τ₂ τ₃ F _)

theorem sTests₁ : sTests C (D.st₁ L₁) (imp₁ D L₁ y) τ₁ =
    (passT C D.ds₁ (rhoT C D.ds₁ τ₁) && fullOf D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ τ₁)) &&
      carriesOf D y (w₁Of C D τ₁)) := by
  show (passT C D.ds₁ (rhoT C D.ds₁ τ₁) && fullOf D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ τ₁)) &&
    sCarries (D.st₁ L₁) (imp₁ D L₁ y) (sWants C (D.st₁ L₁) (rhoT C D.ds₁ τ₁))) = _
  rw [sWants₁ C D L₁ L₂ τ₁ F, sCarries_whole D (D.st₁ L₁) rfl _ y fun _ _ _ => rfl]

theorem sTests₂ : sTests C (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁) τ₂ =
    (passT C D.ds₂ (rhoT C D.ds₂ τ₂) && fullOf D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ τ₂)) &&
      carriesOf D y (w₂Of C D τ₂)) := by
  show (passT C D.ds₂ (rhoT C D.ds₂ τ₂) && fullOf D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ τ₂)) &&
    sCarries (D.st₂ L₁ L₂) (imp₂ C D L₁ L₂ y τ₁)
      (sWants C (D.st₂ L₁ L₂) (rhoT C D.ds₂ τ₂))) = _
  rw [sWants₂ C D L₁ L₂ τ₂ F, sCarries_whole D (D.st₂ L₁ L₂) rfl _ y fun _ _ _ => rfl]

theorem sTests₃ : sTests C (D.st₃ L₂) (imp₃ C D L₁ L₂ y τ₁ τ₂) τ₃ =
    (passT C D.ds₃ (rhoT C D.ds₃ τ₃) && fullOf D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ τ₃)) &&
      carriesOf D y (w₃Of C D τ₃)) := by
  show (passT C D.ds₃ (rhoT C D.ds₃ τ₃) && fullOf D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ τ₃)) &&
    sCarries (D.st₃ L₂) (imp₃ C D L₁ L₂ y τ₁ τ₂) (sWants C (D.st₃ L₂) (rhoT C D.ds₃ τ₃))) = _
  rw [sWants₃ C D L₁ L₂ τ₃ F, sCarries_whole D (D.st₃ L₂) rfl _ y fun _ _ _ => rfl]

end

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (L₁ L₂ : List LeftT) {Y X₁ X₂ : Type} (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
  (ok3 : X₂ → T3 → Bool) (run₁ : Y → View → Option X₁) (run₂ : X₁ → View → Option X₂)
  (run₃ : X₂ → View → Bool) (silent : Y → TF → TJ → T3 → Bool)

/-- The whole's output, by unfolding. -/
theorem wholeIOR_out_eq (run : Y → View → View → View → Bool) (x : Y)
    (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf C D tF tJ t3).sh) :
    (reductionOfWholeFile C D tF tJ t3 silent run).out x y τ =
      if (passT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ)) &&
          passT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ)) &&
          passT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ)) &&
          fullOf D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ))) &&
          fullOf D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ))) &&
          fullOf D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ))) &&
          carriesOf D y (w₁Of C D ((chainsOf C D tF tJ t3).tr₁ τ) ++
            (w₂Of C D ((chainsOf C D tF tJ t3).tr₂ τ) ++
              w₃Of C D ((chainsOf C D tF tJ t3).tr₃ τ))) &&
          silent x ((chainsOf C D tF tJ t3).msgF τ).2 ((chainsOf C D tF tJ t3).msgJ τ).2
            ((chainsOf C D tF tJ t3).msg3 τ).2 &&
          run x
            (viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
              ((chainsOf C D tF tJ t3).tr₃ τ) (rvT C D.ds₁ ((chainsOf C D tF tJ t3).tr₁ τ)) D.key₁
              (w₁Of C D ((chainsOf C D tF tJ t3).tr₁ τ)))
            (viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
              ((chainsOf C D tF tJ t3).tr₃ τ) (rvT C D.ds₂ ((chainsOf C D tF tJ t3).tr₂ τ)) D.key₂
              (w₂Of C D ((chainsOf C D tF tJ t3).tr₂ τ)))
            (viewOf C D y ((chainsOf C D tF tJ t3).tr₁ τ) ((chainsOf C D tF tJ t3).tr₂ τ)
              ((chainsOf C D tF tJ t3).tr₃ τ) (rvT C D.ds₃ ((chainsOf C D tF tJ t3).tr₃ τ)) D.key₃
              (w₃Of C D ((chainsOf C D tF tJ t3).tr₃ τ)))) = true
        then some () else none := rfl

/-- **Where the whole file's verifier says yes, the row does.** The whole's run is the three runs in
a row. F: the fit of the data and the two lists of trees left. hF, hJ, h3: where the whole's test on
what the three silent rounds send says yes, so do the row's three tests: the first on the instance,
the second and the third on whatever claims the runs have handed on. Of the field `out` alone. -/
theorem rowOf_of_whole (F : RowFit D L₁ L₂)
    (hF : ∀ x a b c, silent x a b c = true → okF x a = true)
    (hJ : ∀ x a b c v x₁, silent x a b c = true → run₁ x v = some x₁ → okJ x₁ b = true)
    (h3 : ∀ x a b c v v' x₁ x₂, silent x a b c = true → run₁ x v = some x₁ →
      run₂ x₁ v' = some x₂ → ok3 x₂ c = true)
    (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str) (τ : Tr (chainsOf C D tF tJ t3).sh)
    (h : (reductionOfWholeFile C D tF tJ t3 silent (runRow run₁ run₂ run₃)).out x y τ = some ()) :
    (rowOf C D tF tJ t3 L₁ L₂ okF okJ ok3 run₁ run₂ run₃).ior.out x y τ = some () := by
  rw [wholeIOR_out_eq] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, carriesOf_append_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨p₁, p₂⟩, p₃⟩, f₁⟩, f₂⟩, f₃⟩, c₁, c₂, c₃⟩, hs⟩, hr⟩ := hc
    obtain ⟨x₁, x₂, r₁, r₂, r₃⟩ := runRow_true hr
    rw [rowOf_out_eq, sTests₁ C D L₁ L₂ y _ F, sTests₂ C D L₁ L₂ y _ _ F,
      sTests₃ C D L₁ L₂ y _ _ _ F,
      sView₁ C D L₁ L₂ y _ ((chainsOf C D tF tJ t3).tr₂ τ) ((chainsOf C D tF tJ t3).tr₃ τ) F,
      sView₂ C D L₁ L₂ y _ _ ((chainsOf C D tF tJ t3).tr₃ τ) F, sView₃ C D L₁ L₂ y _ _ _ F,
      hF x _ _ _ hs, p₁, f₁, c₁, r₁]
    show (if okJ x₁ _ = true then _ else none).bind _ = some ()
    rw [hJ x _ _ _ _ x₁ hs r₁, p₂, f₂, c₂, r₂]
    show (if ok3 x₂ _ = true then _ else none) = some ()
    rw [h3 x _ _ _ _ _ x₁ x₂ hs r₁ r₂, p₃, f₃, c₃, r₃]
    rfl
  · cases h

end

end OnBytes.Maker
