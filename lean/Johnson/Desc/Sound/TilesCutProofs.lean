-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TilesCutProofs.lean: proofs of the statements of Johnson/Desc/Sound/Tiles.lean on
the maker of the pieces: `CutBlocks`, `CutData`, `CutBack`, `CutBase`, `TiledOfFit`; and `FitsOfOk`
from `FitOfOk`.

The road to `TiledOfFit`. (1) `count_match`: where declared rounds match rounds' data, they read as
many columns, at all draws, as the data's draws ask for. (2) `sCol_isSome`, `opened_length`: at
every stage a want has a column, since a want is made only where the stage knows the tree's depth:
so a stage's view shows as many columns as there are wants. (3) `depth_agrees`: at the trees that a
stretch opens, the stage's own depth is the file's. (4) `piece_ok`: one piece is owed its stretch
and its trees are listed. (5) `matches_split`, `inTime_append` and the laws on a tree's shape carry
the premises from a chain to its first stretch and to the rest: an induction along the blocks.
Limits: those of the statements, which stand in Johnson/Desc/Sound/Tiles.lean. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Tiles
import Johnson.Desc.Sound.FoldIsRowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-! ## 1 The maker -/

theorem cutRow_nil (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
    (i base : ℕ) (ds : List RDT) (b : Block S Cl) :
    cutRow rest putBack i base ds b [] = (pieceOf b base ds putBack (rest i ds), []) := rfl

theorem cutRow_cons (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (putBack : List Fmt.RoundView)
    (i base : ℕ) (ds : List RDT) (b b' : Block S Cl) (l : List (Block S Cl)) :
    cutRow rest putBack i base ds b (b' :: l) =
      (pieceOf b base (ds.take b.rounds.length) [] (rest i (ds.take b.rounds.length)),
        (cutRow rest putBack (i + 1) (base + nTrees (ds.take b.rounds.length))
          (ds.drop b.rounds.length) b' l).1 ::
        (cutRow rest putBack (i + 1) (base + nTrees (ds.take b.rounds.length))
          (ds.drop b.rounds.length) b' l).2) := rfl

theorem cutBlocks : CutBlocks := by
  intro C F S Cl W rest putBack l
  induction l with
  | nil => intro b i base ds; rfl
  | cons b' l ih =>
    intro b i base ds
    rw [cutRow_cons]
    exact congrArg (List.cons b) (ih b' _ _ _)

theorem cutData : CutData := by
  intro C F S Cl W rest putBack l
  induction l with
  | nil =>
    intro b i base ds
    rw [cutRow_nil]
    show [pieceOf b base ds putBack (rest i ds)].flatMap (·.ds) = ds
    simp [pieceOf]
  | cons b' l ih =>
    intro b i base ds
    rw [cutRow_cons]
    show rowData _ (_ :: _) = ds
    rw [rowData_cons, ih]
    exact List.take_append_drop _ _

theorem cutBack : CutBack := by
  intro C F S Cl W rest putBack l
  induction l with
  | nil => intro b i base ds; rfl
  | cons b' l ih =>
    intro b i base ds
    rw [cutRow_cons]
    exact ih b' _ _ _

theorem cutBase : CutBase := by
  intro C F S Cl W rest putBack l b i base ds
  cases l <;> rfl

/-! ## 2 Declared rounds and rounds' data read as much -/

theorem wantsOf_nil (a : ℕ) (dep : ℕ → Option ℕ) (Rs : List Fmt.Drawn) :
    wantsOf a dep [] Rs = [] := by cases Rs <;> rfl

/-- What the draws of one round ask of one tree. -/
def treeWants (dep : ℕ → Option ℕ) (poss : List ℕ) (j : ℕ) : List Want :=
  match dep j with
  | none => []
  | some b => (Fmt.listOf (poss.map (· % 2 ^ b))).map fun x => Want.tree j x

theorem wantsOf_cons (a : ℕ) (dep : ℕ → Option ℕ) (d : RDT) (ds : List RDT) (R : Fmt.Drawn)
    (Rs : List Fmt.Drawn) : wantsOf a dep (d :: ds) (R :: Rs) =
      (d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ a))).map fun x => Want.table s.item x) ++
      (d.opens.flatMap (treeWants dep R.poss)) ++ wantsOf a dep ds Rs := rfl

theorem count_stored (a : ℕ) (poss : List ℕ) : ∀ st : List Fmt.Stored, (∀ s ∈ st, s.sh.a = a) →
    ((st.map fun s => (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (Fmt.storedKey s.item, x, s.sh.W)).flatMap id).length =
      (st.flatMap fun s => (Fmt.listOf ((Fmt.partOf s poss).map (· % 2 ^ a))).map fun x =>
        Want.table s.item x).length
  | [], _ => rfl
  | s :: st, h => by
    have ih := count_stored a poss st fun t ht => h t (List.mem_cons_of_mem _ ht)
    have hs := h s List.mem_cons_self
    simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_map, id_eq, ih, hs]

theorem count_opens (ft : ℕ) (dep : ℕ → Option ℕ) (poss : List ℕ) :
    ∀ (os : List (Fmt.Shape × Fmt.TreeSource)) (js : List ℕ),
    List.Forall₂ (fun (o : Fmt.Shape × Fmt.TreeSource) (j : ℕ) => dep j = some o.1.a) os js →
    ((os.map fun o => (Fmt.listOf (poss.map (· % 2 ^ o.1.a))).map fun x =>
        (o.1.tree - ft, x, o.1.W)).flatMap id).length = (js.flatMap (treeWants dep poss)).length
  | _, _, .nil => rfl
  | o :: os, j :: js, .cons h t => by
    have ih := count_opens ft dep poss os js t
    have e : treeWants dep poss j =
        (Fmt.listOf (poss.map (· % 2 ^ o.1.a))).map fun x => Want.tree j x := by
      unfold treeWants
      rw [h]
    simp only [List.map_cons, List.flatMap_cons, List.length_append, List.length_map, id_eq, ih, e]

/-- **Where declared rounds match rounds' data, they read as many columns as the data's draws ask
for**, at all draws. -/
theorem count_match (ft a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT) (Rs : List Fmt.Drawn), Matches a dep rs ds →
      ((groupsOf ft rs Rs).flatMap id).length = (wantsOf a dep ds Rs).length
  | [], [], Rs, _ => by cases Rs <;> rfl
  | _ :: _, [], [], _ => rfl
  | r :: rs, [], R :: Rs, h => by
    have h' : (r.stored = [] ∧ r.opens = []) ∧ Matches a dep rs [] := h
    have ih := count_match ft a dep rs [] Rs h'.2
    rw [wantsOf_nil] at ih ⊢
    have e : groupsOf ft (r :: rs) (R :: Rs) = groupsOf ft rs Rs := by
      simp only [groupsOf, h'.1.1, h'.1.2, List.map_nil, List.nil_append]
    rw [e, ih]
  | [], _ :: _, _, h => (h : False).elim
  | _ :: _, _ :: _, [], _ => rfl
  | r :: rs, d :: ds, R :: Rs, h => by
    have h' : RoundMatch a dep r d ∧ Matches a dep rs ds := h
    have ih := count_match ft a dep rs ds Rs h'.2
    obtain ⟨h1, h2, h3⟩ := h'.1
    rw [wantsOf_cons, h1]
    simp only [groupsOf, List.flatMap_append, List.length_append, ih,
      count_stored a R.poss r.stored h2, count_opens ft dep R.poss r.opens d.opens h3]

/-! ## 3 At every stage a want has a column -/

theorem length_filterMap_of_isSome {α β : Type} (f : α → Option β) : ∀ l : List α,
    (∀ x ∈ l, (f x).isSome = true) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    rw [List.filterMap_cons_some hy, List.length_cons, List.length_cons,
      length_filterMap_of_isSome f l fun z hz => h z (List.mem_cons_of_mem _ hz)]

/-- A wanted position of the stored table lies within it. -/
theorem mem_wantsOf_table (a : ℕ) (dep : ℕ → Option ℕ) (item x : ℕ) :
    ∀ (ds : List RDT) (Rs : List Fmt.Drawn), Want.table item x ∈ wantsOf a dep ds Rs → x < 2 ^ a
  | [], _, h => by rw [wantsOf_nil] at h; cases h
  | _ :: _, [], h => by cases h
  | d :: ds, R :: Rs, h => by
      unfold wantsOf at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 h
          obtain ⟨z, hz, e⟩ := List.mem_map.1 hs
          cases e
          obtain ⟨u, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hz)
          exact Nat.mod_lt _ (Nat.two_pow_pos a)
        · obtain ⟨i, _, hs⟩ := List.mem_flatMap.1 h
          cases hb : dep i with
          | none => rw [hb] at hs; cases hs
          | some b =>
            rw [hb] at hs
            obtain ⟨_, _, e⟩ := List.mem_map.1 hs
            cases e
      · exact mem_wantsOf_table a dep item x ds Rs h

/-- At every stage each want has a column: a want is made only where the stage knows the depth. -/
theorem sCol_isSome (C : CK) (T : StageD) (y : T.Ei.Str) (τ : Iop.Tr (uLT C T.ds))
    (Rs : List Fmt.Drawn) : ∀ w ∈ wantsOf T.a T.depth T.ds Rs, (sCol C T y τ w).isSome = true := by
  intro w hw
  cases w with
  | table item x =>
    have hx := mem_wantsOf_table _ _ item x _ _ hw
    show (if h : x < 2 ^ T.a then some (y.1 ⟨x, h⟩).2 else none).isSome = true
    rw [dif_pos hx]
    rfl
  | tree j x =>
    obtain ⟨-, b, hb, hx⟩ := mem_wantsOf_tree _ _ j x _ _ hw
    show (if j < T.base then (posL T.Lin j x).map y.2
      else colAtST C T.ds τ (j - T.base) x).isSome = true
    unfold StageD.depth at hb
    by_cases hj : j < T.base
    · rw [if_pos hj] at hb ⊢
      obtain ⟨p, hp⟩ := posL_of_find _ j x b hb hx
      rw [hp]
      rfl
    · rw [if_neg hj] at hb ⊢
      obtain ⟨c, hc⟩ := colAtST_isSome C _ τ _ x b hb hx
      rw [hc]
      rfl

/-- So a stage's view shows as many columns as there are wants. -/
theorem opened_length (C : CK) (T : StageD) (y : T.Ei.Str) (τ : Iop.Tr (uLT C T.ds)) :
    (sView C T y τ).opened.length =
      (wantsOf T.a T.depth T.ds (drawnT C T.ds (rhoT C T.ds τ))).length := by
  refine length_filterMap_of_isSome _ _ fun w hw => ?_
  rw [Option.isSome_map]
  exact sCol_isSome C T y τ _ w hw

/-- What a view's rounds show as drawn is what was drawn. -/
theorem rvT_drawn (C : CK) : ∀ (ds : List RDT) (τ : Iop.Tr (uLT C ds)),
    (rvT C ds τ).map (·.drawn) = drawnT C ds (rhoT C ds τ)
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => by
    show (_ :: (rvT C ds τ).map (·.drawn)) = (_ :: drawnT C ds (rhoT C ds τ))
    rw [rvT_drawn C ds τ]

/-! ## 4 Laws on the premises -/

theorem forall₂_right {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨x, hx, hr⟩ := forall₂_right t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- Every tree that matched data open has a depth. -/
theorem matches_dep (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    Matches a dep rs ds → ∀ d ∈ ds, ∀ j ∈ d.opens, ∃ a', dep j = some a'
  | _, [], _, _, hd => by cases hd
  | [], _ :: _, h, _, _ => (h : False).elim
  | r :: rs, d :: ds, h, e, he => by
    have h' : RoundMatch a dep r d ∧ Matches a dep rs ds := h
    intro j hj
    rcases List.mem_cons.1 he with rfl | he
    · obtain ⟨o, -, ho⟩ := forall₂_right h'.1.2.2 j hj
      exact ⟨_, ho⟩
    · exact matches_dep a dep rs ds h'.2 e he j hj

theorem matches_split (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (rs₁ rs₂ : List Fmt.DeclaredRound) (ds : List RDT), Matches a dep (rs₁ ++ rs₂) ds →
      Matches a dep rs₁ (ds.take rs₁.length) ∧ Matches a dep rs₂ (ds.drop rs₁.length)
  | [], rs₂, ds, h => by
    simp only [List.length_nil, List.take_zero, List.drop_zero]
    exact ⟨trivial, h⟩
  | r :: rs₁, rs₂, [], h => by
    have h' : (r.stored = [] ∧ r.opens = []) ∧ Matches a dep (rs₁ ++ rs₂) [] := h
    obtain ⟨h1, h2⟩ := matches_split a dep rs₁ rs₂ [] h'.2
    simp only [List.take_nil, List.drop_nil] at h1 h2 ⊢
    exact ⟨⟨h'.1, h1⟩, h2⟩
  | r :: rs₁, rs₂, d :: ds, h => by
    have h' : RoundMatch a dep r d ∧ Matches a dep (rs₁ ++ rs₂) ds := h
    obtain ⟨h1, h2⟩ := matches_split a dep rs₁ rs₂ ds h'.2
    simp only [List.length_cons, List.take_succ_cons, List.drop_succ_cons]
    exact ⟨⟨h'.1, h1⟩, h2⟩

theorem inTime_below : ∀ (ds : List RDT) (B : ℕ), InTime B ds → OpensBelow B ds
  | [], _, _ => fun _ hd => by cases hd
  | d :: ds, B, h => by
    have h' : (∀ j ∈ d.opens, j < B + d.trees.length) ∧ InTime (B + d.trees.length) ds := h
    intro e he j hj
    rw [nTrees_cons]
    rcases List.mem_cons.1 he with rfl | he
    · have := h'.1 j hj
      omega
    · have := inTime_below ds _ h'.2 e he j hj
      omega

theorem inTime_append : ∀ (ds es : List RDT) (B : ℕ), InTime B (ds ++ es) →
    InTime B ds ∧ InTime (B + nTrees ds) es
  | [], es, B, h => ⟨trivial, by simpa [nTrees] using h⟩
  | d :: ds, es, B, h => by
    have h' : (∀ j ∈ d.opens, j < B + d.trees.length) ∧
      InTime (B + d.trees.length) (ds ++ es) := h
    obtain ⟨h1, h2⟩ := inTime_append ds es _ h'.2
    refine ⟨⟨h'.1, h1⟩, ?_⟩
    rw [nTrees_cons, ← Nat.add_assoc]
    exact h2

theorem treeShT_lt : ∀ (ds : List RDT) (n : ℕ) (sh : Fmt.Shape), treeShT ds n = some sh →
    n < nTrees ds
  | [], _, _, h => by cases h
  | d :: ds, n, sh, h => by
    rw [treeShT_cons] at h
    rw [nTrees_cons]
    by_cases h1 : n < d.trees.length
    · omega
    · rw [if_neg h1] at h
      have := treeShT_lt ds _ sh h
      omega

theorem lastRounds_le : ∀ (l : List (Block S Cl)) (b : Block S Cl),
    lastRounds b l ≤ ((b :: l).flatMap (·.rounds)).length
  | [], b => by simp [lastRounds]
  | b' :: l, b => by
    have := lastRounds_le l b'
    rw [List.flatMap_cons, List.length_append]
    show lastRounds b' l ≤ _
    omega

/-- At the trees that a stretch opens, the stage's own depth is the file's. -/
theorem depth_agrees (F : Frame) (dep : ℕ → Option ℕ) (base : ℕ) (ds : List RDT)
    (hO : OpensBelow base ds)
    (own : ∀ n sh, treeShT ds n = some sh → dep (base + n) = some sh.a)
    (listed : ∀ j a', dep j = some a' → (F.all.filter (·.no == j)).map (·.a) = [a'])
    (hdep : ∀ d ∈ ds, ∀ j ∈ d.opens, ∃ a', dep j = some a') :
    ∀ d ∈ ds, ∀ j ∈ d.opens, (stg F base ds).depth j = dep j := by
  intro d hd j hj
  obtain ⟨a', ha⟩ := hdep d hd j hj
  rw [depth_eq]
  by_cases h : j < base
  · rw [if_pos h, ha]
    exact find_of_filter _ _ _ (listed j a' ha)
  · rw [if_neg h]
    have hlt := hO d hd j hj
    obtain ⟨sh, hsh⟩ := treeShT_some_of_lt ds (j - base) (by omega)
    have t := own _ _ hsh
    rw [show base + (j - base) = j by omega] at t
    rw [hsh, t]
    rfl

/-! ## 5 One piece, and the row -/

/-- One piece is owed its stretch, and its trees are listed. -/
theorem piece_ok (dep : ℕ → Option ℕ) (b : Block S Cl) (base : ℕ) (ds : List RDT)
    (back : List Fmt.RoundView) (x : Rest C F S W ds) (hM : Matches F.a dep b.rounds ds)
    (hlen : ds.length + back.length = b.rounds.length) (hT : InTime base ds)
    (own : ∀ n sh, treeShT ds n = some sh → dep (base + n) = some sh.a)
    (listed : ∀ j a', dep j = some a' → (F.all.filter (·.no == j)).map (·.a) = [a']) :
    (pieceOf b base ds back x).Owed ∧ (pieceOf b base ds back x).Listed := by
  refine ⟨⟨hlen, fun y τ => ?_⟩, fun n sh h => listed _ _ (own n sh h), inTime_below ds base hT⟩
  have e1 : ((sView C (stg F base ds) y τ).rounds ++ back).map (·.drawn) =
      drawnT C ds (rhoT C ds τ) ++ back.map (·.drawn) := by
    rw [List.map_append]
    exact congrArg (· ++ _) (rvT_drawn C ds τ)
  have e2 : wantsOf F.a dep ds (drawnT C ds (rhoT C ds τ) ++ back.map (·.drawn)) =
      wantsOf F.a dep ds (drawnT C ds (rhoT C ds τ)) := by
    have t := wantsOf_append F.a dep ds [] (drawnT C ds (rhoT C ds τ)) (back.map (·.drawn))
      (drawnT_length C ds _)
    rw [List.append_nil] at t
    rw [t, wantsOf_nil, List.append_nil]
  show ((groupsOf F.ft b.rounds (((sView C (stg F base ds) y τ).rounds ++ back).map
    (·.drawn))).flatMap id).length = (sView C (stg F base ds) y τ).opened.length
  rw [e1, count_match F.ft F.a dep b.rounds ds _ hM, e2,
    ← wantsOf_congr F.a (stg F base ds).depth dep ds _
      (depth_agrees F dep base ds (inTime_below ds base hT) own listed (matches_dep _ _ _ _ hM))]
  exact (opened_length C (stg F base ds) y τ).symm

theorem tiled_cons (p q : Piece C F S Cl W) (l : List (Piece C F S Cl W)) :
    Tiled p (q :: l) ↔
      p.Owed ∧ p.Listed ∧ p.back = [] ∧ q.base = p.base + p.trees ∧ Tiled q l := Iff.rfl

/-- **Under `ChainFit` the maker's pieces tile the chain.** -/
theorem tiledOfFit : TiledOfFit := by
  intro C F S Cl W rest putBack dep l
  induction l with
  | nil =>
    intro b i base ds h
    rw [cutRow_nil]
    have hM : Matches F.a dep b.rounds ds := by simpa using h.rounds
    have hl : ds.length + putBack.length = b.rounds.length := by simpa using h.count
    exact piece_ok dep b base ds putBack (rest i ds) hM hl h.inTime h.own h.listed
  | cons b' l ih =>
    intro b i base ds h
    rw [cutRow_cons]
    have hM := matches_split F.a dep b.rounds ((b' :: l).flatMap (·.rounds)) ds
      (by have t := h.rounds; rwa [List.flatMap_cons] at t)
    have hc := h.count
    rw [List.flatMap_cons, List.length_append] at hc
    have hs : putBack.length ≤ lastRounds b' l := h.sealLast
    have hr := lastRounds_le l b'
    have hle : b.rounds.length ≤ ds.length := by omega
    have hds : ds.take b.rounds.length ++ ds.drop b.rounds.length = ds := List.take_append_drop _ _
    have hT := inTime_append (ds.take b.rounds.length) (ds.drop b.rounds.length) base
      (by rw [hds]; exact h.inTime)
    have own₁ : ∀ n sh, treeShT (ds.take b.rounds.length) n = some sh →
        dep (base + n) = some sh.a := by
      intro n sh hn
      have t : treeShT (ds.take b.rounds.length ++ ds.drop b.rounds.length) n = some sh := by
        rw [treeShT_append, if_pos (treeShT_lt _ _ _ hn)]
        exact hn
      rw [hds] at t
      exact h.own n sh t
    have own₂ : ∀ n sh, treeShT (ds.drop b.rounds.length) n = some sh →
        dep (base + nTrees (ds.take b.rounds.length) + n) = some sh.a := by
      intro n sh hn
      have t : treeShT (ds.take b.rounds.length ++ ds.drop b.rounds.length)
          (nTrees (ds.take b.rounds.length) + n) = some sh := by
        rw [treeShT_append, if_neg (by omega), Nat.add_sub_cancel_left]
        exact hn
      rw [hds] at t
      have u := h.own _ sh t
      rwa [← Nat.add_assoc] at u
    have p := piece_ok dep b base (ds.take b.rounds.length) [] (rest i _) hM.1
      (by rw [List.length_take, List.length_nil]; omega) hT.1 own₁ h.listed
    refine (tiled_cons _ _ _).2 ⟨p.1, p.2, rfl, cutBase _ _ _ _ _ _ _ _ _ _ _ _, ih b' (i + 1) _ _
      ⟨hM.2, ?_, hs, hT.2, own₂, h.listed⟩⟩
    rw [List.length_drop]
    omega

/-! ## 6 The three chains -/

/-- `FitsOfOk` from `FitOfOk`. -/
theorem fitsOfOk_of (h : FitOfOk) : FitsOfOk := by
  intro a R₁ R₂ R₃ e₁ e₂ e₃ d₁ d₂ d₃ w₁ w₂ w₃ hok C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃
    rest₁ rest₂ rest₃ r g₁ g₂ g₃ hs hc
  obtain ⟨f₁, f₂, f₃⟩ := h a R₁ R₂ R₃ e₁ e₂ e₃ d₁ d₂ d₃ w₁ w₂ w₃ hok S₁ S₂ S₃ Cl b₁ l₁ b₂ l₂ b₃ l₃ r
    (dataOf a R₁ R₂ R₃).key₁ (dataOf a R₁ R₂ R₃).key₂ (dataOf a R₁ R₂ R₃).key₃ T.ft₁ T.ft₂ T.ft₃
    g₁ g₂ g₃ hs
  have p₁ := congrArg Prod.fst hc.c₁
  have q₁ := congrArg Prod.snd hc.c₁
  have p₂ := congrArg Prod.fst hc.c₂
  have q₂ := congrArg Prod.snd hc.c₂
  have p₃ := congrArg Prod.fst hc.c₃
  have q₃ := congrArg Prod.snd hc.c₃
  simp only at p₁ q₁ p₂ q₂ p₃ q₃
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p₁, q₁]; exact cutData _ _ _ _ _ _ _ _ _ _ _ _
  · rw [p₂, q₂]; exact cutData _ _ _ _ _ _ _ _ _ _ _ _
  · rw [p₃, q₃]; exact cutData _ _ _ _ _ _ _ _ _ _ _ _
  · rw [p₁]; exact cutBase _ _ _ _ _ _ _ _ _ _ _ _
  · rw [p₂]; exact cutBase _ _ _ _ _ _ _ _ _ _ _ _
  · rw [p₃]; exact cutBase _ _ _ _ _ _ _ _ _ _ _ _
  · rw [p₁, q₁]; exact tiledOfFit _ _ _ _ _ _ _ _ _ _ _ _ _ f₁
  · rw [p₂, q₂]; exact tiledOfFit _ _ _ _ _ _ _ _ _ _ _ _ _ f₂
  · rw [p₃, q₃]; exact tiledOfFit _ _ _ _ _ _ _ _ _ _ _ _ _ f₃

end VerifiableInference.Desc.Sound
