-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeLaws.lean: the lists of read leaves of a whole file (rdWhole,
OnBytes/Maker/ListedWhole.lean) are the right ones: they meet LeavesOK
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedForests.lean) at the file's wire records and at the test "is this
position among those that the file's description reads".

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Main names.
  risingOf_mem, risingOf_rising: risingOf l has the members of l and rises strictly.
  leavesOK_trees: LeavesT from an equation for each tree, by the tree's place in the list of lists.
  leavesOK_readAt_some, leavesOK_readAt_none: readAt where a position stands, and where none does.
  leavesOK_round: the lists of one written round's trees are the right ones.
  leavesOK_app: LeavesOK along two shapes laid behind each other.
  rdChain_length, rdChain_local, rdChain_shared: a chain's lists, for local and for shared rounds.
  leavesOK_mem_leafWants: a pair is among leafWants exactly if its want is in the list.
  leavesOK_wantsOf_lt, leavesOK_wantsAll_lt: a wanted leaf lies below 2 ^ (its tree's depth).
  leavesOK_treeShT_lt: a tree that has a shape is one of the stretch's trees.
  leavesOK_whole: **the lists of the whole file are the right ones.**

Limits. Nothing on the stored table's read positions (rdEWhole). Nothing on where openings stand in
a proof string. Nothing on the time that a run takes. Nothing on soundness. The program does
not import this file.


-/
import OnBytes.Maker.ListedWhole
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-! ## risingOf -/

/-- risingOf l has the members of l. -/
theorem risingOf_mem (l : List ℕ) (j : ℕ) : j ∈ risingOf l ↔ j ∈ l := by
  unfold risingOf
  rw [List.mem_mergeSort, List.mem_dedup]

/-- risingOf l rises strictly. -/
theorem risingOf_rising (l : List ℕ) : (risingOf l).Pairwise (· < ·) := by
  unfold risingOf
  have h1 : (l.dedup.mergeSort fun a b => decide (a ≤ b)).Pairwise
      (fun a b => decide (a ≤ b) = true) :=
    List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1)
        (of_decide_eq_true h2)))
      (fun a b => by
        rcases Nat.le_total a b with h | h
        · exact Bool.or_eq_true_iff.2 (Or.inl (decide_eq_true h))
        · exact Bool.or_eq_true_iff.2 (Or.inr (decide_eq_true h))) _
  have h2 : (l.dedup.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.2 (List.nodup_dedup l)
  exact (h1.and h2).imp fun h => Nat.lt_of_le_of_ne (of_decide_eq_true h.1) h.2

/-! ## The trees of one round -/

/-- LeavesT from an equation for each tree, by the tree's place in the list of lists. -/
theorem leavesOK_trees {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (isRead : r.Pos → Bool) :
    ∀ (ds : List ℕ) (k : ℕ) (jss : List (List ℕ)),
      (∀ i, i < ds.length → jss.getD i [] =
        (List.range (2 ^ ds.getD i 0)).filter (readAt (posAt (k + i)) isRead)) →
      LeavesT posAt isRead k ds jss
  | [], _, _, _ => trivial
  | d :: ds, k, jss, h => by
    refine ⟨?_, leavesOK_trees posAt isRead ds (k + 1) jss.tail fun i hi => ?_⟩
    · have h0 := h 0 (Nat.succ_pos _)
      have e : jss.getD 0 [] = jss.headD [] := by cases jss <;> rfl
      rw [← e, h0]
      rfl
    · have h1 := h (i + 1) (Nat.succ_lt_succ hi)
      have e : jss.getD (i + 1) [] = jss.tail.getD i [] := by cases jss <;> simp
      rw [← e, h1, List.getD_cons_succ, show k + (i + 1) = k + 1 + i by omega]

/-- readAt where a position stands. -/
theorem leavesOK_readAt_some {r : Round} (posAt : ℕ → Option r.Pos) (isRead : r.Pos → Bool)
    {j : ℕ} {p : r.Pos} (h : posAt j = some p) : readAt posAt isRead j = isRead p := by
  simp only [readAt, h]

/-- readAt where no position stands. -/
theorem leavesOK_readAt_none {r : Round} (posAt : ℕ → Option r.Pos) (isRead : r.Pos → Bool)
    {j : ℕ} (h : posAt j = none) : readAt posAt isRead j = false := by
  simp only [readAt, h]

/-- The lists of one written round's trees are the right ones. b: the number of the round's first
tree. ws: the wanted pairs of a tree's number and a leaf. -/
theorem leavesOK_round (C : CK) (d : RDT) (isRead : PosT d.trees → Bool) (ws : List (ℕ × ℕ))
    (b : ℕ) (hR : ∀ p, isRead p = true ↔ (b + treeIn d.trees p, leafIn d.trees p) ∈ ws)
    (hB : ∀ k x sh, d.trees[k]? = some sh → (b + k, x) ∈ ws → x < 2 ^ sh.a) :
    LeavesT (r := (roundT C d).up) (posAtT d.trees) isRead 0 (d.trees.map (·.a))
      ((List.range d.trees.length).map fun k =>
        risingOf ((ws.filter fun w => w.1 == b + k).map (·.2))) := by
  refine leavesOK_trees (r := (roundT C d).up) (posAtT d.trees) isRead _ 0 _ fun i hi => ?_
  rw [List.length_map] at hi
  have hs : d.trees[i]? = some (d.trees[i]'hi) := List.getElem?_eq_getElem hi
  have e1 : ((List.range d.trees.length).map fun k =>
        risingOf ((ws.filter fun w => w.1 == b + k).map (·.2))).getD i [] =
      risingOf ((ws.filter fun w => w.1 == b + i).map (·.2)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have e2 : (d.trees.map (·.a)).getD i 0 = (d.trees[i]'hi).a := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hs]
    rfl
  rw [e1, e2, Nat.zero_add]
  refine rising_eq_filter (risingOf_rising _) fun j => ?_
  have hm : j ∈ risingOf ((ws.filter fun w => w.1 == b + i).map (·.2)) ↔ (b + i, j) ∈ ws := by
    rw [risingOf_mem, List.mem_map]
    constructor
    · rintro ⟨⟨n, y⟩, hw, rfl⟩
      obtain ⟨h1, h2⟩ := List.mem_filter.1 hw
      have e : n = b + i := beq_iff_eq.1 h2
      subst e
      exact h1
    · intro h
      exact ⟨(b + i, j), List.mem_filter.2 ⟨h, beq_self_eq_true _⟩, rfl⟩
  rw [hm]
  constructor
  · intro hw
    have hj := hB i j _ hs hw
    obtain ⟨p, hp⟩ := posAtT_some d.trees i j _ hs hj
    obtain ⟨h1, h2⟩ := in_posAtT d.trees i j p hp
    refine ⟨hj, ?_⟩
    rw [leavesOK_readAt_some (r := (roundT C d).up) _ isRead hp]
    exact (hR p).2 (by rw [h1, h2]; exact hw)
  · rintro ⟨_, hr⟩
    cases hp : posAtT d.trees i j with
    | none =>
      rw [leavesOK_readAt_none (r := (roundT C d).up) _ isRead hp] at hr
      cases hr
    | some p =>
      rw [leavesOK_readAt_some (r := (roundT C d).up) _ isRead hp] at hr
      obtain ⟨h1, h2⟩ := in_posAtT d.trees i j p hp
      have h3 := (hR p).1 hr
      rwa [h1, h2] at h3

/-! ## Shapes laid behind each other -/

/-- LeavesOK along two shapes laid behind each other. -/
theorem leavesOK_app {lam K : ℕ} : ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u}
    (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B) (isRead : OPos (s ++ u) → Bool)
    (rd₁ rd₂ : Leaves), rd₁.length = s.length →
    LeavesOK s A W (fun p => isRead (OPos.left p)) rd₁ →
    LeavesOK u B V (fun p => isRead (OPos.right (s := s) p)) rd₂ →
    LeavesOK (s ++ u) (RoundSplits.app A B) (WireSB.app W V) isRead (rd₁ ++ rd₂)
  | [], _, _, _, _, _, _, [], _, _, _, h => h
  | [], _, _, _, _, _, _, _ :: _, _, hl, _, _ => by cases hl
  | _ :: _, _, _, _, _, _, _, [], _, hl, _, _ => by cases hl
  | _ :: _, _, (_, _), _, (_, W), V, isRead, _ :: rd₁, rd₂, hl, h1, h2 =>
    ⟨h1.1, h1.2.1,
      leavesOK_app W V (fun p => isRead (.inr p)) rd₁ rd₂ (Nat.succ.inj hl) h1.2.2 h2⟩

/-! ## A chain's written rounds -/

/-- One entry for each round. -/
theorem rdChain_length (shared : Bool) (ws : List (ℕ × ℕ)) :
    ∀ (ds : List RDT) (b : ℕ), (rdChain shared ws b ds).length = ds.length
  | [], _ => rfl
  | d :: ds, b => congrArg (· + 1) (rdChain_length shared ws ds (b + d.trees.length))

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- The lists of a chain of local rounds are the right ones. b: the number of the chain's first
tree. A position counts as read exactly if its tree and leaf are among ws; a leaf among ws lies
below its tree's number of leaves. -/
theorem rdChain_local (ws : List (ℕ × ℕ)) :
    ∀ (ds : List RDT) (b : ℕ) (isRead : OPos (uLT C ds) → Bool),
      (∀ q, isRead q = true ↔ (b + treeAt C ds q, leafAt C ds q) ∈ ws) →
      (∀ n x sh, treeShT ds n = some sh → (b + n, x) ∈ ws → x < 2 ^ sh.a) →
      LeavesOK (uLT C ds) (RoundSplits.allLocal (uLT C ds)) (wiresLo C K chal ds) isRead
        (rdChain false ws b ds)
  | [], _, _, _, _ => trivial
  | d :: ds, b, isRead, hR, hB => by
    have h1 := leavesOK_round C d (fun p => isRead (.inl p)) ws b (fun p => hR (.inl p))
      (fun k x sh hk => hB k x sh (by
        have hl : k < d.trees.length := (List.getElem?_eq_some_iff.1 hk).1
        rw [treeShT_cons, if_pos hl]
        exact hk))
    have h2 := rdChain_local ws ds (b + d.trees.length) (fun q => isRead (.inr q))
      (fun q => by
        rw [hR (.inr q), Nat.add_assoc]
        rfl)
      (fun n x sh hn hw => hB (d.trees.length + n) x sh
        (by
          rw [treeShT_cons, if_neg (by omega), Nat.add_sub_cancel_left]
          exact hn)
        (by
          rw [← Nat.add_assoc]
          exact hw))
    exact ⟨trivial, h1, h2⟩

/-- The same for a chain of shared rounds. -/
theorem rdChain_shared (ws : List (ℕ × ℕ)) :
    ∀ (ds : List RDT) (b : ℕ) (isRead : OPos (uLT C ds) → Bool),
      (∀ q, isRead q = true ↔ (b + treeAt C ds q, leafAt C ds q) ∈ ws) →
      (∀ n x sh, treeShT ds n = some sh → (b + n, x) ∈ ws → x < 2 ^ sh.a) →
      LeavesOK (uLT C ds) (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) (wiresSh C K chal ds) isRead
        (rdChain true ws b ds)
  | [], _, _, _, _ => trivial
  | d :: ds, b, isRead, hR, hB => by
    have h1 := leavesOK_round C d (fun p => isRead (.inl p)) ws b (fun p => hR (.inl p))
      (fun k x sh hk => hB k x sh (by
        have hl : k < d.trees.length := (List.getElem?_eq_some_iff.1 hk).1
        rw [treeShT_cons, if_pos hl]
        exact hk))
    have h2 := rdChain_shared ws ds (b + d.trees.length) (fun q => isRead (.inr q))
      (fun q => by
        rw [hR (.inr q), Nat.add_assoc]
        rfl)
      (fun n x sh hn hw => hB (d.trees.length + n) x sh
        (by
          rw [treeShT_cons, if_neg (by omega), Nat.add_sub_cancel_left]
          exact hn)
        (by
          rw [← Nat.add_assoc]
          exact hw))
    exact ⟨h1, trivial, h2⟩

end

/-! ## The wants -/

/-- A pair is among leafWants exactly if the want for that tree and leaf is in the list. -/
theorem leavesOK_mem_leafWants (j x : ℕ) :
    ∀ ws : List Want, (j, x) ∈ leafWants ws ↔ Want.tree j x ∈ ws
  | [] => by simp only [leafWants, List.not_mem_nil]
  | .tree _ _ :: ws => by
    simp only [leafWants, List.mem_cons, leavesOK_mem_leafWants j x ws, Prod.mk.injEq,
      Want.tree.injEq]
  | .table _ _ :: ws => by
    simp only [leafWants, List.mem_cons, leavesOK_mem_leafWants j x ws, reduceCtorEq, false_or]

/-- A wanted leaf lies below 2 ^ (its tree's depth). -/
theorem leavesOK_wantsOf_lt (a : ℕ) (dep : ℕ → Option ℕ) :
    ∀ (ds : List RDT) (Rs : List Fmt.Drawn) (j x : ℕ), Want.tree j x ∈ wantsOf a dep ds Rs →
      ∃ b, dep j = some b ∧ x < 2 ^ b
  | [], _, _, _, h => by simp only [wantsOf, List.not_mem_nil] at h
  | _ :: _, [], _, _, h => by simp only [wantsOf, List.not_mem_nil] at h
  | d :: ds, R :: Rs, j, x, h => by
    rw [wantsOf] at h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨s, _, hs⟩ := List.mem_flatMap.1 h
        obtain ⟨y, _, e⟩ := List.mem_map.1 hs
        cases e
      · obtain ⟨j', _, hj⟩ := List.mem_flatMap.1 h
        cases hd : dep j' with
        | none =>
          simp only [hd, List.not_mem_nil] at hj
        | some b =>
          simp only [hd] at hj
          obtain ⟨y, hy, e⟩ := List.mem_map.1 hj
          cases e
          obtain ⟨z, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hy)
          exact ⟨b, hd, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩
    · exact leavesOK_wantsOf_lt a dep ds Rs j x h

/-- A tree that has a shape is one of the stretch's trees. -/
theorem leavesOK_treeShT_lt : ∀ (ds : List RDT) (n : ℕ) (sh : Fmt.Shape),
    treeShT ds n = some sh → n < (ds.map (·.trees.length)).sum
  | [], _, _, h => by cases h
  | d :: ds, n, sh, h => by
    rw [treeShT_cons] at h
    show n < d.trees.length + (ds.map (·.trees.length)).sum
    by_cases hn : n < d.trees.length
    · omega
    · rw [if_neg hn] at h
      have h1 := leavesOK_treeShT_lt ds _ sh h
      omega

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- A leaf wanted by any of the three chains lies below 2 ^ (its tree's depth). -/
theorem leavesOK_wantsAll_lt (ρ : Rho (chainsOf C D tF tJ t3).sh) (j x : ℕ)
    (h : Want.tree j x ∈ wantsAll C D tF tJ t3 ρ) : ∃ b, D.depth j = some b ∧ x < 2 ^ b := by
  rcases List.mem_append.1 h with h | h
  · exact leavesOK_wantsOf_lt _ _ _ _ j x h
  · rcases List.mem_append.1 h with h | h
    · exact leavesOK_wantsOf_lt _ _ _ _ j x h
    · exact leavesOK_wantsOf_lt _ _ _ _ j x h

variable {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The lists of the whole file are the right ones.** -/
theorem leavesOK_whole (x : Xi) (ρ : Rho (chainsOf C D tF tJ t3).sh)
    (pl : Plains (chainsOf C D tF tJ t3).sh) :
    LeavesOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh
      (fun p => decide (p ∈ (wholeDesc C D tF tJ t3 silent run).reads x ρ pl))
      (rdWhole C D tF tJ t3 ρ) := by
  have hW : ∀ j y, (j, y) ∈ leafWants (wantsAll C D tF tJ t3 ρ) →
      ∃ b, D.depth j = some b ∧ y < 2 ^ b := fun j y h =>
    leavesOK_wantsAll_lt C D tF tJ t3 ρ j y ((leavesOK_mem_leafWants j y _).1 h)
  have c₁ := rdChain_local C K chal (leafWants (wantsAll C D tF tJ t3 ρ)) D.ds₁ 0
    (fun q => decide ((chainsOf C D tF tJ t3).i₁ q ∈
      (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ))
    (fun q => by
      rw [decide_eq_true_iff, Nat.zero_add, leavesOK_mem_leafWants]
      exact reads₁ C D tF tJ t3 silent run ρ q)
    (fun n y sh hn hw => by
      obtain ⟨b, hb, hy⟩ := hW _ _ hw
      have hl : n < D.t₁ := leavesOK_treeShT_lt D.ds₁ n sh hn
      rw [Nat.zero_add] at hb
      unfold WholeD.depth at hb
      rw [if_pos hl, hn] at hb
      cases hb
      exact hy)
  have c₂ := rdChain_shared C K chal (leafWants (wantsAll C D tF tJ t3 ρ)) D.ds₂ D.t₁
    (fun q => decide ((chainsOf C D tF tJ t3).i₂ q ∈
      (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ))
    (fun q => by
      rw [decide_eq_true_iff, leavesOK_mem_leafWants]
      exact reads₂ C D tF tJ t3 silent run ρ q)
    (fun n y sh hn hw => by
      obtain ⟨b, hb, hy⟩ := hW _ _ hw
      have hl : n < D.t₂ := leavesOK_treeShT_lt D.ds₂ n sh hn
      unfold WholeD.depth at hb
      rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos hl, hn] at hb
      cases hb
      exact hy)
  have c₃ := rdChain_local C K chal (leafWants (wantsAll C D tF tJ t3 ρ)) D.ds₃ (D.t₁ + D.t₂)
    (fun q => decide ((chainsOf C D tF tJ t3).i₃ q ∈
      (reductionOfWholeFile C D tF tJ t3 silent run).reads ρ))
    (fun q => by
      rw [decide_eq_true_iff, leavesOK_mem_leafWants]
      exact reads₃ C D tF tJ t3 silent run ρ q)
    (fun n y sh hn hw => by
      obtain ⟨b, hb, hy⟩ := hW _ _ hw
      unfold WholeD.depth at hb
      rw [if_neg (by omega), if_neg (by omega),
        show D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n by omega, hn] at hb
      cases hb
      exact hy)
  have l₁ : (rdChain false (leafWants (wantsAll C D tF tJ t3 ρ)) 0 D.ds₁).length =
      (uLT C D.ds₁).length := by rw [rdChain_length, length_uLT]
  have l₂ : (rdChain true (leafWants (wantsAll C D tF tJ t3 ρ)) D.t₁ D.ds₂).length =
      (uLT C D.ds₂).length := by rw [rdChain_length, length_uLT]
  exact ⟨trivial, trivial, leavesOK_app _ _ _ _ _ l₁ c₁
    ⟨trivial, trivial, leavesOK_app _ _ _ _ _ l₂ c₂ ⟨trivial, trivial, c₃⟩⟩⟩

end

end OnBytes.Maker

#print axioms OnBytes.Maker.leavesOK_whole
