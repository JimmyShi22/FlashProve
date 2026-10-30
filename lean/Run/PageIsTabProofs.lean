-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsTabProofs.lean: the book-keeping of Merkle trees, proved: the five statements of
Run/PageIsTab.lean, on which opening in the lenient reader's output belongs to which tree in the
order of sending. Many statements of this library are written twice: a definition in the namespace
`Spec` states a proposition, and a theorem of the same name outside that namespace proves it
(lean/GLOSSARY.md).

The statements are in Run/PageIsTab.lean, under `ok S = true` (the limits of the generic
construction, the function from a description to a protocol, Run/PlanQTypes.lean) and
`LaxFacts h S o` (what the lenient reader's output is, Run/PageIs.lean). The proofs use no typed
term and no hash: lists alone; a hash function h is a parameter of `LaxFacts` and `TraceL` and
occurs nowhere else.

1. What the file contains. Proofs. Each lemma holds under the hypotheses of its statement.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems. `pi_want`, `pi_row`, `pi_rowOf`, `pi_sent`, `pi_perm`.

4. What is not claimed. See Run/PageIsTab.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsTab
import Fmt.Rules8Ok

set_option autoImplicit false

namespace Run.PQ
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src Shape Round ItemValue Item)

/-! ## Lists -/

theorem tab_one_eq {α : Type} (p : α → Bool) (l : List α) (h : (l.filter p).length = 1) (a b : α)
    (ha : a ∈ l) (pa : p a = true) (hb : b ∈ l) (pb : p b = true) : a = b := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h
  have h1 : a ∈ l.filter p := List.mem_filter.2 ⟨ha, pa⟩
  have h2 : b ∈ l.filter p := List.mem_filter.2 ⟨hb, pb⟩
  rw [hc] at h1 h2
  rw [List.mem_singleton.1 h1, List.mem_singleton.1 h2]

theorem tab_one_of_mem {α : Type} (p : α → Bool) (l : List α) (h : (l.filter p).length ≤ 1) (a : α)
    (ha : a ∈ l) (pa : p a = true) : (l.filter p).length = 1 :=
  Nat.le_antisymm h (List.length_pos_of_mem (List.mem_filter.2 ⟨ha, pa⟩))

theorem tab_find_one {α : Type} (p : α → Bool) (l : List α) (h : (l.filter p).length = 1) (a : α)
    (ha : a ∈ l) (pa : p a = true) : l.find? p = some a := by
  rcases hf : l.find? p with _ | x
  · exact absurd pa (by rw [List.find?_eq_none] at hf; simpa using hf a ha)
  · rw [tab_one_eq p l h a x ha pa (List.mem_of_find?_eq_some hf) (List.find?_some hf)]

theorem tab_lookup_find {β : Type} (k : ℕ) :
    ∀ l : List (ℕ × β), l.lookup k = (l.find? fun e => e.1 == k).map (·.2)
  | [] => rfl
  | (a, b) :: l => by
      rw [List.lookup_cons, List.find?_cons]
      by_cases e : k = a
      · subst e
        simp
      · have e1 : (k == a) = false := beq_false_of_ne e
        have e2 : (a == k) = false := beq_false_of_ne (Ne.symm e)
        simp only [e1, e2]
        exact tab_lookup_find k l

theorem tab_lookup_one {β : Type} (k : ℕ) (l : List (ℕ × β))
    (h : (l.filter fun e => e.1 == k).length = 1) (v : β) (hv : (k, v) ∈ l) :
    l.lookup k = some v := by
  rw [tab_lookup_find, tab_find_one _ l h (k, v) hv (by simp)]
  rfl

theorem tab_f2R {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ y ∈ l2, ∃ x ∈ l1, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons hab t, y, hy => by
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ⟨_, List.mem_cons_self, hab⟩
      · obtain ⟨x, hx, hxy⟩ := tab_f2R t y hy'
        exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩

theorem tab_f2L {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ x ∈ l1, ∃ y ∈ l2, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons hab t, x, hx => by
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact ⟨_, List.mem_cons_self, hab⟩
      · obtain ⟨y, hy, hxy⟩ := tab_f2L t x hx'
        exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem tab_f2count {α β : Type} {R : α → β → Prop} (p : α → Bool)
    (q : β → Bool) (hpq : ∀ x y, R x y → q y = p x) :
    ∀ {l1 : List α} {l2 : List β},
      List.Forall₂ R l1 l2 → (l2.filter q).length = (l1.filter p).length
  | _, _, .nil => rfl
  | _, _, .cons hab t => by
      rw [List.filter_cons, List.filter_cons, hpq _ _ hab]
      split
      · rw [List.length_cons, List.length_cons, tab_f2count p q hpq t]
      · exact tab_f2count p q hpq t

/-! ## What the limits of the generic construction say -/

/-- What is used of the limits: at most one root in a round; own trees alone; each own tree opened
at most once; the conditions on the rounds. -/
structure TabOk (S : _root_.Fmt.Spec) : Prop where
  one   : ∀ r ∈ S.rounds, r.entry.roots ≤ 1
  own   : ∀ x ∈ allOpens S, (ownNo x).isSome = true
  once  : ∀ n, n < nRoots S → ((allOpens S).filter fun x => ownNo x == some n).length ≤ 1
  rok   : _root_.Fmt.roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds = true

theorem tab_limits (S : _root_.Fmt.Spec) (h : ok S = true) : TabOk S := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, _⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  exact _root_.Fmt.ok_rounds h0

/-- what is used of one round's conditions -/
theorem tab_round (P : Plan) (nr : Bool) (ft : ℕ) (after : Bool) (sent : ℕ)
    (r : Round) (h : r.ok P nr ft after sent = true) :
    _root_.Fmt.countItem .root r.items = r.entry.roots ∧
    ∀ sh n, (sh, Src.own n) ∈ r.opens →
      n < sent + r.entry.roots ∧ sh.tree = ft + n ∧ sh.stored = false := by
  simp only [_root_.Fmt.Round.ok, Bool.and_eq_true, and_assoc, beq_iff_eq,
    List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2.1, fun sh n hm => ?_⟩
  have := (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2) (sh, Src.own n) hm
  have h2 : (decide (n < sent + r.entry.roots) && sh.tree == ft + n && !sh.stored && !nr) = true :=
    this.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at h2
  exact ⟨h2.1.1.1, h2.1.1.2, h2.1.2⟩

/-! ## The trees in the order of sending -/

theorem tab_shape_some (S : _root_.Fmt.Spec) (n : ℕ)
    (h : ((allOpens S).filter fun x => ownNo x == some n).length = 1) :
    ∃ sh, shapeOfOwn S n = some sh := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h
  have hm : c ∈ (allOpens S).filter fun x => ownNo x == some n := by
    rw [hc]; exact List.mem_singleton.2 rfl
  have hm' := List.mem_filter.1 hm
  exact ⟨c.1, by unfold shapeOfOwn; rw [tab_find_one _ _ h c hm'.1 hm'.2]; rfl⟩

/-- For rounds `rs` before which `sent` roots were sent: their n-th tree is the tree whose root is
the (`sent` + n)-th sent: its shape is `shapeOfOwn S (sent + n)`, or
`bareShape S.firstTree (sent + n)` where no opening names that tree; and there is none beyond their
roots; under the hypotheses of the statement. `tab_tree` below is the case of all rounds. -/
theorem tab_treeSh (S : _root_.Fmt.Spec) :
    ∀ (rs : List Round) (sent : ℕ), sent + (rs.map (·.entry.roots)).sum = nRoots S →
      (∀ r ∈ rs, r.entry.roots ≤ 1) →
      ∀ n, treeSh (rdsFrom S sent rs) n =
        if n < (rs.map (·.entry.roots)).sum then
          some ((shapeOfOwn S (sent + n)).getD (bareShape S.firstTree (sent + n)))
        else none
  | [], _, _, _, n => by simp [rdsFrom, treeSh]
  | r :: rs, sent, hsum, h1, n => by
      rw [List.map_cons, List.sum_cons] at hsum ⊢
      have ih := tab_treeSh S rs (sent + r.entry.roots) (by omega)
        (fun r' hr' => h1 r' (List.mem_cons_of_mem _ hr'))
      have hr1 := h1 r List.mem_cons_self
      by_cases h0 : r.entry.roots = 0
      · have e : treeSh (rdsFrom S sent (r :: rs)) n =
            treeSh (rdsFrom S (sent + r.entry.roots) rs) n := by
          simp only [rdsFrom, treeSh, if_pos h0]
        rw [e, ih n, h0, Nat.add_zero, Nat.zero_add]
      · have h1' : r.entry.roots = 1 := by omega
        have e : treeSh (rdsFrom S sent (r :: rs)) n =
            if n = 0 then some ((shapeOfOwn S sent).getD (bareShape S.firstTree sent))
            else treeSh (rdsFrom S (sent + r.entry.roots) rs) (n - 1) := by
          simp only [rdsFrom, treeSh, if_neg h0]
        rw [e, ih (n - 1), h1']
        by_cases hn : n = 0
        · subst hn
          rw [if_pos rfl, if_pos (by omega), Nat.add_zero]
        · rw [if_neg hn]
          by_cases hl : n - 1 < (rs.map (·.entry.roots)).sum
          · rw [if_pos hl, if_pos (by omega), show sent + 1 + (n - 1) = sent + n by omega]
          · rw [if_neg hl, if_neg (by omega)]

theorem tab_tree (S : _root_.Fmt.Spec) (t : TabOk S) (n : ℕ) :
    treeSh (rds S) n =
      if n < nRoots S then some ((shapeOfOwn S n).getD (bareShape S.firstTree n)) else none := by
  have := tab_treeSh S S.rounds 0 (by simp [nRoots]) t.one n
  rw [Nat.zero_add] at this
  exact this

/-! ## What is used of the reader's output -/

/-- an opening of the description beside the opening read -/
def TabOF (acc : List ByteArray) (poss : List ℕ) (x : Shape × Src) (y : Shape × List ℕ × OpenOut) :
    Prop :=
  y.1 = x.1 ∧
  y.2.1 = _root_.Fmt.listOf (poss.map (· % 2 ^ x.1.a)) ∧
  ∀ n, x.2 = Src.own n → acc[n]? = some y.2.2.root

/-- the rounds of the description beside the rounds read; acc: the roots sent before -/
def TabTR : List Round → List RoundOut → List ByteArray → Prop
  | [], [], _ => True
  | r :: rs, ro :: ros, acc =>
    List.Forall₂ (TabOF (acc ++ _root_.Fmt.rootsOf ro.vals) ro.drawn.poss) r.opens ro.opens ∧
    TabTR rs ros (acc ++ _root_.Fmt.rootsOf ro.vals)
  | _, _, _ => False

theorem tab_of (P : Plan) (roots : Array ByteArray) (poss : List ℕ) (x : Shape × Src)
    (y : Shape × List ℕ × OpenOut) (h : OpenFacts P roots poss x y) :
    TabOF roots.toList poss x y := by
  refine ⟨h.sh, h.xs, fun n hn => ?_⟩
  have := h.root
  rw [hn] at this
  rw [Array.getElem?_toList]
  exact this

theorem tab_tr (h : HId) (P : Plan) :
    ∀ (rs : List Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → TabTR rs ros roots.toList
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, t => t.elim
  | _ :: _, [], _, _, t => t.elim
  | r :: rs, ro :: ros, c, roots, t => by
      obtain ⟨_, _, _, _, t5, t6⟩ := t
      have e : (roots ++ (_root_.Fmt.rootsOf ro.vals).toArray).toList =
          roots.toList ++ _root_.Fmt.rootsOf ro.vals := by simp
      refine ⟨?_, ?_⟩
      · rw [← e]
        exact t5.imp fun x y hxy => tab_of P _ _ x y hxy
      · rw [← e]
        exact tab_tr h P rs ros _ _ t6

/-- Under `TabTR rs ros acc`: every opening read stands beside an opening of the description; the
roots noted there are a beginning of all roots. -/
theorem tab_pairR :
    ∀ (rs : List Round) (ros : List RoundOut) (acc : List ByteArray), TabTR rs ros acc →
      ∀ ro ∈ ros, ∀ y ∈ ro.opens, ∃ r ∈ rs, ∃ x ∈ r.opens, ∃ acc' rest,
        TabOF acc' ro.drawn.poss x y ∧
        acc ++ ros.flatMap (fun ro => _root_.Fmt.rootsOf ro.vals) = acc' ++ rest
  | [], [], _, _, _, hro, _, _ => by cases hro
  | [], _ :: _, _, t, _, _, _, _ => t.elim
  | _ :: _, [], _, t, _, _, _, _ => t.elim
  | r :: rs, ro :: ros, acc, t, ro', hro, y, hy => by
      rcases List.mem_cons.1 hro with rfl | hro'
      · obtain ⟨x, hx, hxy⟩ := tab_f2R t.1 y hy
        exact ⟨r, List.mem_cons_self, x, hx, _, ros.flatMap (fun ro => _root_.Fmt.rootsOf ro.vals),
          hxy, by rw [List.flatMap_cons, List.append_assoc]⟩
      · obtain ⟨r', hr', x, hx, acc', rest, hxy, e⟩ := tab_pairR rs ros _ t.2 ro' hro' y hy
        exact ⟨r', List.mem_cons_of_mem _ hr', x, hx, acc', rest, hxy,
          by rw [List.flatMap_cons, ← List.append_assoc]; exact e⟩

/-- Under `TabTR rs ros acc`: for every opening of the description there is an opening read of the
same shape. -/
theorem tab_pairL :
    ∀ (rs : List Round) (ros : List RoundOut) (acc : List ByteArray),
      TabTR rs ros acc → ∀ r ∈ rs, ∀ x ∈ r.opens, ∃ ro ∈ ros, ∃ y ∈ ro.opens, y.1 = x.1
  | [], [], _, _, _, hr, _, _ => by cases hr
  | [], _ :: _, _, t, _, _, _, _ => t.elim
  | _ :: _, [], _, t, _, _, _, _ => t.elim
  | r :: rs, ro :: ros, acc, t, r', hr, x, hx => by
      rcases List.mem_cons.1 hr with rfl | hr'
      · obtain ⟨y, hy, hxy⟩ := tab_f2L t.1 x hx
        exact ⟨ro, List.mem_cons_self, y, hy, hxy.1⟩
      · obtain ⟨ro', hro', y, hy, hxy⟩ := tab_pairL rs ros _ t.2 r' hr' x hx
        exact ⟨ro', List.mem_cons_of_mem _ hro', y, hy, hxy⟩

/-- Under `TabTR rs ros acc`: as many openings read as openings of the description have a shape with
a given property. -/
theorem tab_count (p : Shape → Bool) :
    ∀ (rs : List Round) (ros : List RoundOut) (acc : List ByteArray), TabTR rs ros acc →
      ((ros.flatMap (·.opens)).filter fun y => p y.1).length =
        ((rs.flatMap (·.opens)).filter fun x => p x.1).length
  | [], [], _, _ => rfl
  | [], _ :: _, _, t => t.elim
  | _ :: _, [], _, t => t.elim
  | r :: rs, ro :: ros, acc, t => by
      rw [List.flatMap_cons, List.flatMap_cons, List.filter_append, List.filter_append,
        List.length_append, List.length_append, tab_count p rs ros _ t.2]
      congr 1
      exact tab_f2count (fun x => p x.1) (fun y => p y.1) (fun x y hxy => congrArg p hxy.1) t.1

/-! ## Every opening of the description is some own tree's -/

theorem tab_rounds (P : Plan) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List Round) (after : Bool) (sent : ℕ), _root_.Fmt.roundsOk P nr ft after sent rs =
        true →
      ∀ r ∈ rs, ∀ sh n, (sh, Src.own n) ∈ r.opens →
        n < sent + (rs.map (·.entry.roots)).sum ∧ sh.tree = ft + n ∧ sh.stored = false
  | [], _, _, _, _, hr, _, _, _ => by cases hr
  | r :: rs, after, sent, h, r', hr, sh, n, hm => by
      simp only [_root_.Fmt.roundsOk, Bool.and_eq_true] at h
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 hr with rfl | hr'
      · have := (tab_round P nr ft after sent r' h.1).2 sh n hm
        exact ⟨by omega, this.2⟩
      · have := tab_rounds P nr ft rs _ _ h.2 r' hr' sh n hm
        exact ⟨by omega, this.2⟩

/-- what an opening of the description is -/
structure TabGood (S : _root_.Fmt.Spec) (x : Shape × Src) (n : ℕ) : Prop where
  src   : x.2 = Src.own n
  lt    : n < nRoots S
  tree  : x.1.tree = S.firstTree + n
  plain : x.1.stored = false
  sh    : treeSh (rds S) n = some x.1

theorem tab_ownNo (x : Shape × Src) (n : ℕ) : ownNo x = some n ↔ x.2 = Src.own n := by
  obtain ⟨sh, src⟩ := x
  cases src with
  | own k => simp [ownNo]
  | given r s => simp [ownNo]

theorem tab_good (S : _root_.Fmt.Spec) (t : TabOk S) (r : Round) (hr : r ∈ S.rounds)
    (x : Shape × Src) (hx : x ∈ r.opens) : ∃ n, TabGood S x n := by
  have hm : x ∈ allOpens S := List.mem_flatMap.2 ⟨r, hr, hx⟩
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (t.own x hm)
  have hs : x.2 = Src.own n := (tab_ownNo x n).1 hn
  have hx' : (x.1, Src.own n) ∈ r.opens := by rw [← hs]; exact hx
  have h3 := tab_rounds _ _ _ S.rounds _ _ t.rok r hr x.1 n hx'
  have hl : n < nRoots S := by have := h3.1; rw [Nat.zero_add] at this; exact this
  refine ⟨n, hs, hl, h3.2.1, h3.2.2, ?_⟩
  rw [tab_tree S t n, if_pos hl]
  unfold shapeOfOwn
  rw [tab_find_one _ _ (tab_one_of_mem _ _ (t.once n hl) x hm (by rw [hn]; simp))
      x hm (by rw [hn]; simp)]
  rfl

/-! ## What the verifier wants, as a list -/

theorem tab_wantRound (S : _root_.Fmt.Spec) (acc : List ByteArray) (poss : List ℕ) :
    ∀ {xs : List (Shape × Src)}
        {ys : List (Shape × List ℕ × OpenOut)},
      List.Forall₂ (TabOF acc poss) xs ys → (∀ x ∈ xs, ∃ n, TabGood S x n) →
    ((xs.filterMap ownNo).flatMap fun n =>
      match treeSh (rds S) n with
      | none => []
      | some s => (_root_.Fmt.listOf (poss.map (· % 2 ^ s.a))).map fun y => (n, y)) = ys.flatMap fun x => x.2.1.map fun y => (x.1.tree - S.firstTree, y)
  | _, _, .nil, _ => rfl
  | x :: xs, y :: ys, .cons hab t, hg => by
      obtain ⟨n, g⟩ := hg x List.mem_cons_self
      have e1 : ownNo x = some n := (tab_ownNo x n).2 g.src
      rw [List.filterMap_cons, e1, List.flatMap_cons, List.flatMap_cons,
        tab_wantRound S acc poss t fun x' hx' => hg x' (List.mem_cons_of_mem _ hx')]
      congr 1
      simp only [g.sh]
      rw [hab.2.1, hab.1, g.tree, Nat.add_sub_cancel_left]

theorem tab_wantL (S : _root_.Fmt.Spec) :
    ∀ (rs : List Round) (ros : List RoundOut) (acc : List ByteArray) (sent : ℕ), TabTR rs ros acc →
      (∀ r ∈ rs, ∀ x ∈ r.opens, ∃ n, TabGood S x n) →
      wantedL (rds S) (rdsFrom S sent rs) (ros.map (·.drawn)) =
        ros.flatMap fun ro =>
          ro.opens.flatMap fun x => x.2.1.map fun y => (x.1.tree - S.firstTree, y)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, t, _ => t.elim
  | _ :: _, [], _, _, t, _ => t.elim
  | r :: rs, ro :: ros, acc, sent, t, hg => by
      rw [List.flatMap_cons,
        ← tab_wantL S rs ros _ (sent + r.entry.roots) t.2 fun r' hr' =>
          hg r' (List.mem_cons_of_mem _ hr'),
        ← tab_wantRound S _ _ t.1 (hg r List.mem_cons_self)]
      rfl

theorem pi_want : Spec.pi_want := fun h S o hok hf =>
  tab_wantL S S.rounds o.rounds.toList [] 0 (tab_tr h S.plan _ _ _ _ hf.trace)
    fun r hr x hx => tab_good S (tab_limits S hok) r hr x hx

/-! ## An opening read is the opening of its tree -/

theorem tab_opensB (o : ChainOut) :
    opensB o = (o.rounds.toList.flatMap (·.opens)).map fun y => (y.1.tree, y.1.W, obOf y) := by
  unfold opensB
  rw [List.map_flatMap]
  rfl

/-- Under `TabOk S` and `TabTR S.rounds ros []`: as many openings read as openings of the
description have the number of own tree n. -/
theorem tab_cntB (S : _root_.Fmt.Spec) (t : TabOk S) (ros : List RoundOut)
    (tr : TabTR S.rounds ros []) (n : ℕ) :
    ((ros.flatMap (·.opens)).filter fun y => y.1.tree == S.firstTree + n).length =
      ((allOpens S).filter fun x => ownNo x == some n).length := by
  rw [tab_count (fun sh => sh.tree == S.firstTree + n) S.rounds ros [] tr]
  congr 1
  refine List.filter_congr fun x hx => ?_
  obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
  obtain ⟨k, g⟩ := tab_good S t r hr x hxr
  rw [g.tree, (tab_ownNo x k).2 g.src]
  by_cases e : k = n
  · subst e
    simp
  · have e1 : (S.firstTree + k == S.firstTree + n) = false := beq_false_of_ne (by omega)
    have e2 : (some k == some n) = false := beq_false_of_ne (by simpa using e)
    rw [e1, e2]

/-- Under `TabOk S` and `TabTR S.rounds ros []`, for n below the number of roots: at most one
opening read has the number of own tree n. -/
theorem tab_oneB (S : _root_.Fmt.Spec) (t : TabOk S) (ros : List RoundOut)
    (tr : TabTR S.rounds ros []) (n : ℕ) (hn : n < nRoots S) :
    ((ros.flatMap (·.opens)).filter fun y => y.1.tree == S.firstTree + n).length ≤ 1 := by
  rw [tab_cntB S t ros tr n]
  exact t.once n hn

/-- Under `TabOk S` and `TabTR S.rounds ros []`: an opening read has the number of a root sent. -/
theorem tab_readNo (S : _root_.Fmt.Spec) (t : TabOk S) (ros : List RoundOut)
    (tr : TabTR S.rounds ros []) (y : Shape × List ℕ × OpenOut) (hy : y ∈ ros.flatMap (·.opens)) :
    ∃ k, k < nRoots S ∧ y.1.tree = S.firstTree + k := by
  obtain ⟨ro, hro, hyr⟩ := List.mem_flatMap.1 hy
  obtain ⟨r, hr, x, hx, _, _, hxy, _⟩ := tab_pairR _ _ _ tr ro hro y hyr
  obtain ⟨k, g⟩ := tab_good S t r hr x hx
  exact ⟨k, g.lt, by rw [hxy.1]; exact g.tree⟩

theorem tab_row (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut) (hok : ok S = true)
    (hf : LaxFacts h S o) (ro : RoundOut) (hro : ro ∈ o.rounds.toList)
    (y : Shape × List ℕ × OpenOut) (hy : y ∈ ro.opens) :
    ∃ n, treeSh (rds S) n = some y.1 ∧ TreeRow S o n y.1 y := by
  have t := tab_limits S hok
  have tr : TabTR S.rounds o.rounds.toList [] := tab_tr h S.plan _ _ _ _ hf.trace
  obtain ⟨r, hr, x, hx, acc', rest, hxy, e⟩ := tab_pairR _ _ _ tr ro hro y hy
  obtain ⟨n, g⟩ := tab_good S t r hr x hx
  have hyB : y ∈ o.rounds.toList.flatMap (·.opens) := List.mem_flatMap.2 ⟨ro, hro, hy⟩
  have hno : y.1.tree = S.firstTree + n := by rw [hxy.1]; exact g.tree
  have h1 := tab_one_of_mem _ _ (tab_oneB S t o.rounds.toList tr n g.lt) y hyB (by rw [hno]; simp)
  refine ⟨n, by rw [hxy.1]; exact g.sh, ?_⟩
  refine { mem := ⟨ro, hro, hy⟩, shape := rfl, no := hno, plain := by rw [hxy.1]; exact g.plain,
           look := ?_, want := ?_, root := ?_ }
  · rw [tab_opensB]
    refine tab_lookup_one _ _ ?_ _ (List.mem_map.2 ⟨y, hyB, rfl⟩)
    rw [List.filter_map, List.length_map, hno]
    exact h1
  · intro y'
    rw [pi_want h S o hok hf]
    simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨ro', hro', x', hx', y'', hy'', e1, rfl⟩
      obtain ⟨r2, hr2, x2, hx2, _, _, hxy2, _⟩ := tab_pairR _ _ _ tr ro' hro' x' hx'
      obtain ⟨k, g2⟩ := tab_good S t r2 hr2 x2 hx2
      have hk : x'.1.tree = S.firstTree + k := by rw [hxy2.1]; exact g2.tree
      have hkn : k = n := by rw [hk, Nat.add_sub_cancel_left] at e1; exact e1
      have : x' = y :=
        tab_one_eq _ _ h1 x' y (List.mem_flatMap.2 ⟨ro', hro', hx'⟩)
          (by rw [hk, hkn]; simp) hyB (by rw [hno]; simp)
      rw [← this]
      exact hy''
    · intro hy'
      exact ⟨ro, hro, y, hy, y', hy', by rw [hno, Nat.add_sub_cancel_left], rfl⟩
  · have h2 : acc'[n]? = some y.2.2.root := hxy.2.2 n g.src
    have e' : rootsB o = acc' ++ rest := by rw [← e]; rfl
    obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.1 h2
    rw [e', List.getElem?_append_left hl]
    exact h2

theorem pi_rowOf : Spec.pi_rowOf := fun h S o hok hf ro hro x hx => tab_row h S o hok hf ro hro x hx

theorem pi_row : Spec.pi_row := by
  intro h S o hok hf n sh hsh
  have t := tab_limits S hok
  have tr : TabTR S.rounds o.rounds.toList [] := tab_tr h S.plan _ _ _ _ hf.trace
  rw [tab_tree S t n] at hsh
  by_cases hn : n < nRoots S
  · by_cases hex : ∃ c ∈ allOpens S, (ownNo c == some n) = true
    swap
    · -- no opening of the description names tree n
      right
      have h0 : ((allOpens S).filter fun x => ownNo x == some n) = [] :=
        List.filter_eq_nil_iff.2 fun c hc hp => hex ⟨c, hc, hp⟩
      have hB : ∀ y ∈ o.rounds.toList.flatMap (·.opens), y.1.tree ≠ S.firstTree + n := by
        have hl : ((o.rounds.toList.flatMap (·.opens)).filter fun y =>
              y.1.tree == S.firstTree + n) = [] :=
          List.length_eq_zero_iff.1 (by rw [tab_cntB S t _ tr n, h0]; rfl)
        exact fun y hy e => List.filter_eq_nil_iff.1 hl y hy (beq_iff_eq.2 e)
      have hnone : shapeOfOwn S n = none := by
        unfold shapeOfOwn
        rw [List.find?_eq_none.2 fun c hc hp => hex ⟨c, hc, hp⟩]
        rfl
      rw [if_pos hn, hnone] at hsh
      have e : sh = bareShape S.firstTree n := (Option.some.inj hsh).symm
      subst e
      refine ⟨hnone, rfl, ?_, fun y hy => ?_⟩
      · show (opensB o).lookup (S.firstTree + n) = none
        rw [tab_opensB, tab_lookup_find, List.find?_eq_none.2 fun z hz hp => ?_]
        · rfl
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
          exact hB y hy (beq_iff_eq.1 hp)
      · rw [pi_want h S o hok hf] at hy
        simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hy
        obtain ⟨ro, hro, x, hx, _, _, e1, _⟩ := hy
        have hxB : x ∈ o.rounds.toList.flatMap (·.opens) := List.mem_flatMap.2 ⟨ro, hro, hx⟩
        obtain ⟨k, _, hk⟩ := tab_readNo S t _ tr x hxB
        exact hB x hxB (by rw [hk, Nat.add_sub_cancel_left] at e1; rw [hk, e1])
    left
    obtain ⟨c, hm1, hm2⟩ := hex
    obtain ⟨r, hr, hcr⟩ := List.mem_flatMap.1 hm1
    obtain ⟨ro, hro, y, hy, hyc⟩ := tab_pairL _ _ _ tr r hr c hcr
    obtain ⟨k, hk, row⟩ := tab_row h S o hok hf ro hro y hy
    obtain ⟨k', g⟩ := tab_good S t r hr c hcr
    have e1 : k' = n := by
      have := (tab_ownNo c k').2 g.src
      rw [this] at hm2
      simpa using hm2
    have e2 : k = n := by
      have a := row.no
      rw [hyc, g.tree, e1] at a
      omega
    subst e2
    have e3 : sh = y.1 := by
      rw [if_pos hn, ← tab_tree S t k |>.trans (if_pos hn), hk] at hsh
      exact (Option.some.inj hsh).symm
    rw [e3]
    exact ⟨y, row⟩
  · rw [if_neg hn] at hsh
    cases hsh

/-! ## Roots, round by round -/

theorem tab_digest (b : ByteArray) (i : ℕ) (x : ByteArray) (j : ℕ)
    (h : _root_.Fmt.rdDigest b i = some (x, j)) : x.size = 32 := by
  unfold _root_.Fmt.rdDigest _root_.Fmt.rdBytes _root_.Fmt.slice at h
  split at h
  · rename_i hle
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ByteArray.size_extract]
    omega
  · cases h

/-- one item read: a root of 32 bytes where the item is a root, else no root -/
theorem tab_item (f : _root_.Fmt.Fld) (t : Item) (b : ByteArray) (i : ℕ) (x : ItemValue) (j : ℕ)
    (h : _root_.Fmt.readItem f t b i = some (x, j)) (l : List ItemValue) :
    (t = .root ∧
      ∃ d : ByteArray, d.size = 32 ∧ _root_.Fmt.rootsOf (x :: l) = d :: _root_.Fmt.rootsOf l) ∨
    (t ≠ .root ∧ _root_.Fmt.rootsOf (x :: l) = _root_.Fmt.rootsOf l) := by
  cases t with
  | root =>
    left
    replace h : (_root_.Fmt.rdDigest b i).map (fun y => (ItemValue.root y.1, y.2)) = some (x, j) := h
    obtain ⟨⟨d, k⟩, hd, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, d, tab_digest b i d k hd, by rw [← (Prod.mk.inj e).1]; rfl⟩
  | f =>
    right
    replace h : (_root_.Fmt.rdElt f b i).map (fun y => (ItemValue.f y.1, y.2)) = some (x, j) := h
    obtain ⟨⟨d, k⟩, _, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨by simp, by rw [← (Prod.mk.inj e).1]; rfl⟩
  | e =>
    right
    replace h : (_root_.Fmt.rdExt f b i).map (fun y => (ItemValue.e y.1, y.2)) = some (x, j) := h
    obtain ⟨⟨d, k⟩, _, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨by simp, by rw [← (Prod.mk.inj e).1]; rfl⟩
  | word =>
    right
    replace h : (_root_.Fmt.rdWord b i).map (fun y => (ItemValue.word y.1, y.2)) = some (x, j) := h
    obtain ⟨⟨d, k⟩, _, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨by simp, by rw [← (Prod.mk.inj e).1]; rfl⟩
  | answer =>
    right
    replace h : (_root_.Fmt.rdExt f b i).map (fun y => (ItemValue.answer y.1, y.2)) = some (x, j) := h
    obtain ⟨⟨d, k⟩, _, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨by simp, by rw [← (Prod.mk.inj e).1]; rfl⟩

theorem tab_items (f : _root_.Fmt.Fld) :
    ∀ (ts : List Item) (b : ByteArray) (i : ℕ) (l : List ItemValue) (j : ℕ),
      _root_.Fmt.readItems f ts b i = some (l, j) →
      (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root ts ∧
      ∀ d ∈ _root_.Fmt.rootsOf l, d.size = 32
  | [], _, _, l, _, h => by
      simp only [_root_.Fmt.readItems, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨rfl, fun d hd => by cases hd⟩
  | t :: ts, b, i, l, j, h => by
      unfold _root_.Fmt.readItems at h
      rcases h1 : _root_.Fmt.readItem f t b i with _ | ⟨x, k⟩
      · rw [h1] at h; cases h
      · rw [h1] at h
        simp only [] at h
        rcases h2 : _root_.Fmt.readItems f ts b k with _ | ⟨l', k'⟩
        · rw [h2] at h; cases h
        · rw [h2] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ih1, ih2⟩ := tab_items f ts b k l' k' h2
          rw [← h.1]
          rcases tab_item f t b i x k h1 l' with ⟨rfl, d, hd, e⟩ | ⟨hne, e⟩
          · rw [e]
            refine ⟨?_, fun d' hd' => ?_⟩
            · rw [List.length_cons, ih1]
              simp [_root_.Fmt.countItem]
            · rcases List.mem_cons.1 hd' with rfl | hd''
              · exact hd
              · exact ih2 d' hd''
          · rw [e]
            refine ⟨?_, ih2⟩
            rw [ih1]
            have : (t == Item.root) = false := beq_false_of_ne hne
            simp [_root_.Fmt.countItem, this]

theorem tab_whole (f : _root_.Fmt.Fld) (ts : List Item) (msg : ByteArray) (l : List ItemValue)
    (h : _root_.Fmt.whole (_root_.Fmt.readItems f ts) msg = some l) :
    (_root_.Fmt.rootsOf l).length = _root_.Fmt.countItem .root ts ∧
    ∀ d ∈ _root_.Fmt.rootsOf l, d.size = 32 := by
  unfold _root_.Fmt.whole at h
  rcases h1 : _root_.Fmt.readItems f ts msg 0 with _ | ⟨l', k⟩
  · rw [h1] at h; cases h
  · rw [h1] at h
    simp only [] at h
    split at h
    · rw [← Option.some.inj h]
      exact tab_items f ts msg 0 l' k h1
    · cases h

/-- Round by round: as many roots are read as the entry says, under the hypotheses of the statement.
The first half of the conclusion is the relation of `Spec.pi_sent`. -/
theorem tab_sentL (h : HId) (S : _root_.Fmt.Spec) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray)
        (after : Bool) (sent : ℕ),
      TraceL h S.plan rs ros c roots → _root_.Fmt.roundsOk S.plan nr ft after sent rs = true →
      sent + (rs.map (·.entry.roots)).sum = nRoots S → (∀ r ∈ rs, r.entry.roots ≤ 1) →
      List.Forall₂
        (fun (d : RD) (ro : RoundOut) =>
          (d.tree = none ∧ _root_.Fmt.rootsOf ro.vals = []) ∨
          (d.tree.isSome = true ∧ ∃ r : ByteArray, r.size = 32 ∧ _root_.Fmt.rootsOf ro.vals = [r]))
        (rdsFrom S sent rs) ros ∧
      (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals).length = (rs.map (·.entry.roots)).sum
  | [], [], _, _, _, _, _, _, _, _ => ⟨.nil, rfl⟩
  | [], _ :: _, _, _, _, _, t, _, _, _ => t.elim
  | _ :: _, [], _, _, _, _, t, _, _, _ => t.elim
  | r :: rs, ro :: ros, c, roots, after, sent, t, hk, hsum, h1 => by
      obtain ⟨_, t2, _, _, _, t6⟩ := t
      simp only [_root_.Fmt.roundsOk, Bool.and_eq_true] at hk
      rw [List.map_cons, List.sum_cons] at hsum
      obtain ⟨ih1, ih2⟩ := tab_sentL h S nr ft rs ros _ _ _ (sent + r.entry.roots) t6 hk.2
        (by omega) fun r' hr' => h1 r' (List.mem_cons_of_mem _ hr')
      obtain ⟨w1, w2⟩ := tab_whole _ _ _ _ t2
      rw [(tab_round _ _ _ _ _ r hk.1).1] at w1
      have hr1 := h1 r List.mem_cons_self
      refine ⟨List.Forall₂.cons ?_ ih1,
        by rw [List.flatMap_cons, List.length_append, ih2, w1, List.map_cons, List.sum_cons]⟩
      show ((if r.entry.roots = 0 then none
              else some ((shapeOfOwn S sent).getD (bareShape S.firstTree sent))) = none ∧
          _) ∨
        ((if r.entry.roots = 0 then none
              else some ((shapeOfOwn S sent).getD (bareShape S.firstTree sent))).isSome = true ∧
          _)
      by_cases h0 : r.entry.roots = 0
      · left
        rw [if_pos h0]
        exact ⟨rfl, List.length_eq_zero_iff.1 (by rw [w1, h0])⟩
      · right
        rw [if_neg h0]
        obtain ⟨d, hd⟩ :=
          List.length_eq_one_iff.1 (show (_root_.Fmt.rootsOf ro.vals).length = 1 by omega)
        exact ⟨rfl, d, w2 d (by rw [hd]; exact List.mem_singleton.2 rfl), hd⟩

theorem tab_sent (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut)
    (hok : ok S = true) (hf : LaxFacts h S o) :
    List.Forall₂
      (fun (d : RD) (ro : RoundOut) =>
        (d.tree = none ∧ _root_.Fmt.rootsOf ro.vals = []) ∨
        (d.tree.isSome = true ∧ ∃ r : ByteArray, r.size = 32 ∧ _root_.Fmt.rootsOf ro.vals = [r]))
      (rds S) o.rounds.toList ∧
    (rootsB o).length = nRoots S :=
  tab_sentL h S _ _ S.rounds o.rounds.toList _ _ _ 0 hf.trace (tab_limits S hok).rok
    (by simp [nRoots]) (tab_limits S hok).one

theorem pi_sent : Spec.pi_sent := fun h S o hok hf => (tab_sent h S o hok hf).1

theorem tab_rootsLen (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut)
    (hok : ok S = true) (hf : LaxFacts h S o) : (rootsB o).length = nRoots S :=
  (tab_sent h S o hok hf).2

/-! ## The openings read are the trees that the description opens, each once -/

theorem pi_perm : Spec.pi_perm := by
  intro h S o hok hf
  have t := tab_limits S hok
  have tr : TabTR S.rounds o.rounds.toList [] := tab_tr h S.plan _ _ _ _ hf.trace
  rw [tab_rootsLen h S o hok hf, List.perm_iff_count]
  intro n
  have hB : ∀ y ∈ o.rounds.toList.flatMap (·.opens),
      ∃ k, k < nRoots S ∧ y.1.tree = S.firstTree + k :=
    tab_readNo S t _ tr
  have e : List.count n ((o.rounds.toList.flatMap (·.opens)).map fun x => x.1.tree - S.firstTree) =
      ((o.rounds.toList.flatMap (·.opens)).filter fun y => y.1.tree == S.firstTree + n).length := by
    rw [List.count, List.countP_map, List.countP_eq_length_filter]
    congr 1
    refine List.filter_congr fun y hy => ?_
    obtain ⟨k, _, hk⟩ := hB y hy
    show (y.1.tree - S.firstTree == n) = (y.1.tree == S.firstTree + n)
    rw [hk, Nat.add_sub_cancel_left]
    by_cases e : k = n
    · subst e; simp
    · rw [beq_false_of_ne e, beq_false_of_ne (by omega)]
  rw [e, tab_cntB S t _ tr n]
  by_cases hs : (shapeOfOwn S n).isSome = true
  · -- some opening of the description names tree n: exactly one does
    obtain ⟨sh, hsh⟩ := Option.isSome_iff_exists.1 hs
    unfold shapeOfOwn at hsh
    obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.1 hsh
    have hm : x ∈ allOpens S := List.mem_of_find?_eq_some hx
    have hp : (ownNo x == some n) = true :=
      List.find?_some (p := fun o : Shape × Src => ownNo o == some n) hx
    obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hm
    obtain ⟨k, g⟩ := tab_good S t r hr x hxr
    have hk : k = n := by
      have := (tab_ownNo x k).2 g.src
      rw [this] at hp
      simpa using hp
    have hn : n < nRoots S := hk ▸ g.lt
    rw [tab_one_of_mem _ _ (t.once n hn) x hm hp,
      List.count_filter (p := fun n => (shapeOfOwn S n).isSome) hs,
      List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 hn)]
  · -- none does
    have h0 : ((allOpens S).filter fun x => ownNo x == some n) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx hp
      apply hs
      unfold shapeOfOwn
      rw [Option.isSome_map]
      exact List.find?_isSome.2 ⟨x, hx, hp⟩
    have hnot : n ∉ (List.range (nRoots S)).filter fun n => (shapeOfOwn S n).isSome := fun hm =>
      hs (List.mem_filter.1 hm).2
    rw [h0, List.count_eq_zero_of_not_mem hnot]
    rfl

end Run.PQ
