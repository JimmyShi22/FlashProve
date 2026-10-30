-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsTabProofs.lean.
TWO: CUT BY PROGRAM out of the library's Run/PageIsTabProofs.lean (only what the entry's clause
holds and stands on a declaration that the sibling says again), then turned by hand where it had to
be. THE HEAD BELOW IS THE LIBRARY's AND SPEAKS OF THE LIBRARY's FILE: much of what it announces IS
NOT HERE, and what it says of "one root | one tree a round" is not true of this file. HERE STAND
ONLY: TabOk, tab_limits, tab_treeSh, tab_tree, TabGood, tab_good, tab_wantRound, tab_wantL, pi_want,
tab_cntB, tab_oneB, tab_readNo, tab_row, pi_rowOf, pi_row, tab_sentL, tab_sent, pi_sent,
tab_rootsLen, pi_perm.

Run/PageIsTabProofs.lean: the book-keeping of Merkle trees, proved: the five statements of
Run/PageIsTab.lean (Run.PQ.Spec.pi_want, pi_row, pi_rowOf, pi_sent, pi_perm).

The statements stand in Run/PageIsTab.lean, under ok S = true (the limits of the generic
construction, Run/PlanQTypes.lean) and LaxFacts h S o (what the lenient reader's output is,
Run/PageIs.lean). The proofs use no typed term and no hash: lists alone.

1. What the file contains. Proofs. The main steps, not every lemma.
   TabOk S            What is used of the limits: at most one root in a round; own trees alone; each
                      own tree opened at most once; the conditions on the rounds.
   tab_tree           The n-th tree of the rounds' data is the tree whose root is the n-th sent:
                      treeSh (rds S) n is shapeOfOwn S n, or bareShape S.firstTree n where no
                      opening names tree n, for n below the number of roots, and none beyond.
   TabGood S x n      What an opening x of the description is: of own tree n, with n below the
                      number of roots; its number in the leaves' labels is S.firstTree + n; not
                      stored; its shape is the n-th tree's (tab_good).
   TabTR, TabOF       What is used of the reader's output, round beside round and opening beside
                      opening: the same shape; the list made from the round's drawn positions; the
                      root noted is the n-th of the roots sent so far (tab_tr, from TraceL).
   tab_pairR, tab_pairL   Every opening read stands beside one of the description, and the other way
                          round. tab_count, tab_cntB, tab_oneB: as many openings read as openings of
                          the description have a given tree's number: at most one.
   tab_row            An opening read is the opening of its tree: all fields of TreeRow.
   tab_items, tab_whole, tab_sentL   As many roots are read in a round as its entry says, each of 32
                                     bytes.

2. What is checked when the file compiles. Nothing beyond the proofs.

3. Theorems. pi_want, pi_row, pi_rowOf, pi_sent, pi_perm.

4. What is not claimed. See Run/PageIsTab.lean.

Terms: lean/GLOSSARY.md.

-/
import Run.PageIsTabProofs
import OnBytes.TypedOracleCompiler.Run.PageIs   -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQS   -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQSMore
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.PlanQTypes
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseChain
import OnBytes.TypedOracleCompiler.Run.ParseBS  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFnTag
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinDefs
import OnBytes.TypedOracleCompiler.Run.ThinTie  -- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDet  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDetProofs
import OnBytes.TypedOracleCompiler.Run.TwinTie  -- TWO: reached in the library through files that are not said again
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseThin
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.ParseLaws
import OnBytes.TypedOracleCompiler.Run.PageIsTab
import Fmt.Rules8Ok

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src Shape Round ItemValue Item)

/-! ## Lists -/

/-! ## What the road's limits say -/

/-- what is used of the limits (TWO: said again: the library's has "at most ONE root a round";
nothing below uses the clause) -/
structure TabOk (S : _root_.Fmt.Spec) : Prop where
  one   : ∀ r ∈ S.rounds, r.entry.roots ≤ TypedOracleCompiler.Iop.maxRt
  own   : ∀ x ∈ allOpens S, (ownNo x).isSome = true
  once  : ∀ n, n < nRoots S → ((allOpens S).filter fun x => ownNo x == some n).length ≤ 1
  rok   : _root_.Fmt.roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds = true

theorem tab_limits (S : _root_.Fmt.Spec) (h : ok S = true) : TabOk S := by
  simp only [ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, _⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  exact _root_.Fmt.ok_rounds h0

/-! ## The trees in the order of sending -/

/-- the n-th tree of the rounds' data is the tree whose root is the n-th sent -/
theorem tab_treeSh (S : _root_.Fmt.Spec) :
    ∀ (rs : List Round) (sent : ℕ), sent + (rs.map (·.entry.roots)).sum = nRoots S →
      ∀ n, treeSh (rdsFrom S sent rs) n =
        if n < (rs.map (·.entry.roots)).sum then
          some ((shapeOfOwn S (sent + n)).getD (bareShape S.firstTree (sent + n)))
        else none
  | [], _, _, n => by simp [rdsFrom, treeSh]
  | r :: rs, sent, hsum, n => by
      rw [List.map_cons, List.sum_cons] at hsum ⊢
      have ih := tab_treeSh S rs (sent + r.entry.roots) (by omega)
      have e : treeSh (rdsFrom S sent (r :: rs)) n =
          if n < r.entry.roots then
            ((List.range r.entry.roots).map fun k =>
              (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k)))[n]?
          else treeSh (rdsFrom S (sent + r.entry.roots) rs) (n - r.entry.roots) := by
        simp only [rdsFrom, treeSh, List.length_map, List.length_range]
      rw [e, ih (n - r.entry.roots)]
      by_cases hn : n < r.entry.roots
      · rw [if_pos hn, if_pos (by omega), List.getElem?_map, List.getElem?_range hn]
        rfl
      · rw [if_neg hn]
        by_cases hl : n - r.entry.roots < (rs.map (·.entry.roots)).sum
        · rw [if_pos hl, if_pos (by omega),
            show sent + r.entry.roots + (n - r.entry.roots) = sent + n by omega]
        · rw [if_neg hl, if_neg (by omega)]

theorem tab_tree (S : _root_.Fmt.Spec) (_t : TabOk S) (n : ℕ) :
    treeSh (rds S) n =
      if n < nRoots S then some ((shapeOfOwn S n).getD (bareShape S.firstTree n)) else none := by
  have := tab_treeSh S S.rounds 0 (by simp [nRoots]) n
  rw [Nat.zero_add] at this
  exact this

/-! ## What is used of the reader's output -/

/-! ## Every opening of the description is some own tree's -/

/-- what an opening of the description is -/
structure TabGood (S : _root_.Fmt.Spec) (x : Shape × Src) (n : ℕ) : Prop where
  src   : x.2 = Src.own n
  lt    : n < nRoots S
  tree  : x.1.tree = S.firstTree + n
  plain : x.1.stored = false
  sh    : treeSh (rds S) n = some x.1

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
      | some s => (_root_.Fmt.listOf (poss.map (· % 2 ^ s.a))).map fun y => (n, y)) = ys.flatMap fun
          x => x.2.1.map fun y => (x.1.tree - S.firstTree, y)
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

/-! ## An opening read is THE opening of its tree -/

/-- as many openings read as openings of the description have a tree's number -/
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

/-- at most one opening read has a tree's number -/
theorem tab_oneB (S : _root_.Fmt.Spec) (t : TabOk S) (ros : List RoundOut)
    (tr : TabTR S.rounds ros []) (n : ℕ) (hn : n < nRoots S) :
    ((ros.flatMap (·.opens)).filter fun y => y.1.tree == S.firstTree + n).length ≤ 1 := by
  rw [tab_cntB S t ros tr n]
  exact t.once n hn

/-- an opening read has the number of a root sent -/
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

/-- round by round: as many roots are read as the entry says -/
theorem tab_sentL (h : HId) (S : _root_.Fmt.Spec) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List Round) (ros : List RoundOut) (c : Chain) (roots : Array ByteArray)
        (after : Bool) (sent : ℕ),
      TraceL h S.plan rs ros c roots → _root_.Fmt.roundsOk S.plan nr ft after sent rs = true →
      sent + (rs.map (·.entry.roots)).sum = nRoots S →
      List.Forall₂
        (fun (d : RD) (ro : RoundOut) =>
          d.trees.length = (_root_.Fmt.rootsOf ro.vals).length ∧
          ∀ r ∈ _root_.Fmt.rootsOf ro.vals, r.size = 32)
        (rdsFrom S sent rs) ros ∧
      (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals).length = (rs.map (·.entry.roots)).sum
  | [], [], _, _, _, _, _, _, _ => ⟨.nil, rfl⟩
  | [], _ :: _, _, _, _, _, t, _, _ => t.elim
  | _ :: _, [], _, _, _, _, t, _, _ => t.elim
  | r :: rs, ro :: ros, c, roots, after, sent, t, hk, hsum => by
      obtain ⟨_, t2, _, _, _, t6⟩ := t
      simp only [_root_.Fmt.roundsOk, Bool.and_eq_true] at hk
      rw [List.map_cons, List.sum_cons] at hsum
      obtain ⟨ih1, ih2⟩ := tab_sentL h S nr ft rs ros _ _ _ (sent + r.entry.roots) t6 hk.2
        (by omega)
      obtain ⟨w1, w2⟩ := tab_whole _ _ _ _ t2
      rw [(tab_round _ _ _ _ _ r hk.1).1] at w1
      refine ⟨List.Forall₂.cons ?_ ih1,
        by rw [List.flatMap_cons, List.length_append, ih2, w1, List.map_cons, List.sum_cons]⟩
      refine ⟨?_, w2⟩
      show ((List.range r.entry.roots).map fun k =>
          (shapeOfOwn S (sent + k)).getD (bareShape S.firstTree (sent + k))).length = _
      rw [List.length_map, List.length_range, w1]

theorem tab_sent (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut)
    (hok : ok S = true) (hf : LaxFacts h S o) :
    List.Forall₂
      (fun (d : RD) (ro : RoundOut) =>
        d.trees.length = (_root_.Fmt.rootsOf ro.vals).length ∧
        ∀ r ∈ _root_.Fmt.rootsOf ro.vals, r.size = 32)
      (rds S) o.rounds.toList ∧
    (rootsB o).length = nRoots S :=
  tab_sentL h S _ _ S.rounds o.rounds.toList _ _ _ 0 hf.trace (tab_limits S hok).rok
    (by simp [nRoots])

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

end TypedOracleCompiler.Run.PQ
