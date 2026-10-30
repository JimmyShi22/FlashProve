-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageIsRows.lean: FROM THE BOOK-KEEPING OF TREES (Run/PageIsTab.lean) TO WHAT
Run/PageIsForest.lean ASKS AND GIVES. After the library's Run/PageIsRows.lean.
HERE IS PROOF WRITTEN, NOT TEXT SAID AGAIN: four inductions over the rounds that case on "has this
round a tree" go through a lemma on A ROUND's TREES.
  AS TEXT (but for the parameters Bd | leaf)   walk_root, tree_roots, wanted_le, drawn_fits, cnt_le
  LEFT TO THE LIBRARY   idxLen
  TURNED     SentRel, nTrees
  WRITTEN ANEW   rows_ind, tree_iff, cnt_range, trees_roots
  NEW        rowsT_of, treeT_iff, cntT_range (a round's trees); posAtS_inl, posAtS_inr, lt_of_posAtT
             (what posAtS says of a position of the first round | of a later)

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageIsForest
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs
import Run.PageIsRows

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
    TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
export _root_.Run.PQ (idxLen)
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- a round of the road and a round as read go together: as many trees as roots, each root of 32
bytes (Run/PageIsTab.lean: pi_sent's relation) -/
def SentRel (d : RD) (ro : RoundOut) : Prop :=
  d.trees.length = (_root_.Fmt.rootsOf ro.vals).length ∧
      ∀ r ∈ _root_.Fmt.rootsOf ro.vals, r.size = 32

theorem lt_of_posAtT (ts : List _root_.Fmt.Shape) (k x : ℕ) (p : PosT ts)
    (h : posAtT ts k x = some p) :
    k < ts.length := by
  by_contra hk
  rw [posAtT_none ts k (Nat.le_of_not_lt hk) x] at h
  cases h

section
variable (C : CK) (tbl : List (ℕ × ℕ × OpenB)) (sb : ℕ) (W : ℕ → ℕ → Prop)

theorem posAtS_cons (d : RD) (ds : List RD) (n y : ℕ) :
    posAtS C (d :: ds) n y =
      if n < d.trees.length then (posAtT d.trees n y).map .inl
      else (posAtS C ds (n - d.trees.length) y).map .inr := rfl

theorem posAtS_inl (d : RD) (ds : List RD) (n y : ℕ) (p : PosT d.trees) :
    posAtS C (d :: ds) n y = some (.inl p) ↔ posAtT d.trees n y = some p := by
  rw [posAtS_cons]
  constructor
  · intro h
    by_cases hn : n < d.trees.length
    · rw [if_pos hn] at h
      obtain ⟨q, hq, e⟩ := Option.map_eq_some_iff.1 h
      rw [hq, Sum.inl.inj e]
    · rw [if_neg hn] at h
      obtain ⟨q, -, e⟩ := Option.map_eq_some_iff.1 h
      cases e
  · intro h
    rw [if_pos (lt_of_posAtT _ _ _ _ h), h]
    rfl

theorem posAtS_inr (d : RD) (ds : List RD) (n y : ℕ) (q : OPos (uL C ds)) :
    posAtS C (d :: ds) n y = some (.inr q) ↔
      d.trees.length ≤ n ∧ posAtS C ds (n - d.trees.length) y = some q := by
  rw [posAtS_cons]
  constructor
  · intro h
    by_cases hn : n < d.trees.length
    · rw [if_pos hn] at h
      obtain ⟨q', -, e⟩ := Option.map_eq_some_iff.1 h
      cases e
    · rw [if_neg hn] at h
      obtain ⟨q', hq, e⟩ := Option.map_eq_some_iff.1 h
      exact ⟨Nat.le_of_not_lt hn, by rw [hq, Sum.inr.inj e]⟩
  · rintro ⟨hn, h⟩
    rw [if_neg (Nat.not_lt.2 hn), h]
    rfl

/-- TWO: a round's trees: from the book-keeping tree by tree to RowsT -/
theorem rowsT_of (all : List _root_.Fmt.Shape) (isRead : PosT all → Bool) (Wk : ℕ → ℕ → Prop)
    (hrow : ∀ k sh, all[k]? = some sh →
      (∃ Ob, tbl.lookup sh.tree = some (sh.W, Ob) ∧ Ob.a = sh.a ∧ Ob.ok sb sh.W = true ∧
        Ob.idx ≠ [] ∧ ∀ y, Wk k y ↔ y ∈ Ob.idx) ∨
      (tbl.lookup sh.tree = none ∧ ∀ y, ¬ Wk k y))
    (hrd : ∀ k x p, posAtT all k x = some p → (isRead p = true ↔ Wk k x)) :
    ∀ (k : ℕ) (ts : List _root_.Fmt.Shape) (R : List ByteArray), (∀ i, all[k + i]? = ts[i]?) →
      ts.length = R.length → (∀ r ∈ R, r.size = 32) → RowsT tbl sb all isRead k ts R
  | _, [], [], _, _, _ => trivial
  | _, [], _ :: _, _, h, _ => by cases h
  | _, _ :: _, [], _, h, _ => by cases h
  | k, sh :: ts, root :: R, hsuf, hl, h32 => by
    have hk : all[k]? = some sh := by simpa using hsuf 0
    refine ⟨h32 root List.mem_cons_self, ?_,
      rowsT_of all isRead Wk hrow hrd (k + 1) ts R (fun i => by
        have := hsuf (i + 1)
        rw [List.getElem?_cons_succ] at this
        rw [← this]
        congr 1
        omega) (Nat.succ.inj hl) fun r hr => h32 r (List.mem_cons_of_mem _ hr)⟩
    rcases hrow k sh hk with ⟨Ob, h1, h2, h3, h4, hw⟩ | ⟨h1, hw⟩
    · refine Or.inl ⟨Ob, h1, h2, h3, h4, fun x p hp => ?_⟩
      rw [Bool.eq_iff_iff, hrd k x p hp, decide_eq_true_iff, hw]
    · refine Or.inr ⟨h1, fun x p hp => ?_⟩
      rw [← Bool.not_eq_true, hrd k x p hp]
      exact hw x

/-- FROM THE BOOK-KEEPING OF TREES TO THE HYPOTHESIS ROUND BY ROUND -/
theorem rows_ind :
    ∀ (ds : List RD) (ros : List RoundOut) (n0 : ℕ) (isRead : OPos (uL C ds) → Bool),
      List.Forall₂ SentRel ds ros →
      (∀ n sh, treeSh ds n = some sh →
        (∃ Ob, tbl.lookup sh.tree = some (sh.W, Ob) ∧ Ob.a = sh.a ∧ Ob.ok sb sh.W = true ∧
          Ob.idx ≠ [] ∧ ∀ y, W (n0 + n) y ↔ y ∈ Ob.idx) ∨
        (tbl.lookup sh.tree = none ∧ ∀ y, ¬ W (n0 + n) y)) →
      (∀ q, isRead q = true ↔ ∃ n y, W (n0 + n) y ∧ posAtS C ds n y = some q) →
      RowsL C tbl sb ds ros isRead
  | [], _, _, _, _, _, _ => trivial
  | d :: ds, _, n0, isRead, .cons (b := ro) (l₂ := ros) hs ht, hrow, hrd => by
    obtain ⟨hlen, h32⟩ := hs
    refine ⟨rowsT_of tbl sb d.trees (fun p => isRead (.inl p)) (fun k y => W (n0 + k) y)
        (fun k sh hk => hrow k sh (by
          show (if k < d.trees.length then d.trees[k]? else _) = some sh
          rw [if_pos (List.getElem?_eq_some_iff.1 hk).1, hk]))
        (fun k x p hp => ?_) 0 d.trees _ (fun i => by rw [Nat.zero_add]) hlen h32,
      rows_ind ds ros (n0 + d.trees.length) _ ht (fun n sh h => ?_) fun q => ?_⟩
    · rw [hrd]
      constructor
      · rintro ⟨n, y, hw, hq⟩
        have hq' := (posAtS_inl C d ds n y p).1 hq
        obtain ⟨e1, e2⟩ := place_posAtT d.trees n y p hq'
        obtain ⟨e3, e4⟩ := place_posAtT d.trees k x p hp
        rw [← e3, ← e4, e1, e2]
        exact hw
      · intro hw
        exact ⟨k, x, hw, (posAtS_inl C d ds k x p).2 hp⟩
    · have h' : treeSh (d :: ds) (d.trees.length + n) = some sh := by
        show (if d.trees.length + n < d.trees.length then _
          else treeSh ds (d.trees.length + n - d.trees.length)) = some sh
        rw [if_neg (by omega), Nat.add_sub_cancel_left, h]
      rcases hrow _ sh h' with ⟨Ob', h1, h2, h3, h4, h5⟩ | ⟨h1, h5⟩
      · exact Or.inl ⟨Ob', h1, h2, h3, h4, fun y => by rw [← h5, Nat.add_assoc]⟩
      · exact Or.inr ⟨h1, fun y => by rw [Nat.add_assoc]; exact h5 y⟩
    · rw [hrd]
      constructor
      · rintro ⟨n, y, hwn, hp⟩
        obtain ⟨hn, hq⟩ := (posAtS_inr C d ds n y q).1 hp
        exact ⟨n - d.trees.length, y,
          by rw [Nat.add_assoc, Nat.add_sub_cancel' hn]; exact hwn, hq⟩
      · rintro ⟨n, y, hwn, hp⟩
        exact ⟨d.trees.length + n, y, by rw [← Nat.add_assoc]; exact hwn,
          (posAtS_inr C d ds _ y q).2 ⟨Nat.le_add_right _ _,
              by rw [Nat.add_sub_cancel_left]; exact hp⟩⟩

end

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (O : ByteArray → ByteArray) (D : PageD L .onl)
  (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray)

/-- TWO: a round's trees -/
theorem treeT_iff :
    ∀ (ts : List _root_.Fmt.Shape) (R : List ByteArray), ts.length = R.length →
      (treeAllT O D tbl run ts R = true ↔
        ∀ (k : ℕ) (sh : _root_.Fmt.Shape), ts[k]? = some sh →
          tbl.lookup sh.tree = none ∨
          ∃ x root, tbl.lookup sh.tree = some x ∧ R[k]? = some root ∧
            walkOb O D run sh.tree x.1 x.2 = root)
  | [], [], _ => ⟨fun _ k sh h => by simp at h, fun _ => rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | sh0 :: ts, r :: R, hl => by
    show (((match tbl.lookup sh0.tree with
        | none => true
        | some x =>
            decide (walkOb O D run sh0.tree x.1 x.2 = r)) && treeAllT O D tbl run ts R) = true) ↔ _
    rw [Bool.and_eq_true, treeT_iff ts R (Nat.succ.inj hl)]
    constructor
    · rintro ⟨h0, hn⟩ k sh hsh
      cases k with
      | zero =>
        obtain rfl : sh0 = sh := by simpa using hsh
        cases hl' : tbl.lookup sh0.tree with
        | none => exact Or.inl rfl
        | some x =>
          rw [hl'] at h0
          exact Or.inr ⟨x, r, rfl, rfl, of_decide_eq_true h0⟩
      | succ k => simpa using hn k sh (by simpa using hsh)
    · intro H
      refine ⟨?_, fun k sh hsh => by simpa using H (k + 1) sh (by simpa using hsh)⟩
      rcases H 0 sh0 rfl with hl' | ⟨x, root, hl', hr, hw⟩
      · rw [hl']
      · rw [hl']
        have : root = r := (Option.some.inj hr).symm
        subst this
        exact decide_eq_true hw

/-- "every tree that has a record in the table, in the order of sending, walks to its root", tree by
tree -/
theorem tree_iff :
    ∀ (ds : List RD) (ros : List RoundOut), List.Forall₂ SentRel ds ros →
      (treeAll O D tbl run ds ros = true ↔
        ∀ n sh, treeSh ds n = some sh →
          tbl.lookup sh.tree = none ∨
          ∃ x root,
            tbl.lookup sh.tree = some x ∧
            (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals)[n]? = some root ∧
            walkOb O D run sh.tree x.1 x.2 = root)
  | [], _, .nil => by
    refine ⟨fun _ n sh h => ?_, fun _ => rfl⟩
    have h' : (none : Option _root_.Fmt.Shape) = some sh := h
    cases h'
  | d :: ds, _, .cons (b := ro) (l₂ := ros) hs ht => by
    have ih := tree_iff ds ros ht
    obtain ⟨hlen, -⟩ := hs
    show ((treeAllT O D tbl run d.trees (_root_.Fmt.rootsOf ro.vals) &&
      treeAll O D tbl run ds ros) = true) ↔ _
    rw [Bool.and_eq_true, ih, treeT_iff O D tbl run d.trees _ hlen, List.flatMap_cons]
    constructor
    · rintro ⟨h0, hn⟩ n sh hsh
      have hsh' : (if n < d.trees.length then d.trees[n]? else treeSh ds (n - d.trees.length)) =
          some sh := hsh
      by_cases hlt : n < d.trees.length
      · rw [if_pos hlt] at hsh'
        rw [List.getElem?_append_left (by rw [← hlen]; exact hlt)]
        exact h0 n sh hsh'
      · rw [if_neg hlt] at hsh'
        rw [List.getElem?_append_right (by rw [← hlen]; exact Nat.le_of_not_lt hlt), ← hlen]
        exact hn _ sh hsh'
    · intro H
      refine ⟨fun k sh hk => ?_, fun n sh hsh => ?_⟩
      · have hlt : k < d.trees.length := (List.getElem?_eq_some_iff.1 hk).1
        have := H k sh (by
          show (if k < d.trees.length then d.trees[k]? else _) = some sh
          rw [if_pos hlt, hk])
        rwa [List.getElem?_append_left (by rw [← hlen]; exact hlt)] at this
      · have := H (d.trees.length + n) sh (by
          show (if d.trees.length + n < d.trees.length then _
            else treeSh ds (d.trees.length + n - d.trees.length)) = some sh
          rw [if_neg (by omega), Nat.add_sub_cancel_left, hsh])
        rwa [List.getElem?_append_right (by rw [← hlen]; exact Nat.le_add_right _ _), ← hlen,
          Nat.add_sub_cancel_left] at this

end

section
variable (Bd : Type) (leaf : Bd → Option (Nat × Nat × ByteArray))
  (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- the walk of the table's record of an opening is the walk of the opening -/
theorem walk_root (run : ByteArray)
    (x : _root_.Fmt.Shape × List ℕ × OpenOut) (hp : x.1.stored = false) :
    walkOb O (PDS Bd S C dec leaf) run x.1.tree x.1.W (obOf x) =
      rootOf (_root_.Fmt.HO O) S.cfg run x.1 x.2.1 x.2.2 := by
  obtain ⟨⟨a, W, st, tr⟩, xs, op⟩ := x
  dsimp only at hp
  subst hp
  rfl

/-- "EVERY OPENED TREE, IN THE ORDER OF SENDING" IS "EVERY OPENING, IN THE FILE'S ORDER" -/
theorem tree_roots (o : ChainOut) (run : ByteArray)
    (hok : ok S = true) (hf : LaxFacts (_root_.Fmt.HO O) S o) :
    treeAll O (PDS Bd S C dec leaf) (opensB o) run (rds S) o.rounds.toList =
      rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList := by
  rw [Bool.eq_iff_iff,
    tree_iff O (PDS Bd S C dec leaf) (opensB o) run (rds S) o.rounds.toList (pi_sent _ S o hok hf)]
  unfold rootsAll
  simp only [List.all_eq_true]
  constructor
  · intro H ro hro x hx
    obtain ⟨n, hsh, row⟩ := pi_rowOf _ S o hok hf ro hro x hx
    obtain ⟨y, root, hl, hr, hw⟩ :=
      (H n x.1 hsh).resolve_left (by rw [row.look]; exact Option.some_ne_none _)
    have hy : y = (x.1.W, obOf x) := Option.some.inj (hl.symm.trans row.look)
    have hroot : root = x.2.2.root := Option.some.inj (hr.symm.trans row.root)
    subst hy hroot
    rw [← walk_root Bd leaf O S C dec run x row.plain,
      show walkOb O (PDS Bd S C dec leaf) run x.1.tree x.1.W (obOf x) = x.2.2.root from hw]
    exact bytes_beq_self _
  · intro H n sh hsh
    rcases pi_row _ S o hok hf n sh hsh with ⟨x, row⟩ | bare
    · obtain ⟨ro, hro, hx⟩ := row.mem
      have hs := row.shape
      subst hs
      exact Or.inr
        ⟨_, _, row.look, row.root,
          (walk_root Bd leaf O S C dec run x row.plain).trans (bytes_beq _ _ (H ro hro x hx))⟩
    · exact Or.inl bare.look

end

/-! ### The number of checks -/

/-- the number of trees -/
def nTrees : List RD → ℕ
  | [] => 0
  | d :: ds => d.trees.length + nTrees ds

/-- TWO: a round's trees -/
theorem cntT_range (tbl : List (ℕ × ℕ × OpenB)) (first : ℕ) :
    ∀ (ts : List _root_.Fmt.Shape) (n0 : ℕ), (∀ k sh, ts[k]? = some sh →
        sh.tree = first + (n0 + k)) →
      cntT tbl ts = ((List.range' n0 ts.length).map fun n => idxLen tbl (first + n)).sum
  | [], _, _ => rfl
  | sh :: ts, n0, h => by
    have h0 : sh.tree = first + (n0 + 0) := h 0 sh rfl
    show idxLen tbl sh.tree + cntT tbl ts =
      ((List.range' n0 (ts.length + 1)).map fun n => idxLen tbl (first + n)).sum
    rw [cntT_range tbl first ts (n0 + 1) fun k sh' hs => by
        rw [h (k + 1) sh' (by simpa using hs)]; omega,
      List.range'_succ, List.map_cons, List.sum_cons, h0, Nat.add_zero]

theorem cnt_range (tbl : List (ℕ × ℕ × OpenB)) (first : ℕ) :
    ∀ (ds : List RD) (n0 : ℕ), (∀ n sh, treeSh ds n = some sh → sh.tree = first + (n0 + n)) →
      cntO tbl ds = ((List.range' n0 (nTrees ds)).map fun n => idxLen tbl (first + n)).sum
  | [], _, _ => rfl
  | d :: ds, n0, h => by
    show cntT tbl d.trees + cntO tbl ds =
      ((List.range' n0 (d.trees.length + nTrees ds)).map fun n => idxLen tbl (first + n)).sum
    rw [cntT_range tbl first d.trees n0 (fun k sh hk => h k sh (by
          show (if k < d.trees.length then d.trees[k]? else _) = some sh
          rw [if_pos (List.getElem?_eq_some_iff.1 hk).1, hk])),
      cnt_range tbl first ds (n0 + d.trees.length) (fun n sh hs => by
        rw [h (d.trees.length + n) sh (by
          show (if d.trees.length + n < d.trees.length then _
            else treeSh ds (d.trees.length + n - d.trees.length)) = some sh
          rw [if_neg (by omega), Nat.add_sub_cancel_left, hs])]
        omega),
      ← List.sum_append, ← List.map_append, List.range'_append_1]

theorem trees_roots :
    ∀ (ds : List RD) (ros : List RoundOut), List.Forall₂ SentRel ds ros →
      nTrees ds = (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals).length
  | [], _, .nil => rfl
  | d :: ds, _, .cons (b := ro) (l₂ := ros) hs ht => by
    rw [List.flatMap_cons, List.length_append, ← trees_roots ds ros ht, ← hs.1]
    rfl

/-- what is wanted is at most what the wiring allows, if each round's drawn positions are at most
the entry's number -/
theorem wanted_le (all : List RD) :
    ∀ (ds : List RD) (Ds : List _root_.Fmt.Drawn),
      List.Forall₂ (fun (d : RD) (D : _root_.Fmt.Drawn) => D.poss.length ≤ d.entry.poss) ds Ds →
      (wantedL all ds Ds).length ≤ nOpen ds
  | [], _, .nil => Nat.le_refl _
  | d :: ds, _, .cons (b := D) (l₂ := Ds) h ht => by
    show (_ ++ wantedL all ds Ds).length ≤
      (d.entry.poss * d.opens.length :: ds.map fun d => d.entry.poss * d.opens.length).sum
    rw [List.length_append, List.sum_cons]
    exact Nat.add_le_add (share_len all d.opens _ _ h) (wanted_le all ds Ds ht)

theorem drawn_fits (h : HId) (S : _root_.Fmt.Spec) (P : Plan) :
    ∀ (rs : List _root_.Fmt.Round)
        (ros : List RoundOut) (c : Chain) (roots : Array ByteArray) (sent : ℕ),
      TraceL h P rs ros c roots →
      List.Forall₂ (fun (d : RD) (D : _root_.Fmt.Drawn) => D.poss.length ≤ d.entry.poss)
        (rdsFrom S sent rs) (ros.map (·.drawn))
  | [], [], _, _, _, _ => .nil
  | r :: rs, ro :: ros, c, roots, sent, t => by
    obtain ⟨-, -, hd, -, -, t'⟩ := t
    refine .cons ?_ (drawn_fits h S P rs ros _ _ _ t')
    show ro.drawn.poss.length ≤ r.entry.poss
    rw [hd, CostP.drawRound_poss]
  | [], _ :: _, _, _, _, t => t.elim
  | _ :: _, [], _, _, _, t => t.elim

/-- THE VERIFIER FORMS AT MOST AS MANY CHECKS AS THE WIRING ALLOWS -/
theorem cnt_le (h : HId) (S : _root_.Fmt.Spec) (o : ChainOut)
    (hok : ok S = true) (hf : LaxFacts h S o) :
    cntO (opensB o) (rds S) ≤ nOpen (rds S) := by
  have h1 := cnt_range (opensB o) S.firstTree (rds S) 0 fun n sh hs => by
    rcases pi_row h S o hok hf n sh hs with ⟨x, row⟩ | bare
    · rw [row.no, Nat.zero_add]
    · rw [bare.shape, Nat.zero_add]
      rfl
  have h2 : nTrees (rds S) = (rootsB o).length :=
    trees_roots (rds S) o.rounds.toList (pi_sent h S o hok hf)
  have h3 : (((o.rounds.toList.flatMap (·.opens)).map fun x => x.1.tree - S.firstTree).map
        fun n => idxLen (opensB o) (S.firstTree + n)).sum =
      ((List.range (rootsB o).length).map fun n => idxLen (opensB o) (S.firstTree + n)).sum := by
    have hp := pi_perm h S o hok hf
    have hnd := hp.nodup_iff.2 (List.nodup_range.filter _)
    have hlt : ∀ n ∈ (o.rounds.toList.flatMap (·.opens)).map (fun x => x.1.tree - S.firstTree),
        n < (rootsB o).length :=
      fun n hn => List.mem_range.1 (List.mem_filter.1 (hp.mem_iff.1 hn)).1
    rw [← List.sum_toFinset _ hnd, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    refine Finset.sum_subset
      (fun n hn => Finset.mem_range.2 (hlt n (List.mem_toFinset.1 hn))) fun n _ hn => ?_
    unfold idxLen
    cases hl : (opensB o).lookup (S.firstTree + n) with
    | none => rfl
    | some y =>
      obtain ⟨ro, hro, hy⟩ := List.mem_flatMap.1 (mem_of_lookup _ _ _ hl)
      obtain ⟨x, hx, hxy⟩ := List.mem_map.1 hy
      refine absurd
        (List.mem_toFinset.2 (List.mem_map.2 ⟨x, List.mem_flatMap.2 ⟨ro, hro, hx⟩, ?_⟩)) hn
      rw [show x.1.tree = S.firstTree + n from congrArg Prod.fst hxy, Nat.add_sub_cancel_left]
  have h4 : ((o.rounds.toList.flatMap (·.opens)).map fun x => x.1.tree - S.firstTree).map
        (fun n => idxLen (opensB o) (S.firstTree + n)) =
      (o.rounds.toList.flatMap (·.opens)).map fun x => x.2.1.length := by
    rw [List.map_map]
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨ro, hro, hx'⟩ := List.mem_flatMap.1 hx
    obtain ⟨n, -, row⟩ := pi_rowOf h S o hok hf ro hro x hx'
    show idxLen (opensB o) (S.firstTree + (x.1.tree - S.firstTree)) = x.2.1.length
    rw [show S.firstTree + (x.1.tree - S.firstTree) = x.1.tree by rw [row.no]; omega]
    unfold idxLen
    rw [row.look]
    rfl
  have h5 : (wanted (rds S) (o.rounds.toList.map (·.drawn))).length =
      ((o.rounds.toList.flatMap (·.opens)).map fun x => x.2.1.length).sum := by
    rw [pi_want h S o hok hf, ← List.flatMap_assoc, List.length_flatMap]
    simp only [List.length_map]
  have h6 : (wanted (rds S) (o.rounds.toList.map (·.drawn))).length ≤ nOpen (rds S) :=
    wanted_le (rds S) (rds S) _ (drawn_fits h S S.plan S.rounds o.rounds.toList _ _ 0 hf.trace)
  rw [h1, h2, ← List.range_eq_range', ← h3, h4, ← h5]
  exact h6

end TypedOracleCompiler.Run.PQ
