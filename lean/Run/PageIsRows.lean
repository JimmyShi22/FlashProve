-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsRows.lean: lemmas on the Merkle openings in a proof file, for the comparison of two
verifiers in Run/PageIs.lean: under the hypotheses below, "every opened tree in the order of
sending" is "every opening in the file's order", and the number of checks is at most what the wiring
allows.

Definitions, lemmas with their proofs; no Spec.
Run/PageIs.lean compares two verifiers of a proof file: the compiled verifier on what a lenient
reader cuts out of the file, and the format's strict verifier. This file is a tool for one part of
that comparison, `Spec.pi_after`. It leads from the statements of Run/PageIsTab.lean (which opening
in the reader's output belongs to which tree in the order of sending) to what the lemmas of
Run/PageIsForest.lean assume (`RowsL`) and yield (`treeAll`, `cntO`).
Throughout, ds is a list of rounds' data (`RD`, Run/PlanQTypes.lean; `rds S` for a description S of
a file's rounds), ros is a list of rounds as a reader hands them out, and tbl is a table that has,
under a tree's number, the tree's width and the record of its opening (`OpenB`, Run/ParseBS.lean). A
position is listed if it is in the record's list idx. A walk recomputes a root from the opened
leaves and the digests given. `ok S = true` says that S is within the limits of the generic
construction (Run/PlanQTypes.lean). `LaxFacts h S o` (Run/PageIs.lean) is what `Spec.pi_facts`
states, under its hypotheses, of the lenient reader's output o; `opensB o` (Run/ParseChain.lean) is
the table made from o.

Main names:
  `tree_roots` (for `ok S = true` and `LaxFacts (Fmt.HO O) S o`), `cnt_le` (for `ok S = true` and
    `LaxFacts h S o`): the title's two statements. What the wiring allows is `nOpen`
    (Run/PlanQWire.lean): the bound that the verifier's data carry.
  `rows_ind`: gives `RowsL`; its doc comment has the hypotheses in full.

Limits: this file says nothing on soundness. It says nothing on the assembly into `pi_after`:
elsewhere.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIsForest
import Run.PageIsTabProofs
import Run.PageIsReaders
import Run.CostFmtProofs
import Run.PlanQWireLaws

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-- A round's data d and a round ro as a reader hands it out go together: d has no tree and ro's
items have no root, or d has a tree and ro's items have exactly one root, of 32 bytes. This is the
relation in `Spec.pi_sent` (Run/PageIsTab.lean). -/
def SentRel (d : RD) (ro : RoundOut) : Prop :=
  (d.tree = none ∧ _root_.Fmt.rootsOf ro.vals = []) ∨
  (d.tree.isSome = true ∧ ∃ r : ByteArray, r.size = 32 ∧ _root_.Fmt.rootsOf ro.vals = [r])

section
variable (C : CK) (tbl : List (ℕ × ℕ × OpenB)) (sb : ℕ) (W : ℕ → ℕ → Prop)

/-- `RowsL C tbl sb ds ros isRead` (Run/PageIsForest.lean) follows from three hypotheses. `SentRel`
holds of ds and ros, round by round. For every n with `treeSh ds n = some sh`, either the table has
under sh.tree a record (sh.W, Ob) with Ob.a = sh.a, `Ob.ok sb sh.W = true` and a list Ob.idx that is
not empty, and W (n0 + n) y holds exactly of the y in Ob.idx; or the table has no record under
sh.tree, and W (n0 + n) y holds of no y. And isRead q is true exactly if q is `posAtS C ds n y` for
some n, y with W (n0 + n) y. W is an arbitrary relation; n0 shifts the trees' numbers, and the
induction on the rounds carries it along. -/
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
  | ⟨e, k, items, tree, opens⟩ :: ds, _, n0, isRead, .cons (b := ro) (l₂ := ros) hs ht, hrow, hrd => by
    rcases hs with ⟨htr, hv⟩ | ⟨htr, r, hr32, hv⟩
    · dsimp only at htr
      subst htr
      refine ⟨Or.inl ⟨rfl, hv⟩, rows_ind ds ros n0 _ ht (fun n sh h => hrow n sh h) fun q => ?_⟩
      rw [hrd]
      constructor
      · rintro ⟨n, y, hw, hp⟩
        obtain ⟨q', hq', hq⟩ :=
          Option.map_eq_some_iff.1 (show (posAtS C ds n y).map Sum.inr = some (Sum.inr q) from hp)
        exact ⟨n, y, hw, by rw [hq', Sum.inr.inj hq]⟩
      · rintro ⟨n, y, hw, hp⟩
        exact ⟨n, y, hw, show (posAtS C ds n y).map Sum.inr = some (Sum.inr q) by rw [hp]; rfl⟩
    · obtain ⟨sh, rfl⟩ := Option.isSome_iff_exists.1 htr
      refine ⟨?_, rows_ind ds ros (n0 + 1) _ ht (fun n sh' h => ?_) fun q => ?_⟩
      · rcases hrow 0 sh rfl with ⟨Ob, hl, ha, hok, hne, hw⟩ | ⟨hl, hw⟩
        · refine Or.inr (Or.inl ⟨sh, Ob, r, rfl, hv, hr32, hl, ha, hok, hne, fun x => ?_⟩)
          rw [Bool.eq_iff_iff, hrd, decide_eq_true_iff, ← hw]
          constructor
          · rintro ⟨n, y, hwn, hp⟩
            cases n with
            | zero =>
              have hp' : (if h : y < 2 ^ sh.a then some (Sum.inl (⟨y, h⟩ : Fin (2 ^ sh.a)))
                    else none : Option (Fin (2 ^ sh.a) ⊕ OPos (uL C ds))) =
                  some (Sum.inl x) := hp
              split at hp'
              · have := Sum.inl.inj (Option.some.inj hp')
                rw [← this]
                exact hwn
              · cases hp'
            | succ n =>
              obtain ⟨q', -, hq⟩ := Option.map_eq_some_iff.1
                (show (posAtS C ds n y).map Sum.inr = some (Sum.inl x) from hp)
              cases hq
          · intro hwx
            exact ⟨0, x.val, hwx,
              show (if h : x.val < 2 ^ sh.a then some (Sum.inl (⟨x.val, h⟩ : Fin (2 ^ sh.a)))
                  else none : Option (Fin (2 ^ sh.a) ⊕ OPos (uL C ds))) = some (Sum.inl x)
                from dif_pos x.isLt⟩
        · refine Or.inr (Or.inr ⟨sh, r, rfl, hv, hr32, hl, fun x => ?_⟩)
          rw [← Bool.not_eq_true, hrd]
          rintro ⟨n, y, hwn, hp⟩
          cases n with
          | zero => exact hw y hwn
          | succ n =>
            obtain ⟨q', -, hq⟩ := Option.map_eq_some_iff.1
              (show (posAtS C ds n y).map Sum.inr = some (Sum.inl x) from hp)
            cases hq
      · rcases hrow (n + 1) sh' h with ⟨Ob', h1, h2, h3, h4, h5⟩ | ⟨h1, h5⟩
        · exact Or.inl ⟨Ob', h1, h2, h3, h4, fun y => by rw [← h5, Nat.add_assoc, Nat.add_comm 1 n]⟩
        · exact Or.inr ⟨h1, fun y => by rw [Nat.add_assoc, Nat.add_comm 1 n]; exact h5 y⟩
      · rw [hrd]
        constructor
        · rintro ⟨n, y, hwn, hp⟩
          cases n with
          | zero =>
            have hp' : (if h : y < 2 ^ sh.a then some (Sum.inl (⟨y, h⟩ : Fin (2 ^ sh.a)))
                  else none : Option (Fin (2 ^ sh.a) ⊕ OPos (uL C ds))) =
                some (Sum.inr q) := hp
            split at hp' <;> cases hp'
          | succ n =>
            obtain ⟨q', hq', hq⟩ := Option.map_eq_some_iff.1
              (show (posAtS C ds n y).map Sum.inr = some (Sum.inr q) from hp)
            exact ⟨n, y, by rw [Nat.add_assoc, Nat.add_comm 1 n]; exact hwn,
              by rw [hq', Sum.inr.inj hq]⟩
        · rintro ⟨n, y, hwn, hp⟩
          exact ⟨n + 1, y,
            by rw [Nat.add_assoc, Nat.add_comm 1 n] at hwn; exact hwn,
            show (posAtS C ds n y).map Sum.inr = some (Sum.inr q) by rw [hp]; rfl⟩

end

section
variable {I X : Type} {L : BatchProtocol I X} (O : ByteArray → ByteArray) (D : PageD L .onl)
  (tbl : List (ℕ × ℕ × OpenB)) (run : ByteArray)

/-- "Every tree that has a record in the table, in the order of sending, walks to its root", tree by
tree. If `SentRel` holds of ds and ros, round by round, then `treeAll O D tbl run ds ros = true`
exactly if, for every n with `treeSh ds n = some sh`, the table has no record under sh.tree, or it
has a record x under sh.tree, the roots of ros have an n-th entry, and
`walkOb O D run sh.tree x.1 x.2` is that entry. -/
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
  | ⟨e, k, items, tree, opens⟩ :: ds, _, .cons (b := ro) (l₂ := ros) hs ht => by
    have ih := tree_iff ds ros ht
    rcases hs with ⟨htr, hv⟩ | ⟨htr, r, -, hv⟩
    · dsimp only at htr
      subst htr
      show ((true && treeAll O D tbl run ds ros) = true) ↔ _
      rw [Bool.true_and, ih, List.flatMap_cons, hv, List.nil_append]
      exact Iff.rfl
    · obtain ⟨sh, rfl⟩ := Option.isSome_iff_exists.1 htr
      show (((match tbl.lookup sh.tree with
          | none => true
          | some x => decide (walkOb O D run sh.tree x.1 x.2 = (_root_.Fmt.rootsOf ro.vals).headD default)) && treeAll O D tbl run ds ros) = true) ↔ _
      rw [Bool.and_eq_true, ih, List.flatMap_cons, hv]
      constructor
      · rintro ⟨h0, hn⟩ n sh' hsh
        cases n with
        | zero =>
          have : sh' = sh := (Option.some.inj hsh).symm
          subst this
          cases hl : tbl.lookup sh'.tree with
          | none => exact Or.inl rfl
          | some x =>
            rw [hl] at h0
            exact Or.inr ⟨x, r, rfl, rfl, of_decide_eq_true h0⟩
        | succ n => exact hn n sh' hsh
      · intro H
        refine ⟨?_, fun n sh' hsh => H (n + 1) sh' hsh⟩
        rcases H 0 sh rfl with hl | ⟨x, root, hl, hr, hw⟩
        · rw [hl]
        · rw [hl]
          have : root = r := (Option.some.inj hr).symm
          subst this
          exact decide_eq_true hw

end

section
variable (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool)

/-- For an opening x of a tree that is not stored (`hp`): the walk of the table's record of x
(`walkOb` at `obOf x`) is the walk of the opening (`rootOf`, Run/PageIs.lean). -/
theorem walk_root (run : ByteArray)
    (x : _root_.Fmt.Shape × List ℕ × OpenOut) (hp : x.1.stored = false) :
    walkOb O (PDS S C dec) run x.1.tree x.1.W (obOf x) =
      rootOf (_root_.Fmt.HO O) S.cfg run x.1 x.2.1 x.2.2 := by
  obtain ⟨⟨a, W, st, tr⟩, xs, op⟩ := x
  dsimp only at hp
  subst hp
  rfl

/-- Under `hok` and `hf`: "every opened tree, in the order of sending" is "every opening, in the
file's order": `treeAll`, at the table `opensB o`, the rounds' data `rds S` and o's rounds, equals
`rootsAll` at o's rounds. -/
theorem tree_roots (o : ChainOut) (run : ByteArray)
    (hok : ok S = true) (hf : LaxFacts (_root_.Fmt.HO O) S o) :
    treeAll O (PDS S C dec) (opensB o) run (rds S) o.rounds.toList =
      rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList := by
  rw [Bool.eq_iff_iff,
    tree_iff O (PDS S C dec) (opensB o) run (rds S) o.rounds.toList (pi_sent _ S o hok hf)]
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
    rw [← walk_root O S C dec run x row.plain,
      show walkOb O (PDS S C dec) run x.1.tree x.1.W (obOf x) = x.2.2.root from hw]
    exact bytes_beq_self _
  · intro H n sh hsh
    rcases pi_row _ S o hok hf n sh hsh with ⟨x, row⟩ | bare
    · obtain ⟨ro, hro, hx⟩ := row.mem
      have hs := row.shape
      subst hs
      exact Or.inr
        ⟨_, _, row.look, row.root,
          (walk_root O S C dec run x row.plain).trans (bytes_beq _ _ (H ro hro x hx))⟩
    · exact Or.inl bare.look

end

/-! ### The number of checks -/

/-- the number of rounds with a tree -/
def nTrees (ds : List RD) : ℕ := (ds.filter fun d => d.tree.isSome).length

/-- the number of listed positions of the record under a tree's number -/
def idxLen (tbl : List (ℕ × ℕ × OpenB)) (t : ℕ) : ℕ := match tbl.lookup t with
  | none => 0
  | some x => x.2.idx.length

theorem cnt_range (tbl : List (ℕ × ℕ × OpenB)) (first : ℕ) :
    ∀ (ds : List RD) (n0 : ℕ), (∀ n sh, treeSh ds n = some sh → sh.tree = first + (n0 + n)) →
      cntO tbl ds = ((List.range' n0 (nTrees ds)).map fun n => idxLen tbl (first + n)).sum
  | [], _, _ => rfl
  | ⟨e, k, items, none, opens⟩ :: ds, n0, h => by
    show 0 + cntO tbl ds = _
    rw [Nat.zero_add, cnt_range tbl first ds n0 fun n sh hs => h n sh hs]
    rfl
  | ⟨e, k, items, some sh, opens⟩ :: ds, n0, h => by
    have h0 : sh.tree = first + (n0 + 0) := h 0 sh rfl
    show idxLen tbl sh.tree + cntO tbl ds =
      ((List.range' n0 (nTrees ds + 1)).map fun n => idxLen tbl (first + n)).sum
    rw [cnt_range tbl first ds (n0 + 1) fun n sh' hs => by rw [h (n + 1) sh' hs]; omega,
      List.range'_succ, List.map_cons, List.sum_cons, h0, Nat.add_zero]

theorem trees_roots :
    ∀ (ds : List RD) (ros : List RoundOut), List.Forall₂ SentRel ds ros →
      nTrees ds = (ros.flatMap fun ro => _root_.Fmt.rootsOf ro.vals).length
  | [], _, .nil => rfl
  | ⟨e, k, items, tree, opens⟩ :: ds, _, .cons (b := ro) (l₂ := ros) hs ht => by
    have ih := trees_roots ds ros ht
    rcases hs with ⟨htr, hv⟩ | ⟨htr, r, -, hv⟩
    · dsimp only at htr
      subst htr
      rw [List.flatMap_cons, hv, List.nil_append, ← ih]
      rfl
    · obtain ⟨sh, rfl⟩ := Option.isSome_iff_exists.1 htr
      rw [List.flatMap_cons, hv, List.length_append, ← ih]
      show nTrees ds + 1 = 1 + nTrees ds
      omega

/-- What is wanted is at most what the wiring allows, if each round's drawn positions are at most
the entry's number (d.entry.poss). -/
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

/-- Under `hok` and `hf`: the verifier forms at most as many checks as the wiring allows, in the
form `cntO (opensB o) (rds S) ≤ nOpen (rds S)`. -/
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

end Run.PQ
