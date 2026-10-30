-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Chain/OpenedLaws.lean: the cut of a view into its openings never fails on a chain that
the strict reader has read.

Main theorem: `openedByPlace_read`. If the strict reader returns o for the description S, then
`openedByPlace S (viewOf S o)` returns, for each round and each opening of that round, the
opening's list of positions zipped with its columns.
So a decision that read columns by place would never say no because of the cut.
-/
import OnBytes.Chain.Opened
import OnBytes.Chain.EngineLaws
import OnBytes.Chain.ReaderLaws
import Run.WalkTieProofs

namespace OnBytes

open Fmt (Qry Hash Plan St Round Stored SpecX Seen ChainOut RoundOut OpenOut Shape Src)

/-- An opening as the reader returns it: the tree's shape, the list, what was read. -/
abbrev Read1 : Type := Shape × List Nat × OpenOut

/-- The opening as a decision sees it. -/
def Read1.opening (x : Read1) : Opening := x.2.1.zip x.2.2.cols

/-- Pieces with any keys, each with as many columns as positions, put one after the other, are
cut again into the pieces. -/
theorem takeOpenings_flat (rest : List (Nat × Nat × List F)) :
    ∀ (L : List (Nat × List Nat × List (List F))), (∀ x ∈ L, x.2.2.length = x.2.1.length) →
    takeOpenings (L.map fun x => x.2.1)
        ((L.flatMap fun x => (x.2.1.zip x.2.2).map fun p => (x.1, p.1, p.2)) ++ rest) =
      some (L.map fun x => x.2.1.zip x.2.2, rest)
  | [], _ => rfl
  | x :: L, hL => by
    have hx : x.2.2.length = x.2.1.length := hL x (by simp)
    have ih := takeOpenings_flat rest L fun y hy => hL y (List.mem_cons_of_mem _ hy)
    have hlen : ((x.2.1.zip x.2.2).map fun p => (x.1, p.1, p.2)).length = x.2.1.length := by
      simp [hx]
    have hpos : (((x.2.1.zip x.2.2).map fun p => (x.1, p.1, p.2)).map fun q => q.2.1) =
        x.2.1 := by
      rw [List.map_map]
      exact List.map_fst_zip (Nat.le_of_eq hx.symm)
    have hcol : (((x.2.1.zip x.2.2).map fun p => (x.1, p.1, p.2)).map fun q => q.2) =
        x.2.1.zip x.2.2 := by
      rw [List.map_map]
      exact List.map_id _
    simp only [List.map_cons, List.flatMap_cons, List.append_assoc, takeOpenings]
    rw [List.take_left' hlen, List.drop_left' hlen, hpos, hcol, ih]
    simp

/-- What the law needs of one opening that was read at the list xs: it carries that list, and it
has as many columns as the list has positions. -/
def ReadAt (xs : List Nat) (y : Read1) : Prop := y.2.1 = xs ∧ y.2.2.cols.length = y.2.1.length

/-- The stored trees' openings of a round stand at the lists of their parts of the draws. -/
theorem stored_lists (h : Hash) (cfg statement : ByteArray) (P : Plan) (poss : List Nat)
    (b : ByteArray) : ∀ (ts : List Stored) (sn : Seen) (i : Nat) (l : List Read1) (sn' : Seen)
      (k : Nat), Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
    List.Forall₂ (fun t y => ReadAt (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) y)
      ts l
  | [], _, _, l, _, _, e => by
    have e' : l = [] := by
      have := Option.some.inj e
      exact (congrArg Prod.fst this).symm
    rw [e']
    exact List.Forall₂.nil
  | t :: ts, sn, i, l, sn', k, e => by
    rw [readStored_cons] at e
    split at e
    · cases e
    · rename_i o ho
      split at e
      · split at e
        · cases e
        · rename_i sn1 _
          split at e
          · cases e
          · rename_i l1 sn2 k1 hr
            have ih := stored_lists h cfg statement P poss b ts sn1 o.next l1 sn2 k1 hr
            have e' : _ :: l1 = l := congrArg Prod.fst (Option.some.inj e)
            rw [← e']
            exact List.Forall₂.cons ⟨rfl, (Run.WalkTie.reader_id h _ _ _ _ _ _ _ _ o ho).1⟩ ih
      · cases e

/-- The other trees' openings of a round stand at the round's draws modulo their lengths. -/
theorem opens_lists (h : Hash) (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : Seen) (i : Nat) (l : List Read1) (sn' : Seen) (k : Nat),
    Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
    List.Forall₂ (fun x y => ReadAt (Fmt.listOf (poss.map (· % 2 ^ x.1.a))) y) os l
  | [], _, _, l, _, _, e => by
    have e' : l = [] := by
      have := Option.some.inj e
      exact (congrArg Prod.fst this).symm
    rw [e']
    exact List.Forall₂.nil
  | (sh, src) :: os, sn, i, l, sn', k, e => by
    rw [readOpens_cons] at e
    split at e
    · cases e
    · rename_i root start _
      split at e
      · cases e
      · rename_i o ho
        split at e
        · split at e
          · cases e
          · rename_i sn1 _
            split at e
            · cases e
            · rename_i l1 sn2 k1 hr
              have ih := opens_lists h cfg P run roots poss b os sn1 o.next l1 sn2 k1 hr
              have e' : _ :: l1 = l := congrArg Prod.fst (Option.some.inj e)
              rw [← e']
              exact List.Forall₂.cons
                ⟨rfl, (Run.WalkTie.reader_id h _ _ _ _ _ _ _ _ o ho).1⟩ ih
        · cases e

/-- What the law needs of one round that was read: its openings are those of its stored trees, at
the lists of their parts, and after them those of its other trees, at the lists of the draws. -/
def RoundFits (r : Round) (ts : List Stored) (ro : RoundOut) : Prop :=
  ∃ A B : List Read1, ro.opens = A ++ B ∧
    List.Forall₂ (fun t y =>
      ReadAt (Fmt.listOf ((Fmt.partOf t ro.drawn.poss).map (· % 2 ^ t.sh.a))) y) ts A ∧
    List.Forall₂ (fun x y => ReadAt (Fmt.listOf (ro.drawn.poss.map (· % 2 ^ x.1.a))) y) r.opens B

/-- A round that the reader accepts adds one round that fits. -/
theorem roundQ_fits (qry : Qry) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) (s s' : St) (r : Round) (ts : List Stored)
    (e : roundQ qry h cfg statement P run b s r ts = some s') :
    ∃ ro, s'.out = s.out.push ro ∧ RoundFits r ts ro := by
  unfold roundQ at e
  split at e
  · cases e
  · split at e
    · cases e
    · split at e
      · cases e
      · split at e
        · cases e
        · dsimp only at e
          split at e
          · cases e
          · split at e
            · cases e
            · rename_i colsS sn1 i2' hS
              split at e
              · cases e
              · rename_i cols sn i3 hO
                have e' := Option.some.inj e
                rw [← e']
                exact ⟨_, rfl, colsS, cols, rfl, stored_lists h _ _ _ _ _ _ _ _ _ _ _ hS,
                  opens_lists h _ _ _ _ _ _ _ _ _ _ _ _ hO⟩

/-- All rounds that the reader accepts fit. -/
theorem foldRoundsQ_fits (qry : Qry) (h : Hash) (cfg statement : ByteArray) (P : Plan)
    (run : Option ByteArray) (b : ByteArray) : ∀ (rs : List (Round × List Stored)) (s s' : St),
    foldRoundsQ qry h cfg statement P run b rs s = some s' →
    ∃ ros : List RoundOut, s'.out.toList = s.out.toList ++ ros ∧
      List.Forall₂ (fun x ro => RoundFits x.1 x.2 ro) rs ros
  | [], s, s', e => by
    have e' : s = s' := Option.some.inj e
    rw [← e']
    exact ⟨[], (List.append_nil _).symm, List.Forall₂.nil⟩
  | x :: rs, s, s', e => by
    rw [foldRoundsQ] at e
    split at e
    · cases e
    · rename_i s1 h1
      obtain ⟨ro, ho, hf⟩ := roundQ_fits qry h cfg statement P run b s s1 x.1 x.2 h1
      obtain ⟨ros, hos, hfs⟩ := foldRoundsQ_fits qry h cfg statement P run b rs s1 s' e
      refine ⟨ro :: ros, ?_, List.Forall₂.cons hf hfs⟩
      rw [hos, ho, Array.toList_push, List.append_assoc]
      rfl

/-- A chain that the reader accepts: its description is in order, and its rounds fit. -/
theorem readChainQ_fits (qry : Qry) (h : Hash) (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat)
    (o : ChainOut) (j : Nat) (e : readChainQ qry h S seen b i = some (o, j)) :
    S.ok = true ∧
      List.Forall₂ (fun x ro => RoundFits x.1 x.2 ro) (S.base.rounds.zip S.stored)
        o.rounds.toList := by
  have rest : ∀ (x : Option ByteArray) (i0 : Nat), restQ qry h S seen b x i0 = some (o, j) →
      List.Forall₂ (fun x ro => RoundFits x.1 x.2 ro) (S.base.rounds.zip S.stored)
        o.rounds.toList := by
    intro x i0 e
    unfold restQ at e
    split at e
    · cases e
    · split at e
      · cases e
      · rename_i s hs
        obtain ⟨ros, hos, hfs⟩ := foldRoundsQ_fits qry h _ _ _ _ b _ _ s hs
        have e' : _ = o := congrArg Prod.fst (Option.some.inj e)
        rw [← e']
        have : s.out.toList = ros := by
          rw [hos]
          rfl
        show List.Forall₂ _ _ s.out.toList
        rw [this]
        exact hfs
  unfold readChainQ at e
  split at e
  · cases e
  · rename_i hok
    refine ⟨by simpa using hok, ?_⟩
    split at e
    · split at e
      · cases e
      · exact rest _ _ e
    · exact rest _ _ e
    · exact rest _ _ e

/-- Openings that stand at the lists f a, each with a key made from a. -/
theorem keyedA {α : Type} (f : α → List Nat) (k : α → Nat) :
    ∀ {as : List α} {ys : List Read1}, List.Forall₂ (fun a y => ReadAt (f a) y) as ys →
    ((as.zip ys).map fun p => (k p.1, p.2.2.1, p.2.2.2.cols)).map (fun x => x.2.1) = as.map f ∧
    ((as.zip ys).map fun p => (k p.1, p.2.2.1, p.2.2.2.cols)).map (fun x => x.2.1.zip x.2.2) =
      ys.map Read1.opening ∧
    ∀ x ∈ (as.zip ys).map (fun p => (k p.1, p.2.2.1, p.2.2.2.cols)), x.2.2.length = x.2.1.length
  | _, _, .nil => ⟨rfl, rfl, fun _ h => by cases h⟩
  | a :: as, y :: ys, .cons h t => by
    obtain ⟨i1, i2, i3⟩ := keyedA f k t
    refine ⟨?_, ?_, ?_⟩
    · rw [List.zip_cons_cons, List.map_cons, List.map_cons, i1, List.map_cons]
      exact congrArg (fun z => z :: as.map f) h.1
    · rw [List.zip_cons_cons, List.map_cons, List.map_cons, i2, List.map_cons]
      rfl
    · intro x hx
      rw [List.zip_cons_cons, List.map_cons] at hx
      rcases List.mem_cons.1 hx with e | hx'
      · rw [e]
        exact h.2
      · exact i3 x hx'

/-- Openings that stand at the lists f a, each with a key of its own. -/
theorem keyedB {α : Type} (f : α → List Nat) (k : Read1 → Nat) :
    ∀ {as : List α} {ys : List Read1}, List.Forall₂ (fun a y => ReadAt (f a) y) as ys →
    (ys.map fun y => (k y, y.2.1, y.2.2.cols)).map (fun x => x.2.1) = as.map f ∧
    ∀ x ∈ ys.map (fun y => (k y, y.2.1, y.2.2.cols)), x.2.2.length = x.2.1.length
  | _, _, .nil => ⟨rfl, fun _ h => by cases h⟩
  | a :: as, y :: ys, .cons h t => by
    obtain ⟨i1, i3⟩ := keyedB f k t
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.map_cons, i1, List.map_cons]
      exact congrArg (fun z => z :: as.map f) h.1
    · intro x hx
      rw [List.map_cons] at hx
      rcases List.mem_cons.1 hx with e | hx'
      · rw [e]
        exact h.2
      · exact i3 x hx'

/-- One round: the view's columns of a round that fits are cut into the round's openings. -/
theorem takeOpenings_round (first : Nat) (r : Round) (ts : List Stored) (ro : RoundOut)
    (hf : RoundFits r ts ro) (rest : List (Nat × Nat × List F)) :
    takeOpenings (listsOf r ts ro.drawn.poss) (Fmt.openedX first ts ro ++ rest) =
      some (ro.opens.map Read1.opening, rest) := by
  obtain ⟨A, B, hAB, hA, hB⟩ := hf
  have hl : ts.length = A.length := hA.length_eq
  obtain ⟨a1, a2, a3⟩ := keyedA
    (fun t : Stored => Fmt.listOf ((Fmt.partOf t ro.drawn.poss).map (· % 2 ^ t.sh.a)))
    (fun t => Fmt.storedKey t.item) hA
  obtain ⟨b1, b3⟩ := keyedB
    (fun x : Shape × Src => Fmt.listOf (ro.drawn.poss.map (· % 2 ^ x.1.a)))
    (fun y => y.1.tree - first) hB
  have hz : ts.zip (A ++ B) = ts.zip A := by
    have e := List.zip_append (l₁ := ts) (r₁ := []) (l₂ := A) (r₂ := B) hl
    rw [List.append_nil] at e
    rw [e, List.zip_nil_left, List.append_nil]
  have hlists : listsOf r ts ro.drawn.poss =
      (((ts.zip A).map fun p => (Fmt.storedKey p.1.item, p.2.2.1, p.2.2.2.cols)) ++
        B.map fun y => (y.1.tree - first, y.2.1, y.2.2.cols)).map (fun x => x.2.1) := by
    unfold listsOf
    simp only [listOfT_eq]
    rw [List.map_append, a1, b1]
  have hflat : Fmt.openedX first ts ro =
      (((ts.zip A).map fun p => (Fmt.storedKey p.1.item, p.2.2.1, p.2.2.2.cols)) ++
        B.map fun y => (y.1.tree - first, y.2.1, y.2.2.cols)).flatMap
          (fun x => (x.2.1.zip x.2.2).map fun p => (x.1, p.1, p.2)) := by
    show ((ts.zip ro.opens).flatMap fun y => (y.2.2.1.zip y.2.2.2.cols).map fun p =>
        (Fmt.storedKey y.1.item, p.1, p.2)) ++
      (ro.opens.drop ts.length).flatMap (fun x => (x.2.1.zip x.2.2.cols).map fun p =>
        (x.1.tree - first, p.1, p.2)) = _
    rw [hAB, hz, List.drop_left' hl.symm, List.flatMap_append, List.flatMap_map,
      List.flatMap_map]
  rw [hlists, hflat, takeOpenings_flat rest _ (by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact a3 x h
    · exact b3 x h), List.map_append, a2, hAB, List.map_append, List.map_map]
  rfl

/-- All rounds: the view's columns of rounds that fit are cut into the rounds' openings. -/
theorem takeRounds_fits (first : Nat) : ∀ (rs : List (Round × List Stored))
    (ros : List RoundOut) (acc : Array (Array Opening)),
    List.Forall₂ (fun x ro => RoundFits x.1 x.2 ro) rs ros →
    takeRounds rs (ros.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩)
        (((rs.map (·.2)).zip ros).flatMap fun y => Fmt.openedX first y.1 y.2) acc =
      some (acc ++ (ros.map fun r => (r.opens.map Read1.opening).toArray).toArray)
  | _, _, acc, .nil => by simp [takeRounds]
  | x :: rs, ro :: ros, acc, .cons h t => by
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.flatMap_cons, takeRounds]
    show (match takeOpenings (listsOf x.1 x.2 ro.drawn.poss) (Fmt.openedX first x.2 ro ++ _) with
      | none => none
      | some (os, rest) => takeRounds rs _ rest (acc.push os.toArray)) = _
    rw [takeOpenings_round first x.1 x.2 ro h]
    show takeRounds rs _ _ (acc.push _) = _
    rw [takeRounds_fits first rs ros _ t]
    simp

/-- **The cut never fails on a chain that was read.** If the reader returns o for the description
S, the view of o is cut into o's openings: for each round and each opening of that round, the
opening's list of positions zipped with its columns. -/
theorem openedByPlace_read (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) (o : ChainOut)
    (j : Nat) (e : readChain S seen b i = some (o, j)) :
    openedByPlace S (viewOf S o) =
      some (o.rounds.map fun r => (r.opens.map Read1.opening).toArray) := by
  have e2 : readChainQ queryH formatHashFastForm S seen b i = some (o, j) := by
    rw [← readChainK_eq Keeper.indexed]
    exact e
  obtain ⟨hok, hf⟩ := readChainQ_fits _ _ S seen b i o j e2
  have hlen : S.stored.length = S.base.rounds.length := by
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at hok
    exact hok.1.2
  have hst : (S.base.rounds.zip S.stored).map (·.2) = S.stored :=
    List.map_snd_zip (Nat.le_of_eq hlen)
  have hc := takeRounds_fits S.base.firstTree _ _ #[] hf
  rw [hst] at hc
  rw [viewOf_eq]
  unfold openedByPlace
  rw [zipT_eq]
  show takeRounds _ (o.rounds.toList.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩)
    ((S.stored.zip o.rounds.toList).flatMap fun y => Fmt.openedX S.base.firstTree y.1 y.2) #[] = _
  rw [hc]
  simp only [Array.empty_append, Option.some.injEq]
  rw [← Array.toList_map, Array.toArray_toList]

end OnBytes
