-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormBehindRead.lean: behind a code switch of the proximity test, whatever trees
the old rows stood in: the tree that the switch has sent is untouched by the reading of the old
rows, so the next stage's reading finds it as it was sent; and the count of roots.

Why. `readSeat_behind` (Johnson/Prover/Link/ReadNew.lean) says the like where the old rows stood in
one tree. The library's laws on the reading (`readOld_keeps`, Johnson/Desc/K12/Law/SwTies.lean) say
that a tree stays but for its count of opened lists; none says which trees' counts change.

Main names (namespace `Johnson.Prover.Link`).
  `openOne_other`, `readOld_other`   a reading changes no tree but those in which the old rows'
      messages have their places
  `OldIn S Bk old`   a premise: the old rows' messages are messages of S, and their places lie in
      trees of Bk
  `readSeat_did`   `ReadSeat` (Johnson/Prover/Link/ReadSeat.lean) at the new tree, behind what a
      switch and its batching have done (`Did`, Johnson/Desc/K12/Law/SwDid.lean)
  `trees_did`, `roots_behind`   the book has the new trees more; the roots rise as the trees do

Limits. `OldIn` and `Did` are asked. Nothing on acceptance, on values or on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ReadNew
import Johnson.Prover.Link.FormNextSwitch
import Johnson.Desc.K12.Law.BookWalk
import OnBytes.Slice.BlkOpenN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- One opening changes no other tree. -/
theorem openOne_other (S : Statement) (ft : ℕ) (pos : Positions) (B0 : TreeBook) (t : ℕ)
    (s s' : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F)))
    (h : Tw.L9.openOne S ft pos B0 t s = .ok s') (k : ℕ) (hk : k ≠ t) :
    s'.1.trees[k]? = s.1.trees[k]? := by
  unfold Tw.L9.openOne at h
  split at h
  · dsimp only at h
    repeat' split at h
    all_goals first
      | (cases h
         show (s.1.trees.modify t _)[k]? = _
         rw [Array.getElem?_modify, if_neg (Ne.symm hk)])
      | cases h
  · cases h

theorem openAll_other (S : Statement) (ft : ℕ) (pos : Positions) (B0 : TreeBook) (k : ℕ) :
    ∀ (l : List ℕ) (s s' : TreeBook × List Tw.L9.Col × Array (ℕ × Array ℕ × Array (Array F))),
      (∀ t ∈ l, k ≠ t) → l.foldlM (fun s t => Tw.L9.openOne S ft pos B0 t s) s = .ok s' →
      s'.1.trees[k]? = s.1.trees[k]?
  | [], s, s', _, h => by cases h; rfl
  | t :: l, s, s', hl, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨s1, h1, h2⟩ := H2K.FoldLaw.bind_ok h
    rw [openAll_other S ft pos B0 k l s1 s' (fun u hu => hl u (List.mem_cons_of_mem _ hu)) h2]
    exact openOne_other S ft pos B0 t s s1 h1 k (hl t List.mem_cons_self)

/-- **A reading changes no tree but those in which the old rows' messages have their places.** -/
theorem readOld_other (i : Tw.L9.SwIn) (pos : Positions) (B : TreeBook) (left : List Tw.L9.Col)
    (ys : Array E) (h : Tw.L9.readOld i pos = .ok (B, left, ys)) (k : ℕ)
    (hk : ∀ o ∈ singleRowsOracles i.old, ∀ pl, i.book.place[o]? = some pl → pl.1 ≠ k) :
    B.trees[k]? = i.book.trees[k]? := by
  obtain ⟨places, cols, opened, hp, hf, -, -⟩ := readOld_inv i pos B left ys h
  refine openAll_other _ _ _ _ k _ _ _ (fun t ht => ?_) hf
  rw [listOfT_eq] at ht
  have ht' : t ∈ (places.map (·.1)).toList := (Fmt.listOf_mem _ t).1 ht
  rw [Array.toList_map] at ht'
  obtain ⟨pl, hpl, rfl⟩ := List.mem_map.1 ht'
  rw [Array.mapM_eq_mapM_toList] at hp
  obtain ⟨out, hout, e⟩ := Option.map_eq_some_iff.1 hp
  obtain rfl : out.toArray = places := e
  obtain ⟨hlen, hat⟩ := list_mapM_inv _ _ _ hout
  obtain ⟨n, hn, e2⟩ := List.getElem_of_mem hpl
  have hn' : n < (singleRowsOracles i.old).toList.length := by
    rw [← hlen]
    exact hn
  have h3 := hat n hn'
  rw [List.getElem?_eq_getElem hn, e2] at h3
  exact (hk _ (Array.mem_toList_iff.1 (List.getElem_mem hn')) pl h3).symm

/-- The old rows' messages are messages of S, and their places lie in trees of Bk. -/
structure OldIn (S : Statement) (Bk : TreeBook) (old : SingleRows) : Prop where
  there : ∀ o ∈ singleRowsOracles old, o < S.oracles.size
  inBook : ∀ o ∈ singleRowsOracles old, ∀ pl, Bk.place[o]? = some pl → pl.1 < Bk.trees.size

section
variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- **The new tree behind a switch, whatever trees the old rows stood in.** -/
theorem readSeat_did (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D)
    (sh : TreeShape) (h1 : others.size = 1) (hs : D.lay.shapes = #[sh])
    (ht : ∀ i, i < 2 → D.lay.tree.getD i 0 = 0 ∧ D.lay.part.getD i 0 = i)
    (ha : T.shape.answers ≠ 0) (hr : (others.getD 0 default).shape.answers = 0)
    (O : OldIn S Bk old) :
    ReadSeat S' Bk' [S.oracles.size] (S.oracles.size + 1) Bk.trees.size
      (newTree ft roots sh S.oracles.size) := by
  have H := ((readSeat_new D T gp others S ft roots Bk sh h1 hs ht h.places ha hr).withRows gp
    D.rows).begun gp (D.grown S)
  obtain ⟨i, left, -, hb, -, -, ho, hrd⟩ := h.read
  rw [h.st]
  refine H.ride (fun _ _ => rfl) (Nat.le_refl _) ?_ fun o p hp => ?_
  · rw [readOld_other i _ _ _ _ hrd Bk.trees.size, hb]
    intro o ho' pl hpl
    rw [ho] at ho'
    rw [hb] at hpl
    have hlt : o < Bk.place.size := by
      rw [← h.places]
      exact O.there o ho'
    have e : (bookSentP ft roots S Bk (Slice.sentOf T others) D.lay).place[o]? = Bk.place[o]? :=
      Array.getElem?_append_left hlt
    rw [e] at hpl
    exact Nat.ne_of_lt (O.inBook o ho' pl hpl)
  · rw [readOld_place i _ _ _ _ hrd, hb]
    exact hp

/-- The book behind has the new trees more. -/
theorem trees_did (h : Did ft cols old T gp others S Bk roots S' Bk' out row lay theta D) :
    Bk'.trees.size = Bk.trees.size + D.lay.shapes.size := by
  obtain ⟨i, left, -, hb, -, -, -, hrd⟩ := h.read
  rw [(H2K.Out.readOld_same i _ _ _ _ hrd).1, hb]
  exact (H2K.Out.bookSentP_sizes ft roots S Bk _ D.lay).1

end

/-- **The roots rise as the trees do**, across a switch and the batching behind it. -/
theorem roots_behind (p : P12) (j : ℕ) (cur nxt : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) (t1 t2 t3 : T12) (rS rC : Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64)))
    (h2 : (switchJ p j cur nxt last cut).decide t1 [rS, rC] gs = .ok t2)
    (h3 : (behindJ p (j + 1) nxt cut).decide t2 [] [] = .ok t3) :
    t3.roots + t1.book.trees.size = t1.roots + t3.book.trees.size := by
  have a := (H2K.Out.switchJ_br p (H2K.Out.bookOwes_counts _) j cur nxt last cut t1 t2
    [rS, rC] gs (Nat.le_refl 2) h2).1
  have b := H2K.Out.behindJ_br p (j + 1) nxt cut t2 t3 h3
  have b1 : t3.book = t2.book := congrArg Prod.fst b
  have b2 : t3.roots = t2.roots := congrArg Prod.snd b
  rw [b1, b2]
  exact a

end Johnson.Prover.Link
