-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/OpenedCols.lean: what the strict reader of a chain has read has columns of their forms'
widths: `ColsFit` (OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean) at a reading.



`assembleS_own` (OnBytes/TypedOracleCompiler/Slice/EntryOpened.lean) asks of the list of the openings of a chain's
own trees that every column has its form's width and that two openings under one number have one
width (`ColsFit`). Here both are shown of what the format's strict reader (`Fmt.readChainX`,
Fmt/Rules8X.lean) hands on. The first is a fact of the parser of an opening, which reads each column
as so many elements as the form says (`Fmt.rdOpening`, Fmt/Rules7.lean). The second is a fact of the
description, which the reader tests before it reads (`Fmt.SpecX.ok`): a tree of the chain's own has
the number "first tree + its place in the order of sending", and is opened under one form.

Theorems; two small definitions (`cols_ok`, `cols_at`).

Main names.
 `cols_pair`, `cols_many`, `cols_rdOpening`: the parser of an opening.
 `cols_opening`, `cols_stored`, `cols_opens`, `cols_round`, `cols_fold`, `cols_chain`: the strict
   reader, part by part: every opening that it hands on has columns of the form's width, one column
   and one salt for each listed place, and the form of a stored tree or of an opened tree of its
   round in the description.
 `cols_roundsOk`, `cols_one`, `cols_storedFlag`: the description.
 `cols_zipIdx`, `cols_ops`: the list of a chain's openings.
 `colsFit_chain`: `ColsFit` at the openings that are not of stored trees, from one yes of the strict
   reader at any hash.
 `colsFit_read`: the same where the description's own part is within the limits of OnBytes/TypedOracleCompiler
   (`TypedOracleCompiler.Run.PQ.ok`, OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean, at `inFile`).

What is asked beside the reader's yes: every tree that a round of the description opens is the
chain's own (no tree is taken over). A tree that is taken over has a number and a form that no
clause of `Fmt.Spec.ok` ties to another's, so "one number, one width" can fail there. The limits
of OnBytes/TypedOracleCompiler say that every opened tree is the chain's own (`own_of_ok`,
OnBytes/TypedOracleCompiler/Run/PageIsReaders.lean).

What is not claimed. Nothing on `RowsL` or `ListedX`. (`cols_chain` has the two lengths that
`ListedX` asks, of every opening; that a read position is listed is not shown.) Nothing on a hash,
a root or a path. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Slice.EntryOpened
import OnBytes.TypedOracleCompiler.Run.PageXTop
import Run.PageIsReaders
import Fmt.Rules8X

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Fmt (Rd rdMany rdPair Shape OpenOut RoundOut ChainOut Plan Src St SpecX Stored Round)
open _root_.Run (HId idb idp)

/-! ## The parser of an opening -/

/-- Two readers, one behind the other, taken apart. -/
theorem cols_pair {α β : Type} {ra : Rd α} {rb : Rd β} {b : ByteArray} {i j : ℕ} {x : α × β}
    (h : rdPair ra rb b i = some (x, j)) :
    ∃ k, ra b i = some (x.1, k) ∧ rb b k = some (x.2, j) := by
  unfold rdPair at h
  rcases h1 : ra b i with _ | ⟨u, k⟩
  · rw [h1] at h
    exact absurd h (by simp)
  · rw [h1] at h
    simp only at h
    rcases h2 : rb b k with _ | ⟨v, l⟩
    · rw [h2] at h
      exact absurd h (by simp)
    · rw [h2] at h
      simp only at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨k, rfl, h2⟩

/-- n values: there are n, and the reader has given each of them somewhere. -/
theorem cols_many {α : Type} (r : Rd α) (b : ByteArray) :
    ∀ (n i : ℕ) (l : List α) (j : ℕ), rdMany r n b i = some (l, j) →
      l.length = n ∧ ∀ x ∈ l, ∃ i' j', r b i' = some (x, j')
  | 0, i, l, j, h => by
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl, fun _ hx => absurd hx (by simp)⟩
  | n + 1, i, l, j, h => by
    unfold rdMany at h
    rcases h1 : r b i with _ | ⟨x, k⟩
    · rw [h1] at h
      exact absurd h (by simp)
    · rw [h1] at h
      simp only at h
      rcases h2 : rdMany r n b k with _ | ⟨l', m⟩
      · rw [h2] at h
        exact absurd h (by simp)
      · rw [h2] at h
        simp only at h
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        obtain ⟨a1, a2⟩ := cols_many r b n k l' m h2
        refine ⟨by rw [List.length_cons, a1], fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨i, k, h1⟩
        · exact a2 y hy

/-- What the parser of an opening accepts has one column with its salt for each listed place, and
every column has the form's width. -/
theorem cols_rdOpening (f : _root_.Fmt.Fld) (sb : ℕ) (sh : Shape) (xs : List ℕ) (b : ByteArray)
    (i j : ℕ) (cs : List (List UInt64 × ByteArray)) (gv : List ByteArray)
    (h : _root_.Fmt.rdOpening f sb sh xs b i = some ((cs, gv), j)) :
    cs.length = xs.length ∧ ∀ c ∈ cs, c.1.length = sh.W := by
  unfold _root_.Fmt.rdOpening at h
  obtain ⟨k, h1, -⟩ := cols_pair h
  obtain ⟨a1, a2⟩ := cols_many _ b _ i cs k h1
  refine ⟨a1, fun c hc => ?_⟩
  obtain ⟨i', j', h3⟩ := a2 c hc
  obtain ⟨k', h4, -⟩ := cols_pair h3
  exact (cols_many _ b _ i' c.1 k' h4).1

/-- What is shown of an opening as a reader hands it on (form, listed places, what was read): every
column has the form's width; there is one column and one salt for each listed place. -/
def cols_ok (x : Shape × List ℕ × OpenOut) : Prop :=
  (∀ c ∈ x.2.2.cols, c.length = x.1.W) ∧ x.2.2.cols.length = x.2.1.length ∧
    x.2.2.salts.length = x.2.1.length

section
variable (h : HId)

/-- One opening of the strict reader. -/
theorem cols_opening (cfg : ByteArray) (f : _root_.Fmt.Fld) (sb : ℕ) (sh : Shape)
    (start : ByteArray) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : OpenOut)
    (e : _root_.Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o) :
    cols_ok (sh, xs, o) := by
  obtain ⟨-, cs, hp, hc, hs⟩ := _root_.Run.PQ.readOpening_some h cfg f sb sh start xs b i o e
  obtain ⟨a1, a2⟩ := cols_rdOpening f sb sh xs b i o.next cs o.given hp
  refine ⟨fun c hcm => ?_, ?_, ?_⟩
  · have hcm' : c ∈ cs.map Prod.fst := hc ▸ hcm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hcm'
    exact a2 y hy
  · show o.cols.length = xs.length
    rw [hc, List.length_map, a1]
  · show o.salts.length = xs.length
    rw [hs, List.length_map, a1]

/-- The stored trees' openings behind one draw. -/
theorem cols_stored (cfg statement : ByteArray) (P : Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : _root_.Fmt.Seen) (i : ℕ)
        (l : List (Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen) (k : ℕ),
      _root_.Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
      ∀ x ∈ l, (∃ t ∈ ts, x.1 = t.sh) ∧ cols_ok x
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact fun x hx => absurd hx (by simp)
  | t :: ts, sn, i, l, sn', k, e => by
      unfold _root_.Fmt.readStored at e
      simp only [idb] at e
      cases ho : _root_.Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
          (_root_.Fmt.listOf ((_root_.Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
      | none => rw [ho] at e; cases e
      | some o =>
        rw [ho] at e
        dsimp only at e
        split at e
        · split at e
          · cases e
          · rename_i sn1 hadd
            cases hrec : _root_.Fmt.readStored (m := Id) h cfg statement P poss b ts sn1 o.next with
            | none => rw [hrec] at e; cases e
            | some z =>
              rw [hrec] at e
              obtain ⟨l1, sn2, k1⟩ := z
              simp only [idp] at e
              obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
              have ih := cols_stored cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hx
              · exact ⟨⟨t, List.mem_cons_self, rfl⟩, cols_opening h _ _ _ _ _ _ b i o ho⟩
              · obtain ⟨⟨t', ht', e'⟩, c⟩ := ih x hx
                exact ⟨⟨t', List.mem_cons_of_mem _ ht', e'⟩, c⟩
        · cases e

/-- The other trees' openings behind one draw. -/
theorem cols_opens (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : _root_.Fmt.Seen) (i : ℕ)
        (l : List (Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen) (k : ℕ),
      _root_.Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
      ∀ x ∈ l, (∃ y ∈ os, x.1 = y.1) ∧ cols_ok x
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact fun x hx => absurd hx (by simp)
  | (sh, src) :: os, sn, i, l, sn', k, e => by
      unfold _root_.Fmt.readOpens at e
      dsimp only at e
      split at e
      · cases e
      · rename_i root start hrs
        simp only [idb] at e
        cases ho : _root_.Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
            (_root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
        | none => rw [ho] at e; cases e
        | some o =>
          rw [ho] at e
          dsimp only at e
          split at e
          · split at e
            · cases e
            · rename_i sn1 hadd
              cases hrec : _root_.Fmt.readOpens (m := Id) h cfg P run roots poss b os sn1
                  o.next with
              | none => rw [hrec] at e; cases e
              | some z =>
                rw [hrec] at e
                obtain ⟨l1, sn2, k1⟩ := z
                simp only [idp] at e
                obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
                have ih := cols_opens cfg P run roots poss b os sn1 o.next l1 sn2 k1 hrec
                intro x hx
                rcases List.mem_cons.1 hx with rfl | hx
                · exact ⟨⟨(sh, src), List.mem_cons_self, rfl⟩,
                    cols_opening h _ _ _ _ _ _ b i o ho⟩
                · obtain ⟨⟨y, hy, e'⟩, c⟩ := ih x hx
                  exact ⟨⟨y, List.mem_cons_of_mem _ hy, e'⟩, c⟩
          · cases e

/-- what is shown of a round's openings: each is a stored tree's of ts or a tree's of r.opens -/
def cols_at (r : Round) (ts : List Stored) (ro : RoundOut) : Prop :=
  ∀ x ∈ ro.opens, ((∃ t ∈ ts, x.1 = t.sh) ∨ ∃ y ∈ r.opens, x.1 = y.1) ∧ cols_ok x

/-- One round. -/
theorem cols_round (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : St) (r : Round) (ts : List Stored)
    (e : _root_.Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ ro : RoundOut, s'.out = s.out.push ro ∧ cols_at r ts ro := by
  unfold _root_.Fmt.roundX at e
  split at e
  · cases e
  · rename_i msg hmsg
    split at e
    · cases e
    · rename_i vals hvals
      split at e
      · cases e
      · rename_i nonce i1 hnon
        simp only [idb] at e
        cases hq : _root_.Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          split at e
          · cases e
          · rename_i u i2 hlist
            cases hs : _root_.Fmt.readStored (m := Id) h cfg statement P
                (_root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2)).poss
                b ts s.seen i2 with
            | none => rw [hs] at e; cases e
            | some y =>
              rw [hs] at e
              obtain ⟨colsS, sn1, i2'⟩ := y
              dsimp only at e
              cases ho : _root_.Fmt.readOpens (m := Id) h cfg P run
                  (s.roots ++ (_root_.Fmt.rootsOf vals).toArray)
                  (_root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf cv.2)).poss
                  b r.opens sn1 i2' with
              | none => rw [ho] at e; cases e
              | some z =>
                rw [ho] at e
                obtain ⟨cols, sn2, i3⟩ := z
                simp only [idp] at e
                obtain rfl := Option.some.inj e
                refine ⟨_, rfl, fun x hx => ?_⟩
                rcases List.mem_append.1 hx with hx | hx
                · obtain ⟨a, c⟩ := cols_stored h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs
                    x hx
                  exact ⟨Or.inl a, c⟩
                · obtain ⟨a, c⟩ := cols_opens h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 ho x hx
                  exact ⟨Or.inr a, c⟩

/-- All rounds. -/
theorem cols_fold (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s s' : St),
      _root_.Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
      ∃ ros : List RoundOut, s'.out.toList = s.out.toList ++ ros ∧
        ∀ ro ∈ ros, ∃ r ∈ rs, cols_at r.1 r.2 ro
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, fun _ hx => absurd hx (by simp)⟩
  | r :: rs, s, s', e => by
      simp only [_root_.Fmt.foldRoundsX, idb] at e
      cases hc : _root_.Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2⟩ := cols_round h cfg statement P run b s s1 r.1 r.2 hc
        obtain ⟨ros, g1, g2⟩ := cols_fold cfg statement P run b rs s1 s' e
        refine ⟨ro :: ros, ?_, fun x hx => ?_⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨r, List.mem_cons_self, h2⟩
          · obtain ⟨r', hr', c⟩ := g2 x hx
            exact ⟨r', List.mem_cons_of_mem _ hr', c⟩

/-- A chain of the strict reader. The description is in order, and each round that was read is a
round of the description with its stored trees, in the sense of `cols_at`. -/
theorem cols_chain (S : SpecX) (seen : _root_.Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : ChainOut)
    (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧ ∀ ro ∈ o.rounds.toList, ∃ r ∈ S.base.rounds.zip S.stored, cols_at r.1 r.2 ro := by
  unfold _root_.Fmt.readChainX at e
  split at e
  · cases e
  · rename_i hok
    refine ⟨by simpa using hok, ?_⟩
    dsimp only at e
    split at e
    · cases e
    · rename_i x i0 hrnd
      simp only [idb] at e
      split at e
      · cases e
      · rename_i hd hst
        split at e
        · cases e
        · rename_i s hf
          simp only [idp] at e
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
          obtain ⟨ros, g1, g2⟩ := cols_fold h _ _ _ _ b _ _ s hf
          intro ro hro
          have g1' : s.out.toList = ros := by simpa using g1
          exact g2 ro (g1' ▸ hro)

end

/-! ## The description -/

/-- Every round of a list that is in order is in order, at some place. -/
theorem cols_roundsOk (P : Plan) (nr : Bool) (ft : ℕ) :
    ∀ (rs : List Round) (after : Bool) (sent : ℕ),
      _root_.Fmt.roundsOk P nr ft after sent rs = true →
      ∀ r ∈ rs, ∃ after' sent', r.ok P nr ft after' sent' = true
  | [], _, _, _, _, hr => absurd hr (by simp)
  | r :: rs, after, sent, h, r', hr' => by
    simp only [_root_.Fmt.roundsOk, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact ⟨after, sent, h.1⟩
    · exact cols_roundsOk P nr ft rs _ _ h.2 r' hr'

/-- In a description that is in order, two openings of trees of the chain's own under one number
have one form. -/
theorem cols_one (S : _root_.Fmt.Spec) (hok : S.ok = true) (r r' : Round)
    (hr : r ∈ S.rounds) (hr' : r' ∈ S.rounds) (y y' : Shape × Src) (hy : y ∈ r.opens)
    (hy' : y' ∈ r'.opens) (n n' : ℕ) (hn : y.2 = .own n) (hn' : y'.2 = .own n')
    (ht : y.1.tree = y'.1.tree) : y.1 = y'.1 := by
  simp only [_root_.Fmt.Spec.ok, Bool.and_eq_true, and_assoc] at hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, h12, -, -⟩ := hok
  have tree : ∀ (q : Round) (z : Shape × Src) (m : ℕ), q ∈ S.rounds → z ∈ q.opens →
      z.2 = .own m → z.1.tree = S.firstTree + m ∧ S.shapeOf m = some z.1 := by
    intro q z m hq hz hm
    obtain ⟨a, s, hqo⟩ := cols_roundsOk _ _ _ S.rounds _ _ h12 q hq
    simp only [_root_.Fmt.Round.ok, Bool.and_eq_true] at hqo
    have hz1 := List.all_eq_true.1 hqo.2 z hz
    rw [hm] at hz1
    simp only [Bool.and_eq_true, beq_iff_eq] at hz1
    refine ⟨hz1.2.1.1.2, ?_⟩
    have hmem : (m, z.1) ∈ S.ownShapes :=
      List.mem_flatMap.2 ⟨q, hq, List.mem_filterMap.2 ⟨z, hz, by rw [hm]⟩⟩
    exact beq_iff_eq.1 (List.all_eq_true.1 h11 _ hmem)
  obtain ⟨t1, s1⟩ := tree r y n hr hy hn
  obtain ⟨t2, s2⟩ := tree r' y' n' hr' hy' hn'
  have e : n = n' := by omega
  subst e
  exact Option.some.inj (s1.symm.trans s2)

/-- In a description that is in order a stored tree's form says that it is stored. -/
theorem cols_storedFlag (S : SpecX) (hok : S.ok = true) (x : Round × List Stored)
    (hx : x ∈ S.base.rounds.zip S.stored) (t : Stored) (ht : t ∈ x.2) : t.sh.stored = true := by
  simp only [_root_.Fmt.SpecX.ok, Bool.and_eq_true] at hok
  have h := List.all_eq_true.1 hok.2 x hx
  simp only [_root_.Fmt.storedOk, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | h
  · rw [List.isEmpty_iff.1 h] at ht
    exact absurd ht (by simp)
  · have h2 := List.all_eq_true.1 h.2 t ht
    simp only [Bool.and_eq_true] at h2
    exact h2.1.1.1.1.1.1.1.1

/-- a member of a numbered list is a member of the list -/
theorem cols_zipIdx {α : Type} : ∀ (l : List α) (n : ℕ) (p : α × ℕ), p ∈ l.zipIdx n → p.1 ∈ l
  | [], _, _, h => absurd h (by simp)
  | a :: l, n, p, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (cols_zipIdx l (n + 1) p h)

/-! ## The list of a chain's openings -/

/-- An opening of the list is an opening of a round that was read. -/
theorem cols_ops (o : ChainOut) (c : ℕ) (op : OpAt) (h : op ∈ opsOf c o) :
    ∃ ro ∈ o.rounds.toList, ∃ x ∈ ro.opens, op.sh = x.1 ∧ op.xs = x.2.1 ∧ op.out = x.2.2 := by
  unfold opsOf at h
  obtain ⟨r, hr, h⟩ := List.mem_flatMap.1 h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  exact ⟨r.1, cols_zipIdx _ _ r hr, x.1, cols_zipIdx _ _ x hx, rfl, rfl, rfl⟩

/-- `ColsFit` at one yes of the strict reader, if the description's rounds open trees of the
chain's own alone. -/
theorem colsFit_chain (h : HId) (S : SpecX) (seen : _root_.Fmt.Seen) (b : ByteArray) (i j : ℕ)
    (o : ChainOut) (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hown : ∀ r ∈ S.base.rounds, ∀ y ∈ r.opens, ∃ n, y.2 = Src.own n) :
    ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored) := by
  obtain ⟨hok, hr⟩ := cols_chain h S seen b i j o e
  have key : ∀ op ∈ (opsOf 1 o).filter (fun op => !op.sh.stored),
      (∀ c ∈ op.out.cols, c.length = op.sh.W) ∧
        ∃ r ∈ S.base.rounds, ∃ y ∈ r.opens, op.sh = y.1 := by
    intro op hop
    obtain ⟨hop1, hns⟩ := List.mem_filter.1 hop
    obtain ⟨ro, hro, x, hx, e1, -, e3⟩ := cols_ops o 1 op hop1
    obtain ⟨rt, hrt, hat⟩ := hr ro hro
    obtain ⟨hsrc, hc⟩ := hat x hx
    refine ⟨by rw [e3, e1]; exact hc.1, ?_⟩
    rcases hsrc with ⟨t, ht, et⟩ | ⟨y, hy, ey⟩
    · rw [e1, et, cols_storedFlag S hok rt hrt t ht] at hns
      cases hns
    · exact ⟨rt.1, (List.of_mem_zip hrt).1, y, hy, e1.trans ey⟩
  refine ⟨fun op hop => (key op hop).1, fun op hop op' hop' ht => ?_⟩
  obtain ⟨-, r, hr1, y, hy, e1⟩ := key op hop
  obtain ⟨-, r', hr1', y', hy', e1'⟩ := key op' hop'
  obtain ⟨n, hn⟩ := hown r hr1 y hy
  obtain ⟨n', hn'⟩ := hown r' hr1' y' hy'
  have hb : S.base.ok = true := by
    simp only [_root_.Fmt.SpecX.ok, Bool.and_eq_true] at hok
    exact hok.1.1
  rw [e1, e1', cols_one S.base hb r r' hr1 hr1' y y' hy hy' n n' hn hn'
    (by rw [← e1, ← e1']; exact ht)]

/-- `ColsFit` from one yes of the strict reader: one yes of the strict reader under a description
whose own part, with the chain's random bytes counted as standing in the file, is within the
limits of OnBytes/TypedOracleCompiler (`TypedOracleCompiler.Run.PQ.ok`): these say that every opened tree is the chain's
own. -/
theorem colsFit_read (h : HId) (S : SpecX)
    (hokb : TypedOracleCompiler.Run.PQ.ok (TypedOracleCompiler.Run.PQ.inFile S.base) = true)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored) :=
  colsFit_chain h S seen b i j o e
    (TypedOracleCompiler.Run.PQ.own_of_ok (TypedOracleCompiler.Run.PQ.inFile S.base) hokb)

end TypedOracleCompiler.Slice
