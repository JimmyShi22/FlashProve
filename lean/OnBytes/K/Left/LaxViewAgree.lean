-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxViewAgree.lean: in the table that the typing makes of the openings of a chain's
own trees, two rows under one key have one column (`Agree`), at a reading.



`assembleS` (OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean) lays the rows of all openings of the chain's own
trees in one table, keyed by the tree's number and the place. A look-up finds the first row of a
key, so what is said of a listed column wants that a key has one column (`Agree`,
OnBytes/TypedOracleCompiler/Run/ViewERead.lean). `agree_of_once` (OnBytes/TypedOracleCompiler/Run/ViewERead3.lean) gives that if
unlike openings have unlike numbers and no opening lists a place twice. Here both are shown of what
the format's strict reader (`Fmt.readChainX`, Fmt/Rules8X.lean) hands on, under a test on the
description: no tree of the chain's own is opened twice in the whole chain.

Theorems; one small definition (`agr_at`).

Main names.
 `agr_stored`, `agr_opens`, `agr_round`, `agr_fold`, `agr_chain`: the strict reader, part by part:
   the forms of a round's openings, in order, are the forms of the round's stored trees and then
   those of its opened trees in the description; every list of places is in order (`Fmt.listOK`).
 `agr_own`: in a description that is in order, a tree of the chain's own has the number "first tree
   + its place in the order of sending", and its form does not say "stored".
 `agr_zipMap`, `agr_zipFlat`, `agr_forms`, `agr_flat`, `agr_mem`, `agr_keep`, `agr_fst`,
   `agr_trees`: lists.
 `agr_numbers`: the numbers of the openings of own trees that were read, in order, are those of the
   description's.
 `agree_tab`: `Agree tab` at tab := the table of the openings that are not of stored trees (the list
   `ownOps o` of OnBytes/K/Left/Lax.lean, written out), under `hown` and `honce`.
 `agr_count`, `agr_once`: `honce` out of the limits of OnBytes/TypedOracleCompiler (`TypedOracleCompiler.Run.PQ.ok`).
 `agree_read`: `Agree tab` for every table that the typing makes of the openings of own trees,
   where the description's own part is within the limits of OnBytes/TypedOracleCompiler: no further test.

What `agree_tab` asks beside the reader's yes. `hown`: every tree that a round of the description
opens is the chain's own. `honce`: the places in the order of sending of all opened trees, over all
rounds, are a list without repeats. It is no general fact: the format lets a chain open a tree in
two rounds. The limits of OnBytes/TypedOracleCompiler have both as clauses (`own_of_ok`,
OnBytes/TypedOracleCompiler/Run/PageIsReaders.lean; `TabOk.once`, OnBytes/TypedOracleCompiler/Run/PageIsTabProofs.lean). For an
entry's typed rounds both lie as evaluations too (OnBytes/Params/EntryFactsRecord.lean:
`record_opens_all_own`, `record_opens_own`).

What is not claimed. Nothing on the table of the stored tables' openings. Nothing on a chain that
opens a tree twice. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.K.OpenedCols
import OnBytes.TypedOracleCompiler.Run.ViewERead3
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs
import Run.WalkTieProofs

set_option autoImplicit false

namespace OnBytes.K.Left
open TypedOracleCompiler.Slice
open _root_.Fmt (Shape OpenOut RoundOut ChainOut Plan Src St SpecX Stored Round)
open _root_.Run (HId idb idp)

/-! ## The strict reader, in order -/

section
variable (h : HId)

/-- The stored trees' openings behind one draw. -/
theorem agr_stored (cfg statement : ByteArray) (P : Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Stored) (sn : _root_.Fmt.Seen) (i : ℕ)
        (l : List (Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen) (k : ℕ),
      _root_.Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
      l.map (·.1) = ts.map (·.sh) ∧ ∀ x ∈ l, _root_.Fmt.listOK x.1.a x.2.1 = true
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact ⟨rfl, fun x hx => absurd hx (by simp)⟩
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
              obtain ⟨a1, a2⟩ := agr_stored cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec
              refine ⟨by rw [List.map_cons, List.map_cons, a1], fun x hx => ?_⟩
              rcases List.mem_cons.1 hx with rfl | hx
              · exact (_root_.Run.PQ.readOpening_some h _ _ _ _ _ _ b i o ho).1
              · exact a2 x hx
        · cases e

/-- The other trees' openings behind one draw. -/
theorem agr_opens (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (Shape × Src)) (sn : _root_.Fmt.Seen) (i : ℕ)
        (l : List (Shape × List ℕ × OpenOut)) (sn' : _root_.Fmt.Seen) (k : ℕ),
      _root_.Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
      l.map (·.1) = os.map (·.1) ∧ ∀ x ∈ l, _root_.Fmt.listOK x.1.a x.2.1 = true
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact ⟨rfl, fun x hx => absurd hx (by simp)⟩
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
                obtain ⟨a1, a2⟩ := agr_opens cfg P run roots poss b os sn1 o.next l1 sn2 k1 hrec
                refine ⟨by rw [List.map_cons, List.map_cons, a1], fun x hx => ?_⟩
                rcases List.mem_cons.1 hx with rfl | hx
                · exact (_root_.Run.PQ.readOpening_some h _ _ _ _ _ _ b i o ho).1
                · exact a2 x hx
          · cases e

/-- What is shown of a round as read: the forms of its openings, in order; its lists of places. -/
def agr_at (r : Round) (ts : List Stored) (ro : RoundOut) : Prop :=
  ro.opens.map (·.1) = ts.map (·.sh) ++ r.opens.map (·.1) ∧
    ∀ x ∈ ro.opens, _root_.Fmt.listOK x.1.a x.2.1 = true

/-- One round. -/
theorem agr_round (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : St) (r : Round) (ts : List Stored)
    (e : _root_.Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ ro : RoundOut, s'.out = s.out.push ro ∧ agr_at r ts ro := by
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
                obtain ⟨a1, a2⟩ := agr_stored h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs
                obtain ⟨c1, c2⟩ := agr_opens h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 ho
                refine ⟨_, rfl, ?_, fun x hx => ?_⟩
                · show (colsS ++ cols).map (·.1) = _
                  rw [List.map_append, a1, c1]
                · rcases List.mem_append.1 hx with hx | hx
                  · exact a2 x hx
                  · exact c2 x hx

/-- All rounds. -/
theorem agr_fold (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Round × List Stored)) (s s' : St),
      _root_.Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
      ∃ ros : List RoundOut, s'.out.toList = s.out.toList ++ ros ∧
        List.Forall₂ (fun r ro => agr_at r.1 r.2 ro) rs ros
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, List.Forall₂.nil⟩
  | r :: rs, s, s', e => by
      simp only [_root_.Fmt.foldRoundsX, idb] at e
      cases hc : _root_.Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2⟩ := agr_round h cfg statement P run b s s1 r.1 r.2 hc
        obtain ⟨ros, g1, g2⟩ := agr_fold cfg statement P run b rs s1 s' e
        refine ⟨ro :: ros, ?_, List.Forall₂.cons h2 g2⟩
        rw [g1, h1, Array.toList_push, List.append_assoc]
        rfl

/-- A chain of the strict reader, in order. -/
theorem agr_chain (S : SpecX) (seen : _root_.Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : ChainOut)
    (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧
      List.Forall₂ (fun r ro => agr_at r.1 r.2 ro) (S.base.rounds.zip S.stored)
        o.rounds.toList := by
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
          obtain ⟨ros, g1, g2⟩ := agr_fold h _ _ _ _ b _ _ s hf
          have g1' : s.out.toList = ros := by simpa using g1
          exact g1' ▸ g2

end

/-! ## The description -/

/-- In a description that is in order, a tree of the chain's own has the number "first tree + its
place in the order of sending", and its form does not say "stored". -/
theorem agr_own (S : _root_.Fmt.Spec) (hok : S.ok = true) (r : Round) (hr : r ∈ S.rounds)
    (y : Shape × Src) (hy : y ∈ r.opens) (n : ℕ) (hn : y.2 = .own n) :
    y.1.tree = S.firstTree + n ∧ y.1.stored = false := by
  simp only [_root_.Fmt.Spec.ok, Bool.and_eq_true, and_assoc] at hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -, -⟩ := hok
  obtain ⟨a, s, hqo⟩ := cols_roundsOk _ _ _ S.rounds _ _ h12 r hr
  simp only [_root_.Fmt.Round.ok, Bool.and_eq_true] at hqo
  have hz1 := List.all_eq_true.1 hqo.2 y hy
  rw [hn] at hz1
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hz1
  exact ⟨hz1.2.1.1.2, hz1.2.1.2⟩

/-! ## Lists -/

/-- a numbered list, mapped by a function of the members alone -/
theorem agr_zipMap {α β : Type} (g : α → β) :
    ∀ (l : List α) (n : ℕ), (l.zipIdx n).map (fun p => g p.1) = l.map g
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, agr_zipMap g l (n + 1)]

/-- the like for lists laid in a row -/
theorem agr_zipFlat {α β : Type} (g : α → List β) :
    ∀ (l : List α) (n : ℕ), (l.zipIdx n).flatMap (fun p => g p.1) = l.flatMap g
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons, agr_zipFlat g l (n + 1)]

/-- The forms of a chain's openings, in the file's order. -/
theorem agr_forms (c : ℕ) (o : ChainOut) :
    (opsOf c o).map (·.sh) = o.rounds.toList.flatMap fun ro => ro.opens.map (·.1) := by
  unfold opsOf
  rw [List.map_flatMap, ← agr_zipFlat (fun ro : RoundOut => ro.opens.map (·.1))]
  refine congrArg (fun g => List.flatMap g (o.rounds.toList.zipIdx)) (funext fun r => ?_)
  rw [List.map_map]
  exact agr_zipMap (fun x : Shape × List ℕ × OpenOut => x.1) r.1.opens 0

/-- Round by round: the forms that were read are the description's. -/
theorem agr_flat : ∀ (rs : List (Round × List Stored)) (ros : List RoundOut),
    List.Forall₂ (fun r ro => agr_at r.1 r.2 ro) rs ros →
      (ros.flatMap fun ro => ro.opens.map (·.1)) =
        rs.flatMap fun r => r.2.map (·.sh) ++ r.1.opens.map (·.1)
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by
    rw [List.flatMap_cons, List.flatMap_cons, h1.1, agr_flat _ _ h2]

/-- A round that was read goes with a round of the description. -/
theorem agr_mem : ∀ (rs : List (Round × List Stored)) (ros : List RoundOut),
    List.Forall₂ (fun r ro => agr_at r.1 r.2 ro) rs ros →
      ∀ ro ∈ ros, ∃ r ∈ rs, agr_at r.1 r.2 ro
  | _, _, .nil, _, h => absurd h (by simp)
  | _, _, .cons h1 h2, ro, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨r, hr, c⟩ := agr_mem _ _ h2 ro h
      exact ⟨r, List.mem_cons_of_mem _ hr, c⟩

/-- Of these forms those that do not say "stored" are the opened trees'. -/
theorem agr_keep : ∀ (rs : List (Round × List Stored)),
    (∀ r ∈ rs, (∀ t ∈ r.2, t.sh.stored = true) ∧ ∀ y ∈ r.1.opens, y.1.stored = false) →
      (rs.flatMap fun r => r.2.map (·.sh) ++ r.1.opens.map (·.1)).filter (fun s => !s.stored) =
        rs.flatMap fun r => r.1.opens.map (·.1)
  | [], _ => rfl
  | r :: rs, h => by
    obtain ⟨h1, h2⟩ := h r List.mem_cons_self
    rw [List.flatMap_cons, List.flatMap_cons, List.filter_append, List.filter_append,
      agr_keep rs fun x hx => h x (List.mem_cons_of_mem _ hx)]
    have e1 : (r.2.map (·.sh)).filter (fun s => !s.stored) = [] := by
      refine List.filter_eq_nil_iff.2 fun s hs => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      rw [h1 t ht]
      simp
    have e2 : (r.1.opens.map (·.1)).filter (fun s => !s.stored) = r.1.opens.map (·.1) := by
      refine List.filter_eq_self.2 fun s hs => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
      rw [h2 y hy]
      rfl
    rw [e1, e2, List.nil_append]

/-- a zip with a list of the same length, read at its first members -/
theorem agr_fst {α β γ : Type} (g : α → List γ) :
    ∀ (l : List α) (m : List β), m.length = l.length →
      ((l.zip m).flatMap fun x => g x.1) = l.flatMap g
  | [], _, _ => by simp
  | _ :: _, [], h => by cases h
  | a :: l, b :: m, h => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons,
      agr_fst g l m (by simpa using h)]

/-- The numbers of a list of opened trees of the chain's own. -/
theorem agr_trees (ft : ℕ) : ∀ (os : List (Shape × Src)),
    (∀ y ∈ os, ∃ n, y.2 = .own n ∧ y.1.tree = ft + n) →
      (os.map (·.1)).map (·.tree) = (os.filterMap _root_.Run.PQ.ownNo).map (ft + ·)
  | [], _ => rfl
  | y :: os, h => by
    obtain ⟨n, hn, ht⟩ := h y List.mem_cons_self
    have e : _root_.Run.PQ.ownNo y = some n := by
      unfold _root_.Run.PQ.ownNo
      rw [hn]
    rw [List.map_cons, List.map_cons, List.filterMap_cons_some e, List.map_cons, ht,
      agr_trees ft os fun z hz => h z (List.mem_cons_of_mem _ hz)]

/-! ## At a reading -/

/-- The numbers of the openings of own trees that were read, in order. -/
theorem agr_numbers (h : HId) (S : SpecX) (seen : _root_.Fmt.Seen) (b : ByteArray) (i j : ℕ)
    (o : ChainOut) (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hown : ∀ r ∈ S.base.rounds, ∀ y ∈ r.opens, ∃ n, y.2 = Src.own n) :
    ((opsOf 1 o).filter fun op => !op.sh.stored).map (·.sh.tree) =
      (S.base.rounds.flatMap fun r => r.opens.filterMap _root_.Run.PQ.ownNo).map
        (S.base.firstTree + ·) := by
  obtain ⟨hok, hF⟩ := agr_chain h S seen b i j o e
  have hb : S.base.ok = true ∧ S.stored.length = S.base.rounds.length := by
    simp only [_root_.Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at hok
    exact ⟨hok.1.1, hok.1.2⟩
  have e1 : ((opsOf 1 o).filter fun op => !op.sh.stored).map (·.sh.tree) =
      (((opsOf 1 o).map (·.sh)).filter fun s => !s.stored).map (·.tree) := by
    rw [List.filter_map, List.map_map]
    rfl
  rw [e1, agr_forms, agr_flat _ _ hF, agr_keep _ fun r hr => ⟨fun t ht =>
      cols_storedFlag S hok r hr t ht, fun y hy => by
        obtain ⟨n, hn⟩ := hown r.1 (List.of_mem_zip hr).1 y hy
        exact (agr_own S.base hb.1 r.1 (List.of_mem_zip hr).1 y hy n hn).2⟩,
    agr_fst (fun r : Round => r.opens.map (·.1)) _ _ hb.2, List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun r hr => ?_
  exact agr_trees S.base.firstTree r.opens fun y hy => by
    obtain ⟨n, hn⟩ := hown r hr y hy
    exact ⟨n, hn, (agr_own S.base hb.1 r hr y hy n hn).1⟩

/-- `Agree` from a yes of the reader, for the table of the chain's own trees: if no tree of the
chain's own is opened twice in the whole chain. -/
theorem agree_tab (h : HId) (S : SpecX) (seen : _root_.Fmt.Seen) (b : ByteArray) (i j : ℕ)
    (o : ChainOut) (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hown : ∀ r ∈ S.base.rounds, ∀ y ∈ r.opens, ∃ n, y.2 = Src.own n)
    (honce : (S.base.rounds.flatMap fun r => r.opens.filterMap _root_.Run.PQ.ownNo).Nodup)
    (tab : List ((ℕ × ℕ) × TypedOracleCompiler.Slice.Row))
    (ht : tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) = some tab) :
    TypedOracleCompiler.Run.PQ.Agree tab := by
  have hn : (((opsOf 1 o).filter fun op => !op.sh.stored).map (·.sh.tree)).Nodup := by
    rw [agr_numbers h S seen b i j o e hown]
    exact honce.map fun a c hac => Nat.add_left_cancel hac
  refine TypedOracleCompiler.Run.PQ.agree_of_once ht
    (fun a ha c hc hac => List.inj_on_of_nodup_map hn ha hc hac) fun a ha => ?_
  obtain ⟨-, hF⟩ := agr_chain h S seen b i j o e
  obtain ⟨ro, hro, x, hx, e1, e2, -⟩ := cols_ops o 1 a (List.mem_filter.1 ha).1
  obtain ⟨r, -, hr⟩ := agr_mem _ _ hF ro hro
  rw [e2]
  exact ((_root_.Run.WalkTie.listOK_spec x.1.a x.2.1 (hr.2 x hx)).2.1).imp
    fun hlt => Nat.ne_of_lt hlt

/-! ## "Once" out of the limits of OnBytes/TypedOracleCompiler -/

/-- how often a value stands among the values of a partial function on a list -/
theorem agr_count {α : Type} (f : α → Option ℕ) (n : ℕ) :
    ∀ l : List α, (l.filterMap f).count n = (l.filter fun x => f x == some n).length
  | [] => rfl
  | a :: l => by
    cases hf : f a with
    | none =>
      rw [List.filterMap_cons_none hf, List.filter_cons_of_neg (by rw [hf]; simp), agr_count f n l]
    | some m =>
      rw [List.filterMap_cons_some hf, List.count_cons, agr_count f n l]
      by_cases hm : m = n
      · subst hm
        rw [List.filter_cons_of_pos (by rw [hf]; simp), List.length_cons]
        simp
      · rw [List.filter_cons_of_neg (by rw [hf]; simpa using hm)]
        simp [hm]

/-- Within the limits of OnBytes/TypedOracleCompiler no tree of the chain's own is opened twice in the whole chain.
-/
theorem agr_once (S : _root_.Fmt.Spec) (hok : TypedOracleCompiler.Run.PQ.ok S = true) :
    (S.rounds.flatMap fun r => r.opens.filterMap _root_.Run.PQ.ownNo).Nodup := by
  have t := TypedOracleCompiler.Run.PQ.tab_limits S hok
  have e : (S.rounds.flatMap fun r => r.opens.filterMap _root_.Run.PQ.ownNo) =
      (_root_.Run.PQ.allOpens S).filterMap _root_.Run.PQ.ownNo := by
    unfold _root_.Run.PQ.allOpens
    rw [List.filterMap_flatMap]
  rw [e, List.nodup_iff_count_le_one]
  intro n
  rw [agr_count]
  by_cases hn : n < _root_.Run.PQ.nRoots S
  · exact t.once n hn
  · have hnil : ((_root_.Run.PQ.allOpens S).filter fun x =>
        _root_.Run.PQ.ownNo x == some n) = [] := by
      refine List.filter_eq_nil_iff.2 fun x hx hxn => hn ?_
      obtain ⟨r, hr, hxr⟩ := List.mem_flatMap.1 hx
      obtain ⟨k, g⟩ := TypedOracleCompiler.Run.PQ.tab_good S t r hr x hxr
      have hk : _root_.Run.PQ.ownNo x = some k := by
        unfold _root_.Run.PQ.ownNo
        rw [g.src]
      rw [hk] at hxn
      have : k = n := by simpa using hxn
      exact this ▸ g.lt
    rw [hnil]
    exact Nat.zero_le _

/-- `Agree` from a yes of the reader, without a new test: one yes of the strict reader under a
description whose own part, with the chain's random bytes counted as standing in the file, is within
the limits of OnBytes/TypedOracleCompiler. -/
theorem agree_read (h : HId) (S : SpecX)
    (hokb : TypedOracleCompiler.Run.PQ.ok (TypedOracleCompiler.Run.PQ.inFile S.base) = true)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ∀ tab, tabOf (fun op => op.sh.tree) ((opsOf 1 o).filter fun op => !op.sh.stored) = some tab →
      TypedOracleCompiler.Run.PQ.Agree tab :=
  fun tab ht => agree_tab h S seen b i j o e
    (TypedOracleCompiler.Run.PQ.own_of_ok (TypedOracleCompiler.Run.PQ.inFile S.base) hokb)
    (agr_once (TypedOracleCompiler.Run.PQ.inFile S.base) hokb) tab ht

end OnBytes.K.Left
