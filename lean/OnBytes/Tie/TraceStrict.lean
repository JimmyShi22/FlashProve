-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TraceStrict.lean: what the strict reader has read is a trace, for EVERY chain.
OnBytes/Tie/StoredRead.lean says it for a chain that has a run value and opens trees of its own
alone. A key's and a proof's later chains open trees that an earlier chain has sent
(`Fmt.Src.given`), and a chain may have no random bytes. Here nothing is asked of the description:
at any hash h, whatever the run value and the sources of the opened trees, the rounds as read,
without the stored tables' openings, are a trace in the library's sense (`Run.PQ.TraceL`), all work
passes, each opening walks to its root FROM ITS OWN START (`startOf`), each stored table's opening
has `StoredFact`, and EACH OPENING WAS READ BY ONE CALL OF THE LIBRARY's READER OF AN OPENING
(`OwnRead`, `StoredReadAt`), so that what that reader's laws say of an opening's own record of
vertices holds of it.
`trace_append` cuts a trace at any round: a stretch of a chain's first n rounds has a trace of its
own.
Main theorems: `readOpens_laxG`, `roundX_factsG`, `foldX_factsG`, `readX_trace`, `readIn_trace`,
`trace_append`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.StoredRead
import OnBytes.Chain.Session
import OnBytes.Chain.ReaderLaws

set_option autoImplicit false

namespace OnBytes.Tie
open Run Run.PQ

/-- The value from which the leaves of an opened tree start: the chain's run value for a tree of its
own, and for a taken-over tree the value that the description gives. -/
def startOf (run : Option ByteArray) : Fmt.Src → Option ByteArray
  | .own _ => run
  | .given _ s => some s

/-- The root to which an opened tree must lead. -/
def rootAt (roots : Array ByteArray) : Fmt.Src → Option ByteArray
  | .own n => roots[n]?
  | .given r _ => some r

/-- Two relations that hold along two lists hold together. -/
theorem forall₂_and {α β : Type} {R S : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ S l l' →
      List.Forall₂ (fun a b => R a b ∧ S a b) l l'
  | _, _, .nil, .nil => .nil
  | _, _, .cons r rs, .cons s ss => .cons ⟨r, s⟩ (forall₂_and rs ss)

section
variable (h : HId)

/-- What the opening y of a tree that is no stored table is: it was read by ONE CALL of the
library's reader of an opening, from the tree's own start, at some place of b; and it walks to its
root. x: the tree's shape and source in the description. -/
def OwnRead (cfg : ByteArray) (P : Fmt.Plan) (run : Option ByteArray) (b : ByteArray)
    (x : Fmt.Shape × Fmt.Src) (y : Fmt.Shape × List ℕ × Fmt.OpenOut) : Prop :=
  ∃ start i, startOf run x.2 = some start ∧
    Fmt.readOpeningW (m := Id) h cfg P.field P.salt x.1 start y.2.1 b i = some y.2.2 ∧
    rootOf h cfg start y.1 y.2.1 (stripO y.2.2) = y.2.2.root

/-- The same of a stored table's opening: its leaves start from cfg, its salts have t.salt bytes. -/
def StoredReadAt (cfg : ByteArray) (P : Fmt.Plan) (b : ByteArray) (t : Fmt.Stored)
    (y : Fmt.Shape × List ℕ × Fmt.OpenOut) : Prop :=
  ∃ i, Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg y.2.1 b i = some y.2.2

/-- Each stored table's opening was read by one call of the reader of an opening. -/
theorem stored_read (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Fmt.Stored) (sn : Fmt.Seen) (i : ℕ)
      (l : List (Fmt.Shape × List ℕ × Fmt.OpenOut)) (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
    List.Forall₂ (StoredReadAt h cfg P b) ts l
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact List.Forall₂.nil
  | t :: ts, sn, i, l, sn', k, e => by
      unfold Fmt.readStored at e
      simp only [idb] at e
      cases ho : Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
          (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
      | none => rw [ho] at e; cases e
      | some o =>
        rw [ho] at e
        dsimp only at e
        split at e
        · split at e
          · cases e
          · rename_i sn1 hadd
            cases hrec : Fmt.readStored (m := Id) h cfg statement P poss b ts sn1 o.next with
            | none => rw [hrec] at e; cases e
            | some z =>
              rw [hrec] at e
              obtain ⟨l1, sn2, k1⟩ := z
              simp only [idp] at e
              obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
              exact List.Forall₂.cons ⟨i, ho⟩
                (stored_read cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec)
        · cases e

/-- One opening and the rest, the rest's facts being given. -/
theorem opens_stepG (cfg : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) (sh : Fmt.Shape) (src : Fmt.Src)
    (os : List (Fmt.Shape × Fmt.Src)) (sn : Fmt.Seen) (i : ℕ)
    (l : List (Fmt.Shape × List ℕ × Fmt.OpenOut)) (sn' : Fmt.Seen) (k : ℕ)
    (root start : ByteArray) (hr : rootAt roots src = some root)
    (hst : startOf run src = some start)
    (ih : ∀ sn1 i1 l1 sn2 k1,
      Fmt.readOpens (m := Id) h cfg P run roots poss b os sn1 i1 = some (l1, sn2, k1) →
      laxOpens P roots poss b os i1 = some (l1.map fun x => (x.1, x.2.1, stripO x.2.2), k1) ∧
      List.Forall₂ (OwnRead h cfg P run b) os l1)
    (e : (do
      match ← Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
          (Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
      | none => pure none
      | some o =>
        if o.root == root then
          match Fmt.addSeen root (Fmt.entered o.seen) sn with
          | none => pure none
          | some sn' =>
            match ← Fmt.readOpens (m := Id) h cfg P run roots poss b os sn' o.next with
            | none => pure none
            | some (l, sn'', k) =>
              pure (some ((sh, Fmt.listOf (poss.map (· % 2 ^ sh.a)), o) :: l, sn'', k))
        else pure none : Id _) = some (l, sn', k)) :
    laxOpens P roots poss b ((sh, src) :: os) i =
        some (l.map fun x => (x.1, x.2.1, stripO x.2.2), k) ∧
      List.Forall₂ (OwnRead h cfg P run b) ((sh, src) :: os) l := by
  simp only [idb] at e
  cases ho : Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
      (Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
  | none => rw [ho] at e; cases e
  | some o =>
    rw [ho] at e
    dsimp only at e
    split at e
    · rename_i hroot
      have hroot' : o.root = root := bytes_beq _ _ hroot
      split at e
      · cases e
      · rename_i sn1 hadd
        cases hrec : Fmt.readOpens (m := Id) h cfg P run roots poss b os sn1 o.next with
        | none => rw [hrec] at e; cases e
        | some z =>
          rw [hrec] at e
          obtain ⟨l1, sn2, k1⟩ := z
          simp only [idp] at e
          obtain ⟨rfl, -, rfl⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
          obtain ⟨ih1, ih2⟩ := ih sn1 o.next l1 sn2 k1 hrec
          obtain ⟨hl, cs, hp, hc, hs⟩ :=
            readOpening_some h cfg P.field P.salt sh start _ b i o ho
          refine ⟨?_, List.Forall₂.cons ⟨start, i, hst, ho, ?_⟩ ih2⟩
          · cases src with
            | own n =>
              have hr' : roots[n]? = some root := hr
              unfold laxOpens
              dsimp only
              rw [hr', hl, hp]
              dsimp only
              rw [ih1]
              show some _ = some _
              rw [List.map_cons]
              unfold stripO
              rw [hc, hs, hroot']
            | given r s =>
              have hr' : r = root := Option.some.inj hr
              subst hr'
              unfold laxOpens
              dsimp only
              rw [hl, hp]
              dsimp only
              rw [ih1]
              show some _ = some _
              rw [List.map_cons]
              unfold stripO
              rw [hc, hs, hroot']
          · exact ((WalkTie.reader_id h cfg P.field P.salt sh start _ b i o ho).2.2.2).symm
    · cases e

/-- The openings behind one draw, whatever their sources. -/
theorem readOpens_laxG (cfg : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (Fmt.Shape × Fmt.Src)) (sn : Fmt.Seen) (i : ℕ)
        (l : List (Fmt.Shape × List ℕ × Fmt.OpenOut)) (sn' : Fmt.Seen) (k : ℕ),
      Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
      laxOpens P roots poss b os i = some (l.map fun x => (x.1, x.2.1, stripO x.2.2), k) ∧
      List.Forall₂ (OwnRead h cfg P run b) os l
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, rfl⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact ⟨rfl, List.Forall₂.nil⟩
  | (sh, src) :: os, sn, i, l, sn', k, e => by
      unfold Fmt.readOpens at e
      dsimp only at e
      have ih := readOpens_laxG cfg P run roots poss b os
      cases src with
      | own n =>
        dsimp only at e
        cases hr : roots[n]? with
        | none => rw [hr] at e; cases e
        | some root =>
          rw [hr] at e
          cases run with
          | none => cases e
          | some s =>
            exact opens_stepG h cfg P (some s) roots poss b sh (.own n) os sn i l sn' k
                root s hr rfl ih e
      | given r s =>
        exact opens_stepG h cfg P run roots poss b sh (.given r s) os sn i l sn' k r s rfl rfl ih e

/-- What one round of the strict reader has done, whatever the run value and the trees' sources. -/
theorem roundX_factsG (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray)
    (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (e : Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut),
      s'.out = s.out.push (roundWithStoredOpenings p) ∧
      s'.chain = nextOf h s.chain r (stripR p.1) ∧
      s'.roots = s.roots ++ (Fmt.rootsOf p.1.vals).toArray ∧
      Fmt.askOK s.chain.label s.chain.rho (s.chain.round + 1) p.1.msg r.kind r.entry.work
        p.1.nonce = true ∧
      Fmt.whole (Fmt.readItems P.field r.items) p.1.msg = some p.1.vals ∧
      p.1.drawn = Fmt.drawRound P.field r.entry r.kind
        (Fmt.rowOf (Fmt.msgA r.entry.work (rowBs h s.chain r (stripR p.1)))) ∧
      p.1.list = Fmt.listOf p.1.drawn.poss ∧
      List.Forall₂ (OpenFacts P (s.roots ++ (Fmt.rootsOf p.1.vals).toArray) p.1.drawn.poss)
        r.opens (stripR p.1).opens ∧
      Fmt.passesA r.entry.work (rowBs h s.chain r (stripR p.1)) = true ∧
      List.Forall₂ (OwnRead h cfg P run b) r.opens p.1.opens ∧
      List.Forall₂ (fun t y => StoredFact h cfg statement p.1.drawn.poss t y ∧
        StoredReadAt h cfg P b t y) ts p.2 := by
  unfold Fmt.roundX at e
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
        cases hq : Fmt.Chain.queryW (m := Id) h s.chain msg r.kind r.entry.work nonce
            ((Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          obtain ⟨hlq, hpass⟩ := query_lax h _ _ _ _ _ _ cv.1 cv.2 hq
          obtain ⟨hk, hc, hvb⟩ := laxQuery_some h _ _ _ _ _ _ cv.1 cv.2 hlq
          split at e
          · cases e
          · rename_i u i2 hlist
            cases hs : Fmt.readStored (m := Id) h cfg statement P
                (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b ts s.seen i2 with
            | none => rw [hs] at e; cases e
            | some y =>
              rw [hs] at e
              obtain ⟨colsS, sn1, i2'⟩ := y
              dsimp only at e
              cases ho : Fmt.readOpens (m := Id) h cfg P run
                  (s.roots ++ (Fmt.rootsOf vals).toArray)
                  (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn1
                  i2' with
              | none => rw [ho] at e; cases e
              | some z =>
                rw [ho] at e
                obtain ⟨cols, sn2, i3⟩ := z
                simp only [idp] at e
                obtain rfl := Option.some.inj e
                have hl0 := forall₂_and (stored_facts h cfg statement P _ b ts s.seen i2
                    colsS sn1 i2' hs)
                  (stored_read h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs)
                obtain ⟨hl1, hl2⟩ :=
                  readOpens_laxG h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 ho
                refine ⟨(⟨msg, vals, nonce, _, _, cols⟩, colsS), rfl, hc, rfl, hk, hvals, ?_, rfl,
                  laxOpens_facts P _ _ b r.opens i2' _ i3 hl1, hpass, hl2, hl0⟩
                show Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2) = _
                rw [hvb]
                rfl

/-- All rounds of a chain, whatever the run value and the trees' sources. -/
theorem foldX_factsG (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s s' : Fmt.St),
    Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
    ∃ rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)),
      s'.out.toList = s.out.toList ++ rc.map roundWithStoredOpenings ∧
      TraceL h P (rs.map (·.1)) (rc.map fun p => stripR p.1) s.chain s.roots ∧
      passL h (rs.map (·.1)) (rc.map fun p => stripR p.1) s.chain = true ∧
      List.Forall₂ (fun x p => p.1.drawn.poss.length = x.1.entry.poss ∧
        List.Forall₂ (OwnRead h cfg P run b) x.1.opens p.1.opens ∧
        List.Forall₂ (fun t y => StoredFact h cfg statement p.1.drawn.poss t y ∧
          StoredReadAt h cfg P b t y) x.2 p.2) rs rc
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, trivial, rfl, List.Forall₂.nil⟩
  | r :: rs, s, s', e => by
      simp only [Fmt.foldRoundsX, idb] at e
      cases hc : Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
          roundX_factsG h cfg statement P run b s s1 r.1 r.2 hc
        obtain ⟨rc, g1, g2, g3, g5⟩ := foldX_factsG cfg statement P run b rs s1 s' e
        refine ⟨p :: rc, ?_, ⟨h4, h5, h6, h7, h8, ?_⟩, ?_, List.Forall₂.cons ⟨?_, h10, h11⟩ g5⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · rw [h2, h3] at g2
          exact g2
        · show (Fmt.passesA r.1.entry.work (rowBs h s.chain r.1 (stripR p.1)) &&
            passL h (rs.map (·.1)) (rc.map fun p => stripR p.1)
              (nextOf h s.chain r.1 (stripR p.1))) = true
          rw [h9, ← h2, g3]
          rfl
        · rw [h6]
          exact CostP.drawRound_poss _ _ _ _

/-- What the strict reader has read of ANY chain, at any hash. The chain may begin at any byte,
under any record of vertices; nothing is asked of its random bytes or of the sources of its trees.
-/
theorem readX_trace (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut)
    (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧ o.pd = h 169 0 1 Fmt.zero32 S.base.params ∧
    ∃ rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)),
      o.rounds.toList = rc.map roundWithStoredOpenings ∧
      TraceL h S.base.plan S.base.rounds (rc.map fun p => stripR p.1)
        ⟨S.base.label, o.rho0, 0⟩ #[] ∧
      passL h S.base.rounds (rc.map fun p => stripR p.1) ⟨S.base.label, o.rho0, 0⟩ = true ∧
      List.Forall₂ (fun x p => p.1.drawn.poss.length = x.1.entry.poss ∧
        List.Forall₂ (OwnRead h S.base.cfg S.base.plan o.run b) x.1.opens p.1.opens ∧
        List.Forall₂ (fun t y => StoredFact h S.base.cfg S.base.statement p.1.drawn.poss t y ∧
          StoredReadAt h S.base.cfg S.base.plan b t y) x.2 p.2)
        (S.base.rounds.zip S.stored) rc := by
  obtain ⟨hok, x, i0, hd, s, -, -, hf, rfl, -⟩ := readX_stages h S seen b i o j e
  have hlen : S.stored.length = S.base.rounds.length := by
    have := hok
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have hz : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (by omega)
  obtain ⟨rc, g1, g2, g3, g5⟩ := foldX_factsG h _ _ _ _ _ _ _ _ hf
  rw [hz] at g2 g3
  exact ⟨hok, rfl, rc, by simpa using g1, g2, g3, g5⟩

/-! ## The roots of the openings -/

/-- The roots of one round's openings as read: a stored table's is the one that the statement's item
holds; a tree's of the chain's own is the root sent under its number among `roots` (all that were
sent up to and with this round); a taken-over tree's is the description's. -/
def RoundRoots (statement : ByteArray) (roots : Array ByteArray)
    (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) : Prop :=
  ∃ colsS cols, ro.opens = colsS ++ cols ∧
    List.Forall₂ (fun t y => Fmt.itemRoot statement t.item = some y.2.2.root) x.2 colsS ∧
    List.Forall₂ (fun z y => rootAt roots z.2 = some y.2.2.root) x.1.opens cols

/-- The same of all rounds, the roots sent being gathered on the way. -/
def RoundsRoots (statement : ByteArray) : Array ByteArray →
    List (Fmt.Round × List Fmt.Stored) → List Fmt.RoundOut → Prop
  | _, [], [] => True
  | roots, x :: xs, ro :: ros =>
    RoundRoots statement (roots ++ (Fmt.rootsOf ro.vals).toArray) x ro ∧
      RoundsRoots statement (roots ++ (Fmt.rootsOf ro.vals).toArray) xs ros
  | _, _, _ => False

/-- An opening's facts in a trace name its root. -/
theorem openFacts_roots (P : Fmt.Plan) (roots : Array ByteArray) (poss : List ℕ) :
    ∀ (os : List (Fmt.Shape × Fmt.Src)) (l : List (Fmt.Shape × List ℕ × Fmt.OpenOut)),
      List.Forall₂ (OpenFacts P roots poss) os (l.map fun x => (x.1, x.2.1, stripO x.2.2)) →
      List.Forall₂ (fun z y => rootAt roots z.2 = some y.2.2.root) os l
  | [], [], _ => List.Forall₂.nil
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | z :: os, y :: l, h => by
    cases h with
    | cons h1 h2 =>
      refine List.Forall₂.cons ?_ (openFacts_roots P roots poss os l h2)
      have e := h1.root
      cases hz : z.2 with
      | own n =>
        rw [hz] at e
        exact e
      | given r s =>
        rw [hz] at e
        exact e

/-- From a trace and the stored openings' facts to the roots of all rounds. -/
theorem trace_roots (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored))
      (rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut))) (c : Fmt.Chain)
      (roots : Array ByteArray),
      TraceL h P (rs.map (·.1)) (rc.map fun p => stripR p.1) c roots →
      List.Forall₂ (fun x p => p.1.drawn.poss.length = x.1.entry.poss ∧
        List.Forall₂ (OwnRead h cfg P run b) x.1.opens p.1.opens ∧
        List.Forall₂ (fun t y => StoredFact h cfg statement p.1.drawn.poss t y ∧
          StoredReadAt h cfg P b t y) x.2 p.2) rs rc →
      RoundsRoots statement roots rs (rc.map roundWithStoredOpenings)
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, f => by cases f
  | _ :: _, [], _, _, _, f => by cases f
  | x :: rs, p :: rc, c, roots, t, f => by
    obtain ⟨-, -, -, -, t5, t6⟩ := t
    cases f with
    | cons f1 f2 =>
      refine ⟨⟨p.2, p.1.opens, rfl, f1.2.2.imp fun _ _ q => q.1.root, ?_⟩,
        trace_roots cfg statement P run b rs rc _ _ t6 f2⟩
      exact openFacts_roots P _ _ _ _ t5

/-- The roots of all openings of a chain that the strict reader has read, at any hash. -/
theorem readX_roots (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut)
    (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    RoundsRoots S.base.statement #[] (S.base.rounds.zip S.stored) o.rounds.toList := by
  obtain ⟨hok, -, rc, g1, g2, -, g5⟩ := readX_trace h S seen b i o j e
  have hlen : S.stored.length = S.base.rounds.length := by
    have := hok
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have hz : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (by omega)
  rw [g1]
  refine trace_roots h S.base.cfg S.base.statement S.base.plan o.run b _ rc
    ⟨S.base.label, o.rho0, 0⟩ #[] ?_ g5
  rw [hz]
  exact g2

/-- The chain's head: the random bytes x are the description's or the file's; the run value and
the first value of what was read are what the format's start of a chain makes of the label, the
parameters' digest, THE STATEMENT and x. -/
theorem readX_head (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut)
    (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ∃ x i0 hd, Fmt.rndOf S.base b i = some (x, i0) ∧
      Fmt.startChainW (m := Id) h S.base.label o.pd S.base.statement x = some hd ∧
      hd.run = o.run ∧ hd.rho0 = o.rho0 := by
  obtain ⟨-, x, i0, hd, s, hx, hst, -, rfl, -⟩ := readX_stages h S seen b i o j e
  exact ⟨x, i0, hd, hx, hst, rfl, rfl⟩

/-- A chain that has random bytes, in the file or given, has a run value. -/
theorem readX_run (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut)
    (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hr : S.base.rand ≠ .none) : ∃ run, o.run = some run := by
  obtain ⟨-, x, i0, hd, s, hx, hst, -, rfl, -⟩ := readX_stages h S seen b i o j e
  have hx' : ∃ y, x = some y := by
    unfold Fmt.rndOf at hx
    cases hrand : S.base.rand with
    | inFile =>
      rw [hrand] at hx
      obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 hx
      exact ⟨y, (Prod.mk.inj hy).1.symm⟩
    | given y =>
      rw [hrand] at hx
      exact ⟨y, (Prod.mk.inj (Option.some.inj hx)).1.symm⟩
    | none => exact absurd hrand hr
  obtain ⟨y, rfl⟩ := hx'
  unfold Fmt.startChainW at hst
  split at hst
  · dsimp only at hst
    split at hst
    · simp only [idb] at hst
      split at hst
      · simp only [idp] at hst
        obtain rfl := Option.some.inj hst
        exact ⟨_, rfl⟩
      · cases hst
    · cases hst
  · cases hst

/-- The same of a chain that the program's reader has read within a session. -/
theorem readIn_trace (S : Fmt.SpecX) (b : ByteArray) (i : ℕ) (s s' : Session) (r : ChainRead)
    (e : readIn S b i s = some (r, s')) :
    S.ok = true ∧
    ∃ rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)),
      r.out.rounds.toList = rc.map roundWithStoredOpenings ∧
      TraceL Fmt.formatHash S.base.plan S.base.rounds (rc.map fun p => stripR p.1)
        ⟨S.base.label, r.out.rho0, 0⟩ #[] ∧
      passL Fmt.formatHash S.base.rounds (rc.map fun p => stripR p.1) ⟨S.base.label, r.out.rho0, 0⟩ =
        true := by
  unfold readIn at e
  cases h1 : readChain S s.seen b i with
  | none => simp [h1] at e
  | some y =>
    obtain ⟨o, j⟩ := y
    simp only [h1, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]
    rw [readChain_eq] at h1
    obtain ⟨hok, -, rc, g1, g2, g3, -⟩ := readX_trace Fmt.formatHash S s.seen b i o j h1
    exact ⟨hok, rc, g1, g2, g3⟩

/-- A chain's seal is the digest that its last round as read has drawn. -/
theorem seal_eq (r : ChainRead) (x : ByteArray) (e : r.seal = some x) :
    ∃ ro, r.out.rounds.back? = some ro ∧ ro.drawn.digest = some x := by
  unfold ChainRead.seal at e
  cases hb : r.out.rounds.back? with
  | none => simp [hb] at e
  | some ro => exact ⟨ro, rfl, by simpa [hb] using e⟩

/-- The reader's chain behind a list of rounds. -/
def chainAfter : List Fmt.Round → List Fmt.RoundOut → Fmt.Chain → Fmt.Chain
  | r :: rs, ro :: ros, c => chainAfter rs ros (nextOf h c r ro)
  | _, _, c => c

/-- The roots sent in a list of rounds as read. -/
def rootsAfter (ros : List Fmt.RoundOut) (roots : Array ByteArray) : Array ByteArray :=
  ros.foldl (fun a ro => a ++ (Fmt.rootsOf ro.vals).toArray) roots

/-- A trace can be cut at any round: the first rounds have a trace of their own, and the others
one that begins at the reader's chain and roots behind them. -/
theorem trace_append (P : Fmt.Plan) :
    ∀ (rs₁ rs₂ : List Fmt.Round) (ros : List Fmt.RoundOut) (c : Fmt.Chain)
      (roots : Array ByteArray), TraceL h P (rs₁ ++ rs₂) ros c roots →
      TraceL h P rs₁ (ros.take rs₁.length) c roots ∧
      TraceL h P rs₂ (ros.drop rs₁.length) (chainAfter h rs₁ (ros.take rs₁.length) c)
        (rootsAfter (ros.take rs₁.length) roots)
  | [], rs₂, ros, c, roots, t => by
      refine ⟨?_, ?_⟩
      · show TraceL h P [] (ros.take 0) c roots
        rw [List.take_zero]
        trivial
      · show TraceL h P rs₂ (ros.drop 0) (chainAfter h [] (ros.take 0) c)
          (rootsAfter (ros.take 0) roots)
        rw [List.take_zero, List.drop_zero]
        exact t
  | r :: rs₁, rs₂, [], c, roots, t => by
      exact absurd t (by simp [TraceL])
  | r :: rs₁, rs₂, ro :: ros, c, roots, t => by
      obtain ⟨t1, t2, t3, t4, t5, t6⟩ := t
      obtain ⟨u1, u2⟩ := trace_append P rs₁ rs₂ ros _ _ t6
      exact ⟨⟨t1, t2, t3, t4, t5, u1⟩, u2⟩

end

end OnBytes.Tie
