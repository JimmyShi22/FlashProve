-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredRead.lean: what the strict reader has read of a chain that opens stored tables.

The strict reader with stored tables (`Fmt.readChainX`) reads, behind a round's draw of positions,
first the openings of the stored tables and then those of the chain's own trees. This file says what
its output is, for a chain that begins at any byte of a file and under any record of tree vertices.
If the chain has a run value and opens no taken-over tree, its rounds without the stored tables'
openings are a trace in the library's sense (`Run.PQ.TraceL`), all work passes, and every own
opening walks to its root. A chain's run value is the hash of the parameters' digest and the chain's
32 random bytes. A taken-over tree is one whose root the description gives, from another chain.
Each stored table's opening has the right form, lists the positions that its share of the round's
drawn positions gives, and walks to the root that the statement holds for that table (`StoredFact`
spells this out).

Main definitions: `StoredFact`, `roundWithStoredOpenings`.
Main theorems: `stored_facts`, `roundX_facts`, `foldX_facts`, `readX_stages`.
OnBytes/Tie/StoredMain.lean uses them. The reader is taken at a plain function h for the hash
(`(m := Id)`). The library's `stripR` leaves the vertices met out of a round.
It claims nothing on what a chain proves.
-/
import Run.ParseLaxXIsProofs
import Fmt.Rules8Steps
import Run.CostFmtProofs

set_option autoImplicit false

namespace OnBytes.Tie
open Run Run.PQ

/-- What one opening of a stored table is, as the strict reader hands it out. t says which table
is opened and at which part of the round's draws `poss`. -/
structure StoredFact (h : HId) (cfg statement : ByteArray) (poss : List ℕ) (t : Fmt.Stored)
    (y : Fmt.Shape × List ℕ × Fmt.OpenOut) : Prop where
  /-- the shape is the table's -/
  sh : y.1 = t.sh
  /-- the list is made from the table's part of the draws -/
  xs : y.2.1 = Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))
  /-- the list is sorted, without repeats, not empty and within the tree -/
  okl : Fmt.listOK t.sh.a y.2.1 = true
  /-- the root is the one in the statement's item -/
  root : Fmt.itemRoot statement t.item = some y.2.2.root
  /-- columns, salts and digests have the numbers and lengths that the list asks for -/
  okb : (⟨t.sh.a, y.2.1, y.2.2.cols, y.2.2.salts, y.2.2.given⟩ : OpenB).ok t.salt t.sh.W = true
  /-- the walk from the opened leaves ends in the root -/
  walk : rootOf h cfg cfg t.sh y.2.1 y.2.2 = y.2.2.root

/-- A round as read, put together from its part without stored tables and the stored tables'
openings, which come first. -/
def roundWithStoredOpenings (p : Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)) : Fmt.RoundOut :=
  ⟨p.1.msg, p.1.vals, p.1.nonce, p.1.drawn, p.1.list, p.2 ++ p.1.opens⟩

section
variable (h : HId)

/-- Each opening that `Fmt.readStored` has read behind one draw of positions has `StoredFact`. -/
theorem stored_facts (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Fmt.Stored) (sn : Fmt.Seen) (i : ℕ)
      (l : List (Fmt.Shape × List ℕ × Fmt.OpenOut)) (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
    List.Forall₂ (StoredFact h cfg statement poss) ts l
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
        · rename_i hroot
          have hroot' : Fmt.itemRoot statement t.item = some o.root := lxi_opt _ _ hroot
          split at e
          · cases e
          · rename_i sn1 hadd
            cases hrec : Fmt.readStored (m := Id) h cfg statement P poss b ts sn1 o.next with
            | none => rw [hrec] at e; cases e
            | some z =>
              rw [hrec] at e
              obtain ⟨l1, sn2, k1⟩ := z
              simp only [idp] at e
              obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
              have ih := stored_facts cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec
              obtain ⟨hl, cs, hp, hc, hs⟩ :=
                readOpening_some h cfg P.field t.salt t.sh cfg _ b i o ho
              refine List.Forall₂.cons ⟨rfl, rfl, hl, hroot', ?_, ?_⟩ ih
              · show (⟨t.sh.a, _, o.cols, o.salts, o.given⟩ : OpenB).ok t.salt t.sh.W = true
                rw [hc, hs]
                exact open_ok P.field t.salt t.sh _ b i cs o.given o.next hp hl
              · exact ((WalkTie.reader_id h cfg P.field t.salt t.sh cfg _ b i o ho).2.2.2).symm
        · cases e

/-- What one round of the strict reader has done, in a chain with a run value, if it opens no
taken-over tree: the new state's output, chain value and roots, the facts that make up `TraceL`, the
work, the walks, and
`StoredFact` of each stored table's opening. -/
theorem roundX_facts (cfg statement : ByteArray) (P : Fmt.Plan) (run : ByteArray) (b : ByteArray)
    (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (hown : ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    (e : Fmt.roundX (m := Id) h cfg statement P (some run) b s r ts = some s') :
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
      (∀ x ∈ p.1.opens, rootOf h cfg run x.1 x.2.1 (stripO x.2.2) = x.2.2.root) ∧
      List.Forall₂ (StoredFact h cfg statement p.1.drawn.poss) ts p.2 := by
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
              cases ho : Fmt.readOpens (m := Id) h cfg P (some run)
                  (s.roots ++ (Fmt.rootsOf vals).toArray)
                  (Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2)).poss b r.opens sn1
                  i2' with
              | none => rw [ho] at e; cases e
              | some z =>
                rw [ho] at e
                obtain ⟨cols, sn2, i3⟩ := z
                simp only [idp] at e
                obtain rfl := Option.some.inj e
                have hl0 := stored_facts h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs
                obtain ⟨hl1, hl2⟩ :=
                  readOpens_lax h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 hown ho
                refine ⟨(⟨msg, vals, nonce, _, _, cols⟩, colsS), rfl, hc, rfl, hk, hvals, ?_, rfl,
                  laxOpens_facts P _ _ b r.opens i2' _ i3 hl1, hpass, hl2, hl0⟩
                show Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2) = _
                rw [hvb]
                rfl

/-- All rounds of a chain with a run value, if none opens a taken-over tree. Without the stored
tables' openings they are a trace (`TraceL`), all work passes, and all own openings walk to their
roots. Each stored table's opening has `StoredFact`. Each round has drawn as many positions as its
entry of the plan says. -/
theorem foldX_facts (cfg statement : ByteArray) (P : Fmt.Plan) (run : ByteArray) (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s s' : Fmt.St),
    (∀ r ∈ rs, ∀ x ∈ r.1.opens, ∃ n, x.2 = .own n) →
    Fmt.foldRoundsX (m := Id) h cfg statement P (some run) b rs s = some s' →
    ∃ rc : List (Fmt.RoundOut × List (Fmt.Shape × List ℕ × Fmt.OpenOut)),
      s'.out.toList = s.out.toList ++ rc.map roundWithStoredOpenings ∧
      TraceL h P (rs.map (·.1)) (rc.map fun p => stripR p.1) s.chain s.roots ∧
      passL h (rs.map (·.1)) (rc.map fun p => stripR p.1) s.chain = true ∧
      rootsAll h cfg run (rc.map fun p => stripR p.1) = true ∧
      List.Forall₂ (fun x p => p.1.drawn.poss.length = x.1.entry.poss ∧
        List.Forall₂ (StoredFact h cfg statement p.1.drawn.poss) x.2 p.2) rs rc
  | [], s, s', _, e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, trivial, rfl, rfl, List.Forall₂.nil⟩
  | r :: rs, s, s', hown, e => by
      simp only [Fmt.foldRoundsX, idb] at e
      cases hc : Fmt.roundX (m := Id) h cfg statement P (some run) b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
          roundX_facts h cfg statement P run b s s1 r.1 r.2 (hown r List.mem_cons_self) hc
        obtain ⟨rc, g1, g2, g3, g4, g5⟩ := foldX_facts cfg statement P run b rs s1 s'
          (fun r' hr' => hown r' (List.mem_cons_of_mem _ hr')) e
        refine ⟨p :: rc, ?_, ⟨h4, h5, h6, h7, h8, ?_⟩, ?_, ?_, List.Forall₂.cons ⟨?_, h11⟩ g5⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · rw [h2, h3] at g2
          exact g2
        · show (Fmt.passesA r.1.entry.work (rowBs h s.chain r.1 (stripR p.1)) &&
            passL h (rs.map (·.1)) (rc.map fun p => stripR p.1)
              (nextOf h s.chain r.1 (stripR p.1))) = true
          rw [h9, ← h2, g3]
          rfl
        · show ((stripR p.1).opens.all (fun x => rootOf h cfg run x.1 x.2.1 x.2.2 == x.2.2.root) &&
            rootsAll h cfg run (rc.map fun p => stripR p.1)) = true
          rw [g4, Bool.and_true, List.all_eq_true]
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          show (rootOf h cfg run y.1 y.2.1 (stripO y.2.2) == y.2.2.root) = true
          rw [h10 y hy]
          exact bytes_beq_self _
        · rw [h6]
          exact CostP.drawRound_poss _ _ _ _

/-- If the strict reader with stored tables has read a chain, then each of its stages has
succeeded. The chain may begin at any byte i, and the record `seen` may hold anything.
`h 169 0 1 Fmt.zero32 S.base.params` is the parameters' digest: the format's hash call 169. -/
theorem readX_stages (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧ ∃ (x : Option ByteArray) (i0 : ℕ) (hd : Fmt.ChainHead) (s : Fmt.St),
      Fmt.rndOf S.base b i = some (x, i0) ∧
      Fmt.startChainW (m := Id) h S.base.label (h 169 0 1 Fmt.zero32 S.base.params)
        S.base.statement x = some hd ∧
      Fmt.foldRoundsX (m := Id) h S.base.cfg S.base.statement S.base.plan hd.run b
        (S.base.rounds.zip S.stored)
        (⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], seen, #[]⟩ : Fmt.St) = some s ∧
      o = ⟨h 169 0 1 Fmt.zero32 S.base.params, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩ ∧
      j = s.pos := by
  unfold Fmt.readChainX at e
  split at e
  · cases e
  · rename_i hok
    dsimp only at e
    split at e
    · cases e
    · rename_i x i0 hr
      simp only [Fmt.paramsDigestW, idb] at e
      cases hst : Fmt.startChainW (m := Id) h S.base.label (h 169 0 1 Fmt.zero32 S.base.params)
          S.base.statement x with
      | none => rw [hst] at e; cases e
      | some hd =>
        rw [hst] at e
        dsimp only at e
        cases hf : Fmt.foldRoundsX (m := Id) h S.base.cfg S.base.statement S.base.plan hd.run b
            (S.base.rounds.zip S.stored)
            (⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], seen, #[]⟩ : Fmt.St) with
        | none => rw [hf] at e; cases e
        | some s =>
          rw [hf] at e
          simp only [idp] at e
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
          exact ⟨by simpa using hok, x, i0, hd, s, hr, hst, hf, rfl, rfl⟩

end

end OnBytes.Tie

#print axioms OnBytes.Tie.foldX_facts
#print axioms OnBytes.Tie.readX_stages
