-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadFacts.lean: what the rounds of a chain are that the program's reader has read, for
every chain: also one that opens trees taken over from another chain.

Statements and proofs. The strict reader with stored tables (`Fmt.readChainX`, Fmt/Rules8X.lean)
reads, behind a round's draw of positions, first the stored tables' openings, each at the list of
its part of the draws, and then the trees', each at the list of the draws cut to the tree's depth.
OnBytes/Tie/StoredRead.lean says more of its output, for a chain with a run's value that opens no
tree taken over from another chain. Here less is said, of every chain: with or without a run's
value, and also where a round opens trees that are taken over (`Fmt.Src.given`).

Main names:
  `OpenRead salt s l y`: of an opening y as read: its shape is s, its list is l, the list is in
    order, and columns, salts and digests have the numbers and lengths that the list asks for.
  `RoundRead P x ro`: of a description's round x, with its stored tables, and a round ro as read:
    the message is read as the round's items; what is drawn is drawn by the format's rule, and as
    many positions as the plan's entry says; the openings are the stored tables' and then the
    trees', one for each, each `OpenRead` at the list that the draws of ro give.
  `opens_read`, `roundX_read`, `foldX_read`, `readX_read`: from one list of openings to a whole
    chain, at any function for the hash. `readChain_read`: of the reader that the program runs.
  `RoundListed`, `readX_listed`, `readChain_listed`: the shapes and the lists alone.
  `readChain_vals`: round by round the message is read as the round's items.
  `ListedAsDrawn a dl ros`, `PartsWithin dl ros`: the lists, and that no stored table's part of the
    draws is shortened, in the letters of the plain data of a file's chain (`Three.RDL`).
  `readChain_asDrawn`, `readIn_asDrawn`, `readChain_within`, `readIn_within`, `readIn_view`: at a
    reading that has returned.
Limits: that the stored tables of the description under which a chain was read are those of the
plain data is a hypothesis here. Nothing is said of roots, walks or the record of vertices. Nothing
on what a chain proves. Nothing on soundness.


-/
import OnBytes.Tie.StoredLists
import OnBytes.Chain.ReaderLaws
import OnBytes.Three.Data

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-- What an opening is, as the strict reader hands it out. salt: the bytes of a leaf's salt. -/
structure OpenRead (salt : ℕ) (s : Fmt.Shape) (l : List ℕ)
    (y : Fmt.Shape × List ℕ × Fmt.OpenOut) : Prop where
  /-- the shape is the description's -/
  sh : y.1 = s
  /-- the list -/
  xs : y.2.1 = l
  /-- the list is sorted, without repeats, not empty and within the tree -/
  okl : Fmt.listOK s.a y.2.1 = true
  /-- columns, salts and digests have the numbers and lengths that the list asks for -/
  okb : (⟨s.a, y.2.1, y.2.2.cols, y.2.2.salts, y.2.2.given⟩ : OpenB).ok salt s.W = true

/-- Of a description's round, with its stored tables, and a round as read. -/
structure RoundRead (P : Fmt.Plan) (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) :
    Prop where
  /-- the message is read as the round's items -/
  vals : Fmt.whole (Fmt.readItems P.field x.1.items) ro.msg = some ro.vals
  /-- what is drawn is drawn by the format's rule for the round's entry and kind, from some row -/
  drawn : ∃ row, ro.drawn = Fmt.drawRound P.field x.1.entry x.1.kind row
  /-- as many positions are drawn as the plan's entry says -/
  poss : ro.drawn.poss.length = x.1.entry.poss
  /-- the stored tables' openings, then the trees' -/
  opens : ∃ cs co : List (Fmt.Shape × List ℕ × Fmt.OpenOut), ro.opens = cs ++ co ∧
    List.Forall₂ (fun (t : Fmt.Stored) y =>
      OpenRead t.salt t.sh (Fmt.listOf ((Fmt.partOf t ro.drawn.poss).map (· % 2 ^ t.sh.a))) y)
      x.2 cs ∧
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) y =>
      OpenRead P.salt s.1 (Fmt.listOf (ro.drawn.poss.map (· % 2 ^ s.1.a))) y) x.1.opens co

/-- The shapes and the lists alone. -/
def RoundListed (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) : Prop :=
  ∃ cs co : List (Fmt.Shape × List ℕ × Fmt.OpenOut), ro.opens = cs ++ co ∧
    List.Forall₂ (fun (t : Fmt.Stored) (y : Fmt.Shape × List ℕ × Fmt.OpenOut) =>
      y.1 = t.sh ∧ y.2.1 = Fmt.listOf ((Fmt.partOf t ro.drawn.poss).map (· % 2 ^ t.sh.a))) x.2 cs ∧
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) (y : Fmt.Shape × List ℕ × Fmt.OpenOut) =>
      y.1 = s.1 ∧ y.2.1 = Fmt.listOf (ro.drawn.poss.map (· % 2 ^ s.1.a))) x.1.opens co

theorem RoundRead.listed {P : Fmt.Plan} {x : Fmt.Round × List Fmt.Stored} {ro : Fmt.RoundOut}
    (H : RoundRead P x ro) : RoundListed x ro := by
  obtain ⟨cs, co, ho, h1, h2⟩ := H.opens
  exact ⟨cs, co, ho, h1.imp fun _ _ f => ⟨f.sh, f.xs⟩, h2.imp fun _ _ f => ⟨f.sh, f.xs⟩⟩

section
variable (h : HId)

/-- Each opening that `Fmt.readOpens` has read behind one draw of positions; whichever tree it
opens. -/
theorem opens_read (cfg : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (Fmt.Shape × Fmt.Src)) (sn : Fmt.Seen) (i : ℕ)
      (l : List (Fmt.Shape × List ℕ × Fmt.OpenOut)) (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) y =>
      OpenRead P.salt s.1 (Fmt.listOf (poss.map (· % 2 ^ s.1.a))) y) os l
  | [], sn, i, l, sn', k, e => by
      obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
      exact List.Forall₂.nil
  | (sh, src) :: os, sn, i, l, sn', k, e => by
      unfold Fmt.readOpens at e
      dsimp only at e
      split at e
      · cases e
      · rename_i root start hrs
        simp only [idb] at e
        cases ho : Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
            (Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
        | none => rw [ho] at e; cases e
        | some o =>
          rw [ho] at e
          dsimp only at e
          split at e
          · split at e
            · cases e
            · rename_i sn1 hadd
              cases hrec : Fmt.readOpens (m := Id) h cfg P run roots poss b os sn1 o.next with
              | none => rw [hrec] at e; cases e
              | some z =>
                rw [hrec] at e
                obtain ⟨l1, sn2, k1⟩ := z
                simp only [idp] at e
                obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
                obtain ⟨hl, cs, hp, hc, hs⟩ :=
                  readOpening_some h cfg P.field P.salt sh start _ b i o ho
                refine List.Forall₂.cons ⟨rfl, rfl, hl, ?_⟩
                  (opens_read cfg P run roots poss b os sn1 o.next l1 sn2 k1 hrec)
                show (⟨sh.a, _, o.cols, o.salts, o.given⟩ : OpenB).ok P.salt sh.W = true
                rw [hc, hs]
                exact open_ok P.field P.salt sh _ b i cs o.given o.next hp hl
          · cases e

/-- One round of the strict reader. -/
theorem roundX_read (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (e : Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ ro : Fmt.RoundOut, s'.out = s.out.push ro ∧ RoundRead P (r, ts) ro := by
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
                exact ⟨⟨msg, vals, nonce, _, _, colsS ++ cols⟩, rfl, hvals, ⟨_, rfl⟩,
                  CostP.drawRound_poss _ _ _ _, colsS, cols, rfl,
                  (stored_facts h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs).imp
                    (fun _ _ f => ⟨f.sh, f.xs, f.okl, f.okb⟩),
                  opens_read h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 ho⟩

/-- All rounds of a chain. -/
theorem foldX_read (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s s' : Fmt.St),
    Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
    ∃ ros : List Fmt.RoundOut,
      s'.out.toList = s.out.toList ++ ros ∧ List.Forall₂ (RoundRead P) rs ros
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, List.Forall₂.nil⟩
  | r :: rs, s, s', e => by
      simp only [Fmt.foldRoundsX, idb] at e
      cases hc : Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2⟩ := roundX_read h cfg statement P run b s s1 r.1 r.2 hc
        obtain ⟨ros, g1, g2⟩ := foldX_read cfg statement P run b rs s1 s' e
        refine ⟨ro :: ros, ?_, List.Forall₂.cons h2 g2⟩
        rw [g1, h1, Array.toList_push, List.append_assoc]
        rfl

/-- **A chain that the strict reader has read**, from any byte, under any record of vertices: the
description is in order, and round by round `RoundRead`. -/
theorem readX_read (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧
      List.Forall₂ (RoundRead S.base.plan) (S.base.rounds.zip S.stored) o.rounds.toList := by
  obtain ⟨hok, x, i0, hd, s, -, -, hf, rfl, -⟩ := readX_stages h S seen b i o j e
  obtain ⟨ros, g1, g2⟩ := foldX_read h _ _ _ _ b _ _ s hf
  refine ⟨hok, ?_⟩
  show List.Forall₂ _ _ s.out.toList
  rw [g1]
  exact g2

/-- The shapes and the lists alone. -/
theorem readX_listed (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    S.ok = true ∧ List.Forall₂ RoundListed (S.base.rounds.zip S.stored) o.rounds.toList :=
  ⟨(readX_read h S seen b i o j e).1, (readX_read h S seen b i o j e).2.imp fun _ _ f => f.listed⟩

end

/-- A description in order has stored tables for each round. -/
theorem stored_length {S : Fmt.SpecX} (hok : S.ok = true) :
    S.stored.length = S.base.rounds.length := by
  unfold Fmt.SpecX.ok at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  exact hok.1.2

/-- **The same of the reader that the program runs.** -/
theorem readChain_read (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    S.ok = true ∧
      List.Forall₂ (RoundRead S.base.plan) (S.base.rounds.zip S.stored) o.rounds.toList :=
  readX_read Fmt.formatHash S seen b i o j ((readChain_eq S seen b i).symm.trans e)

theorem readChain_listed (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    S.ok = true ∧ List.Forall₂ RoundListed (S.base.rounds.zip S.stored) o.rounds.toList :=
  readX_listed Fmt.formatHash S seen b i o j ((readChain_eq S seen b i).symm.trans e)

/-- **Round by round the message is read as the round's items.** -/
theorem readChain_vals (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    List.Forall₂ (fun (r : Fmt.Round) (ro : Fmt.RoundOut) =>
      Fmt.whole (Fmt.readItems S.base.plan.field r.items) ro.msg = some ro.vals)
      S.base.rounds o.rounds.toList := by
  obtain ⟨hok, H⟩ := readChain_read S seen b i o j e
  have hm : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (le_of_eq (stored_length hok).symm)
  rw [← hm, List.forall₂_map_left_iff]
  exact H.imp fun _ _ f => f.vals

/-! ## In the letters of a file's plain data -/

/-- Round by round: a stored table's opening lists what its part of the draws gives at the depth a;
every opening behind the stored tables' lists what the draws give at its own depth. -/
def ListedAsDrawn (a : ℕ) (dl : List Three.RDL) (ros : List Fmt.RoundOut) : Prop :=
  ∀ p ∈ dl.zip ros,
    (∀ tz ∈ p.1.stored.zip p.2.opens,
      tz.2.2.1 = Fmt.listOf ((Fmt.partOf tz.1 p.2.drawn.poss).map (· % 2 ^ a))) ∧
    ∀ z ∈ p.2.opens.drop p.1.stored.length,
      z.2.1 = Fmt.listOf (p.2.drawn.poss.map (· % 2 ^ z.1.a))

/-- Pairs with a list that goes on behind the first list's length. -/
theorem zip_append_more {α β : Type} : ∀ (l : List α) (m n : List β), l.length = m.length →
    l.zip (m ++ n) = l.zip m
  | [], _, _, _ => by simp
  | _ :: _, [], _, e => by cases e
  | a :: l, b :: m, n, e => by
    rw [List.cons_append, List.zip_cons_cons, List.zip_cons_cons,
      zip_append_more l m n (Nat.succ.inj e)]

/-- What holds of every pair holds of every member on the right. -/
theorem forall₂_right {α β : Type} {R : α → β → Prop} {Q : β → Prop}
    (hq : ∀ a b, R a b → Q b) : ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, Q b
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons h t, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hq _ _ h
    · exact forall₂_right hq t b hb

/-- One round. -/
theorem round_asDrawn (a : ℕ) (d : Three.RDL) (x : Fmt.Round × List Fmt.Stored)
    (ro : Fmt.RoundOut) (H : RoundListed x ro) (hst : x.2 = d.stored)
    (ha : ∀ t ∈ d.stored, t.sh.a = a) :
    (∀ tz ∈ d.stored.zip ro.opens,
      tz.2.2.1 = Fmt.listOf ((Fmt.partOf tz.1 ro.drawn.poss).map (· % 2 ^ a))) ∧
    ∀ z ∈ ro.opens.drop d.stored.length,
      z.2.1 = Fmt.listOf (ro.drawn.poss.map (· % 2 ^ z.1.a)) := by
  obtain ⟨cs, co, ho, h1, h2⟩ := H
  rw [hst] at h1
  have hl : d.stored.length = cs.length := h1.length_eq
  constructor
  · rintro ⟨t, y⟩ htz
    rw [ho, zip_append_more _ _ _ hl] at htz
    have hR := (List.forall₂_iff_zip.1 h1).2 htz
    show y.2.1 = _
    rw [hR.2, ha t (List.of_mem_zip htz).1]
  · intro z hz
    rw [ho, List.drop_left' hl.symm] at hz
    exact forall₂_right (Q := fun z => z.2.1 = Fmt.listOf (ro.drawn.poss.map (· % 2 ^ z.1.a)))
      (fun s y hy => by
        show y.2.1 = _
        rw [hy.2, hy.1]) h2 z hz

/-- **From the description's rounds to the data's.** -/
theorem listedAsDrawn_of (a : ℕ) :
    ∀ (dl : List Three.RDL) (xs : List (Fmt.Round × List Fmt.Stored)) (ros : List Fmt.RoundOut),
    List.Forall₂ RoundListed xs ros → xs.map (·.2) = dl.map (·.stored) →
    (∀ d ∈ dl, ∀ t ∈ d.stored, t.sh.a = a) → ListedAsDrawn a dl ros
  | [], _, _, _, _, _ => by
    intro p hp
    simp at hp
  | _ :: _, _, _, .nil, e, _ => by cases e
  | d :: dl, x :: xs, ro :: ros, .cons h t, e, ha => by
    intro p hp
    rw [List.map_cons, List.map_cons] at e
    obtain ⟨e1, e2⟩ := List.cons.inj e
    rw [List.zip_cons_cons] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact round_asDrawn a d x ro h e1 (ha d List.mem_cons_self)
    · exact listedAsDrawn_of a dl xs ros t e2
        (fun d' hd' => ha d' (List.mem_cons_of_mem _ hd')) p hp

/-- **At a chain that the program's reader has read.** hst: the description's stored tables are the
data's. ha: they have the depth a. -/
theorem readChain_asDrawn (a : ℕ) (dl : List Three.RDL) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (hst : S.stored = dl.map (·.stored)) (ha : ∀ d ∈ dl, ∀ t ∈ d.stored, t.sh.a = a) :
    ListedAsDrawn a dl o.rounds.toList := by
  obtain ⟨hok, H⟩ := readChain_listed S seen b i o j e
  refine listedAsDrawn_of a dl _ _ H ?_ ha
  rw [← hst]
  exact List.map_snd_zip (le_of_eq (stored_length hok))

/-- The same of a reading within a verdict. -/
theorem readIn_asDrawn (a : ℕ) (dl : List Three.RDL) (S : Fmt.SpecX) (b : ByteArray) (i : ℕ)
    (s s' : Session) (c : ChainRead) (e : readIn S b i s = some (c, s'))
    (hst : S.stored = dl.map (·.stored)) (ha : ∀ d ∈ dl, ∀ t ∈ d.stored, t.sh.a = a) :
    ListedAsDrawn a dl c.out.rounds.toList := by
  unfold readIn at e
  cases hr : readChain S s.seen b i with
  | none => rw [hr] at e; cases e
  | some z =>
    rw [hr] at e
    obtain ⟨o, j⟩ := z
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    exact readChain_asDrawn a dl S s.seen b i o j hr hst ha

/-- The view of a chain as read is the strict reader's view of what was read. -/
theorem readIn_view (S : Fmt.SpecX) (b : ByteArray) (i : ℕ) (s s' : Session) (c : ChainRead)
    (e : readIn S b i s = some (c, s')) : c.view = Fmt.viewX S c.out := by
  unfold readIn at e
  cases hr : readChain S s.seen b i with
  | none => rw [hr] at e; cases e
  | some z =>
    rw [hr] at e
    obtain ⟨o, j⟩ := z
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    exact viewOf_eq S o

/-! ## No stored table's part of the draws is shortened -/

/-- Round by round each stored table's part ends within the round's draws. -/
def PartsWithin (dl : List Three.RDL) (ros : List Fmt.RoundOut) : Prop :=
  ∀ p ∈ dl.zip ros, ∀ t ∈ p.1.stored, t.lo + t.count ≤ p.2.drawn.poss.length

/-- In a round whose stored tables are in order each part ends within the entry's number. -/
theorem storedOk_within {st : ByteArray} {r : Fmt.Round} {ts : List Fmt.Stored}
    (h : Fmt.storedOk st r ts = true) (t : Fmt.Stored) (ht : t ∈ ts) :
    t.lo + t.count ≤ r.entry.poss := by
  unfold Fmt.storedOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with he | h
  · rw [List.isEmpty_iff.1 he] at ht
    cases ht
  · exact partsFrom_le ts 0 _ h.1.2 t ht

theorem partsWithin_of (st : ByteArray) :
    ∀ (dl : List Three.RDL) (xs : List (Fmt.Round × List Fmt.Stored)) (ros : List Fmt.RoundOut),
    List.Forall₂ (fun (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) =>
      ro.drawn.poss.length = x.1.entry.poss) xs ros →
    (∀ x ∈ xs, Fmt.storedOk st x.1 x.2 = true) → xs.map (·.2) = dl.map (·.stored) →
    PartsWithin dl ros
  | [], _, _, _, _, _ => by
    intro p hp
    simp at hp
  | _ :: _, _, _, .nil, _, e => by cases e
  | d :: dl, x :: xs, ro :: ros, .cons h t, hs, e => by
    intro p hp
    rw [List.map_cons, List.map_cons] at e
    obtain ⟨e1, e2⟩ := List.cons.inj e
    rw [List.zip_cons_cons] at hp
    rcases List.mem_cons.1 hp with rfl | hp
    · intro u hu
      show u.lo + u.count ≤ ro.drawn.poss.length
      rw [h]
      exact storedOk_within (hs x List.mem_cons_self) u (e1 ▸ hu)
    · exact partsWithin_of st dl xs ros t (fun x' hx' => hs x' (List.mem_cons_of_mem _ hx')) e2 p hp

/-- **At a chain that the program's reader has read.** -/
theorem readChain_within (dl : List Three.RDL) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : ℕ) (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (hst : S.stored = dl.map (·.stored)) : PartsWithin dl o.rounds.toList := by
  obtain ⟨hok, H⟩ := readChain_read S seen b i o j e
  refine partsWithin_of S.base.statement dl _ _ (H.imp fun _ _ f => f.poss) ?_ ?_
  · have h2 := hok
    unfold Fmt.SpecX.ok at h2
    simp only [Bool.and_eq_true, List.all_eq_true] at h2
    exact h2.2
  · rw [← hst]
    exact List.map_snd_zip (le_of_eq (stored_length hok))

/-- The same of a reading within a verdict. -/
theorem readIn_within (dl : List Three.RDL) (S : Fmt.SpecX) (b : ByteArray) (i : ℕ)
    (s s' : Session) (c : ChainRead) (e : readIn S b i s = some (c, s'))
    (hst : S.stored = dl.map (·.stored)) : PartsWithin dl c.out.rounds.toList := by
  unfold readIn at e
  cases hr : readChain S s.seen b i with
  | none => rw [hr] at e; cases e
  | some z =>
    rw [hr] at e
    obtain ⟨o, j⟩ := z
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    exact readChain_within dl S s.seen b i o j hr hst

end OnBytes.Maker
