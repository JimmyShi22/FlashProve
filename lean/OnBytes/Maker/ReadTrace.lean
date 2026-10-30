-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ReadTrace.lean: a chain that the program's reader has read, round by round, with what
ties each round to the hash chain and each opening to the description: for every chain, also one
that opens trees taken over from another chain.

Statements and proofs. OnBytes/Maker/ReadFacts.lean says of a round as read what can be said without
the hash. Here the hash h is a letter of the statements. The library's `Run.PQ.TraceL`
(Run/PageIs.lean) is the pattern; it is proved of chains with a run's value that open their own
trees alone (OnBytes/Tie/StoredRead.lean), and of every chain in OnBytes/Tie/TraceStrict.lean
(`OnBytes.Tie.readX_trace`, from the same premise: the name `readX_trace` stands twice, there and
here). What this file adds: the shape, the list as drawn and the root of `srcOf` in one record for
each opening, and the law at the reader that the program runs.

Main names:
  `srcOf run roots s`: the root and the start of the tree that a description's opening names: of an
    own tree the root sent under its number and the chain's run's value; of a tree taken over the
    root and the start that the description gives.
  `OpenAt h cfg f salt sh start root xs b y`: the opening y has the shape sh and the list xs; it is
    what the reader of an opening hands out at these letters, from some byte of b on; and the root
    to which its walk led is `root`.
  `RoundAt h cfg st P run b x ro c roots`: of a description's round x and a round ro as read, at the
    chain's state c and the roots sent before: the call is in order; the message is read as the
    round's items; what is drawn is drawn from the row that the hash chain gives at c for the
    round's message and nonce (`Run.PQ.rowBs`); the listed positions; the work passes; each stored
    table's opening is `OpenAt` the table's salt and shape, the start cfg and the root in the
    statement's item; each tree's is `OpenAt` the plan's salt, the description's shape, and the root
    and start of `srcOf`.
  `TraceX`: all rounds, the state going on by `Run.PQ.nextOf` and the roots by the rounds' own.
  `readX_trace`, `readChain_trace`: of a chain that was read.
  `readChain_run`: a chain whose description has random bytes, in the file or given, has a run's
    value.
Limits: nothing is said of the record of vertices (OnBytes/Maker/ReadWalks.lean). That a tree taken
over has the root and the start of the chain that sent it is a matter of the description, not of the
reading: it is not stated here (OnBytes/Maker/SrcFitsOf.lean has it). Nothing on what a chain
proves. Nothing on soundness.


-/
import OnBytes.Maker.ReadWalks

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-- The root and the start of the tree that a description's opening names. -/
def srcOf (run : Option ByteArray) (roots : Array ByteArray) :
    Fmt.Src → Option (ByteArray × ByteArray)
  | .own n =>
    match roots[n]?, run with
    | some r, some s => some (r, s)
    | _, _ => none
  | .given r s => some (r, s)

/-- An opening as read, at the letters at which the reader of an opening was called. -/
structure OpenAt (h : HId) (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ) (sh : Fmt.Shape)
    (start root : ByteArray) (xs : List ℕ) (b : ByteArray) (y : OpenedY) : Prop where
  /-- the shape -/
  shape : y.1 = sh
  /-- the list -/
  list : y.2.1 = xs
  /-- what the reader of an opening has handed out -/
  read : ∃ i, Fmt.readOpeningW (m := Id) h cfg f salt sh start xs b i = some y.2.2
  /-- the root to which the walk led -/
  rootIs : y.2.2.root = root

theorem OpenAt.walked {h : HId} {cfg : ByteArray} {f : Fmt.Fld} {salt : ℕ} {sh : Fmt.Shape}
    {start root : ByteArray} {xs : List ℕ} {b : ByteArray} {y : OpenedY}
    (H : OpenAt h cfg f salt sh start root xs b y) : Walked h cfg y := by
  obtain ⟨i, e⟩ := H.read
  exact ⟨f, salt, start, b, i, by rw [H.shape, H.list]; exact e⟩

/-- Of a description's round, with its stored tables, and a round as read, at the chain's state c
and the roots sent before. -/
structure RoundAt (h : HId) (cfg st : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (x : Fmt.Round × List Fmt.Stored) (ro : Fmt.RoundOut) (c : Fmt.Chain)
    (roots : Array ByteArray) : Prop where
  /-- the call is in order -/
  ask : Fmt.askOK c.label c.rho (c.round + 1) ro.msg x.1.kind x.1.entry.work ro.nonce = true
  /-- the message is read as the round's items -/
  vals : Fmt.whole (Fmt.readItems P.field x.1.items) ro.msg = some ro.vals
  /-- what is drawn is drawn from the hash chain's row -/
  drawn : ro.drawn = Fmt.drawRound P.field x.1.entry x.1.kind
    (Fmt.rowOf (Fmt.msgA x.1.entry.work (rowBs h c x.1 ro)))
  /-- the listed positions -/
  list : ro.list = Fmt.listOf ro.drawn.poss
  /-- the work passes -/
  pass : Fmt.passesA x.1.entry.work (rowBs h c x.1 ro) = true
  /-- the stored tables' openings, then the trees' -/
  opens : ∃ cs co : List OpenedY, ro.opens = cs ++ co ∧
    List.Forall₂ (fun (t : Fmt.Stored) y => ∃ root, Fmt.itemRoot st t.item = some root ∧
      OpenAt h cfg P.field t.salt t.sh cfg root
        (Fmt.listOf ((Fmt.partOf t ro.drawn.poss).map (· % 2 ^ t.sh.a))) b y) x.2 cs ∧
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) y => ∃ rs,
      srcOf run (roots ++ (Fmt.rootsOf ro.vals).toArray) s.2 = some rs ∧
      OpenAt h cfg P.field P.salt s.1 rs.2 rs.1
        (Fmt.listOf (ro.drawn.poss.map (· % 2 ^ s.1.a))) b y) x.1.opens co

/-- All rounds: the state goes on by the hash chain, the roots by the rounds' own. -/
def TraceX (h : HId) (cfg st : ByteArray) (P : Fmt.Plan) (run : Option ByteArray) (b : ByteArray) :
    List (Fmt.Round × List Fmt.Stored) → List Fmt.RoundOut → Fmt.Chain → Array ByteArray → Prop
  | [], [], _, _ => True
  | x :: xs, ro :: ros, c, roots =>
    RoundAt h cfg st P run b x ro c roots ∧
      TraceX h cfg st P run b xs ros (nextOf h c x.1 ro) (roots ++ (Fmt.rootsOf ro.vals).toArray)
  | _, _, _, _ => False

section
variable (h : HId)

/-- The stored tables' openings behind one draw of positions. -/
theorem stored_at (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List ℕ) (b : ByteArray) :
    ∀ (ts : List Fmt.Stored) (sn : Fmt.Seen) (i : ℕ) (l : List OpenedY) (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readStored (m := Id) h cfg statement P poss b ts sn i = some (l, sn', k) →
    List.Forall₂ (fun (t : Fmt.Stored) y => ∃ root, Fmt.itemRoot statement t.item = some root ∧
      OpenAt h cfg P.field t.salt t.sh cfg root
        (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b y) ts l
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
              exact List.Forall₂.cons ⟨o.root, lxi_opt _ _ hroot, rfl, rfl, ⟨i, ho⟩, rfl⟩
                (stored_at cfg statement P poss b ts sn1 o.next l1 sn2 k1 hrec)
        · cases e

/-- The trees' openings behind one draw of positions. -/
theorem opens_at (cfg : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List ℕ) (b : ByteArray) :
    ∀ (os : List (Fmt.Shape × Fmt.Src)) (sn : Fmt.Seen) (i : ℕ) (l : List OpenedY)
      (sn' : Fmt.Seen) (k : ℕ),
    Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i = some (l, sn', k) →
    List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) y => ∃ rs, srcOf run roots s.2 = some rs ∧
      OpenAt h cfg P.field P.salt s.1 rs.2 rs.1 (Fmt.listOf (poss.map (· % 2 ^ s.1.a))) b y) os l
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
          · rename_i hroot
            split at e
            · cases e
            · rename_i sn1 hadd
              cases hrec : Fmt.readOpens (m := Id) h cfg P run roots poss b os sn1 o.next with
              | none => rw [hrec] at e; cases e
              | some z =>
                rw [hrec] at e
                obtain ⟨l1, sn2, k1⟩ := z
                simp only [idp] at e
                obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
                refine List.Forall₂.cons ⟨(root, start), ?_, rfl, rfl, ⟨i, ho⟩, bytes_beq _ _ hroot⟩
                  (opens_at cfg P run roots poss b os sn1 o.next l1 sn2 k1 hrec)
                cases src with
                | own n => exact hrs
                | given r s => exact hrs
          · cases e

/-- One round of the strict reader. -/
theorem roundX_at (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (e : Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    ∃ ro : Fmt.RoundOut, s'.out = s.out.push ro ∧ s'.chain = nextOf h s.chain r ro ∧
      s'.roots = s.roots ++ (Fmt.rootsOf ro.vals).toArray ∧
      RoundAt h cfg statement P run b (r, ts) ro s.chain s.roots := by
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
                refine ⟨⟨msg, vals, nonce, _, _, colsS ++ cols⟩, rfl, hc, rfl, hk, hvals, ?_, rfl,
                  hpass, colsS, cols, rfl,
                  stored_at h cfg statement P _ b ts s.seen i2 colsS sn1 i2' hs,
                  opens_at h cfg P run _ _ b r.opens sn1 i2' cols sn2 i3 ho⟩
                show Fmt.drawRound P.field r.entry r.kind (Fmt.rowOf cv.2) = _
                rw [hvb]
                rfl

/-- All rounds of a chain. -/
theorem foldX_trace (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s s' : Fmt.St),
    Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s = some s' →
    ∃ ros : List Fmt.RoundOut, s'.out.toList = s.out.toList ++ ros ∧
      TraceX h cfg statement P run b rs ros s.chain s.roots
  | [], s, s', e => by
      obtain rfl := Option.some.inj e
      exact ⟨[], (List.append_nil _).symm, trivial⟩
  | r :: rs, s, s', e => by
      simp only [Fmt.foldRoundsX, idb] at e
      cases hc : Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
      | none => rw [hc] at e; cases e
      | some s1 =>
        rw [hc] at e
        dsimp only at e
        obtain ⟨ro, h1, h2, h3, h4⟩ := roundX_at h cfg statement P run b s s1 r.1 r.2 hc
        obtain ⟨ros, g1, g2⟩ := foldX_trace cfg statement P run b rs s1 s' e
        refine ⟨ro :: ros, ?_, h4, ?_⟩
        · rw [g1, h1, Array.toList_push, List.append_assoc]
          rfl
        · rw [h2, h3] at g2
          exact g2

/-- **A chain that the strict reader has read**: its head was made from the parameters' digest, the
statement and the random bytes; its rounds are a trace from the head's first value and no root. -/
theorem readX_trace (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ∃ (x : Option ByteArray) (i0 : ℕ), Fmt.rndOf S.base b i = some (x, i0) ∧
      Fmt.startChainW (m := Id) h S.base.label (h 169 0 1 Fmt.zero32 S.base.params)
        S.base.statement x = some ⟨o.run, o.rho0⟩ ∧
      TraceX h S.base.cfg S.base.statement S.base.plan o.run b (S.base.rounds.zip S.stored)
        o.rounds.toList ⟨S.base.label, o.rho0, 0⟩ #[] := by
  obtain ⟨-, x, i0, hd, s, hr, hst, hf, rfl, -⟩ := readX_stages h S seen b i o j e
  obtain ⟨ros, g1, g2⟩ := foldX_trace h _ _ _ _ b _ _ s hf
  have hl : s.out.toList = ros := g1
  refine ⟨x, i0, hr, hst, ?_⟩
  show TraceX h _ _ _ hd.run b _ s.out.toList _ _
  rw [hl]
  exact g2

/-- A head that is made from random bytes has a run's value. -/
theorem startChain_run (lab : ℕ) (pd st rnd : ByteArray) (hd : Fmt.ChainHead)
    (e : Fmt.startChainW (m := Id) h lab pd st (some rnd) = some hd) :
    ∃ run, hd.run = some run := by
  unfold Fmt.startChainW at e
  split at e
  · dsimp only at e
    split at e
    · simp only [idb] at e
      split at e
      · simp only [idp] at e
        obtain rfl := Option.some.inj e
        exact ⟨_, rfl⟩
      · cases e
    · cases e
  · cases e

end

/-- **The same of the reader that the program runs.** -/
theorem readChain_trace (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    ∃ (x : Option ByteArray) (i0 : ℕ), Fmt.rndOf S.base b i = some (x, i0) ∧
      Fmt.startChainW (m := Id) Fmt.formatHash S.base.label (Fmt.formatHash 169 0 1 Fmt.zero32 S.base.params)
        S.base.statement x = some ⟨o.run, o.rho0⟩ ∧
      TraceX Fmt.formatHash S.base.cfg S.base.statement S.base.plan o.run b (S.base.rounds.zip S.stored)
        o.rounds.toList ⟨S.base.label, o.rho0, 0⟩ #[] :=
  readX_trace Fmt.formatHash S seen b i o j ((readChain_eq S seen b i).symm.trans e)

/-- **A chain whose description has random bytes, in the file or given, has a run's value.** -/
theorem readChain_run (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (hr : S.base.rand ≠ .none) : ∃ run, o.run = some run := by
  obtain ⟨x, i0, h1, h2, -⟩ := readChain_trace S seen b i o j e
  cases x with
  | some rnd => exact startChain_run Fmt.formatHash _ _ _ rnd ⟨o.run, o.rho0⟩ h2
  | none =>
    exfalso
    unfold Fmt.rndOf at h1
    cases hS : S.base.rand with
    | none => exact hr hS
    | given y => rw [hS] at h1; cases h1
    | inFile =>
      rw [hS] at h1
      cases hs : Fmt.slice b i 32 with
      | none => rw [hs] at h1; cases h1
      | some z => rw [hs] at h1; cases h1

end OnBytes.Maker
