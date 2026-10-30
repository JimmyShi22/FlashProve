-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsChain.lean: from the verdict "accepted" on a proof file to every call of
the first chain's block, each in its place: the chain over the links, tied at both ends to the file.

 1. LinkStep: one call of runLinkH (OnBytes/Model/StagesLinks.lean), whole: the chain's first call
    for the link, from the context in which the call of runLinkH began; the tests between (they
    leave all as it was); the link's routine, from the context that the first call has left; the two
    tests behind it; the row on the table, if the link leaves one, up to the context that runLinkH
    leaves; and what runLinkH returns.
 2. LinksChain: the calls of runLinkH over a list of links, each from the state of the calls, the
    result and the context that the one before has left. runLinksFrom_chain. LinksChain.split: the
    chain cut at place j: the chain before the link, from the chain's own start; the link's step;
    the chain behind it, to the chain's own end.
 3. startOf s v: the context from which a block is run on a whole view (Blk.runNamed's own record).
    runOn_start, accepted_start: accepted ⟹ the file was read as r, and the first chain's block has
    run from startOf (firstStart c.first) r.first.view to a context without a mark in which nothing
    is left over.
 4. FileRan, accepted_file: accepted ⟹ every call of the first chain's block, from that start to
    that end: ChainCheck.start, the chain over the links, ChainCheck.finish, the reply's test (it
    was true), the number of rows, the first part of the test on the table, the seal.
 5. accepted_head: accepted, and the last link is of kind 2 ⟹ that link's step stands at the end of
    the chain of the file's own run; the state chk with which its routine was started has
    chk.plain[0]? = some reply, the caller's reply; and what the step returns is what the chain
    returns.
For every context that is named: no dry run; no mark.

Limits: one direction: from the verdict. Hypothesis: every link's routine keeps (AllKeep,
OnBytes/Tie/Pv/Keeps/KeepsLinks.lean). Nothing is said on what a call does.
-/
import OnBytes.Tie.Pv.Keeps.KeepsLoop
import OnBytes.Tie.Pv.Keeps.KeepsLinks

namespace OnBytes.L5

open OnBytes OnBytes.Model OnBytes.Model.Stages

/-! ## Reads that leave all as it was -/

theorem runs_blkGet {α : Type} {x : Option α} {n : String} {c : Ctx} {a : α} {c' : Ctx}
    (h : Runs (Blk.get x n) c a c') : x = some a ∧ c' = c := by
  cases x with
  | none => cases h
  | some y => cases h; exact ⟨rfl, rfl⟩

theorem runs_oracle {o : Nat} {c : Ctx} {a : Oracle} {c' : Ctx} (h : Runs (Blk.oracle o) c a c') :
    c' = c := by
  unfold Blk.oracle at h
  obtain ⟨S, c1, h1, h2⟩ := HasRuns.runs_bind h
  have e1 : (Except.ok (c.st, c) : Except Failure (Statement × Ctx)) = .ok (S, c1) := h1
  cases e1
  exact (runs_blkGet h2).2

/-- The test on the index-mask message reads and tests: it leaves the context as it was. -/
theorem indexMasksH_same {links : Array LinkH} {p : Params.First} {k : ChainCheck} {c : Ctx}
    {a : Nat}
    {c' : Ctx} (h : Runs (indexMasksH links p k) c a c') : c' = c := by
  unfold indexMasksH at h
  obtain ⟨_, c1, h1, h⟩ := HasRuns.runs_bind h
  obtain ⟨-, e1⟩ := runs_mustAs h1
  split at h
  · obtain ⟨x, c2, h2, h⟩ := HasRuns.runs_bind h
    obtain ⟨led, c3, h3, h⟩ := HasRuns.runs_bind h
    obtain ⟨_, c4, h4, h⟩ := HasRuns.runs_bind h
    obtain ⟨-, e5⟩ := HasRuns.runs_pure h
    rw [e5, (runs_mustAs h4).2, (runs_blkGet h3).2, runs_oracle h2, e1]
  · exact Fails.elim h

theorem runs_inPlace' {α : Type} {n : String} {b : Blk α} {c : Ctx} {a : α} {c' : Ctx}
    (h : Runs (Blk.inPlace n b) c a c') : Runs b c a c' := by
  have h' : (match b c with
    | .error e => .error (if e.place.isEmpty then { e with place := n } else e)
    | .ok x => .ok x) = (Except.ok (a, c') : Except Failure (α × Ctx)) := h
  split at h'
  · cases h'
  · rename_i x hx
    cases h'
    exact hx

/-! ## One link -/

/-- One call of runLinkH, whole. check out c: with what and where it began; r c': what it returned
and left; cEnd: the context at the very end of the run in which it stands. -/
structure LinkStep (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (cEnd : Ctx) (l : Nat)
    (X : LinkH) (check : ChainCheck) (out : Proof.LinksResult) (c : Ctx)
    (r : ChainCheck × Proof.LinksResult) (c' : Ctx) (chk : ChainCheck) (o : Option WsForkOut)
    (C' : LinkCtx) (F' : Fork) (c1 c2 : Ctx) : Prop where
  first : check.first c = .ok (chk, c1)
  masks : (l == 0) = true → indexMasksH links p chk c1 = .ok (r.2.indexMasks, c1)
  masks' : ¬(l == 0) = true → r.2.indexMasks = out.indexMasks
  plainHead : (X.kind == 2) = true → (chk.plain.size == 1) = true ∧ r.2.reply = chk.plain[0]?
  plainElse : ¬(X.kind == 2) = true → (chk.plain.size == 0) = true ∧ r.2.reply = out.reply
  atLink : (chk.link == l) = true
  run : X.run { check := chk, link := l, arrayOf := X.arrayOf, list := X.Tp } X.Fp c1 =
    .ok (((o, C'), F'), c2)
  closed : (C'.handed && C'.done) = true
  same : samePlan X F' C'.list = true
  next : r.1 = C'.check
  row : X.fv = true → ∃ o' row, o = some o' ∧
    pendingRowH wsLay r.2.indexMasks o' X.NCL p.lin c2 = .ok (row, c') ∧
    r.2.pending = out.pending ++ [row]
  noRow : ¬X.fv = true → c' = c2 ∧ r.2.pending = out.pending
  v1 : c1.ch.dry = false
  v2 : c2.ch.dry = false
  m0 : cEnd.failed = none → c.failed = none
  m1 : cEnd.failed = none → c1.failed = none
  m2 : cEnd.failed = none → c2.failed = none

/-- runLinkH, taken apart whole. -/
theorem runLinkH_step (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat) (X : LinkH)
    [KeepsM X.run] (check : ChainCheck) (out : Proof.LinksResult) {c : Ctx}
    {r : ChainCheck × Proof.LinksResult} {c' cEnd : Ctx} (d : View (m := Blk) c)
    (B : Clean (m := Blk) cEnd → Clean (m := Blk) c')
    (h : Runs (runLinkH links p wsLay l X check out) c r c') :
    ∃ chk o C' F' c1 c2, LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2 := by
  unfold runLinkH at h
  peel1_from h d B 1
  -- eight goals: the head's link or not; a row on the table or not; the first link or not
  all_goals first
    | (
      have i2 := indexMasksH_same r2
      subst i2
      obtain ⟨i3a, i3⟩ := runs_pure' r3
      subst i3a
      subst i3
      obtain ⟨t4, i4⟩ := runs_mustAs r4
      subst i4
      obtain ⟨t5, i5⟩ := runs_must r5
      subst i5
      have rRun := runs_inPlace' r6
      obtain ⟨t7, i7⟩ := runs_mustAs r7
      subst i7
      obtain ⟨t8, i8⟩ := runs_mustAs r8
      subst i8
      obtain ⟨iE, iE'⟩ := runs_pure' h
      subst iE
      subst iE'
      refine ⟨_, _, _, _, _, _,
        { first := r1,
          masks := fun _ => r2,
          masks' := fun hx => absurd ‹(l == 0) = true› hx,
          plainHead := ?_, plainElse := ?_, atLink := t5, run := rRun, closed := t7, same := t8,
          next := rfl,
          row := fun _ => ⟨_, _, by assumption, r9, rfl⟩,
          noRow := fun hx => absurd ‹X.fv = true› hx,
          v1 := d5, v2 := d6, m0 := b0, m1 := b5, m2 := b6 }⟩
      all_goals first
        | exact fun _ => ⟨t4, rfl⟩
        | exact fun hx => absurd hx ‹¬(X.kind == 2) = true›
        | exact fun hx => absurd ‹(X.kind == 2) = true› hx)
    | (
      have i2 := indexMasksH_same r2
      subst i2
      obtain ⟨i3a, i3⟩ := runs_pure' r3
      subst i3a
      subst i3
      obtain ⟨t4, i4⟩ := runs_mustAs r4
      subst i4
      obtain ⟨t5, i5⟩ := runs_must r5
      subst i5
      have rRun := runs_inPlace' r6
      obtain ⟨t7, i7⟩ := runs_mustAs r7
      subst i7
      obtain ⟨t8, i8⟩ := runs_mustAs r8
      subst i8
      obtain ⟨iE, iE'⟩ := runs_pure' h
      subst iE
      subst iE'
      refine ⟨_, _, _, _, _, _,
        { first := r1,
          masks := fun _ => r2,
          masks' := fun hx => absurd ‹(l == 0) = true› hx,
          plainHead := ?_, plainElse := ?_, atLink := t5, run := rRun, closed := t7, same := t8,
          next := rfl,
          row := fun hx => absurd hx ‹¬X.fv = true›,
          noRow := fun _ => ⟨rfl, rfl⟩,
          v1 := d5, v2 := d6, m0 := b0, m1 := b5, m2 := b6 }⟩
      all_goals first
        | exact fun _ => ⟨t4, rfl⟩
        | exact fun hx => absurd hx ‹¬(X.kind == 2) = true›
        | exact fun hx => absurd ‹(X.kind == 2) = true› hx)
    | (
      obtain ⟨i2a, i2⟩ := runs_pure' r2
      subst i2a
      subst i2
      obtain ⟨t4, i4⟩ := runs_mustAs r3
      subst i4
      obtain ⟨t5, i5⟩ := runs_must r4
      subst i5
      have rRun := runs_inPlace' r5
      obtain ⟨t7, i7⟩ := runs_mustAs r6
      subst i7
      obtain ⟨t8, i8⟩ := runs_mustAs r7
      subst i8
      obtain ⟨iE, iE'⟩ := runs_pure' h
      subst iE
      subst iE'
      refine ⟨_, _, _, _, _, _,
        { first := r1,
          masks := fun hx => absurd hx ‹¬(l == 0) = true›,
          masks' := fun _ => rfl,
          plainHead := ?_, plainElse := ?_, atLink := t5, run := rRun, closed := t7, same := t8,
          next := rfl,
          row := fun _ => ⟨_, _, by assumption, r8, rfl⟩,
          noRow := fun hx => absurd ‹X.fv = true› hx,
          v1 := d4, v2 := d5, m0 := b0, m1 := b4, m2 := b5 }⟩
      all_goals first
        | exact fun _ => ⟨t4, rfl⟩
        | exact fun hx => absurd hx ‹¬(X.kind == 2) = true›
        | exact fun hx => absurd ‹(X.kind == 2) = true› hx)
    | (
      obtain ⟨i2a, i2⟩ := runs_pure' r2
      subst i2a
      subst i2
      obtain ⟨t4, i4⟩ := runs_mustAs r3
      subst i4
      obtain ⟨t5, i5⟩ := runs_must r4
      subst i5
      have rRun := runs_inPlace' r5
      obtain ⟨t7, i7⟩ := runs_mustAs r6
      subst i7
      obtain ⟨t8, i8⟩ := runs_mustAs r7
      subst i8
      obtain ⟨iE, iE'⟩ := runs_pure' h
      subst iE
      subst iE'
      refine ⟨_, _, _, _, _, _,
        { first := r1,
          masks := fun hx => absurd hx ‹¬(l == 0) = true›,
          masks' := fun _ => rfl,
          plainHead := ?_, plainElse := ?_, atLink := t5, run := rRun, closed := t7, same := t8,
          next := rfl,
          row := fun hx => absurd hx ‹¬X.fv = true›,
          noRow := fun _ => ⟨rfl, rfl⟩,
          v1 := d4, v2 := d5, m0 := b0, m1 := b4, m2 := b5 }⟩
      all_goals first
        | exact fun _ => ⟨t4, rfl⟩
        | exact fun hx => absurd hx ‹¬(X.kind == 2) = true›
        | exact fun hx => absurd ‹(X.kind == 2) = true› hx)

/-! ## The chain over the links -/

/-- The calls of runLinkH over a list of links, each from the state of the chain's calls, the result
and the context that the one before has left. l: the number of the first of them. -/
def LinksChain (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (cEnd : Ctx) :
    List LinkH → Nat → ChainCheck → Proof.LinksResult → Ctx → ChainCheck × Proof.LinksResult → Ctx →
    Prop
  | [], _, check, out, c, r, c' => r = (check, out) ∧ c' = c
  | X :: rest, l, check, out, c, r, c' =>
    ∃ r1 cm chk o C' F' c1 c2,
      LinkStep links p wsLay cEnd l X check out c r1 cm chk o C' F' c1 c2 ∧ cm.ch.dry = false ∧
      (cEnd.failed = none → cm.failed = none) ∧
      LinksChain links p wsLay cEnd rest (l + 1) r1.1 r1.2 cm r c'

/-- runLinksFrom, taken apart whole. -/
theorem runLinksFrom_chain (links : Array LinkH) (p : Params.First) (wsLay : WsLay) (cEnd : Ctx) :
    ∀ (rest : List LinkH), (∀ X ∈ rest, KeepsM X.run) → ∀ (l : Nat) (check : ChainCheck)
      (out : Proof.LinksResult) (c : Ctx) (r : ChainCheck × Proof.LinksResult) (c' : Ctx),
      View (m := Blk) c → (Clean (m := Blk) cEnd → Clean (m := Blk) c') →
      Runs (runLinksFrom links p wsLay rest l check out) c r c' →
      LinksChain links p wsLay cEnd rest l check out c r c'
  | [], _, l, check, out, c, r, c', _, _, h => by
    unfold runLinksFrom at h
    exact runs_pure' h
  | Y :: rest, hk, l, check, out, c, r, c', d, B, h => by
    haveI := hk Y List.mem_cons_self
    have hk' : ∀ Z ∈ rest, KeepsM Z.run := fun Z hZ => hk Z (List.mem_cons_of_mem _ hZ)
    haveI := keepsM_runLinksFrom links p wsLay rest hk'
    unfold runLinksFrom at h
    peel1_from h d B 1
    obtain ⟨chk, o, C', F', k1, k2, S⟩ := runLinkH_step links p wsLay l Y check out d b1 r1
    exact ⟨_, _, chk, o, C', F', k1, k2, S, d1, b1,
      runLinksFrom_chain links p wsLay cEnd rest hk' (l + 1) _ _ _ _ _ d1 B h⟩

/-- The chain cut at place j: before the link, the link's step, behind the link. -/
theorem LinksChain.split {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} :
    ∀ {rest : List LinkH} {l : Nat} {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
      {r : ChainCheck × Proof.LinksResult} {c' : Ctx},
      LinksChain links p wsLay cEnd rest l check out c r c' → ∀ (j : Nat) (X : LinkH),
      rest[j]? = some X → ∃ check0 out0 c0 r1 cm chk o C' F' c1 c2,
        LinksChain links p wsLay cEnd (rest.take j) l check out c (check0, out0) c0 ∧
        LinkStep links p wsLay cEnd (l + j) X check0 out0 c0 r1 cm chk o C' F' c1 c2 ∧
        cm.ch.dry = false ∧ (cEnd.failed = none → cm.failed = none) ∧
        LinksChain links p wsLay cEnd (rest.drop (j + 1)) (l + j + 1) r1.1 r1.2 cm r c'
  | [], _, _, _, _, _, _, _, _, _, hj => by cases hj
  | Y :: rest, l, check, out, c, r, c', h, j, X, hj => by
    obtain ⟨r1, cm, chk, o, C', F', c1, c2, S, d, m, T⟩ := h
    cases j with
    | zero =>
      have e : Y = X := Option.some.inj hj
      subst e
      exact ⟨check, out, c, r1, cm, chk, o, C', F', c1, c2, ⟨rfl, rfl⟩, S, d, m, T⟩
    | succ j =>
      obtain ⟨check0, out0, c0, r1', cm', chk', o', C'', F'', c1', c2', A, S', d', m', B⟩ :=
        LinksChain.split T j X hj
      have e : l + (j + 1) = (l + 1) + j := by omega
      rw [e]
      exact ⟨check0, out0, c0, r1', cm', chk', o', C'', F'', c1', c2',
        ⟨r1, cm, chk, o, C', F', c1, c2, S, d, m, A⟩, S', d', m', B⟩

/-! ## From the verdict: where the first chain's block began and where it ended -/

/-- The context from which a block is run on a whole view: Blk.runNamed's own record, at dry :=
false, the view's rounds and its opened columns. -/
def startOf (s : Start) (v : Fmt.View) : Ctx :=
  { ch := { dry := false, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
            left := v.rounds, opened := v.opened },
    st := s.st, book := s.book, keepNotes := false }

/-- A run on a whole view that gives a value: the block has run from startOf s v, and has left a
context without a mark in which nothing is left over. -/
theorem runOn_start {α : Type} {b : Blk α} {s : Start} {v : Fmt.View} {a : α}
    (h : b.runOn s v = .ok a) :
    ∃ c', b (startOf s v) = .ok (a, c') ∧ c'.failed = none ∧
      (c'.ch.entries.isEmpty && c'.ch.settled) = true ∧
      (c'.ch.cur.isNone && c'.ch.opened.isEmpty && c'.ch.left.isEmpty) = true := by
  unfold Blk.runOn at h
  split at h
  · cases h
  · rename_i a' c' hr
    split at h
    · cases h
    · rename_i hf
      split at h
      · cases h
      · rename_i h1
        split at h
        · rename_i h2
          have ea : a' = a := Except.ok.inj h
          unfold Blk.runNamed at hr
          split at hr
          · exact ⟨c', by rw [← ea]; exact hr, hf, by simpa using h1, h2⟩
          · cases hr
        · cases h

/-- Accepted: the file was read as r; the first chain's block has run from the context that is made
of the first chain's start and r's view; it has left no mark and nothing over; and the file's tail
is not refused. -/
theorem accepted_start {c : Params.ProofChains} {table : Params.TableName} {copy : Nat}
    {request words : ByteArray} {reply : E} {links : Blk Proof.LinksResult} {file : ByteArray}
    (h : Proof.check c table copy request words reply links file = .accepted) :
    ∃ r fin cE,
      (Proof.readProof c table copy request words (Proof.firstBlock c.first links reply)
        file).fromStart = .ok r ∧
      Proof.firstBlock c.first links reply (startOf (Proof.firstStart c.first) r.first.view) =
        .ok (fin, cE) ∧
      cE.failed = none ∧ (cE.ch.entries.isEmpty && cE.ch.settled) = true ∧
      (cE.ch.cur.isNone && cE.ch.opened.isEmpty && cE.ch.left.isEmpty) = true ∧
      Proof.tailRefusal (Proof.tailPublic c table) fin r = none := by
  unfold Proof.check at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · rename_i hp
      rw [Proof.proofRefusal_eq] at hp
      split at hp
      · cases hp
      · rename_i real hj
        unfold Proof.judge at hj
        split at hj
        · rename_i a ha
          cases hj
          obtain ⟨cE, k1, k2, k3, k4⟩ := runOn_start ha
          exact ⟨r, _, cE, hr, k1, k2, k3, k4, hp⟩
        · cases hj

/-! ## The first chain's block, whole -/

/-- All calls of the first chain's block in the run that the verdict rests on. Z: the links.
request, words: the third and the fourth item of the first chain's statement, as `Proof.readProof`
takes them; here both are letters. At a model's call request is the value that
`Proof.requestItem` makes and words the request file's own bytes. Both are strings of bytes: a swap
is no error of types. -/
structure FileRan (Z : Array LinkH) (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (reply : E) (wsLay : WsLay) (file : ByteArray) (r : Proof.ProofRead)
    (fin : Proof.FirstEnd) (cE : Ctx) (check0 : ChainCheck) (ca : Ctx)
    (rN : ChainCheck × Proof.LinksResult) (cb cc : Ctx) (lin : LinFirst) (cd : Ctx) : Prop where
  read : (Proof.readProof c table copy request words
    (Proof.firstBlock c.first (runLinksH Z c.first wsLay) reply) file).fromStart = .ok r
  start : ChainCheck.start c.first.shape c.first.layout
    (startOf (Proof.firstStart c.first) r.first.view) = .ok (check0, ca)
  links : LinksChain Z c.first wsLay cE Z.toList 0 check0 {} ca rN cb
  finish : rN.1.finish cb = .ok ((), cc)
  replyIs : rN.2.reply = some reply
  rows : (rN.2.pending.length == c.first.pendingRows) = true
  member : memberFirstVerify c.first.lin rN.2.indexMasks rN.2.pending cc = .ok (lin, cd)
  sealing : Proof.firstEnd lin cd = .ok (fin, cE)
  tail : Proof.tailRefusal (Proof.tailPublic c table) fin r = none
  noMark : cE.failed = none
  planDone : (cE.ch.entries.isEmpty && cE.ch.settled) = true
  nothingLeft : (cE.ch.cur.isNone && cE.ch.opened.isEmpty && cE.ch.left.isEmpty) = true
  viewA : ca.ch.dry = false
  viewB : cb.ch.dry = false
  viewC : cc.ch.dry = false
  viewD : cd.ch.dry = false
  markA : ca.failed = none
  markB : cb.failed = none
  markC : cc.failed = none
  markD : cd.failed = none

/-- Accepted ⟹ every call of the first chain's block, from the context that is made of the file's
own view to the context on which the verdict rests. Hypothesis: every link's routine keeps. -/
theorem accepted_file (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file =
      .accepted) :
    ∃ r fin cE check0 ca rN cb cc lin cd,
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd := by
  obtain ⟨r, fin, cE, hread, hrun, clean, k3, k4, htail⟩ := accepted_start h
  clear h
  have hk' : ∀ Y ∈ Z.toList, KeepsM Y.run := fun Y hY => hk Y (Array.mem_toList_iff.1 hY)
  haveI := keepsM_runLinksFrom Z c.first wsLay Z.toList hk'
  haveI := keepsM_runLinksH Z c.first wsLay hk
  have hr : Runs (Proof.firstBlock c.first (runLinksH Z c.first wsLay) reply)
    (startOf (Proof.firstStart c.first) r.first.view) fin cE := hrun
  clear hrun
  have d : View (m := Blk) (startOf (Proof.firstStart c.first) r.first.view) := rfl
  unfold Proof.firstBlock at hr
  peel1 hr d
  unfold runLinksH at r1
  peel1_from r1 d b1 11
  obtain ⟨e1a, e1⟩ := runs_pure' r1
  subst e1a
  subst e1
  obtain ⟨g2, e2⟩ := runs_blkGet r2
  subst e2
  obtain ⟨t3, e3⟩ := Blk.yields_check _ _ _ _ d2 ((Blk.yields_iff _ _ _ _).2 r3) (b3 clean)
  subst e3
  obtain ⟨t4, e4⟩ := runs_must r4
  subst e4
  have er : a2 = reply := eq_of_beq t3
  subst er
  exact ⟨r, fin, cE, _, _, _, _, _, _, _,
    { read := hread, start := r11,
      links := runLinksFrom_chain Z c.first wsLay cE Z.toList hk' 0 _ _ _ _ _ d11 b12 r12,
      finish := r13, replyIs := g2, rows := t4, member := r5, sealing := hr, tail := htail,
      noMark := clean, planDone := k3, nothingLeft := k4,
      viewA := d11, viewB := d12, viewC := d13, viewD := d5,
      markA := b11 clean, markB := b12 clean, markC := b13 clean, markD := b5 clean }⟩

/-- Accepted ⟹ the head's link received the caller's reply, in its place: behind the chain over the
links before it, from the file's own start; its routine was started with the state chk, and
chk.plain[0]? is the caller's reply. Hypotheses: every link's routine keeps; the last link is of
kind 2. -/
theorem accepted_head (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file = .accepted)
    (Xs : List LinkH) (Xh : LinkH) (hZ : Z.toList = Xs ++ [Xh]) (h2 : Xh.kind = 2) :
    ∃ r fin cE check0 ca rN cb cc lin cd checkH outH cH chk o C' F' c1 c2,
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain Z c.first wsLay cE Xs 0 check0 {} ca (checkH, outH) cH ∧
      LinkStep Z c.first wsLay cE Xs.length Xh checkH outH cH rN cb chk o C' F' c1 c2 ∧
      chk.plain[0]? = some reply := by
  obtain ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, R⟩ := accepted_file Z hk h
  have hj : Z.toList[Xs.length]? = some Xh := by rw [hZ]; simp
  obtain ⟨checkH, outH, cH, r1, cm, chk, o, C', F', c1, c2, A, S, _, _, B⟩ :=
    LinksChain.split R.links Xs.length Xh hj
  have e1 : Z.toList.take Xs.length = Xs := by rw [hZ]; simp
  have e2 : Z.toList.drop (Xs.length + 1) = [] := by rw [hZ]; simp
  rw [e1] at A
  rw [e2] at B
  obtain ⟨b1, b2⟩ : rN = (r1.1, r1.2) ∧ cb = cm := B
  have b1' : rN = r1 := b1
  rw [Nat.zero_add] at S
  subst b1'
  subst b2
  have hk2 : (Xh.kind == 2) = true := by rw [h2]; rfl
  exact ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkH, outH, cH, chk, o, C', F', c1, c2, R,
    A, S, by rw [← (S.plainHead hk2).2]; exact R.replyIs⟩

#print axioms indexMasksH_same
#print axioms runLinkH_step
#print axioms runLinksFrom_chain
#print axioms LinksChain.split
#print axioms runOn_start
#print axioms accepted_start
#print axioms accepted_file
#print axioms accepted_head

end OnBytes.L5
