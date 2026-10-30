-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryCheckRec.lean: the entry's checker (`checkWithR`), and the decision
as a function of both tables' answers and seeds.

At the plain functions. The function sd that gives the seeds and the reader rd stay parameters:
nothing here is at an oracle.

-/
import OnBytes.Tie.EntryPlaceRec

set_option autoImplicit false

namespace OnBytes.Tie

/-! ## What `readWithR` and `checkWithR` return,
whatever rd and sd -/

/-- What `readWithR` returns, whatever rd and sd. -/
theorem readWithR_iff (rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead) (sd : Seeds)
    (p : Params.Link)
    (first : Params.TableName) (file : ByteArray) (r : Entry.EntryRead) :
    readWithR rd sd p first file = some r ↔
      ∃ P, entryPlaceR sd p first file = some P ∧ (rd P.spec file P.byte).run = some r.chain ∧
        r.chain.next = file.size ∧ r.further = P.further ∧ r.block = P.block := by
  unfold readWithR
  cases hP : entryPlaceR sd p first file with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, e, _⟩
      cases e
  | some P =>
    dsimp only
    cases hr : (rd P.spec file P.byte).run with
    | none =>
      constructor
      · intro h
        cases h
      · rintro ⟨P', e, e1, _⟩
        cases e
        rw [hr] at e1
        cases e1
    | some c =>
      dsimp only
      by_cases hn : c.next = file.size
      · rw [if_neg (by simp [hn])]
        constructor
        · intro h
          cases h
          exact ⟨P, rfl, hr, hn, rfl, rfl⟩
        · rintro ⟨P', e, e1, _, e3, e4⟩
          cases e
          rw [hr] at e1
          cases r with
          | mk f b ch =>
            dsimp only at e1 e3 e4
            cases e1
            subst e3 e4
            rfl
      · rw [if_pos (by simpa using hn)]
        constructor
        · intro h
          cases h
        · rintro ⟨P', e, e1, e2, _, _⟩
          cases e
          rw [hr] at e1
          cases e1
          exact absurd e2 hn

/-- What `checkWithR` returns, whatever rd and sd. -/
theorem checkWithR_iff (rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead) (sd : Seeds)
    (params : ByteArray) (first further : Params.TableName) (file : ByteArray) :
    checkWithR rd sd params first file = some further ↔
      ∃ (q : Params.Link) (r : Entry.EntryRead),
        Params.Link.read params = some q ∧ readWithR rd sd q first file = some r ∧
        r.further = further ∧ r.block.decides (Entry.start q) r.chain.view = true := by
  unfold checkWithR
  cases hq : Params.Link.read params with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, _, e, _⟩
      cases e
  | some q =>
    dsimp only
    cases hr : readWithR rd sd q first file with
    | none =>
      constructor
      · intro h
        cases h
      · rintro ⟨q', r, e, e1, _⟩
        cases e
        rw [hr] at e1
        cases e1
    | some r =>
      dsimp only
      cases hd : r.block.decides (Entry.start q) r.chain.view with
      | true =>
        rw [if_pos rfl]
        constructor
        · intro h
          exact ⟨q, r, rfl, hr, Option.some.inj h, hd⟩
        · rintro ⟨q', r', e, e1, e2, _⟩
          cases e
          rw [hr] at e1
          cases e1
          rw [e2]
      | false =>
        rw [if_neg (by decide)]
        constructor
        · intro h
          cases h
        · rintro ⟨q', r', e, e1, _, e3⟩
          cases e
          rw [hr] at e1
          cases e1
          rw [hd] at e3
          cases e3

/-! ## The decision as a function of the two keys -/

/-- **The decision of an entry's check, as a function of the parameters and of the two tables'
keys.** A key holds its table's item number, THE RECORD's ANSWERS AND THE SEEDS (`TableKey`).
With both keys `Params.plainKey` this is `(Params.entryBlock p).decides
(Entry.start p)`. -/
def entryDecR (p : Params.Link) (k0 k1 : TableKey) : Fmt.View → Bool :=
  (linkVerify p.link k0 k1).decides (Entry.start p)

/-- **A YES OF `checkWithR`, SPELLED OUT; WHATEVER rd AND sd; NO OTHER
HYPOTHESIS.** The parameter bytes are read as q; `keyWith sd` gives a key for each of the two
tables; the dry run at keys of zeros states rounds rs; rd reads a chain c, which ends the file,
UNDER THE DESCRIPTION MADE OF q, rs AND THE STATEMENT ON THE TWO TABLES (no seed is in it; the
answers through the statement alone); AND THE DECISION AT THE TWO KEYS IS TRUE ON c's VIEW. ONE WAY.
j is not named; that further stands in the file is not said; the head's test and the two tests on
the parameters are dropped. -/
theorem checkWithR_spelled {rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead} {sd : Seeds}
    {params : ByteArray} {first further : Params.TableName} {file : ByteArray}
    (h : checkWithR rd sd params first file = some further) :
    ∃ (q : Params.Link) (k0 k1 : TableKey) (rs : Params.Rounds) (c : ChainRead) (j : Nat),
      Params.Link.read params = some q ∧
      keyWith sd q.given.plan.field q.given.cfg q.link.table first 0 = some k0 ∧
      keyWith sd q.given.plan.field q.given.cfg q.link.table further 1 = some k1 ∧
      Params.entryRoundsAny q = some rs ∧
      (rd (Params.entrySpecOf q rs (Params.Link.statement first further)) file j).run = some c ∧
      c.next = file.size ∧ entryDecR q k0 k1 c.view = true ∧ further.root.size = 32 := by
  obtain ⟨q, r, hq, hr, e1, hd⟩ := (checkWithR_iff rd sd params first further file).1 h
  obtain ⟨P, hP, h1, h2, h3, h4⟩ := (readWithR_iff rd sd q first file r).1 hr
  obtain ⟨⟨k0, k1, a0, a1, a2⟩, ⟨rs, b1, b2⟩, hs⟩ := entryPlaceR_spec_any hP
  have ef : P.further = further := h3.symm.trans e1
  rw [ef] at a1 b2 hs
  rw [b2] at h1
  rw [h4, a2] at hd
  exact ⟨q, k0, k1, rs, r.chain, P.byte, hq, a0, a1, b1, h1, h2, hd, hs⟩

/-- **At the program's own reader and seeds: a yes of `Entry.check`, spelled out so; no other
hypothesis.** -/
theorem entry_check_spelled {params : ByteArray} {first further : Params.TableName}
    {file : ByteArray} (h : Entry.check params first file = .ok further) :
    ∃ (q : Params.Link) (k0 k1 : TableKey) (rs : Params.Rounds) (c : ChainRead) (j : Nat),
      Params.Link.read params = some q ∧
      tableKey q.given.plan.field q.given.cfg q.link.table first 0 = some k0 ∧
      tableKey q.given.plan.field q.given.cfg q.link.table further 1 = some k1 ∧
      Params.entryRoundsAny q = some rs ∧
      (readIn (Params.entrySpecOf q rs (Params.Link.statement first further)) file j).run =
        some c ∧
      c.next = file.size ∧ entryDecR q k0 k1 c.view = true ∧ further.root.size = 32 := by
  have h' : checkWithR readIn recordSeeds params first file = some further := by
    rw [checkWithR_readIn, h]
    rfl
  exact checkWithR_spelled h'

end OnBytes.Tie

#print axioms OnBytes.Tie.readWithR_iff
#print axioms OnBytes.Tie.checkWithR_iff
#print axioms OnBytes.Tie.checkWithR_spelled
#print axioms OnBytes.Tie.entry_check_spelled
