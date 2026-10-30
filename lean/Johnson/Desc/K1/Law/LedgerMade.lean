-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LedgerMade.lean: WHAT A SENDING OF KIND K1 LAYS IS THE FRESH LEDGER.
Definitions, two statements as definitions of propositions, and their proofs.
IN PLAIN WORDS. Behind a yes of the sending's decision, and behind a yes of the first segment's
opening (`firstSegmentOpening q gp`, on two rounds), every message of the sending that has a mask row and an
answer stands in the statement with the ledger that the admitting of a sample lays: next 0, left the
count of free entries, rows and row bits the shape's, not closed.
Main names:
  `LaysFresh st o s`: message o is there, has the shape s, and its ledger is THE RECORD, field by
    field: { next := 0, left := Send.freeMaskEntries …, rows := max s.maskRows 1,
    logRows := ceilLog2 s.maskRows, closed := false }, the count at the statement's own codes.
  `LaysFresh.ledgerAt`, `LaysFresh.open`: so it is the ledger of 0 takes (`K13.Law.LedgerAt`,
    Johnson/Desc/K13/Law/LedgerWithin.lean), and it is not closed.
  `SameLedgers st st'`: the codes stay, and every message that is there stays with its shape and its
    ledger. `sameLedgers_newGroup`, `_join`, `_joinAll`, `_joinOwn`: a new group and the joinings
    keep it.
  `laysFresh_send`: behind the sending's decision: by `decideSend_iff` (Writes3.lean) and
    `outs_spec` (Joined2.lean), CALLED.
  `laysFresh_firstOwn`, `laysFresh_firstAtS`: behind the opening's decision, and the block's.
  `LedgerMadeAtSend`, `LedgerMadeAtFirst`: THE TWO STATEMENTS; `ledgerMadeAtSend`,
    `ledgerMadeAtFirst`: **they hold.**
BOTH PREMISES ARE WANTED: a message with mask rows and no answer is not sampled: no sample is
admitted: it has no ledger.
What is not claimed. That any later block leaves the ledger. That the message's number is the
plan's. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.LedgerWithin
import Johnson.Desc.K1.Law.Joined2
import Johnson.Desc.K1.Law.GroupAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)

variable {L Cl : Type}

/-- **Message o stands with the shape s and the fresh ledger**, field by field. -/
def LaysFresh (st : Statement) (o : Nat) (s : OracleShape) : Prop :=
  ∃ x : OnBytes.Oracle, st.oracles[o]? = some x ∧ x.shape = s ∧ x.ledger = some
    { next := 0
      left := Send.freeMaskEntries s.maskRows (st.codes.mask.getD s.maskCode default).ell s.answers
      rows := max s.maskRows 1, logRows := ceilLog2 s.maskRows, closed := false }

/-- It is the ledger of 0 takes. -/
theorem LaysFresh.ledgerAt {st : Statement} {o : Nat} {s : OracleShape} (h : LaysFresh st o s)
    (hm : 0 < s.maskRows) (ha : 1 ≤ s.answers) : K13.Law.LedgerAt st o 0 := by
  obtain ⟨x, hx, rfl, hl⟩ := h
  exact K13.Law.ledgerAt_made hx hm ha hl

/-- It is not closed. -/
theorem LaysFresh.open {st : Statement} {o : Nat} {s : OracleShape} (h : LaysFresh st o s) :
    ∃ (x : OnBytes.Oracle) (l : Ledger), st.oracles[o]? = some x ∧ x.ledger = some l ∧
      l.closed = false := by
  obtain ⟨x, hx, _, hl⟩ := h
  exact ⟨x, _, hx, hl, rfl⟩

/-- The codes stay, and every message that is there stays with its shape and its ledger. -/
structure SameLedgers (st st' : Statement) : Prop where
  codes : st'.codes = st.codes
  msg : ∀ (o : Nat) (x : OnBytes.Oracle), st.oracles[o]? = some x →
    ∃ x' : OnBytes.Oracle, st'.oracles[o]? = some x' ∧ x'.shape = x.shape ∧ x'.ledger = x.ledger

theorem SameLedgers.refl (st : Statement) : SameLedgers st st :=
  ⟨rfl, fun _ x hx => ⟨x, hx, rfl, rfl⟩⟩

theorem SameLedgers.trans {a b c : Statement} (h : SameLedgers a b) (k : SameLedgers b c) :
    SameLedgers a c := by
  refine ⟨k.codes.trans h.codes, fun o x hx => ?_⟩
  obtain ⟨y, hy, e1, e2⟩ := h.msg o x hx
  obtain ⟨z, hz, f1, f2⟩ := k.msg o y hy
  exact ⟨z, hz, f1.trans e1, f2.trans e2⟩

theorem LaysFresh.stays {st st' : Statement} {o : Nat} {s : OracleShape} (h : LaysFresh st o s)
    (k : SameLedgers st st') : LaysFresh st' o s := by
  obtain ⟨x, hx, hs, hl⟩ := h
  obtain ⟨x', hx', e1, e2⟩ := k.msg o x hx
  refine ⟨x', hx', e1.trans hs, ?_⟩
  rw [e2, hl, k.codes]

/-- A new group. -/
theorem sameLedgers_newGroup (d d' : DState L) (code maskCode n : Nat)
    (h : Ground.newGroupP d code maskCode = some (n, d')) :
    SameLedgers d.st d'.st ∧ d'.st.oracles.size = d.st.oracles.size := by
  unfold Ground.newGroupP at h
  split at h
  · obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨⟨rfl, fun _ x hx => ⟨x, hx, rfl, rfl⟩⟩, rfl⟩
  · cases h

/-- One message joins. -/
theorem sameLedgers_join (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') : SameLedgers d.st d'.st := by
  obtain ⟨G, _, _, e⟩ := Later.joinP_inv d d' g o kept h
  rw [e]
  refine ⟨rfl, fun j x hx => ?_⟩
  show ∃ x' : OnBytes.Oracle, (d.st.oracles.modify o _)[j]? = some x' ∧ _
  rw [Array.getElem?_modify]
  by_cases hj : o = j
  · rw [if_pos hj, hx]
    exact ⟨_, rfl, rfl, rfl⟩
  · rw [if_neg hj]
    exact ⟨x, hx, rfl, rfl⟩

/-- A list of messages joins. -/
theorem sameLedgers_joinAll (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat))
    (d d' : DState L), joinAll groundG p g l d = some d' → SameLedgers d.st d'.st
  | [], d, d', h => by
    obtain rfl := Option.some.inj h
    exact SameLedgers.refl _
  | x :: l, d, d', h => by
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (sameLedgers_join d e g x.2 _ h1).trans (sameLedgers_joinAll p g l e d' h2)

/-- A moment's own messages join the frame's group. -/
theorem sameLedgers_joinOwn (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y) :
    SameLedgers d.st y.2.st := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    exact sameLedgers_joinAll p f.group _ d d' h1
  · cases h

/-- **Behind the sending's decision.** -/
theorem laysFresh_send (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (i : Nat)
    (hi : i < P.sent.size) (hm : 0 < (P.sent.getD i default).shape.maskRows)
    (ha : 1 ≤ (P.sent.getD i default).shape.answers) :
    LaysFresh d'.st (d.st.oracles.size + i) (P.sent.getD i default).shape := by
  obtain ⟨⟨_, hc, _, _, hfit⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  have hlen : i < (shapesOf P).length := by
    unfold shapesOf
    rw [List.length_map, Array.length_toList]
    exact hi
  obtain ⟨ys', _, hk⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P) d.st.oracles.size
    (answersIn r₂) hfit i hlen
  have hs : (shapesOf P)[i] = (P.sent.getD i default).shape := by
    unfold shapesOf
    rw [List.getElem_map, Array.getElem_toList, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi]
    rfl
  rw [hs] at hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + i]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + i) (P.sent.getD i default).shape
        ys') := by
    show ((d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray)[d.st.oracles.size + i]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by rw [Array.length_toList]; omega),
      Array.length_toList, Nat.add_sub_cancel_left]
    exact hk
  have hcodes : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes := hc
  refine ⟨_, hx, ?_, ?_⟩
  · unfold wr
    rw [if_neg (by omega)]
  · unfold wr
    rw [if_neg (by omega), hcodes]
    show Slice.freshLedger P.codes (P.sent.getD i default).shape = _
    unfold Slice.freshLedger
    rw [if_pos hm]

/-- **Behind the opening's decision.** -/
theorem laysFresh_firstOwn (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) (i : Nat)
    (hi : i < P.sent.size) (hm : 0 < (P.sent.getD i default).shape.maskRows)
    (ha : 1 ≤ (P.sent.getD i default).shape.answers) :
    LaysFresh d'.st (d.st.oracles.size + i) (P.sent.getD i default).shape := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨mask, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, hfin⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj hfin)
  have hn := (sameLedgers_newGroup _ _ _ _ _ ((named_ok _ _ _).1 h1)).2
  have hn' : d₁.st.oracles.size = d.st.oracles.size := hn
  rw [← hn']
  exact (laysFresh_send P owed d₁ d₂ r₁ r₂ ids h2 i hi hm ha).stays
    (sameLedgers_joinOwn _ _ _ _ _ _ ((named_ok _ _ _).1 h3))

/-- **Behind the first segment's opening, at the record.** -/
theorem laysFresh_firstAtS (q : Params.First) (gp : GPar) (s t : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok t) (i : Nat)
    (hi : i < (firstPar q gp).sent.size)
    (hm : 0 < ((firstPar q gp).sent.getD i default).shape.maskRows)
    (ha : 1 ≤ ((firstPar q gp).sent.getD i default).shape.answers) :
    LaysFresh t.st (s.st.oracles.size + i) ((firstPar q gp).sent.getD i default).shape := by
  obtain ⟨c, d', h1, e, _⟩ := firstAtS_ok q gp s t _ gs h
  rw [e]
  exact laysFresh_firstOwn _ _ _ _ (stateOf s ()) d' r₁ r₂ h1 i hi hm ha

/-- **THE STATEMENT, at the sending's decision**: the ledger of 0 takes, not closed. -/
def LedgerMadeAtSend : Prop :=
  ∀ {L : Type} (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat),
    decideSend P owed d [r₁, r₂] = .ok (ids, d') → ∀ i, i < P.sent.size →
    0 < (P.sent.getD i default).shape.maskRows → 1 ≤ (P.sent.getD i default).shape.answers →
    K13.Law.LedgerAt d'.st (d.st.oracles.size + i) 0 ∧
      ∃ (x : OnBytes.Oracle) (l : Ledger), d'.st.oracles[d.st.oracles.size + i]? = some x ∧
        x.ledger = some l ∧ l.closed = false

/-- **THE STATEMENT, at the first segment's opening.** -/
def LedgerMadeAtFirst : Prop :=
  ∀ {Cl : Type} (q : Params.First) (gp : GPar) (s t : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok t →
    ∀ i, i < (firstPar q gp).sent.size →
    0 < ((firstPar q gp).sent.getD i default).shape.maskRows →
    1 ≤ ((firstPar q gp).sent.getD i default).shape.answers →
    K13.Law.LedgerAt t.st (s.st.oracles.size + i) 0 ∧
      ∃ (x : OnBytes.Oracle) (l : Ledger), t.st.oracles[s.st.oracles.size + i]? = some x ∧
        x.ledger = some l ∧ l.closed = false

theorem ledgerMadeAtSend : LedgerMadeAtSend := by
  intro L P owed d d' r₁ r₂ ids h i hi hm ha
  have k := laysFresh_send P owed d d' r₁ r₂ ids h i hi hm ha
  exact ⟨k.ledgerAt hm ha, k.open⟩

theorem ledgerMadeAtFirst : LedgerMadeAtFirst := by
  intro Cl q gp s t r₁ r₂ gs h i hi hm ha
  have k := laysFresh_firstAtS q gp s t r₁ r₂ gs h i hi hm ha
  exact ⟨k.ledgerAt hm ha, k.open⟩

end VerifiableInference.Desc.K1
