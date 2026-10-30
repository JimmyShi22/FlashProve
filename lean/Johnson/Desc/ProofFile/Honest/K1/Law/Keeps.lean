-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/Keeps.lean: what a step of the kind K1 (a sending of oracle
messages with its OOD samples) leaves of the verifier's state as it was, at the first chain's state
(S, Johnson/Desc/First/State.lean). Six definitions of propositions, meant as K1's clauses of the
letter keeps of a thread of the honest side's sentences; three theorems: a return of the kind's own
sub-protocol's decision gives its clause; and four tools. It imports files of the sealed library
alone.

The kind has three sorts of member of its own at that state, of unlike decisions
(Johnson/Desc/K1/AtS.lean, Johnson/Desc/K1/First.lean): so one common part and three clauses. The
member with a step without a round joined behind a commitment:
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsReads.lean.

  K1St T T', groundKeeps_k1St: five relations of the library together, each of which every plain
    function of the ground keeps: the statement has only grown (Grows, Johnson/Desc/Grows.lean); no
    group bears a new mark (NoNewMark, Johnson/Desc/Marks.lean); a linked statement stays linked,
    and a group that bears the mark keeps its mark, its members and its open rows (KeepsLinked,
    Frozen, Johnson/Desc/Ground/Linked.lean); every sampled older message stands behind with its
    shape, its mark and its sample rows (K1.SmpStay, Johnson/Desc/K1/Law/SmpStay.lean).
  K1Rest s s': what every member leaves. WHICH CLAUSE SERVES WHAT: the mark, the reply with the pile
    of rows (out) and the request are as they were: a count of rows on the pile, a flag on the reply
    · no count of rows waits behind · K1St · nothing is taken from a ledger of mask entries: every
    message that is there keeps its shape and its ledger's four numbers (K13.Law.LedStay,
    Johnson/Desc/K13/Law/LedgersStay.lean): a count of entries taken · and its ledger whole, shut or
    not (K1.SameLedgers, Johnson/Desc/K1/Law/LedgerMade.lean): "not shut" · the count of roots has
    not fallen · every older place of the book of trees is as it was (PlacesStay,
    Johnson/IMR/BookFitsSeat.lean).
  K1Out s s': no group gains a message that is there: a message that stands in the statement in
    front and is a member of no group (K1.OutOf, Johnson/Desc/K1/Law/GroupsAtLater.lean) is a member
    of none behind: "the index masks' message is a member of no group". IT STANDS IN K1SendKeeps AND
    IN K1CommitKeeps, NOT IN K1Rest: of the opening it is not said.
  K1SendKeeps, k1_send_keeps: the sending behind the links (K1.sendAtS): beside K1Rest and K1Out:
    the state of the calls and the groups are as they were; every older oracle message is as it was,
    field for field; the chain stands at the members' places, and of what stands there the new
    messages' numbers alone have turned.
  K1CommitKeeps, k1_commit_keeps: a segment's later moment (K1.commitAtS): beside K1Rest: the state
    of the calls is as it was; a link is open in front; of what stands at the chain's place the
    link's context and the sub-proof's ledger alone have turned: so every flag of that place stays;
    the ledger behind has the slots of the one in front with what lies under them (PscRun.SlotsSame,
    OnBytes/Tie/Pv/Psc/PscLater.lean) and every array's numbers of rows and columns (K1.ShapesSame,
    Johnson/Desc/K1/KeepsShapes.lean).
  K1FirstKeeps, k1_first_keeps: the first segment's opening (K1.firstSegmentOpening): beside K1Rest: the chain
    stands between two links in front and behind.
  coreRecv_at, put_rest, firstAtS_sameLedgers: tools.

Not shown here. ONE WAY, FROM A RETURN. Nothing on the member as a chain seats it (guarded,
retyped). The clauses have no letter for the member's parameter: how many messages, roots and places
are new is not said. Of the book's array of trees nothing is said. AT A COMMITMENT AND AT THE
OPENING: of an older group that bears no mark the open rows, and of an older message the pad and
whether it is spent as a mask, are not said to stay (at the sending behind the links they are: the
groups and the older messages are as they were). Of the link's context behind a commitment, and of
the state of the calls behind the opening, nothing is said. The mark is neither read nor written:
that it is none is not said. That a clause is strong enough for an item that reads the state is that
item's filler's to say. The six are definitions: nothing is claimed of them. Nothing on soundness,
on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.KeepsAtS
import Johnson.Desc.K1.KeepsAtSCore
import Johnson.Desc.K1.KeepsSlots
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.Ground.LinkedKeeps
import Johnson.IMR.BookFitsSeat
import Johnson.IMR.WalkGivesAt
import Johnson.Desc.K1.Law.SameLedgersAtLater
import Johnson.Desc.K13.Law.LedgersStay
import Johnson.Desc.K1.Law.GroupsAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (K1.Par K1.sendAtS K1.commitAtS K1.firstSegmentOpening K1.SmpStay Grows NoNewMark
  KeepsLinked Frozen)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (Core CoreRecv GroundKeeps groundKeeps_four)
open VerifiableInference.Desc.K1 (groundKeeps_smpStay SameLedgers OutOf)
open VerifiableInference.Desc.K13.Law (LedStay)
open Meaning.K2 (PlacesStay ps_recv ru_recv coreRecv_places coreRecv_rootsUp)

/-- What every member of the kind leaves of the statement: five relations of the library, each of
which every plain function of the ground keeps. A definition. -/
def K1St (T T' : Statement) : Prop :=
  ((Grows T T' ∧ NoNewMark T T') ∧ (KeepsLinked T T' ∧ Frozen T T')) ∧ K1.SmpStay T T'

/-- Every plain function of the ground keeps it. -/
theorem groundKeeps_k1St : GroundKeeps K1St := groundKeeps_four.and groundKeeps_smpStay

/-- **What every member of the kind leaves of the state as it was.** It is a definition: a premise's
form. Nothing is claimed of it. -/
def K1Rest (s s' : S) : Prop :=
  s'.failed = s.failed ∧ s'.out = s.out ∧ s'.req = s.req ∧ s'.rowsOwed = none ∧
    K1St s.st s'.st ∧ LedStay s.st s'.st ∧ SameLedgers s.st s'.st ∧ s.roots ≤ s'.roots ∧
    PlacesStay s.book s'.book

/-- **No group gains a message that is there**: a message that stands in the statement in front and
is a member of no group is a member of none behind. A definition. -/
def K1Out (s s' : S) : Prop := ∀ i, i < s.st.oracles.size → OutOf i s.st → OutOf i s'.st

/-- **The sending behind the links.** A definition. -/
def K1SendKeeps (s s' : S) : Prop :=
  K1Rest s s' ∧ K1Out s s' ∧ s'.check = s.check ∧ s'.st.groups = s.st.groups ∧
    (∀ o, o < s.st.oracles.size → s'.st.oracles[o]? = s.st.oracles[o]?) ∧
    ∃ a ids, s.here = .mem a ∧ s'.here = .mem { a with ids := ids }

/-- **A segment's later moment.** A definition. -/
def K1CommitKeeps (s s' : S) : Prop :=
  K1Rest s s' ∧ K1Out s s' ∧ s'.check = s.check ∧
    ∃ L F tl L' F', s.link? = some L ∧ s.fork? = some F ∧ s.tl? = some tl ∧
      s'.here = ((s.putLink L').putFork F').here ∧ PscRun.SlotsSame F F' ∧
      VerifiableInference.Desc.K1.ShapesSame F F'

/-- **The first segment's opening.** A definition. -/
def K1FirstKeeps (s s' : S) : Prop :=
  K1Rest s s' ∧ s.here = .between ∧ s'.here = .between

/-- "The roots do not fall, and every older place stays", at a chain that receives at any number of
its first tree. -/
theorem coreRecv_at (ft : Nat) :
    CoreRecv ft fun a b : Core => a.roots ≤ b.roots ∧ PlacesStay a.book b.book :=
  CoreRecv.and
    { coreRecv_rootsUp.toCoreStill with recv := fun d d' sent ids h => ru_recv ft d d' sent ids h }
    { coreRecv_places.toCoreStill with recv := fun d d' sent ids h => ps_recv ft d d' sent ids h }

/-- The two puts of an open link write the chain's place alone. -/
theorem put_rest (t : S) (L : LinkCtx) (F : Fork) :
    ((t.putLink L).putFork F).failed = t.failed ∧ ((t.putLink L).putFork F).out = t.out ∧
      ((t.putLink L).putFork F).req = t.req ∧ ((t.putLink L).putFork F).rowsOwed = t.rowsOwed ∧
      ((t.putLink L).putFork F).check = t.check := by
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := t
  cases here with
  | between => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | lay a => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | att a => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | head a =>
    by_cases ho : a.opened = true
    · simp [S.putLink, S.putFork, ho]
    · simp [S.putLink, S.putFork, ho]
  | fin a => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | mem a => exact ⟨rfl, rfl, rfl, rfl, rfl⟩

variable {Cl : Type}

/-- The first segment's opening leaves every message that is there with its shape and its ledger: a
new group, the sending, the joinings. -/
theorem firstAtS_sameLedgers {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') : SameLedgers s.st s'.st := by
  unfold K1.firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨g, d₁, ids, d₂, h3, h4, f₁, own, mine, f₂, h5⟩ :=
    VerifiableInference.Desc.K1.firstOwn_ok _ _ _ _ _ _ _ h2
  show SameLedgers s.st d'.st
  exact ((VerifiableInference.Desc.K1.sameLedgers_newGroup _ _ _ _ _ h3).1.trans
    (VerifiableInference.Desc.K1.sameLedgers_kept
      (VerifiableInference.Desc.K1.decideSend_kept _ _ d₁ d₂ rs ids h4))).trans
    (VerifiableInference.Desc.K1.sameLedgers_joinOwn _ _ _ _ _ _ h5)

/-- **A return of the sending behind the links leaves that.** -/
theorem k1_send_keeps {P : K1.Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K1.sendAtS (Cl := Cl) P).decide s rs gs = .ok s') :
    K1SendKeeps s s' := by
  have g := VerifiableInference.Desc.K1.Rel.sendAtS_keeps (Cl := Cl) groundKeeps_k1St P s rs gs s' h
  have c := VerifiableInference.Desc.K1.RelCore.sendAtS_keeps (Cl := Cl) P (coreRecv_at _) s rs gs
    s' h
  have l := VerifiableInference.Desc.K13.Law.sendAtS_ledStay (Cl := Cl) P s rs gs s' h
  have w := VerifiableInference.Desc.K1.sendAtS_sameLedgers (Cl := Cl) P s rs gs s' h
  have k := VerifiableInference.Desc.K1.sendAtS_kept (Cl := Cl) P s s' rs gs h
  simp only [K1.sendAtS] at h
  split at h
  · rename_i a ha
    split at h
    · obtain ⟨y, -, rfl⟩ := VerifiableInference.Desc.Keeps.emap_ok h
      exact ⟨⟨rfl, rfl, rfl, rfl, g, l, w, c.1, c.2⟩, fun i _ hO G hG => hO G (k.2.1 ▸ hG), rfl,
        k.2.1, k.2.2, a, _, ha, rfl⟩
    · cases h
  · cases h

/-- **A return of a segment's later moment leaves that.** -/
theorem k1_commit_keeps {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s') :
    K1CommitKeeps s s' := by
  have g := VerifiableInference.Desc.K1.Rel.commitAtS_keeps (Cl := Cl) groundKeeps_k1St P link
    moment arrays s rs gs s' h
  have c := VerifiableInference.Desc.K1.RelCore.commitAtS_keeps (Cl := Cl) P (coreRecv_at _) link
    moment arrays s rs gs s' h
  have l := VerifiableInference.Desc.K13.Law.commitAtS_ledStay (Cl := Cl) P link moment arrays s rs
    gs s' h
  have w := VerifiableInference.Desc.K1.commitAtS_sameLedgers (Cl := Cl) P link moment arrays s rs
    gs s' h
  have o : K1Out s s' := fun i hi hO =>
    VerifiableInference.Desc.K1.commitAtS_outOf (Cl := Cl) P link moment arrays s s' rs gs h hi hO
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    obtain ⟨y, h1, rfl⟩ := VerifiableInference.Desc.Keeps.emap_ok h
    have r := put_rest (VerifiableInference.Desc.K1.laid s y.held.w) y.held.L y.held.F
    refine ⟨⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, g, l, w, c.1, c.2⟩, o, r.2.2.2.2, L, F, tl, y.held.L,
      y.held.F, hL, hF, ht, ?_, VerifiableInference.Desc.K1.commitOwn_slots h1,
      VerifiableInference.Desc.K1.commitOwn_shapes h1⟩
    obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
    cases here with
    | head a =>
      by_cases ho : a.opened = true
      · simp [S.putLink, S.putFork, VerifiableInference.Desc.K1.laid, ho]
      · simp [S.putLink, S.putFork, VerifiableInference.Desc.K1.laid, ho]
    | _ => rfl
  · cases h

/-- **A return of the first segment's opening leaves that.** -/
theorem k1_first_keeps {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') : K1FirstKeeps s s' := by
  have g := VerifiableInference.Desc.K1.Rel.firstAtS_keeps (Cl := Cl) groundKeeps_k1St q gp s rs gs
    s' h
  have c := VerifiableInference.Desc.K1.RelCore.firstAtS_keeps (Cl := Cl) q gp (coreRecv_at _) s rs
    gs s' h
  have l := VerifiableInference.Desc.K13.Law.firstAtS_ledStay (Cl := Cl) q gp s rs gs s' h
  have w := firstAtS_sameLedgers h
  simp only [K1.firstSegmentOpening] at h
  obtain ⟨_, hb, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  obtain ⟨⟨ck, d⟩, h1, h⟩ := (VerifiableInference.Desc.K1.bind_ok _ _ _).1 h
  cases h
  have hw : s.here = .between := by
    have e : s.atBetween = true := by
      cases hA : s.atBetween with
      | true => rfl
      | false =>
        rw [hA] at hb
        cases hb
    unfold S.atBetween at e
    cases hh : s.here <;> simp [hh] at e ⊢
  exact ⟨⟨rfl, rfl, rfl, rfl, g, l, w, c.1, c.2⟩, hw, hw⟩

end ProofFile.Honest.K1
