-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Keeps.lean: WHAT A YES AT A PLACE OF THE CODE SWITCH LEAVES OF THE VERIFIER's
STATE AS IT WAS, AND HOW WHAT IT TURNS MAY HAVE TURNED: a sentence on the state in front (s) and the
state behind (s'), for each of the kind's three sorts of place; and, for each, the lemma that a yes
gives it. Definitions; statements with their proofs, over the library's own laws on these texts
(Johnson/Top/H0/Tw/K2C/Laws.lean, Closed.lean, KeepsWhole.lean, SendsOn.lean, Reply.lean, Asks.lean,
FinFront.lean; Johnson/Desc/K1/Law/SmpStay.lean).

OF THE KIND's OWN DECISION (`decideWith sendByL8`):
  `K2Common`        at every sort: the mark, the result so far and the request's words are as they
                    were · no count of rows is owed behind · THE STATEMENT HAS ONLY GROWN (`Grows`,
                    Johnson/Desc/Grows.lean: the codes are as they were; every group and every
                    oracle message that was there is there, grown) · EVERY MESSAGE THAT IS SAMPLED
                    IN FRONT STANDS BEHIND AT ITS NUMBER, WITH ITS SHAPE, ITS MARK AND ITS SAMPLE
                    ROWS (`SmpStay`, Johnson/Desc/K1/Law/SmpStay.lean)
  `K2Common.firstRow`   so: at the number of a message that is sampled in front, the first stored
                    sample row is behind what it was in front
  `K2KeepsLink`     at a segment's first place: and the chain stands where it stood. The state of
                    the calls (`check`) turns
  `K2KeepsHead`     at the head's place: and the state of the calls is as it was; of the head's own
                    part two fields alone turn: the kept copies' numbers and the others'
  `K2KeepsFinish`   behind the last segment: and the state of the calls is as it was; of the
                    finish's own part one field alone turns: what the switch returned
  `k2Common_of_yes`, `k2KeepsLink_of_yes`, `k2KeepsHead_of_yes`, `k2KeepsFinish_of_yes`   a yes
                    gives the sentence
OF THE WHOLE PLACE's BLOCK, where quiet steps stand around the kind's own
(Johnson/Desc/ProofFile/Lot/K2.lean). At a segment's first place the block is the kind's own, and
`K2KeepsLink` is the place's sentence.
  `K2PlaceHead`     the head's place (the switch, then the opening of the head's segment):
                    `K2Common`, and the chain stands in the head's segment in front and behind;
                    BEHIND, THE SEGMENT COUNTS AS OPENED, AND EACH OF THE FOUR ARRAYS OF ITS LEDGER
                    OF SLOTS HAS AS MANY ENTRIES AS THE LEDGER STATES SLOTS (that the ledger is the
                    empty one is `headOpen_rest`'s to say, not this sentence's). THE STATE OF THE
                    CALLS TURNS, and more of the head's own part than two fields
  `K2PlaceFinish`   the place behind the last segment (a quiet step, the switch, a quiet step):
                    `K2Common`, the state of the calls is as it was, the chain stands between the
                    segments in front and in the finish behind
  `K2PlaceHead.laid`   so: behind the head's place the segment counts as opened, and its ledger is
                    `Sized` in the library's sense (OnBytes/Tie/Pv/Psc/PscFork.lean)
  `headOpen_rest`, `K2Common.trans`   tools
  `k2PlaceHead_of_yes`, `k2PlaceFinish_of_yes`   a yes of the place's block gives the sentence

NEAR, NOT CALLED: the library's `Left` with `left_of_yes` (Johnson/Top/H0/K2Ties/Left.lean) and
`left_headOpen`, `left_finishFront`, `left_finishBehind` (Johnson/Top/H0/K2Ties/Doors.lean): what an
accept of the switch, and each quiet step around it, leaves of the state, as far as the claims that
stay open across the switch read it. FIVE OF `K2Common`'s SIX CLAUSES ARE FIELDS OF `Left`: the
mark, the result so far, the request's words, `Grows`, `SmpStay`. `Left` has besides: the pending
claims on the committed table, every earlier message's place, every earlier tree's number.
`K2Common` has besides: no count of rows is owed behind. The sentences here on where the chain
stands, on the state of the calls and on the head's and the finish's own parts have no like there.

Limits. NOTHING ON THE SAMPLE ROWS OF A MESSAGE THAT IS NOT SAMPLED IN FRONT, or that is not there
in front: the switch's own new messages get theirs in this very step. NOTHING ON THE BOOK OF TREES
AND THE COUNT OF ROOTS, which turn; nothing on how the state of the calls turns where it turns. A
seat may lay more around a place's block (a guard on the mark, on the reply): not walked here. A
frame fact: it says what the texts do not write, not that a yes means a test. Nothing on any
property.
-/
import Johnson.Top.H0.Tw.K2C.KeepsWhole
import Johnson.Top.H0.Tw.K2C.Closed
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Desc.K1.Law.SmpStay
import OnBytes.Tie.Pv.Psc.PscFork

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc (Block Place Grows)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith decideWith_yes yes_grows yes_keeps_whole
  link_inv head_inv
  finish_inv bindOk HeadPar headOpenQ headOpened headOpenQ_iff headOpenLays headOpenQ_keeps
  openHeadQ finishPlace finishFrontQ finishBehindQ finishFrontQ_iff finishFrontQ_rest
  finishFrontQ_keeps finishBehindQ_iff)
open VerifiableInference.Desc.Ground (groundKeeps_grows)
open Johnson.Desc.First.Walk (emptySlots weightsAtZero)
open _root_.Tw.K2 (sendByL8)

/-- At every sort of place. -/
def K2Common (s s' : S) : Prop :=
  s'.failed = s.failed ∧ s'.out = s.out ∧ s'.req = s.req ∧ s'.rowsOwed = none ∧
    Grows s.st s'.st ∧ SmpStay s.st s'.st

/-- At the number of a message that is sampled in front, the first stored sample row is behind what
it was in front. -/
theorem K2Common.firstRow {s s' : S} (c : K2Common s s') {o : Nat} {x : OnBytes.Oracle}
    (hx : s.st.oracles[o]? = some x) (hs : x.sampled = true) :
    ((s'.st.oracles[o]?).bind fun z => z.sampleRows[0]?) =
      (s.st.oracles[o]?).bind fun z => z.sampleRows[0]? := by
  obtain ⟨x', hx', _, _, hr⟩ := c.2.2.2.2.2.2 o x hx hs
  rw [hx, hx']
  show x'.sampleRows[0]? = x.sampleRows[0]?
  rw [hr]

/-- At a segment's first place. -/
def K2KeepsLink (s s' : S) : Prop := K2Common s s' ∧ s'.here = s.here

/-- At the head's place. -/
def K2KeepsHead (s s' : S) : Prop :=
  K2Common s s' ∧ s'.check = s.check ∧
    ∃ a kept ids, s.here = .head a ∧ s'.here = .head { a with kept := kept, ids := ids }

/-- Behind the last segment. -/
def K2KeepsFinish (s s' : S) : Prop :=
  K2Common s s' ∧ s'.check = s.check ∧ ∃ a sw, s.here = .fin a ∧ s'.here = .fin { a with sw := sw }

variable {p : P2} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

theorem k2Common_of_yes (h : decideWith sendByL8 p s rs gs = .ok s') : K2Common s s' :=
  ⟨(decideWith_yes h).keeps.1, (decideWith_yes h).keeps.2.1, (decideWith_yes h).keeps.2.2,
    (decideWith_yes h).owes, yes_grows h, yes_keeps_whole groundKeeps_smpStay h⟩

theorem k2KeepsLink_of_yes (hp : p.stands = .link) (h : decideWith sendByL8 p s rs gs = .ok s') :
    K2KeepsLink s s' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, k⟩ := link_inv hp h
  exact ⟨k2Common_of_yes h, by rw [k.hOut]⟩

theorem k2KeepsHead_of_yes (hp : p.stands = .head) (h : decideWith sendByL8 p s rs gs = .ok s') :
    K2KeepsHead s s' := by
  obtain ⟨_, _, a, _, w, _, _, k⟩ := head_inv hp h
  exact ⟨k2Common_of_yes h, by rw [k.hOut], a, w.out.kept, w.out.others, k.hHere, by rw [k.hOut]⟩

theorem k2KeepsFinish_of_yes (hp : p.stands = .finish)
    (h : decideWith sendByL8 p s rs gs = .ok s') : K2KeepsFinish s s' := by
  obtain ⟨_, _, a, _, w, _, _, k⟩ := finish_inv hp h
  exact ⟨k2Common_of_yes h, by rw [k.hOut], a, w.out, k.hHere, by rw [k.hOut]⟩

/-! ## The whole place's block -/

/-- The head's place. -/
def K2PlaceHead (s s' : S) : Prop :=
  K2Common s s' ∧ ∃ a b, s.here = .head a ∧ s'.here = .head b ∧ b.opened = true ∧
    b.F.vp.size = b.F.ns ∧ b.F.mf.size = b.F.ns ∧ b.F.LS.size = b.F.ns ∧ b.F.gotF.size = b.F.ns

/-- Behind the head's place: opened, and the ledger's three arrays have one entry for each slot. -/
theorem K2PlaceHead.laid {s s' : S} (h : K2PlaceHead s s') :
    ∃ b, s'.here = .head b ∧ b.opened = true ∧ OnBytes.PscRun.Sized b.F := by
  obtain ⟨_, _, b, _, hb, ho, h1, h2, _, h4⟩ := h
  exact ⟨b, hb, ho, h1, h2, h4⟩

/-- The place behind the last segment. -/
def K2PlaceFinish (s s' : S) : Prop :=
  K2Common s s' ∧ s'.check = s.check ∧ s.atBetween = true ∧ ∃ a, s'.here = .fin a

/-- The opening of the head's segment leaves the mark, the request's words and the count owed;
behind it the segment counts as opened, and its ledger of slots is the empty one of the plan's
count. -/
theorem headOpen_rest {P : HeadPar} {m t : S} (h : headOpenQ P m = .ok t) :
    t.failed = m.failed ∧ t.req = m.req ∧ t.rowsOwed = m.rowsOwed ∧
      ∃ b, t.here = .head b ∧ b.opened = true ∧
        b.F = emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P m t).1 h
  have h1 : s₁ = m.openHead := openHeadQ k.opens
  have h2 : m.openHead =
      { m with here := .head { a with opened := true, L := { a.L with check := m.check } } } := by
    unfold S.openHead
    rw [k.here]
    simp [k.fresh]
  have h3 : (S.here { m with
      here := .head { a with opened := true, L := { a.L with check := m.check } } }) = .head b := by
    rw [← h2, ← h1]
    exact k.opened
  injection h3 with h4
  subst h4
  rw [k.out', h1, h2]
  exact ⟨rfl, rfl, rfl, _, rfl, rfl, rfl⟩

/-- The common sentence, then a step that leaves these fields and under which the statement grows.
-/
theorem K2Common.trans {s m t : S} (c : K2Common s m) (h1 : t.failed = m.failed)
    (h2 : t.out = m.out) (h3 : t.req = m.req) (h4 : t.rowsOwed = m.rowsOwed)
    (h5 : Grows m.st t.st) (h6 : SmpStay m.st t.st) : K2Common s t :=
  ⟨h1.trans c.1, h2.trans c.2.1, h3.trans c.2.2.1, h4.trans c.2.2.2.1, c.2.2.2.2.1.trans h5,
    c.2.2.2.2.2.trans h6⟩

theorem k2PlaceHead_of_yes {Cl : Type} (hp : p.stands = .head) (n : String) (pl : Place)
    (P : HeadPar)
    (h : ((codeSwitchKind p : Block S Cl).andThen n (headOpened n pl P)).decide s rs gs = .ok s') :
    K2PlaceHead s s' := by
  obtain ⟨m, h₁, h₂⟩ := bindOk (x := (codeSwitchKind p : Block S Cl).decide s
    (rs.take (codeSwitchKind p : Block S Cl).rounds.length) (gs.take (codeSwitchKind p : Block S Cl).openings)) h
  have h₁' : decideWith sendByL8 p s _ _ = .ok m := h₁
  have h₂' : headOpenQ P m = .ok s' := h₂
  obtain ⟨c, _, a, _, _, ha, _⟩ := k2KeepsHead_of_yes hp h₁'
  obtain ⟨r1, r2, r3, b, hb, ho', hF⟩ := headOpen_rest h₂'
  obtain ⟨_, _, _, _, _, _, _, ho⟩ := headOpenLays _ _ _ h₂'
  exact ⟨c.trans r1 ho r2 r3 (headOpenQ_keeps groundKeeps_grows h₂')
    (headOpenQ_keeps groundKeeps_smpStay h₂'), a, b, ha, hb, ho', by
      rw [hF]
      simp [emptySlots]⟩

theorem k2PlaceFinish_of_yes {Cl : Type} (hp : p.stands = .finish)
    (h : (finishPlace p : Block S Cl).decide s rs gs = .ok s') : K2PlaceFinish s s' := by
  simp only [finishPlace, Block.andThen, VerifiableInference.Desc.roundlessBlock] at h
  obtain ⟨s₂, h₂, h₃⟩ := bindOk h
  obtain ⟨s₁, h₁, h₂⟩ := bindOk h₂
  have h₁' : finishFrontQ s = .ok s₁ := h₁
  have h₂' : decideWith sendByL8 p s₁ _ _ = .ok s₂ := h₂
  have h₃' : finishBehindQ s₂ = .ok s' := h₃
  obtain ⟨_, _, f3, f4, f5, f6, f7⟩ := finishFrontQ_rest h₁'
  obtain ⟨_, _, _, _, kf⟩ := (finishFrontQ_iff s s₁).1 h₁'
  obtain ⟨c, hc, _⟩ := k2KeepsFinish_of_yes hp h₂'
  obtain ⟨a, mk, _, _, rfl⟩ := (finishBehindQ_iff s₂ s').1 h₃'
  exact ⟨⟨c.1.trans f4, c.2.1.trans f6, c.2.2.1.trans f7, c.2.2.2.1,
    (finishFrontQ_keeps groundKeeps_grows h₁').trans c.2.2.2.2.1,
    (finishFrontQ_keeps groundKeeps_smpStay h₁').trans c.2.2.2.2.2⟩, hc.trans f5, kf.between, _,
    rfl⟩

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.k2Common_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2KeepsLink_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2KeepsHead_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2KeepsFinish_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2PlaceHead_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.k2PlaceFinish_of_yes
#print axioms VerifiableInference.Desc.K2.Honest.K2Common.firstRow
#print axioms VerifiableInference.Desc.K2.Honest.K2PlaceHead.laid
#print axioms VerifiableInference.Desc.K2.Honest.K2Common
#print axioms VerifiableInference.Desc.K2.Honest.K2KeepsLink
#print axioms VerifiableInference.Desc.K2.Honest.K2KeepsHead
#print axioms VerifiableInference.Desc.K2.Honest.K2KeepsFinish
#print axioms VerifiableInference.Desc.K2.Honest.K2PlaceHead
#print axioms VerifiableInference.Desc.K2.Honest.K2PlaceFinish
#print axioms VerifiableInference.Desc.K2.Honest.headOpen_rest
#print axioms VerifiableInference.Desc.K2.Honest.K2Common.trans
