-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Over the seats Stored/HeadSeatAt.lean and Stored/ReplySeatAt.lean, which go with Block.lean and
State.lean. K6On HAS NO CLAUSE
"pointsOf s.look? = pointsOf s.lookHeard?": it would be there so that the two
readers of the lookup's hearing could not part; but x is none until K6's own
hearing, so by reading S.look? answers none in front of K6 while lookHeard? holds the lookup's
value: the clause would be met by no honest run; and there is ONE reader in front: the seat
reads lookHeard? itself. look_setHeard says "s2.look? = s2.lookHeard?".
look_behind: behind the block's decision the two
readers agree: K6After's clause is a theorem of the block (Law/RowPromise.lean). Where the head
below speaks of K6On's last clause, read this.
Johnson/Desc/Kinds/Law/RowPins.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS (idn · the two sums · keys and rider in our own words; planes on neither side) FROM THE FOLD's OWN CALL Block.step OF THE BLOCK AS IT RIDES (Head.blockOf W l): THE PREMISES (ceil) AND (law) OF THE BRIDGE FROM A KIND's RULE OF BAD ELEMENTS TO
A BLOCK's OWN LAW AT THE TABLE (Johnson/Desc/Sound/RuleOwn.lean: OwnOfRule), IN THIS FOLDER's OWN GROUND. **ITS PREMISE (pin) IS OWED.** STATED AND PROVED.


  pointsOf · Pinned · ruleStep · ruleStep_length   (ceil), to the letter, at every record, marked or not, all components, every front: at most priceAt (the front's last round's number). IT IS CHEAP: true by the cut (a list's first n members are at most n), of any list: THE LOAD IS Law/RowPrice.lean's cut_takes_nothingT (the cut takes nothing away
                               where the decision goes on), which wants WellLaid, the tests on the plan and the decision.
  K6On · K6Out · K6In        what is asked of the record in front · what the block opens, at the record behind · what it closes, at the record in front: what the lookup has heard (gk) is READ OFF THE RECORD on both sides (S.lookHeard?).
  RowStepStatement · rowStep   (law), to the letter BUT FOR "the piece's out", IN WHOSE PLACE STANDS Block.step, and for one premise more (Canonical rs); at given components d; the extractor is the identity (the table's: this row lays nothing).
  step_decide · noBad_noDigest · canonical_noDigest · lookHeard_putFork | _setHeard | _leaves · look_putFork | _setHeard   tools.
WHAT IT DOES NOT SAY. **d (THE CELLS AND THE MASK ROW) IS A BARE LETTER UNDER "FOR ALL", TIED TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS**: whoever may pick the mask row behind the draws makes every hidden scalar what they like. A set of bad challenges must be fixed before the witness is spoken of: THAT ORDER IS NOT IN THIS FILE: it lives in the bridge's
notion of a block's goodness ("for a statement, fixed, over the transcripts") and in its premise (pin): where the block says yes, a witness at which all that the block opens holds has the components that a decoder makes of the statement's strings: TYPED AND PAID BY NOTHING AT K6. IT HAS TWO HALVES: that the components which the rule reads are read off pinned messages and the stored cells ALONE is THIS FOLDER's to show (a comp typed over the table's own witness: no text has it; the cells here are integers, a message holds field symbols); that these are what the
decoder gives is the table's. OwnOfRule IS NOT CALLED: "to the letter" is by eye: no Lean has held rowStep against (law). "The piece's out gives Block.step" is owed by whoever
calls it. K6On (the record's ledger WellLaid · the tests on the plan and the request · 0 < d · the heard token below V · what the lookup has heard has its last claim's numbers filled in the ledger · the two readers of the lookup's hearing agree in its points) and Canonical rs ARE PREMISES, AND K6On IS NOT INSIDE THE TABLE's PROMISE AT THIS BORDER: the promise must grow by its clauses and the blocks upstream must pay them. ONE HEARING, TWO READERS: gk is read by S.lookHeard?, the lookup's points inside KeysWorth by S.look? (the field g1 of x): State.lean warns that a later put can part the two: SO K6On ASKS THAT
THEY AGREE IN THE LOOKUP's POINTS (its last clause: pointsOf; rowStep does not spend it: it is there for the tie to the lookup's own sentence on the keys); look_leaves | lookHeard_leaves: the block leaves both, so the clause rides (Law/RowPromise.lean: K6After). IT IS NOT ASKED that the two hearings be
EQUAL: a hearing's type has no decidable equality, so no test with code could say it, and the table's promise takes tests with code alone (Law/K6OnB.lean); what KeysWorth reads of S.look? are these points and nothing else. K6In | K6Out LACK: planes · the row's context (the pins) · "no mark" (Law/RowPromise.lean: unmarked_both has that). At parOf, before := []: the block's own test that the messages with the cells precede its first draw is idle at this seat. K6Out (Opened; join's
form) is a premise: later blocks' laws. No member: that the premises can be met together is not shown. That priceAt's numbers are the plan's prices: Law/K06Rounds.lean. No written challenge is counted.
WHAT IS PAID OF "rs is what decide is shown": Block.step shows decide its rounds without the sealed digest: ruleStep strikes the digests of its front itself (noBad_noDigest): so the law speaks of the rounds AS THE STEP IS HANDED THEM. That these are the written reading's rounds stays outside this file.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open Sound (cutTo strikeLast)
open VerifiableInference.Desc.First (S)

/-- The lookup's points in a hearing of the lookup: its point, and its calls' key points. -/
def pointsOf (g : Option OnBytes.Model.Forest.Heard) : Option (Array E × Array (Array E)) :=
  g.map fun x => (x.zx, x.zk)

/-- The components of a witness that K6's rule reads: the cells, and the mask row. (The name: they are the ones that the table of joints pins at this row: pin 4 0, pinW. NOTHING HERE PINS THEM.) -/
abbrev Pinned : Type := NCells × (Nat → E)

/-- **K6's RULE AT A RECORD IN FRONT AND GIVEN COMPONENTS**, on a front as the step is handed it: the sealed digests are struck first. -/
noncomputable def ruleStep (W : OnBytes.Model.Verify.Public) (s : S) (d : Pinned) (g : List Fmt.RoundView) :
    List E :=
  ruleK6T (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s d.1 d.2 (g.map noDigest)

/-- What is asked of the record in front. -/
def K6On (W : OnBytes.Model.Verify.Public) (s : S) : Prop :=
  WellLaid ((seatAt W.hS (readsOf W)).ledger s) ∧ (parOf W.hS (workOf W)).ok = true ∧
    hasFeatures (parOf W.hS (workOf W)) ∧
    (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true ∧
    (∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V) ∧
    (∀ gk, s.lookHeard? = some gk → CEndFilled gk ((seatAt W.hS (readsOf W)).ledger s))

/-- What the block opens, at the record behind and the components. -/
def K6Out (W : OnBytes.Model.Verify.Public) (s' : S) (d : Pinned) : Prop :=
  Opened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' d.1 d.2 ∧
    ∃ gk, s'.lookHeard? = some gk ∧
      JoinOpened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' d.1 d.2 gk

/-- What it closes, at the record in front and the components. -/
def K6In (W : OnBytes.Model.Verify.Public) (s : S) (d : Pinned) : Prop :=
  FrontIdn (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s d.1 ∧
    FrontRider (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s d.1 ∧
    ∃ gk, s.lookHeard? = some gk ∧
      KeysWorth (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s d.1 d.2 gk

/-- **THE HEAD's OUT-LAW, FROM THE FOLD's OWN CALL, AT GIVEN COMPONENTS.** -/
def RowStepStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (firstTree : Nat) (s : S) (d : Pinned) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    K6On W s → Sound.NoBad (ruleStep W s d) rs → Canonical rs →
    b.step firstTree s rs cols = .ok (s', n) → K6Out W s' d → K6In W s d

namespace Came

/-- **The ceiling, at every record, all components, every front.** -/
theorem ruleStep_length (W : OnBytes.Model.Verify.Public) (s : S) (d : Pinned) (g : List Fmt.RoundView) :
    (ruleStep W s d g).length ≤ priceAt (parOf W.hS (workOf W)) (g.length - 1) := by
  have h := ruleK6T_length (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s d.1 d.2
    (g.map noDigest)
  rwa [List.length_map] at h

theorem canonical_noDigest {rs : List Fmt.RoundView} (h : Canonical rs) : Canonical (rs.map noDigest) := by
  intro r hr
  obtain ⟨r0, h0, rfl⟩ := List.mem_map.mp hr
  exact h r0 h0

/-- A rule that strikes its front's digests itself, on the rounds whole: the rule on the rounds without digests. -/
theorem noBad_noDigest {b : List Fmt.RoundView → List E} {rs : List Fmt.RoundView}
    (h : Sound.NoBad (fun g => b (g.map noDigest)) rs) : Sound.NoBad b (rs.map noDigest) := by
  intro i r hi j x hj hm
  rw [List.getElem?_map] at hi
  obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.mp hi
  refine h i r0 h0 j x hj ?_
  have e : ([] ++ rs.take i ++ [cutTo r0 j]).map noDigest
      = [] ++ (rs.map noDigest).take i ++ [cutTo (noDigest r0) j] := by
    rw [List.nil_append, List.nil_append, List.map_append, List.map_take]
    rfl
  show E.ofTriple x ∈ b (([] ++ rs.take i ++ [cutTo r0 j]).map noDigest)
  rw [e]
  exact hm

/-- Where the step goes on, the block's decision went on, on the rounds without their digests. -/
theorem step_decide {S' Cl : Type} (firstTree : Nat) (b : Block S' Cl) (s : S') (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S') (n : Nat) (h : b.step firstTree s rs cols = .ok (s', n)) :
    ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  unfold Block.step at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i s1 hs1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨_, h.1 ▸ hs1⟩

theorem lookHeard_putFork (s : S) (F : Fork) : (s.putFork F).lookHeard? = s.lookHeard? := by
  unfold S.putFork S.lookHeard?
  cases hh : s.here with
  | head a => by_cases hop : a.opened = true <;> simp [hh, hop]
  | lay a => simp
  | att a => simp
  | between => simp [hh]
  | fin a => simp [hh]
  | mem a => simp [hh]

theorem lookHeard_setHeard (h : OnBytes.Model.Head.Shape) (iU3 : Nat) {s s2 : S} {H : HeardAll}
    (e : (seatAt h iU3).setHeard s H = .ok s2) : s2.lookHeard? = s.lookHeard? := by
  unfold seatAt at e
  dsimp only at e
  split at e
  · rename_i o ho
    split at e
    · simp only [Except.ok.injEq] at e
      subst e
      simp [S.lookHeard?, ho]
    · cases e
  · cases e

/-- **The block's decision leaves what the lookup has heard.** -/
theorem lookHeard_leaves (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) :
    Leaves (fun s : S => s.lookHeard?) (blockAt h iU3 work l) := by
  refine leaves_of_decide_eq (b := kind (fun _ => ()) (seatAt h iU3) l 4 (parOf h work)) rfl
    (k6_leaves _ (seatAt h iU3) l 4 (parOf h work) _ ?_ ?_ ?_)
  · intro s F s1 e
    rw [putFork?_ok (show s.putFork? F = .ok s1 from e), lookHeard_putFork]
  · intro s H s2 e
    exact lookHeard_setHeard h iU3 e
  · intro s w
    rfl

theorem look_putFork (s : S) (F : Fork) : (s.putFork F).look? = s.look? := by
  unfold S.putFork S.look?
  cases hh : s.here with
  | head a => by_cases hop : a.opened = true <;> simp [hh, hop]
  | lay a => simp
  | att a => simp
  | between => simp [hh]
  | fin a => simp [hh]
  | mem a => simp [hh]

/-- **BEHIND THE SEAT's LAYING OF WHAT WAS HEARD THE TWO READERS OF THE LOOKUP's HEARING AGREE**: the
field g1 of x is a copy that the laying makes of lookHeard. -/
theorem look_setHeard (h : OnBytes.Model.Head.Shape) (iU3 : Nat) {s s2 : S} {H : HeardAll}
    (e : (seatAt h iU3).setHeard s H = .ok s2) : s2.look? = s2.lookHeard? := by
  obtain ⟨o, x, _, hx, rfl⟩ := setHeard_form h iU3 e
  simp [S.look?, S.lookHeard?, hx, heardOf]

/-- **So behind the block's decision.** (The decision does not leave what
S.look? reads: x is none in front.) -/
theorem look_behind (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') : s'.look? = s'.lookHeard? := by
  have hd' := hd
  simp only [blockAt, kindWithJoin, kind] at hd'
  obtain ⟨g, H, F, w, s1, s2, _, _, _, e2, hs'⟩ := decide_hears hd'
  have hs2 : s' = s2 := hs'
  subst hs2
  exact look_setHeard h iU3 e2

theorem rowStep : RowStepStatement := by
  intro W l b hb firstTree s d rs cols s' n hon hnb hcan hstep hout
  obtain ⟨gs, hd⟩ := step_decide firstTree b s rs cols s' n hstep
  obtain ⟨hWL, hplan, hd0, hreq, hy, hfill⟩ := hon
  obtain ⟨hopen, gk, hgk, hjoin⟩ := hout
  have hlk : s'.lookHeard? = s.lookHeard? := by
    have hb' := hb
    unfold blockOf at hb'
    cases hU : W.H.tl.ix.U.getD 2 none with
    | none =>
      rw [hU] at hb'
      simp at hb'
    | some i =>
      rw [hU] at hb'
      simp only [Option.map_some, Option.some.injEq] at hb'
      subst hb'
      exact lookHeard_leaves W.hS i _ l s _ gs s' hd
  have hgk' : s.lookHeard? = some gk := hlk ▸ hgk
  obtain ⟨h1, h2, h3⟩ := rowFrontRides W l b hb s d.1 d.2 gk s' (rs.map noDigest) gs hd hWL hplan hd0
    hreq hy (canonical_noDigest hcan) (noBad_noDigest hnb) (hfill gk hgk') hopen hjoin
  exact ⟨h1, h2, gk, hgk', h3⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.ruleStep_length
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lookHeard_leaves
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.look_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowStep
