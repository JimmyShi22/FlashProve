-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupBehindAndRidesPast.lean: the kind "lookup" (K3): the
hypothesis `BehindS` (Honest/Thread/PaysS.lean) at all fifty borders in front of a lookup, at the first chain's thread of `lettersHead` (Honest/Thread/FirstHead.lean)
with "keeps" by the place's kind (`kpBy f`, Honest/Thread/KeepsBy.lean). THE FILE'S NAME PROMISES MORE
THAN THE FILE HOLDS: `RidesPastS` IS NOT SHOWN HERE. One wrapper for it stands here
(`lookupOpenItemsRidePast`), under a premise that is shown of no item.

The thread at which the three theorems on `BehindS` stand, written (L₁).thread below, T₁ in this head:
  (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w).thread
with `csHead` the written list of 55 riders' clauses (Honest/Thread/CsHead.lean). The prover H and the
letters Q, test, carryX, item, n₁, n₂, Vd, ν, st, R, f, w and `Said` are variables.

What is shown.
  `lookupFormRidersAndKeepsBehindTheCalls`: `BehindS T₁ Said (borderOf l false)`, l < 25.
  `lookupFormRidersAndKeepsBehindTheDigits`: `BehindS T₁ Said (borderOf l true)`, l < 24.
  `lookupFormRidersAndKeepsBehindTheHeadsDigits`: `BehindS T₁ Said (borderOf 24 true)`.
  `lookupBehindFromTheRidersColumns`: the same at any list of clauses and any border b₀ of the
    reply's clause that is not the one behind the lookup, from the two columns on the riders.
  `lookupOpenItemsRidePast`: `RidesPastS` at a lookup's border, general in Rd and b₀, from
    `openItemsGoBack`. That premise is shown here of no item. IT IS MEANT FOR THE LOOKUPS ON THE CALLS
    ALONE. At the lookups on the digits the link's own forms are open, and their meaning reads parts
    of the state of which the library's `SameBut` says nothing:
    Honest/K3/Term/LookupFormsDoNotGoBackOverSameBut.lean [not in this library] refutes the
    premise's like there, under its own conditions. Where the premise fails this theorem says
    nothing.
  Lemmas: the borders' numbers; what each sort's clause of "keeps" leaves; the lookups' clause by
    place, sort by sort, and `SameBut` from it, with no test on the slots in use; which clauses of
    `csHead` stay past a lookup and which it lays.

Which clause of `csHead` meets which border, and how it is shown.
  calls, even link and link 24: none is laid, none stays.
  calls, link 2 g + 1: lays "R g of what the lookup returned": `lays_att_head`
    (Honest/K3/Law/Thread/LaysAttHead.lean), under `attentionClauseHoldsOfEveryHearing`.
  digits, l < 24: lays `st l`: `lookupLaysWhatStands` (Honest/K3/Term/LookupLaysWhatStands.lean), under
    `standingGivesTheClause`. At link 2 g + 1 "R g …" stays, at link
    2 g "the link's own rounds have returned something" stays: the lookups' clause turns two
    fields of the link's own part alone.
  digits, link 24: lays "the ledger's next free slot is ν": `lays_nextHead_3531_thin`
    (Honest/K3/Law/Thread/NextThin.lean), under ν = 3531; lays "one fold has been drawn": from "none
    has been drawn", which the riders hold in front; lays `st 24`: as at l < 24. "The head's rounds
    have heard" and "the tables have been set" stay.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` at the hash function `secondHashFunction`.
  `saidGivesWordsBelowThePrime`: the letter `Said` gives `SaidOk`.
  On the letter f, two in the place of an equation f .K3 = k3KeepsAt Zp:
    `keepsGivesTheLookupClause`: f at the kind K3 gives the lookups' own clause `k3KeepsAt`
      (Honest/K3/Law/Thread/K3KeepsAt.lean). Used where a clause stays, and for `RidesPastS`.
    `theStepPaysTheRestOfKeeps` (`StepPaysTheWholeKeepsClause`): behind the member's step, from the
      lookups' own clause and the form behind, f at the kind K3 holds at the lookup's place.
    Where f .K3 is `k3KeepsAt Zp` both hold (`stepPaysTheLookupClauseItself`).
  On the letter ν: `nextFreeSlotIsTheWrittenOne`: ν = 3531. That the slot is 3531 is shown under `h`
    alone (its scope, its reading of the files, its public part), not at named files.
  On the letter R: `attentionClauseHoldsOfEveryHearing`: R g holds of whatever the hearing returns
    at public parameters of the shape of the plan at g. At R g o := "at the plan a at g, `lookR a o`"
    (Johnson/Desc/K5/Honest/Law/LookR.lean) it holds: Honest/K3/Term/LookupAttentionClauseAtLookR.lean.
  On the letter st: `standingGivesTheClause`: an implication on states alone: at the first slot of the
    public structure's place, `StandsHere true standsAtNumber first t` (Honest/K3/Law/Thread/
    LaysStands.lean: "what the lookup has heard stands for some rounds") gives `st l t`. At
    st l := that sentence it is the identity.

No hypothesis on the prover's halves is asked: nothing here reads H.

Not shown here: that `st 24` stays past sub-protocol number 346, which csHead's span (346 to 347) asks
of that sub-protocol's own clause of "keeps": it is another kind's.

Limits. Implications. Nothing here shows that the invariant or a step holds at any run, or that the
hypotheses on f, R and st hold at the values that the thread's authors give these letters. At the
full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFormBehind
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupLaysWhatStands
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.KeepsThread
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietAtHeadLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysAttHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.NextThin
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidesPast
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.ProofFile.Honest.Thread.RidersAnd
import Johnson.Desc.ProofFile.Honest.Thread.RidersStayH
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain FileDescription Place Strs KindName OpenedColumn)
open VerifiableInference.Desc.First (HeadOwn AttOwn)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.Sound (MsgT GoesBack)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open VerifiableInference.OnPublicFiles (SameBut relOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script head_rides_and head_reply_next head_keeps_kind)
open ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 The borders' numbers -/

theorem callsBorderBelowTheHead {l : Nat} (linkBelowTheHead : l < 24) :
    borderOf l false = 14 * l + 3 := by
  unfold borderOf ixOf
  rw [if_neg (show ¬ l = 24 by omega)]
  rfl

theorem digitsBorderBelowTheHead {l : Nat} (linkBelowTheHead : l < 24) :
    borderOf l true = 14 * l + 8 := by
  unfold borderOf ixOf
  rw [if_neg (show ¬ l = 24 by omega)]
  rfl

theorem callsBorderAtTheHead : borderOf 24 false = 340 := rfl

theorem digitsBorderAtTheHead : borderOf 24 true = 345 := rfl

/-- The border from which the reply's clause speaks is behind no lookup. -/
theorem replyBorderIsBehindNoLookup (l : Nat) (d : Bool) : 339 ≠ borderOf l d + 1 := by
  unfold borderOf ixOf
  split <;> split <;> omega

/-! ## 2 What the sorts' clauses of "keeps" leave, on states alone -/

theorem digitsLeaveTheAttentionReturn {sh : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : FS}
    (hK : K3KeepsDigits sh claims s s') {a : AttOwn} (ha : s.here = .att a) :
    ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨_, tl, F, Hd, G, _, _, hA, _⟩ := hK
  rcases hA with ⟨a₁, h1, _⟩ | ⟨a₁, h1, e⟩ | ⟨a₁, h1, _, _⟩
  · rw [ha] at h1
    exact nomatch h1
  · obtain rfl : a = a₁ := VerifiableInference.Desc.First.Here.att.inj (ha.symm.trans h1)
    subst e
    exact ⟨_, rfl, rfl⟩
  · rw [ha] at h1
    exact nomatch h1

theorem digitsLeaveTheLayersOwnRounds {sh : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : FS}
    (hK : K3KeepsDigits sh claims s s') {a} (ha : s.here = .lay a) :
    ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  obtain ⟨_, tl, F, Hd, G, _, _, hA, _⟩ := hK
  rcases hA with ⟨a₁, h1, e⟩ | ⟨a₁, h1, _⟩ | ⟨a₁, h1, _, _⟩
  · obtain rfl : a = a₁ := VerifiableInference.Desc.First.Here.lay.inj (ha.symm.trans h1)
    subst e
    exact ⟨_, rfl, rfl⟩
  · rw [ha] at h1
    exact nomatch h1
  · rw [ha] at h1
    exact nomatch h1

theorem headDigitsTurnTheHeadsOwnPart {sh : OnBytes.Model.Forest.Shape} {s s' : FS}
    (hK : K3KeepsHead sh s s') {a : HeadOwn} (ha : s.here = .head a) :
    ∃ a', s'.here = .head a' ∧ a'.x = a.x ∧ a'.t = a.t ∧
      a'.tl.foldDrawn = a.tl.foldDrawn + 1 := by
  obtain ⟨_, tl, F, Hd, G, a₀, claim, htl, _, h1, ho, e, _⟩ := hK
  obtain rfl : a = a₀ := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans h1)
  have etl : a.tl = tl := by
    simpa [VerifiableInference.Desc.First.S.tl?, ha, ho] using htl
  subst e
  refine ⟨_, rfl, rfl, rfl, ?_⟩
  show tl.foldDrawn + 1 = a.tl.foldDrawn + 1
  rw [etl]

/-! ## 3 The lookups' clause by place, sort by sort, under the library's hypothesis -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem lookupClauseAtTheCalls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (linkBelow : l < 25) {t t' : FS} (hk : k3KeepsAt Zp (IM.k3Place l false) t t') :
    ∃ sh, K3KeepsCalls sh t t' := by
  obtain ⟨s, hs, -, e2, e3, -⟩ := site_digits_paid h l linkBelow false
  rw [← e3] at hk
  exact ⟨s.shape, k3KeepsAt_calls hk hs e2⟩

theorem lookupClauseAtTheDigits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (linkBelowTheHead : l < 24) {t t' : FS} (hk : k3KeepsAt Zp (IM.k3Place l true) t t') :
    ∃ sh claims, K3KeepsDigits sh claims t t' := by
  obtain ⟨s, hs, e1, e2, e3, -⟩ := site_digits_paid h l (by omega) true
  obtain ⟨used, claims, hq⟩ := quiet_digits_head h l linkBelowTheHead
  rw [← e3] at hk
  rw [← e1] at hq
  exact ⟨s.shape, claims, k3KeepsAt_digits hk hs e2 hq⟩

theorem lookupClauseAtTheHeadsDigits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {t t' : FS}
    (hk : k3KeepsAt Zp (IM.k3Place 24 true) t t') : ∃ sh, K3KeepsHead sh t t' := by
  obtain ⟨s, hs, e1, e2, e3, -⟩ := site_digits_paid h 24 (by omega) true
  rw [← e3] at hk
  exact ⟨s.shape, k3KeepsAt_head hk hs e2 (quiet_head_site h s e1)⟩

/-- The lookups' clause at a lookup's place gives the library's "the same but". No test on the
slots in use is asked. -/
theorem lookupClauseGivesSameBut (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat}
    (linkBelow : l < 25) (d : Bool) {t t' : FS} (hk : k3KeepsAt Zp (IM.k3Place l d) t t') :
    SameBut t t' := by
  cases d with
  | false =>
    obtain ⟨sh, hK⟩ := lookupClauseAtTheCalls h linkBelow hk
    exact keepsCalls_sameBut hK
  | true =>
    by_cases e : l = 24
    · subst e
      obtain ⟨sh, hK⟩ := lookupClauseAtTheHeadsDigits h hk
      exact keepsHead_sameBut hK
    · obtain ⟨sh, c, hK⟩ := lookupClauseAtTheDigits h (by omega) hk
      exact keepsDigits_sameBut hK

end

/-! ## 4 The premise on the rest of "keeps" -/

/-- **The member's step pays the whole clause of "keeps".** From the invariant with `Said` in front
of sub-protocol number b, the sub-protocol's step from s to s', the clause `lookupClause` at s and
s', and the form at the next border, the clause `wholeClause` holds at s and s'. A definition, meant
as a hypothesis: it is asked where the thread's clause of "keeps" at the kind K3 says more than the
lookups' own clause. -/
def StepPaysTheWholeKeepsClause {Bk : ProverCoinCounts} {V W X Pb : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (lookupClause wholeClause : FS → FS → Prop) :
    Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → lookupClause s s' →
    T.Form (b + 1) k s' y.2 → wholeClause s s'

/-- Where the whole clause is the lookups' own, the premise holds. -/
theorem stepPaysTheLookupClauseItself {Bk : ProverCoinCounts} {V W X Pb : Type}
    (T : Thread Bk FS ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat)
    (lookupClause : FS → FS → Prop) :
    StepPaysTheWholeKeepsClause T Said b lookupClause lookupClause :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ => hk

/-! ## 5 At the thread of `lettersHead` with "keeps" by the place's kind -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LK" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w

/-- Behind the step of the thread's member at a lookup's border the lookups' own clause holds, and
the member stands at the lookup's place. -/
theorem lookupClauseHoldsBehindTheStep {l : Nat} (linkBelow : l < 25) (d : Bool)
    {blk : Block TS ProofFile.Cl} (memberAtBorder : (LK).thread.bs[borderOf l d]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (memberStepped : (LK).thread.Stepped blk k s m E ds y cols s') :
    blk.place = IM.k3Place l d ∧ k3KeepsAt Zp (IM.k3Place l d) s s' := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hp, hM⟩ :=
    memberAt_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w l linkBelow d
  exact ⟨(hM.place blk memberAtBorder).trans hp,
    k3KeepsAt_pays _ _ _ _ Fd Zp Bs base cF A B O (IM.k3Place l d) lot blk hM.inLot hp
      (hM.mem blk memberAtBorder) (hM.place blk memberAtBorder) (hM.plan blk memberAtBorder) _ s s'
      _ _ cols memberStepped.2⟩

/-- The thread's "keeps" at a lookup's border gives the lookups' own clause at the lookup's place.
-/
theorem keepsGiveTheLookupClauseAtTheBorder
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {l : Nat}
    (linkBelow : l < 25) (d : Bool) {t t' : TS} (hk : (LK).thread.keeps (borderOf l d) t t') :
    k3KeepsAt Zp (IM.k3Place l d) t t' := by
  obtain ⟨blk, hblk, hp⟩ := member_thread h H Q test carryX item n₁ n₂ b₀ Vd Rd f w l linkBelow d
  have hkind : blk.place.kind = KindName.K3 := by rw [hp]
  have h1 := (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hblk hkind t t').1 hk
  rw [hp] at h1
  exact keepsGivesTheLookupClause _ _ _ h1

/-- What the lookup on the calls of an attention link returned stays past that link's lookup on the
digits. -/
theorem attentionReturnStaysPastTheDigits
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {g : Nat}
    (groupBelow : g < 12) (lo hi : Nat) (fact : Option OnBytes.Model.Forest.Heard → Prop) :
    StaysBy (LK).thread (borderOf (2 * g + 1) true) (riderAtt lo hi fun a => fact a.g) :=
  staysBy_att_read (LK).thread (fun a => a.g) (R := fact) fun s s' hK a ha => by
    obtain ⟨sh, c, hD⟩ := lookupClauseAtTheDigits h (show 2 * g + 1 < 24 by omega)
      (keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
        keepsGivesTheLookupClause (show 2 * g + 1 < 25 by omega) true hK)
    exact digitsLeaveTheAttentionReturn hD ha

/-- "The layers' link's own rounds have returned something" stays past that link's lookup on the
digits. -/
theorem layersOwnRoundsStayPastTheDigits
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {g : Nat}
    (groupBelow : g < 12) (lo hi : Nat) :
    StaysBy (LK).thread (borderOf (2 * g) true)
      ⟨lo, hi, fun _ _ s => ∃ o, s.own? = some o⟩ :=
  staysBy_own (LK).thread fun s s' hK a ha => by
    obtain ⟨sh, c, hD⟩ := lookupClauseAtTheDigits h (show 2 * g < 24 by omega)
      (keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
        keepsGivesTheLookupClause (show 2 * g < 25 by omega) true hK)
    exact digitsLeaveTheLayersOwnRounds hD ha

/-- A fact on what the head's rounds heard and on its tables stays past the head's lookup on the
digits. -/
theorem headsHearingStaysPastTheDigits
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') (lo hi : Nat)
    (fact : HeadOwn → Prop)
    (factReadsTheseTwo : ∀ a a' : HeadOwn, a'.x = a.x → a'.t = a.t → fact a → fact a') :
    StaysBy (LK).thread (borderOf 24 true) (riderHead lo hi fact) :=
  staysBy_head_of (LK).thread fun s s' hK a ha => by
    obtain ⟨sh, hD⟩ := lookupClauseAtTheHeadsDigits h
      (keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
        keepsGivesTheLookupClause (show 24 < 25 by omega) true hK)
    obtain ⟨a', h1, ex, et, -⟩ := headDigitsTurnTheHeadsOwnPart hD ha
    exact ⟨a', h1, factReadsTheseTwo a a' ex et⟩

/-- **`RidesPastS` at a lookup's border, from "every open item goes back over the same-but".**
Conditional on `openItemsGoBack`, which is shown here of no item. MEANT AT d = false ALONE: at a lookup
on the digits items "forms" of the link are open whose meaning reads what `SameBut` leaves free, so
that the premise is not to be had there (Honest/K3/Term/LookupFormsDoNotGoBackOverSameBut.lean
[not in this library]), and this theorem then says nothing. The digits' road:
Honest/K3/Term/LookupFormsRidePastTheDigits.lean. -/
theorem lookupOpenItemsRidePast
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t') {l : Nat}
    (linkBelow : l < 25) (d : Bool) (base : Nat)
    (baseBelowTheTrees : base ≤ treesTo (LK).bs (borderOf l d))
    (openItemsGoBack : ∀ w' i, i ∈ (LK).thread.opened (borderOf l d) →
      i ∉ ((LK).thread.row (borderOf l d)).shuts → i ∉ ((LK).thread.row (borderOf l d)).owes →
      GoesBack (relOf SameBut base) (i.holds (LK).N ((LK).mg w'))) :
    RidesPastS (LK).thread Said (borderOf l d) :=
  ridesPastS_of _ Said (ridesPast_of_sameBut (LK) (borderOf l d) base
    (fun _ _ hk => lookupClauseGivesSameBut h linkBelow d
      (keepsGiveTheLookupClauseAtTheBorder h H Q test carryX item n₁ n₂ b₀ Vd Rd f w
        keepsGivesTheLookupClause linkBelow d hk))
    baseBelowTheTrees openItemsGoBack)

end

/-! ## 6 `BehindS` from the riders' two columns -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LC" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) (kpBy f) w

/-- **`BehindS` at a lookup's border, at any list of riders' clauses.** The form behind: by
`lookupFormHoldsBehindTheStep`. "keeps": the lookups' own clause by the step, the rest by the
premise. The reply's clause: the lookups' clause leaves what the chain hands on. -/
theorem lookupBehindFromTheRidersColumns
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelow : l < 25) (d : Bool) (replyBorderIsNotBehind : b₀ ≠ borderOf l d + 1)
    (theStepPaysTheRestOfKeeps : StepPaysTheWholeKeepsClause (LC).thread Said (borderOf l d)
      (k3KeepsAt Zp (IM.k3Place l d)) (f .K3 (IM.k3Place l d)))
    (ridersStay : ∀ c ∈ cs, c.lo ≤ borderOf l d → borderOf l d + 1 ≤ c.hi →
      StaysBy (LC).thread (borderOf l d) c)
    (ridersAreLaid : ∀ c ∈ cs, c.lo = borderOf l d + 1 →
      LaysAtS (LC).thread Said (borderOf l d) c) :
    BehindS (LC).thread Said (borderOf l d) := by
  refine behindS_of_keeps_and (LC).thread Said
    (R₀ := fun c v t => b₀ ≤ c → t.out.reply = some v.x.asked)
    (head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs (kpBy f) w) ?_ ?_ ridersStay
    ridersAreLaid
  · intro blk hblk k s m E ds y cols s' hA hd hS
    have hF := lookupFormHoldsBehindTheStep h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs)
      (kpBy f) w Said saidGivesWordsBelowThePrime linkBelow d hblk hA hS
    obtain ⟨e, hk⟩ := lookupClauseHoldsBehindTheStep h H Q test carryX item n₁ n₂ b₀ Vd
      (ridersOf cs) f w linkBelow d hblk hS
    have hkind : blk.place.kind = KindName.K3 := by rw [e]
    refine ⟨hF, (head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) f w hblk hkind
      s s').2 ?_⟩
    rw [e]
    exact theStepPaysTheRestOfKeeps blk hblk k s m E ds y cols s' hA hd hS hk hF
  · intro blk hblk k s m E ds y cols s' hA _ hS
    obtain ⟨-, hk⟩ := lookupClauseHoldsBehindTheStep h H Q test carryX item n₁ n₂ b₀ Vd
      (ridersOf cs) f w linkBelow d hblk hS
    have hA' := hA.1
    unfold Thr at hA'
    have hR := ((head_rides_and h H Q test carryX item n₁ n₂ b₀ Vd cs (kpBy f) w (borderOf l d)
      m.st.input s).1 hA'.2.2.2.2.2.1).1
    exact head_reply_next (asked := fun v : Local W₀ Rc ProofFile.Inst Tr => v.x.asked) hR
      (fun e => absurd e replyBorderIsNotBehind)
      (fun _ => by rw [(lookupClauseGivesSameBut h linkBelow d hk).out])

end

/-! ## 7 At the first chain's thread with the written list of riders, the reply's clause from 339 -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

local notation "L₁" =>
  lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w

/-- The head's lookup on the digits lays "one fold has been drawn": from the clause "none has been
drawn", which the riders hold in front of it, and the lookups' own clause. -/
theorem headsDigitsLayTheFoldCount :
    LaysAtS (L₁).thread Said (borderOf 24 true) (riderHead 346 347 fun a => a.tl.foldDrawn = 1) := by
  intro blk hblk k s m E ds y cols s' hA _ hS
  have hA' := hA.1
  unfold Thr at hA'
  have hR := ((head_rides_and h H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) (kpBy f) w
    (borderOf 24 true) m.st.input s).1 hA'.2.2.2.2.2.1).2
  have hq : ∃ a, s.here = .head a ∧ a.tl.foldDrawn = 0 :=
    riders_at hR (c := riderHead 344 345 fun a => a.tl.foldDrawn = 0)
      ((csHead_mem ν st R _).2 (Or.inl (Or.inl (Or.inl
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
      (show 344 ≤ 345 by omega) (show 345 ≤ 345 by omega)
  obtain ⟨a, ha, h0⟩ := hq
  obtain ⟨-, hk⟩ := lookupClauseHoldsBehindTheStep h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w (show 24 < 25 by omega) true hblk hS
  obtain ⟨sh, hH⟩ := lookupClauseAtTheHeadsDigits h hk
  obtain ⟨a', h1, -, -, h2⟩ := headDigitsTurnTheHeadsOwnPart hH ha
  refine ⟨a', h1, ?_⟩
  show a'.tl.foldDrawn = 1
  rw [h2, h0]

/-- **`BehindS` at the lookup on the calls, at all twenty-five links.** -/
theorem lookupFormRidersAndKeepsBehindTheCalls
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelow : l < 25)
    (theStepPaysTheRestOfKeeps : StepPaysTheWholeKeepsClause (L₁).thread Said (borderOf l false)
      (k3KeepsAt Zp (IM.k3Place l false)) (f .K3 (IM.k3Place l false)))
    (attentionClauseHoldsOfEveryHearing : ∀ g, g < 12 → ∀ a, (P5J.At.X Zp).A[g]? = some a →
      ∀ p : VerifiableInference.Desc.First.Look.P, p.shape = some a.fs →
      ∀ F rs Hd G₁, hearVia p F rs = some (Hd, G₁) → R g (some Hd)) :
    BehindS (L₁).thread Said (borderOf l false) := by
  have hb : borderOf l false = 340 ∨ (l < 24 ∧ borderOf l false = 14 * l + 3) := by
    by_cases e : l = 24
    · subst e
      exact Or.inl rfl
    · exact Or.inr ⟨by omega, callsBorderBelowTheHead (by omega)⟩
  refine lookupBehindFromTheRidersColumns h H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) f w
    Said saidGivesWordsBelowThePrime linkBelow false (replyBorderIsBehindNoLookup l false)
    theStepPaysTheRestOfKeeps ?_ ?_
  · intro c hc h1 h2
    exfalso
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    all_goals
      dsimp only [riderHead, riderAtt] at h1 h2
      rcases hb with hb | ⟨hl24, hb⟩ <;> rw [hb] at h1 h2 <;> omega
  · intro c hc h1
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    all_goals first
      | (exfalso; dsimp only [riderHead, riderAtt] at h1;
         rcases hb with hb | ⟨hl24, hb⟩ <;> rw [hb] at h1 <;> omega)
      | skip
    have e : l = 2 * g + 1 := by
      dsimp only [riderAtt] at h1
      rcases hb with hb | ⟨hl24, hb⟩ <;> rw [hb] at h1 <;> omega
    subst e
    obtain ⟨a, ha⟩ := (H2K5.Door.scope_all h).2.2 g hg
    rw [border_odd]
    exact laysAtS_of _ _ (lays_att_head h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy f) w g hg a ha (R g)
      (attentionClauseHoldsOfEveryHearing g hg a ha))

/-- **`BehindS` at the lookup on the digits, at the twenty-four links below the head's.** -/
theorem lookupFormRidersAndKeepsBehindTheDigits
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m) {l : Nat}
    (linkBelowTheHead : l < 24)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    (theStepPaysTheRestOfKeeps : StepPaysTheWholeKeepsClause (L₁).thread Said (borderOf l true)
      (k3KeepsAt Zp (IM.k3Place l true)) (f .K3 (IM.k3Place l true)))
    (standsAtNumber : Nat)
    (standingGivesTheClause : ∀ p, placeAt Zp.p.X l true = some p → ∀ t,
      StandsHere true standsAtNumber p.first t → st l t) :
    BehindS (L₁).thread Said (borderOf l true) := by
  have hb := digitsBorderBelowTheHead linkBelowTheHead
  refine lookupBehindFromTheRidersColumns h H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) f w
    Said saidGivesWordsBelowThePrime (by omega) true (replyBorderIsBehindNoLookup l true)
    theStepPaysTheRestOfKeeps ?_ ?_
  · intro c hc h1 h2
    rw [hb] at h1 h2
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    all_goals first
      | (exfalso; dsimp only [riderHead, riderAtt] at h1 h2; omega)
      | skip
    · have e : l = 2 * g + 1 := by
        dsimp only [riderAtt] at h1 h2
        omega
      subst e
      exact attentionReturnStaysPastTheDigits h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w keepsGivesTheLookupClause hg _ _ (R g)
    · have e : l = 2 * g := by
        dsimp only at h1 h2
        omega
      subst e
      exact layersOwnRoundsStayPastTheDigits h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w keepsGivesTheLookupClause hg _ _
  · intro c hc h1
    rw [hb] at h1
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    all_goals first
      | (exfalso; dsimp only [riderHead, riderAtt] at h1; omega)
      | skip
    have e : l' = l := by
      dsimp only at h1
      omega
    subst e
    exact laysAtS_of _ _ (lookupLaysWhatStands h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w (by omega) true standsAtNumber _
      (fun p hp _ t hst => standingGivesTheClause p hp t hst))

/-- **`BehindS` at the lookup on the digits of the head's link.** -/
theorem lookupFormRidersAndKeepsBehindTheHeadsDigits
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (keepsGivesTheLookupClause : ∀ p t t', f .K3 p t t' → k3KeepsAt Zp p t t')
    (theStepPaysTheRestOfKeeps : StepPaysTheWholeKeepsClause (L₁).thread Said (borderOf 24 true)
      (k3KeepsAt Zp (IM.k3Place 24 true)) (f .K3 (IM.k3Place 24 true)))
    (nextFreeSlotIsTheWrittenOne : ν = 3531)
    (standsAtNumber : Nat)
    (standingGivesTheClause : ∀ p, placeAt Zp.p.X 24 true = some p → ∀ t,
      StandsHere true standsAtNumber p.first t → st 24 t) :
    BehindS (L₁).thread Said (borderOf 24 true) := by
  have hb : borderOf 24 true = 345 := rfl
  refine lookupBehindFromTheRidersColumns h H Q test carryX item n₁ n₂ 339 Vd (csHead ν st R) f w
    Said saidGivesWordsBelowThePrime (by omega) true (replyBorderIsBehindNoLookup 24 true)
    theStepPaysTheRestOfKeeps ?_ ?_
  · intro c hc h1 h2
    rw [hb] at h1 h2
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    all_goals first
      | (exfalso; dsimp only [riderHead, riderAtt] at h1 h2; omega)
      | skip
    · exact headsHearingStaysPastTheDigits h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w keepsGivesTheLookupClause _ _ _
        (fun a a' ex _ hp => by
          show a'.x.isSome = true
          rw [ex]
          exact hp)
    · exact headsHearingStaysPastTheDigits h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w keepsGivesTheLookupClause _ _ _
        (fun a a' _ et hp => by
          show a'.t.isSome = true
          rw [et]
          exact hp)
  · intro c hc h1
    rw [hb] at h1
    rcases (csHead_mem ν st R c).1 hc with
      ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
    all_goals first
      | (exfalso; dsimp only [riderHead, riderAtt] at h1; omega)
      | skip
    · subst nextFreeSlotIsTheWrittenOne
      exact laysAtS_of _ _ (lays_nextHead_3531_thin h H Q test carryX item n₁ n₂ 339 Vd _ f w 346)
    · exact headsDigitsLayTheFoldCount h H Q test carryX item n₁ n₂ Vd ν st R f w Said
    · exact laysAtS_of _ _ (lookupLaysWhatStands h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) f w (by omega) true standsAtNumber _
        (fun p hp _ t hst => standingGivesTheClause p hp t hst))

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.callsBorderBelowTheHead
#print axioms ProofFile.Honest.K3.Term.digitsBorderBelowTheHead
#print axioms ProofFile.Honest.K3.Term.callsBorderAtTheHead
#print axioms ProofFile.Honest.K3.Term.digitsBorderAtTheHead
#print axioms ProofFile.Honest.K3.Term.replyBorderIsBehindNoLookup
#print axioms ProofFile.Honest.K3.Term.digitsLeaveTheAttentionReturn
#print axioms ProofFile.Honest.K3.Term.digitsLeaveTheLayersOwnRounds
#print axioms ProofFile.Honest.K3.Term.headDigitsTurnTheHeadsOwnPart
#print axioms ProofFile.Honest.K3.Term.lookupClauseAtTheCalls
#print axioms ProofFile.Honest.K3.Term.lookupClauseAtTheDigits
#print axioms ProofFile.Honest.K3.Term.lookupClauseAtTheHeadsDigits
#print axioms ProofFile.Honest.K3.Term.lookupClauseGivesSameBut
#print axioms ProofFile.Honest.K3.Term.stepPaysTheLookupClauseItself
#print axioms ProofFile.Honest.K3.Term.lookupClauseHoldsBehindTheStep
#print axioms ProofFile.Honest.K3.Term.keepsGiveTheLookupClauseAtTheBorder
#print axioms ProofFile.Honest.K3.Term.attentionReturnStaysPastTheDigits
#print axioms ProofFile.Honest.K3.Term.layersOwnRoundsStayPastTheDigits
#print axioms ProofFile.Honest.K3.Term.headsHearingStaysPastTheDigits
#print axioms ProofFile.Honest.K3.Term.lookupOpenItemsRidePast
#print axioms ProofFile.Honest.K3.Term.lookupBehindFromTheRidersColumns
#print axioms ProofFile.Honest.K3.Term.headsDigitsLayTheFoldCount
#print axioms ProofFile.Honest.K3.Term.lookupFormRidersAndKeepsBehindTheCalls
#print axioms ProofFile.Honest.K3.Term.lookupFormRidersAndKeepsBehindTheDigits
#print axioms ProofFile.Honest.K3.Term.lookupFormRidersAndKeepsBehindTheHeadsDigits
