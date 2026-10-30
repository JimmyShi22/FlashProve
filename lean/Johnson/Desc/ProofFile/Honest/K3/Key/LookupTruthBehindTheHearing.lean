-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
Johnson/Desc/ProofFile/Honest/K3/Key/LookupTruthBehindTheHearing.lean: (K-P2) THE EXCHANGE WITHOUT A THREAD, JOINED. Behind the
verifier's hearing of what a lookup's seated row has played (`BehindYes`, Honest/K3/Law/Joined.lean), from a ledger that is
made anew for the lookup: THE TABLE's THREE SENTENCES `FormsObjects`, `WorthPlanes`, `WorthKeys`
(Johnson/Desc/Key/KeyK3Items.lean) HOLD, at every table of homes and all mask entries by home that read as the coins spent.
It pays five of the premises of Honest/K3/Key/LookupLeavesTheThreeSentences.lean out of the hearing's return. General in
the face, the summands and the reader of the input. Theorems with proofs.

  `heardFormsAreScoped`           behind a hearing from a ledger whose count stands at 0: the forms left, the forms beside the
                                  parts' points and the leads of the three claims name slots of the lookup alone, and no
                                  entry of a virtual row
  `heardKeyFormsAreTheCourses`    what was heard has a form a part, and it is the course's
  `lookupTruthAtACourse`          the three sentences at a course, from what the hearing's return hands of it
  `lookupTruthBehindTheHearing`   **the three sentences**, from `BehindYes`

Hypotheses that remain, by name. ledger: the ledger in front has room for the lookup from 0 on. hearing; behindYes. lawful:
the summands are `Lawful` at every course of these letters (at a key file's record:
Honest/K3/FastLaw/PartsKey.lean's `lawful_key_fast` under `KeyMidHyp`). masks: at every such course whose coins are the
row's, the mask under each slot is the coin spent (E2E/Lookup/Key/LedgerIsTheKeyBook.lean). reads: the mask entry at slot
j's home reads as the mask at j: THIS CARRIES CONTENT AND IS PAID IN NO FILE YET: which number stands under a slot is
E2E/Lookup/Key/LedgerIsTheKeyBook.lean's `theLedgerIsTheKeyBook`; that the owner's message holds its coin at that number is
the debt `SenderLaysItsCoinsInTheOrderOfTaking` there, of the two owners' senders. planesAre, keysAre: the two letters
against the table's sums (Honest/K3/Key/LookupRecordReadsAsTheSentences.lean). That the key file's sub-protocol hears from
such a ledger, made anew at each lookup, and lays what was heard: E2E/Lookup/Key/LookupStepLaysTheHearingAtTheKey.lean.

Limits. Implications. No thread, no state, no book. Nothing says here that a run of the offline prover meets the premises.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Key.LookupLeavesTheThreeSentences
import Johnson.Desc.ProofFile.Honest.K3.Law.Joined

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K3.Key
open OnBytes (E zeroE oneE addE mulE subE Slot Tensor)
open OnBytes.Slice (GE readE)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV HeardG PlaneClaim hearV planesV toHeardG)
open VerifiableInference.Desc.Key (closedAt planeSum sumE FormsObjects WorthPlanes WorthKeys)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Parts (ScopedG heard_names hearV_ne planesV_ne row_names in_empty in_slot in_ofConst)

/-! ## 1 What the forms name -/

/-- **Behind a hearing from a ledger whose count stands at 0, every form names slots of the lookup alone.** -/
theorem heardFormsAreScoped (face : LFace) {front behind closed : Fork} {rounds : List Fmt.RoundView} {heard : HeardV}
    {claims : List PlaneClaim} (atZero : front.next = 0)
    (hearing : hearV face front rounds = some (heard, behind))
    (closing : planesV face heard behind = some (claims, closed)) :
    (∀ a ∈ heard.rows.toList, ScopedG face.slots a) ∧ (∀ k ∈ heard.keys, ScopedG face.slots k.2) ∧
      ∀ c ∈ claims, ScopedG face.slots c.lead := by
  obtain ⟨hok, hm⟩ := hearV_messages hearing
  have h2 := two_le_planes_of_ok _ hok
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := heard_names h2 hm
  obtain ⟨m1, m2, m3⟩ := hearV_ne hearing
  rw [atZero, Nat.zero_add] at n1 n2 n3 n5 n7
  refine ⟨fun a ha => ⟨m1 a ha, fun t ht => (n1 a ha t ht).2⟩,
    fun k hk => ⟨m2 k hk, fun t ht => (n2 k hk t ht).2⟩, fun c hc => ⟨planesV_ne hearing closing c hc, ?_⟩⟩
  have hv := closing
  unfold planesV at hv
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hv
  obtain ⟨y1, y2⟩ := y
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, _⟩ := e
  have hlead := (row_names (lo := 0) (hi := face.slots) hy n3 (in_empty _ _) (Nat.zero_le _) n5).1
  rw [← e1] at hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact fun t ht => (hlead t ht).2
  · exact fun t ht => (in_slot (lo := 0) (Nat.zero_le _) n7 t ht).2
  · exact fun t ht => (in_ofConst 0 face.slots _ t ht).2

/-! ## 2 The forms beside the parts' points -/

/-- **What was heard has a form a part, and it is the course's; the point beside it is the run's.** -/
theorem heardKeyFormsAreTheCourses {W : Type} (course : Course W) {heard : HeardV} (heardIs : HeardIs course heard)
    (points : PointsAgree course.f heard course.a.base (course.t.heard ++ course.ds)) :
    heard.keys.length = course.f.parts.length ∧
      ∀ x ∈ heard.keys.zipIdx, x.1.2 = course.form (.key x.2 (course.f.parts.getD x.2 0)) ∧
        x.1.1 = (ptsOf course.f course.a.base (course.t.heard ++ course.ds)).keyPt x.2
          (course.f.parts.getD x.2 0) := by
  have hl : heard.keys.length = course.f.parts.length := by
    have := congrArg List.length heardIs.keys
    simpa using this
  refine ⟨hl, fun x hx => ?_⟩
  have hget : heard.keys[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hlt : x.2 < course.f.parts.length := by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.1 hget).1
  have hpart : course.f.parts.zipIdx[x.2]? = some (course.f.parts.getD x.2 0, x.2) := by
    rw [List.getElem?_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp
  constructor
  · have e := congrArg (fun l => l[x.2]?) heardIs.keys
    simp only [List.getElem?_map, hget, hpart, Option.map_some] at e
    exact Option.some.inj e
  · have e := congrArg (fun l => l[x.2]?) points.keys
    simp only [List.getElem?_map, hget, hpart, Option.map_some] at e
    exact Option.some.inj e

/-! ## 3 The three sentences -/

/-- **The three sentences at a course**: from what the hearing's return hands of a course. -/
theorem lookupTruthAtACourse {W : Type} (course : Course W) {front behind : Fork} {rounds : List Fmt.RoundView}
    {heard : HeardV} (ledger : LedgerIn course.f 0 front)
    (hearing : hearV course.f front rounds = some (heard, behind)) (heardIs : HeardIs course heard)
    (points : PointsAgree course.f heard course.a.base (course.t.heard ++ course.ds))
    (planes : List (E × E) → GE) (keys : Nat → Array E → GE) (left : Left course planes keys heard behind)
    (mask : Nat → GE) (masks : MasksAre course mask)
    (home : Array Slot) (maskEntry : Slot → E) (homes : home.size = course.f.slots)
    (reads : ∀ j, j < home.size → readE (maskEntry (home.getD j default)) = mask j)
    (bit : Nat → E) (planesAre : ∀ pairs, planes pairs = readE (planeSum course.f pairs bit))
    (key : Nat → Nat → E)
    (keysAre : ∀ part, part < course.f.parts.length →
      readE heard.alpha - keys part (course.pts.keyPt part (course.f.parts.getD part 0)) =
        readE (sumE (2 ^ course.f.parts.getD part 0) fun k =>
          mulE ((Tensor.eq (course.pts.keyPt part (course.f.parts.getD part 0)).toList.reverse).entry k)
            (subE heard.alpha (key part k)))) :
    FormsObjects ReadAlike course.f (toHeardG heard) behind home maskEntry ∧
      WorthPlanes ReadAlike course.f (toHeardG heard) behind home maskEntry bit ∧
      WorthKeys ReadAlike course.f (toHeardG heard) behind home maskEntry key := by
  have room : front.next + course.f.slots ≤ front.ns := by
    rw [ledger.next]
    exact ledger.room
  have free : ∀ j, front.next ≤ j → j < front.next + course.f.slots → ¬ Filled front j := by
    intro j h1 h2
    rw [ledger.next] at h2
    exact ledger.free j h1 h2
  obtain ⟨claims, closed, closing, three, closes⟩ :=
    closingReturnsBehindTheHearing course.f ledger.sized room free hearing
  obtain ⟨scopedRows, scopedKeys, scopedLeads⟩ := heardFormsAreScoped course.f ledger.next hearing closing
  rw [← homes] at scopedRows scopedKeys scopedLeads
  obtain ⟨asMany, forms⟩ := heardKeyFormsAreTheCourses course heardIs points
  have sizedBehind : Sized behind := (hearV_later hearing).sized ledger.sized
  have halpha : rd course.pts.alpha = readE heard.alpha := by
    rw [points.alpha]
    rfl
  refine ⟨lookupLeavesFormsObjects course planes keys home maskEntry mask left masks closing closes reads
      scopedRows,
    lookupLeavesWorthPlanes course planes keys home maskEntry mask left masks sizedBehind closing three closes
      reads scopedLeads bit (fun c _ => planesAre c.pairs),
    lookupLeavesWorthKeys course planes keys home maskEntry mask left masks closing closes reads scopedKeys key
      asMany (fun x hx => (forms x hx).1) fun x hx => ?_⟩
  have hget : heard.keys[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have hlt : x.2 < course.f.parts.length := by
    have h := (List.getElem?_eq_some_iff.1 hget).1
    rw [asMany] at h
    exact h
  have hpoint : x.1.1 = course.pts.keyPt x.2 (course.f.parts.getD x.2 0) := (forms x hx).2
  rw [halpha, hpoint]
  exact keysAre x.2 hlt

/-- **BEHIND THE HEARING OF WHAT THE LOOKUP's SEATED ROW HAS PLAYED, THE TABLE's THREE SENTENCES HOLD.** -/
theorem lookupTruthBehindTheHearing {V₁ W₁ X₁ W : Type} (lookup : At) (jobs : LookJobs W) (wit : W₁ → W)
    (mid : Mid W₁ X₁) (draws : List Fmt.Drawn)
    (coins : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ jobs wit lookup).parts)
    {front behind : Fork} {rounds : List Fmt.RoundView} {heard : HeardV}
    (ledger : LedgerIn lookup.face 0 front) (hearing : hearV lookup.face front rounds = some (heard, behind))
    (behindYes : BehindYes lookup jobs 0 wit mid draws coins heard behind)
    (planes : List (E × E) → GE) (keys : Nat → Array E → GE)
    (lawful : ∀ stageCoins, Lawful (courseAt lookup jobs 0 wit mid draws stageCoins) planes keys)
    (mask : Nat → GE)
    (masks : ∀ stageCoins, CoinsAre (V := Unit) (courseAt lookup jobs 0 wit mid draws stageCoins)
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ jobs lookup) coins) →
      MasksAre (courseAt lookup jobs 0 wit mid draws stageCoins) mask)
    (home : Array Slot) (maskEntry : Slot → E) (homes : home.size = lookup.face.slots)
    (reads : ∀ j, j < home.size → readE (maskEntry (home.getD j default)) = mask j)
    (bit : Nat → E) (planesAre : ∀ pairs, planes pairs = readE (planeSum lookup.face pairs bit))
    (key : Nat → Nat → E)
    (keysAre : ∀ part, part < lookup.face.parts.length →
      readE heard.alpha - keys part
          ((ptsOf lookup.face lookup.base (mid.st.heard ++ draws)).keyPt part (lookup.face.parts.getD part 0)) =
        readE (sumE (2 ^ lookup.face.parts.getD part 0) fun k =>
          mulE ((Tensor.eq ((ptsOf lookup.face lookup.base (mid.st.heard ++ draws)).keyPt part
            (lookup.face.parts.getD part 0)).toList.reverse).entry k) (subE heard.alpha (key part k)))) :
    FormsObjects ReadAlike lookup.face (toHeardG heard) behind home maskEntry ∧
      WorthPlanes ReadAlike lookup.face (toHeardG heard) behind home maskEntry bit ∧
      WorthKeys ReadAlike lookup.face (toHeardG heard) behind home maskEntry key := by
  obtain ⟨stageCoins, coinsAre, heardIs, points, _, leftOf⟩ := behindYes
  exact lookupTruthAtACourse (courseAt lookup jobs 0 wit mid draws stageCoins) ledger hearing heardIs points planes
    keys (leftOf planes keys (lawful stageCoins)) mask (masks stageCoins coinsAre) home maskEntry homes reads bit
    planesAre key keysAre

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.heardFormsAreScoped
#print axioms ProofFile.Honest.K3.Key.heardKeyFormsAreTheCourses
#print axioms ProofFile.Honest.K3.Key.lookupTruthAtACourse
#print axioms ProofFile.Honest.K3.Key.lookupTruthBehindTheHearing
