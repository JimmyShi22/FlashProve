--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/EveryAt.lean: THE ACCEPTANCE AT EVERY LIST THAT CAN BE SAMPLED
(`accepts_every_list`, ShapeAll.lean in this folder) LAID INTO THE FRAME's SENTENCES: what
`saysYes_seat` asks where the frame's letter holds (`K12At`, SaysYesK12.lean) follows, AT EVERY LIST
OF THE MEMBER's CHALLENGES, from a structure that names none of them; so a seated proximity test is
accepted (`Accepted`, Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) AT EVERY LETTER FOR A FALL:
this member states none. Definitions, statements and proofs.

  `accepts_every_rounds`   `accepts_every_list` at the block's own list of declared rounds, from
                 the two tests on the plan and the kind's own
  `K12Front`     WHAT IS ASKED WHERE THE LETTER HOLDS, NO CHALLENGE OF THE TEST NAMED: the clauses
                 agree · opens · enters of `K12At` · on the plan: `planB`, the kind's own test,
                 `formPubB`, the count of rounds · `FrontAsks` · `DataFront` at the coins that the
                 second part reads · the seat's leaving returns behind whatever the block accepts
  **`k12At_every`**   `K12Front` ⟹ `K12At` at every list that the block's rounds can sample
  `K12SeatedF`, **`accepted_every`**   the premises of `accepted_k12` (Seated.lean) with `K12Front`
                 in `K12At`'s stead ⟹ `Accepted T fall b` at every letter fall: so also beside
                 members that state a fall

Limits. `K12Front` is asked, at every stand of the thread and at whatever coins the book lends; no
member of it is given. NO LETTER EXCUSES A FRONT: three clauses of `FrontAsks` (the mark "tidy", no
written-out factor, the front's test on the open rows) read values of the open rows, which hang on
the challenges in front of the test; they are shown at no front that a run reaches; should one fail
at a stand of the thread, `K12SeatedF` is false, and the form to use is `accepted_k12` at a fall
that reads the state. Where "leaves" is paid: `leaves_ranges` (Ended.lean). Outside `drawsFit`
nothing is said. Where the first fold's fresh table has come earlier; three stages or more.
`Accepted` is a premise's form of the frame's. Nothing on completeness, on soundness or on what is
hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.OneToAll
import Johnson.Desc.ProofFile.Honest.K12.Seated
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.K12.Law.StepGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- `accepts_every_list` at the block's own list of declared rounds. -/
theorem accepts_every_rounds (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (K : Codes)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (hF : formPubB J.p = true)
    (hp : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true) (Sf : FrontAsks J w fr K Dp)
    (Dt : DataFront J w fr C Dp c R) (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true) :
    ∃ t', (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ w fr)
      ((testAll J w fr C (byNo ds)).rs.map noDigest) (testAll J w fr C (byNo ds)).gs = .ok t' := by
  rw [H2K.Sw.k12_rounds guardedProximityTestParts J.p hp] at hd
  cases hs : J.p.nums.stages with
  | nil =>
    unfold formPubB at hF
    rw [hs] at hF
    cases hF
  | cons a l =>
    cases l with
    | nil =>
      unfold formPubB at hF
      rw [hs] at hF
      cases hF
    | cons next rest =>
      exact accepts_every_list J w fr C K Dp c R hP a next rest hs (formPub_of_B _ _ _ _ hs hF) Sf
        Dt ds hd

/-- **What is asked where the letter holds; no challenge of the test is named.** -/
structure K12Front (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (st : S) (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart J : Part V W X), restPart J]) : Prop where
  agree : Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)
  opens : ∃ depths src₀,
    (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))).map (·.1) = depths ∧
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAt E (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))) src₀
  enters : enter st = .ok (J.rec₀ m.st.input (frontOf m))
  planOk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true
  form : formPubB J.p = true
  count : termLen J.p.nums.stages = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length
  asks : ∃ (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows),
    planB J.p K Dp.ts.length = true ∧ FrontAsks J m.st.input (frontOf m) K Dp ∧
      DataFront J m.st.input (frontOf m) (restCoins J c.2.1) Dp cc R
  leaves : ∀ t' rs gs, (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ m.st.input (frontOf m))
    rs gs = .ok t' → ∃ s', leave st t' = .ok s'

/-- **`K12At` at every list that the block's rounds can sample.** -/
theorem k12At_every (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (st : S) (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : K12Front J enter leave st m E c) (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true) :
    K12At J enter leave st m E ds c := by
  obtain ⟨K, Dp, cc, R, hP, Sf, Dt⟩ := h.asks
  obtain ⟨t', ht⟩ := accepts_every_rounds J _ _ _ K Dp cc R hP h.form h.planOk Sf Dt ds hd
  exact ⟨h.agree, (length_test J _ _ _ _).trans h.count, h.opens, h.enters, t', ht,
    h.leaves t' _ _ ht⟩

/-- The premises of `accepted_k12`, with `K12Front` in `K12At`'s stead. -/
structure K12SeatedF (T : Thread Bk S Cl V W X Pb) (b : ℕ) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S) : Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g
  stands : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    Thr T b k st m E →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    K12Front J enter leave st m E c

/-- **It is accepted, whatever the letter for a fall says**: also where it says nothing. -/
theorem accepted_every (T : Thread Bk S Cl V W X Pb) (b : ℕ) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (h : K12SeatedF T b J enter leave) (fall : ℕ → S → List Fmt.Drawn → Option String) :
    Accepted T fall b :=
  accepted_k12 T b J enter leave fall
    ⟨h.member, h.half, h.stages, fun k st m E ds c hT hd _ hc =>
      k12At_every J enter leave st m E c (h.stands k st m E c hT hc) ds hd⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.accepts_every_rounds
#print axioms ProofFile.Honest.K12.k12At_every
#print axioms ProofFile.Honest.K12.accepted_every
