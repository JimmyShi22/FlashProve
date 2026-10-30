-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingStand.lean: a proximity test whose job's state on
entry agrees with the verifier's but for the rows' targets. The job's own clauses `K12At.enters` and
`DataAsks.allSay` ask true targets. So at each stand the job is patched at that one input and front:
the verifier's record there, its own state everywhere else. The patched job and the job have one
half, since the prover's text does not read targets, so the frame's sentence "its step accepts" is
had at the job from what is shown at the patched job. General in the job, the thread, the seat and
the letter for a fall. The patch is one text for whoever needs it.

  `recAtStand`, `atStand`   the state on entry and the job with one stand patched
  `atStand_here`           there it is the record handed
  `recAtStand_agrees`      where the record agrees with the job's state there, the patched state
                           agrees with the job's at every input and front
  `testHalf_atStand`       so the two halves are one
  `seatOf_atStand`         a seat reads the job's numbers alone
  `saysYes_at_stand`       `SaysYes` at the job, from `K12At` at the job patched at each stand
  `accepts_every_roundsD`  `accepts_every_listD` (ClosingAccepts.lean) at the block's own rounds
  `K12FrontD`, `k12At_everyD`   what is asked at a stand, no challenge of the test named: `K12At`
                           at every list that the block's rounds can sample
  `acceptedS_of_says`      from `SaysYes` to `AcceptedS` (Thread/PaysS.lean)
  `K12SeatedStand`, `acceptedS_at_stand`   the premises on a thread's letters, and `AcceptedS` at
                           every letter for a fall

By what. `testHalf_one` (K12/Blind/All.lean); `saysYes_seat` (K12/SaysYesSeat.lean) called at one
stand at a time, with the letter "just this stand"; `accepts_every_listD`, `length_test`
(K12/TermLen.lean), `k12_rounds` (Johnson/Desc/K12/FrameLaws.lean), `formPub_of_B`
(K12/FormPubAt.lean), `step_takes` (Thread/Ties.lean).

Limits.
- `recAtStand` decides an equation of inputs and of fronts by classical choice: it is no function to
  run, and a stand spoken of is fixed outside it. No prover's side is patched: the half at the
  chain's place stays `proverSideOfProximityTest J`; the patched job is a term of comparison alone.
- `K12SeatedStand` is asked; no thread is shown to meet it here. Its clause `stands` holds all of
  `K12FrontD`.
- Where the record does not agree with the job's state at the stand nothing is said.
- Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `K12SeatedStand`, `acceptedS_at_stand`, `acceptedS_of_says` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread from `ThrS` as a premise, `AcceptedS` as an end.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingAccepts
import Johnson.Desc.ProofFile.Honest.K12.Blind.All
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 The patch -/

open Classical in
/-- **The state on entry with one stand patched**: T at the input w₀ and the front fr₀; the job's own
state everywhere else. -/
noncomputable def recAtStand (J : TestJob W X) (w₀ : W) (fr₀ : Front X) (T : T12) :
    W → Front X → T12 :=
  fun w fr => if w = w₀ ∧ fr = fr₀ then T else J.rec₀ w fr

/-- **The job with one stand patched.** -/
noncomputable def atStand (J : TestJob W X) (w₀ : W) (fr₀ : Front X) (T : T12) : TestJob W X :=
  { J with rec₀ := recAtStand J w₀ fr₀ T }

theorem atStand_here (J : TestJob W X) (w₀ : W) (fr₀ : Front X) (T : T12) :
    (atStand J w₀ fr₀ T).rec₀ w₀ fr₀ = T := by
  show recAtStand J w₀ fr₀ T w₀ fr₀ = T
  unfold recAtStand
  exact if_pos ⟨rfl, rfl⟩

theorem recAtStand_agrees {J : TestJob W X} {w₀ : W} {fr₀ : Front X} {T : T12}
    (h : Blind.Agree (J.rec₀ w₀ fr₀) T) (w : W) (fr : Front X) :
    Blind.Agree (J.rec₀ w fr) (recAtStand J w₀ fr₀ T w fr) := by
  unfold recAtStand
  split
  · rename_i e
    obtain ⟨rfl, rfl⟩ := e
    exact h
  · exact rfl

/-- **The patched job and the job have one half.** -/
theorem testHalf_atStand {J : TestJob W X} {w₀ : W} {fr₀ : Front X} {T : T12}
    (h : Blind.Agree (J.rec₀ w₀ fr₀) T) :
    (proverSideOfProximityTest (atStand J w₀ fr₀ T) : Placed V W X) = proverSideOfProximityTest J :=
  Blind.testHalf_one J (recAtStand J w₀ fr₀ T) (recAtStand_agrees h)

theorem seatOf_atStand {b : Block S Cl} {J : TestJob W X} {enter : S → Except String T12}
    {leave : S → T12 → Except String S} (hb : SeatOf b J enter leave) (w₀ : W) (fr₀ : Front X)
    (T : T12) : SeatOf b (atStand J w₀ fr₀ T) enter leave :=
  ⟨hb.place, hb.rounds, hb.oracles, hb.decide⟩

/-! ## 2 The sentence, stand by stand -/

/-- **`SaysYes` at a job whose state on entry agrees with the verifier's but for targets.** HE:
wherever A holds the way in returns a record that agrees with the job's state at the member's front.
HA: `K12At` at the job patched there, at that record. -/
theorem saysYes_at_stand (φ : Face V W Pb) (Bk : ProverCoinCounts) (chain ft : ℕ) (hs : List (Placed V W X))
    (b : Block S Cl) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (hb : SeatOf b J enter leave)
    (fall : S → List Fmt.Drawn → Option String) (A : Coins Bk → S → Mid W X → Env → Prop)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J))
    (HE : ∀ k st m E, A k st m E → ∃ T, enter st = .ok T ∧
      Blind.Agree (J.rec₀ m.st.input (frontOf m)) T)
    (HA : ∀ k st m E ds T (J' : TestJob W X), J' = atStand J m.st.input (frontOf m) T →
      ∀ c : RowCoins [(firstPart J' : Part V W X), restPart J'],
      A k st m E → enter st = .ok T →
      drawsFit (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds ds = true → fall st ds = none →
      lendRow Bk (Bk.rowsOf chain) (k.look chain) J'.p.place
        [(firstPart J' : Part V W X), restPart J'] 0 = .ok c →
      K12At J' enter leave st m E ds c) :
    SaysYes φ Bk chain ft hs b fall A := by
  intro k₀ s₀ m₀ E₀ ds₀ l₀ y₀ c₀ hA hd hq hfl hl hy hc
  obtain ⟨T, hT, hAg⟩ := HE k₀ s₀ m₀ E₀ hA
  obtain ⟨J', hJ'⟩ : ∃ J', J' = atStand J m₀.st.input (frontOf m₀) T := ⟨_, rfl⟩
  have hh : (proverSideOfProximityTest J' : Placed V W X) = proverSideOfProximityTest J := by
    rw [hJ']
    exact testHalf_atStand hAg
  have hp : J'.p = J.p := by
    rw [hJ']
    rfl
  have hseat : SeatOf b J' enter leave := by
    rw [hJ']
    exact seatOf_atStand hb _ _ T
  have hst' : J'.p.nums.stages = s :: t :: rest := by
    rw [hp]
    exact hst
  have hf' : (hs.find? fun g => g.place == J'.p.place) = some (proverSideOfProximityTest J') := by
    rw [hh, hp]
    exact hf
  have key := saysYes_seat φ Bk chain ft hs b J' enter leave hseat fall
    (fun k st m E => k = k₀ ∧ st = s₀ ∧ m = m₀ ∧ E = E₀) s t rest hst' hk hf' (by
      rintro k st m E ds c ⟨rfl, rfl, rfl, rfl⟩ hdr hfall hlend
      exact HA k st m E ds T J' hJ' c hA hT hdr hfall hlend)
  exact key k₀ s₀ m₀ E₀ ds₀ l₀ y₀ c₀ ⟨rfl, rfl, rfl, rfl⟩ hd hq hfl hl hy hc

/-! ## 3 At every list of challenges -/

/-- `accepts_every_listD` at the block's own list of declared rounds. -/
theorem accepts_every_roundsD (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (K : Codes)
    (Dp : Plain) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hP : planB J.p K Dp.ts.length = true) (hF : formPubB J.p = true)
    (hp : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true) (Sf : FrontAsksD J w fr K Dp)
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
      exact accepts_every_listD J w fr C K Dp c R hP a next rest hs (formPub_of_B _ _ _ _ hs hF) Sf
        Dt ds hd

/-- **What is asked at a stand; no challenge of the test is named.** -/
structure K12FrontD (J : TestJob W X) (enter : S → Except String T12)
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
    planB J.p K Dp.ts.length = true ∧ FrontAsksD J m.st.input (frontOf m) K Dp ∧
      DataFront J m.st.input (frontOf m) (restCoins J c.2.1) Dp cc R
  leaves : ∀ t' rs gs, (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ m.st.input (frontOf m))
    rs gs = .ok t' → ∃ s', leave st t' = .ok s'

/-- **`K12At` at every list that the block's rounds can sample.** -/
theorem k12At_everyD (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (st : S) (m : Mid W X) (E : Env)
    (c : RowCoins [(firstPart J : Part V W X), restPart J])
    (h : K12FrontD J enter leave st m E c) (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true) :
    K12At J enter leave st m E ds c := by
  obtain ⟨K, Dp, cc, R, hP, Sf, Dt⟩ := h.asks
  obtain ⟨t', ht⟩ := accepts_every_roundsD J _ _ _ K Dp cc R hP h.form h.planOk Sf Dt ds hd
  exact ⟨h.agree, (length_test J _ _ _ _).trans h.count, h.opens, h.enters, t', ht,
    h.leaves t' _ _ ht⟩

/-! ## 4 At a thread -/

/-- From `SaysYes` at a letter that the pair gives, `AcceptedS`. -/
theorem acceptedS_of_says (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} {fall : ℕ → S → List Fmt.Drawn → Option String}
    {fl : S → List Fmt.Drawn → Option String} {A : Coins Bk → S → Mid W X → Env → Prop}
    (hblk : T.bs[b]? = some blk) (h : SaysYes T.φ Bk T.chain T.ft T.hs blk fl A)
    (hA : ∀ k s m E, ThrS T Said b k s m E → A k s m E)
    (hf : ∀ s ds, fall b s ds = none → fl s ds = none) : AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hThr hd hst hn hMv
  rw [hblk] at hblk'
  cases hblk'
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hMv'
  obtain ⟨s', n, hs⟩ := h k s m E ds l y cols (hA k s m E hThr) hd hst (hf s ds hn) hl hy hc
  have hn' : n = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hn'
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hMv, hs⟩

/-- **The premises on a thread's letters**, where the job's state on entry agrees with the verifier's
but for targets. -/
structure K12SeatedStand (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    (b : ℕ) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) : Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g
  enters : ∀ k st m E, ThrS T Said b k st m E → ∃ R, enter st = .ok R ∧
    Blind.Agree (J.rec₀ m.st.input (frontOf m)) R
  stands : ∀ k st m E R (J' : TestJob W X), J' = atStand J m.st.input (frontOf m) R →
    ∀ c : RowCoins [(firstPart J' : Part V W X), restPart J'],
    ThrS T Said b k st m E → enter st = .ok R →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J'.p.place
      [(firstPart J' : Part V W X), restPart J'] 0 = .ok c →
    K12FrontD J' enter leave st m E c

/-- **It is accepted, from the pair, whatever the letter for a fall says.** -/
theorem acceptedS_at_stand (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    (b : ℕ) (J : TestJob W X) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (h : K12SeatedStand T Said b J enter leave)
    (fall : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS T Said fall b := by
  obtain ⟨s, t, rest, hst, hk⟩ := h.stages
  obtain ⟨blk, hblk, hseat⟩ := h.member
  exact acceptedS_of_says T Said hblk
    (saysYes_at_stand T.φ Bk T.chain T.ft T.hs blk J enter leave hseat (fall b) (ThrS T Said b) s t
      rest hst hk h.half h.enters
      fun k st m E ds R J' hJ' c hT he hd _ hc =>
        k12At_everyD J' enter leave st m E c (h.stands k st m E R J' hJ' c hT he hc) ds hd)
    (fun _ _ _ _ x => x) fun _ _ x => x

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.recAtStand
#print axioms ProofFile.Honest.K12.atStand
#print axioms ProofFile.Honest.K12.atStand_here
#print axioms ProofFile.Honest.K12.recAtStand_agrees
#print axioms ProofFile.Honest.K12.testHalf_atStand
#print axioms ProofFile.Honest.K12.seatOf_atStand
#print axioms ProofFile.Honest.K12.saysYes_at_stand
#print axioms ProofFile.Honest.K12.accepts_every_roundsD
#print axioms ProofFile.Honest.K12.K12FrontD
#print axioms ProofFile.Honest.K12.k12At_everyD
#print axioms ProofFile.Honest.K12.acceptedS_of_says
#print axioms ProofFile.Honest.K12.K12SeatedStand
#print axioms ProofFile.Honest.K12.acceptedS_at_stand
