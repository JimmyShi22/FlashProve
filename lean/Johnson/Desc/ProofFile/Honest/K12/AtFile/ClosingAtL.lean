-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/ClosingAtL.lean: the two debts of the first chain's closing
proximity test in the frame's form: `PlaysS` and `AcceptedS` (Thread/PaysS.lean), at that test's
number of the first chain's thread, general in the thread's letters and in what is said of the run,
each premise under its name. The job is any whose state on entry is `doorL`.

  `LetterAtL`        what the thread's letters owe, no run named: where the block stands, its seat,
                     that the half at the place is `proverSideOfProximityTest J`, the job's state on entry
  `FrontAtT`         what is asked at a stand, at the job patched there: `K12FrontD` less `enters`,
                     which is paid here
  `enters_at_L`      at a stand of the pair the way in returns, and the door agrees with it
  `acceptedS_at_L`   `AcceptedS` at every letter for a fall
  `plays_at_L`       `Plays`, and so `playsS_at_L`, at every `Said`
  `door_holds_at_L`  at every stand of the thread at that number, and every front that shows just the
                     stand's rounds, the door takes no default

Why not the general rung. A law whose clause `K12At.enters` is asked at the job itself (`saysYes_seat`,
K12/SaysYesSeat.lean, and whatever stands on it) cannot be met here: `doorL` has no targets and the way
in returns the verifier's, so `enter st = .ok (J.rec₀ …)` is false wherever a target is not 0. Here it
is asked at the job patched at the stand, which has the same half (ClosingStand.lean).

By what. `acceptedS_at_stand` (ClosingStand.lean), `door_at_thr` (ClosingThr.lean); `playsOn_k12`
(K12/PlaysK12.lean), `plays_of_playsOn` (Thread/FileRow.lean), `playsS_of` (Thread/PaysS.lean).
`PlaysOn` reads no state on entry, so `plays_at_L` needs no patch: what a part sends at the door is
what `testAll` shows at it.

Limits.
- `LetterAtL`, `FrontAtT`, the plan's `PlanPlays`, `RunPlays` and the trees' clause are premises;
  no thread is shown to meet them here. A theorem with a false premise says nothing.
- `FrontAtT` holds `FrontAsksD`, whose `door`, `claims`, `plain`, `pub` read the verifier's record, and
  `DataFront`, whose `allSay` reads its targets. That the honest words say them is the debt of the
  rows' items at this border, and of the tie of the thread's witness to the job's rows.
- The job's rows may be zeros where the sender's text refuses (`rowsL`, AtProof/JobL.lean). There
  `DataFront` fails. `hs` is asked at every stand, so one such stand makes it false, and then
  nothing is said of any run.
- Nothing says that a run reaches a stand of the thread at that number.
- `Said` is free: `AcceptedS` from the pair is weaker than from `Thr` alone only where `Said` says
  something.
- Nothing on completeness of the whole chain, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `door_holds_at_L`, `enters_at_L`, `acceptedS_at_L`, `plays_at_L`, `playsS_at_L` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread from `Thr` or `ThrS` as a premise, `Plays`, `PlaysS`, `AcceptedS` as ends.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingThr
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.Thread.FileRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts enterFinish)
open VerifiableInference.Desc.First (S)
open H2K.First (Plain)
open H2K.Pub (sgOf)
open ProofFile.Honest.K10 (Keeps wipeS)
open ProofFile.Honest.K12.AtProof (placeL)
open ProofFile.Honest.K12.Blind (doorL atHandL)
open Johnson.Prover.Link (PS)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **What the thread's letters owe, no run named.** L: the letters. b: the test's number. J: the
job. leave: the seat's way out. start, fall: the door's letters. -/
structure LetterAtL (L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) (b : ℕ)
    (J : TestJob (Local W₀ Rc Xi Tr) X) (leave : S → T12 → Except String S)
    (start : Local W₀ Rc Xi Tr → S) (fall : T12) (blk : Block S Cl)
    (pre t : List (Block S Cl)) : Prop where
  cut : L.bs = pre ++ blk :: t
  number : pre.length = b
  apart : ∀ y ∈ pre, y.place ≠ blk.place
  keeps : ∀ y ∈ pre, Keeps wipeS 0 y
  place : L.ps[b]? = some placeL
  starts : ∀ w, start w = L.first (L.pubOf w.x)
  door : J.rec₀ = doorL L.bs start blk.place fall
  seat : SeatOf blk J enterFinish leave
  half : (L.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s u rest, J.p.nums.stages = s :: u :: rest ∧ s.k = (sgOf s).h + (sgOf s).g

/-- **What is asked at a stand, at the job patched there; no challenge of the test is named.** -/
structure FrontAtT (J : TestJob (Local W₀ Rc Xi Tr) X) (leave : S → T12 → Except String S) (st : S)
    (m : Mid (Local W₀ Rc Xi Tr) X) (E : Env)
    (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J]) :
    Prop where
  agree : Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1)
  opens : ∃ depths src₀,
    (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))).map (·.1) = depths ∧
    OpensFit J (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds depths src₀ E.sent ∧
    OldAt E (J.trees₀ m.st.input (frontOf m) (restCoins J c.2.1).mem
      (J.first m.st.input (frontOf m) (restCoins J c.2.1))) src₀
  planOk : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).planOk = true
  form : formPubB J.p = true
  count : termLen J.p.nums.stages = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length
  asks : ∃ (K : Codes) (Dp : Plain) (cc : ℕ → ℕ → List UInt64) (R : PlainRows),
    planB J.p K Dp.ts.length = true ∧ FrontAsksD J m.st.input (frontOf m) K Dp ∧
      DataFront J m.st.input (frontOf m) (restCoins J c.2.1) Dp cc R
  leaves : ∀ t' rs gs, (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).decide (J.rec₀ m.st.input (frontOf m))
    rs gs = .ok t' → ∃ s', leave st t' = .ok s'

variable {L : ProofFile.Honest.FirstThread.Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M} {b : ℕ}
  {J : TestJob (Local W₀ Rc Xi Tr) X} {leave : S → T12 → Except String S}
  {start : Local W₀ Rc Xi Tr → S} {fall : T12} {blk : Block S Cl} {pre t : List (Block S Cl)}

/-- **At a stand of the thread at the test's number the way in returns, and the door agrees with it
but for targets, at every front that shows just the stand's rounds, and takes no default there.** -/
theorem door_holds_at_L (H : LetterAtL L b J leave start fall blk pre t) {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (h : Thr L.thread b k s m E) :
    ∃ R, enterFinish s = .ok R ∧ ∀ fr : Front X, fr.seen.rounds = m.seen →
      atHandL L.bs start blk.place m.st.input fr = true ∧
        Blind.Agree (J.rec₀ m.st.input fr) R := by
  obtain ⟨R, hR, hd⟩ := door_at_thr L pre t blk H.cut H.number H.apart H.keeps H.place start
    H.starts fall h
  refine ⟨R, hR, fun fr hr => ?_⟩
  rw [H.door]
  exact hd fr hr

/-- The clause `enters` of `K12SeatedStand`, from the pair. -/
theorem enters_at_L (H : LetterAtL L b J leave start fall blk pre t)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (k : Coins Bk) (s : S)
    (m : Mid (Local W₀ Rc Xi Tr) X) (E : Env) (h : ThrS L.thread Said b k s m E) :
    ∃ R, enterFinish s = .ok R ∧ Blind.Agree (J.rec₀ m.st.input (frontOf m)) R := by
  obtain ⟨R, hR, hd⟩ := door_holds_at_L H h.1
  exact ⟨R, hR, (hd (frontOf m) rfl).2⟩

/-- **The test's number of the thread is accepted, from the pair, at every letter for a fall.** -/
theorem acceptedS_at_L (H : LetterAtL L b J leave start fall blk pre t)
    (hb : L.thread.bs[b]? = some blk)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (hs : ∀ k st m E R (J' : TestJob (Local W₀ Rc Xi Tr) X),
      J' = atStand J m.st.input (frontOf m) R →
      ∀ c : RowCoins [(firstPart J' : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J'],
      ThrS L.thread Said b k st m E → enterFinish st = .ok R →
      lendRow Bk (Bk.rowsOf L.thread.chain) (k.look L.thread.chain) J'.p.place
        [(firstPart J' : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J'] 0 = .ok c →
      FrontAtT J' leave st m E c)
    (fl : ℕ → S → List Fmt.Drawn → Option String) : AcceptedS L.thread Said fl b :=
  acceptedS_at_stand L.thread Said b J enterFinish leave
    { member := ⟨blk, hb, H.seat⟩
      half := H.half
      stages := H.stages
      enters := enters_at_L H Said
      stands := fun k st m E R J' hJ' c hT he hc =>
        have F := hs k st m E R J' hJ' c hT he hc
        have e : J'.rec₀ m.st.input (frontOf m) = R := by
          rw [hJ']
          exact atStand_here _ _ _ _
        { agree := F.agree, opens := F.opens
          enters := by rw [e]; exact he
          planOk := F.planOk, form := F.form, count := F.count, asks := F.asks
          leaves := F.leaves } } fl

/-- **The test's number of the thread plays**, from the thread alone. sent: the trees sent in front.
P: the plan. HR: the run's three clauses at every stand. HT: the test's new trees are the thread's
tables. -/
theorem plays_at_L (H : LetterAtL L b J leave start fall blk pre t)
    (hb : L.thread.bs[b]? = some blk) (sent : ℕ) (s u : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: u :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (Pn : PlanPlays J s (u :: rest) sent)
    (HR : ∀ k st m E ds
      (c : RowCoins [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J]),
      Thr L.thread b k st m E → drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
      lendRow Bk (Bk.rowsOf L.thread.chain) (k.look L.thread.chain) J.p.place
        [(firstPart J : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J] 0 = .ok c →
      RunPlays J sent m E c)
    (HT : ∀ k st m E ds y cols, Thr L.thread b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Moved blk k m E ds y cols → L.thread.Trees (L.thread.fresh b) k y.2 (E.add y.1)) :
    Plays L.thread b :=
  plays_of_playsOn L.thread hb (A := Thr L.thread b) (B := fun _ _ _ _ => True)
    (playsOn_k12 L.thread.φ Bk L.thread.chain L.thread.ft L.thread.hs blk J enterFinish leave H.seat
      _ _ s u rest hst hk H.half sent Pn HR
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial))
    (fun _ _ _ _ h => h) HT

/-- **The same, from the pair.** -/
theorem playsS_at_L (Said : ℕ → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (h : Plays L.thread b) : PlaysS L.thread Said b :=
  playsS_of L.thread Said h

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.LetterAtL
#print axioms ProofFile.Honest.K12.FrontAtT
#print axioms ProofFile.Honest.K12.door_holds_at_L
#print axioms ProofFile.Honest.K12.enters_at_L
#print axioms ProofFile.Honest.K12.acceptedS_at_L
#print axioms ProofFile.Honest.K12.plays_at_L
#print axioms ProofFile.Honest.K12.playsS_at_L
