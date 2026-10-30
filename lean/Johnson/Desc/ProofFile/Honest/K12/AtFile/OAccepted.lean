-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OAccepted.lean: the frame's sentence «it is accepted»
at the proximity test on G_omega, member 10 of the proof file's shared thread: the half behind the guard, the
first fold sending its own table. General in the letter that keeps the field.

  `acceptedS_at_own`, `playsS_at_own`   the two sentences at a member at which a test stands whose first fold sends
                 its own table, behind the guard. General in the thread, the letter, the job and the number of
                 trees in front
  `jobDoorO`   the job at the seated place, with the state on entry that the door makes of the field
  `StandO`   the premises on the thread and its letter that the two statements share, each under a name
  `opened_at_ten`   where the thread stands and the letter gives the field, the field is some
  `rec_door`, `door_numbers`   the job's state on entry is the door's; the job's numbers at the seated place
  `accepts_door`, `enters_door`, `count_door`   three fields of `K12AtO` at the job
  `acceptedS_head_O`   `AcceptedS` at member 10; `PlaysS` is OPlays.lean's

The premises, and who pays.
  h, hO, hB     the head; the seated place; the book is the maker's
  hb            the plan's eight blocks
  `StandO`: member, seat, half: the member is the seated test and the half at its place is the job's behind the
                guard: `halfO` (K12/AtProof/HalfO.lean) lays that half at the filling. AT THE FILLING, NOT READ
                THROUGH: this statement stands at the base prover, and the crossing to the term is another law's.
                trees, taken, table, fixedOne, treesU, cover: the thread's fields on trees: `tableShared`,
                `fixedShared` (TableShared.lean); `trees_shared`, `sent_shared` (TableLines.lean)
                front, ahead, ft, chain, begun: as `enters_at_nine` (FieldsAtU.lean)
  hfield        the field holds the columns that the thread's fold read: the letter's, `opened_of_saidField`
  hsay          `SaysAt` at every coin lent, at a stand: what the rows taken in say of the words

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the thread's pair is a premise, `AcceptedS` and `PlaysS` the ends.
- That a stand is reached, that `hsay` can be paid at any run, is not said here.
- Behind a guard `Plays` alone cannot hold: a half behind the guard errs at a field that is none. So the
  sentences stand at a letter that gives the field (hfield); the door's value at the columns is `enters`'s.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OFields
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtTest
import Johnson.Desc.ProofFile.Honest.K12.TreesAtTen
import AtFullSide.K12.LaterJobs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (jobOmega sendPlace treesU)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Own (K12AtO saysYes_seat_guarded)
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place noDigest)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks first frontBlock)
open Desc.K14.Honest (Like)
open Johnson.G (proofSendsFull)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (ManyJob jobAtOmega doorOmegaF colsOpened sentOf SaysAt nums_head_O)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **It is accepted, at a test whose first fold sends its own table, behind the guard**, where what is
said of the run gives the field and the pair gives `K12AtO`. -/
theorem acceptedS_at_own (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g) (n a₁ : ℕ)
    (h1 : depthAt J 1 = some a₁) (hr1 : 1 < (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length)
    (hf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hop : ∀ k st m E, ThrS T Said b k st m E → m.opened.isSome = true)
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (HA : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E → drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
      fall b st ds = none →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      K12AtO J enter leave n st m E ds c) :
    AcceptedS T Said fall b :=
  acceptedS_of_saysYes T Said hblk
    (saysYes_seat_guarded T.φ Bk T.chain T.ft T.hs blk J enter leave hseat (fall b) (ThrS T Said b)
      s t rest hst hk n a₁ h1 hr1 hf hop HA) fun _ _ h => h

/-- **It plays, behind the guard**, where what is said of the run gives the field. -/
theorem playsS_at_own (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
    {b : ℕ} {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J : Placed V W X).needsField)
    (hop : ∀ k s m E, ThrS T Said b k s m E → m.opened.isSome = true) (sent : ℕ)
    (P : PlanPlays J s (t :: rest) sent) (hsent : treesTo T.bs b = sent)
    (hA : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1))
    (hold : ∀ k st m E, ThrS T Said b k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
        ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hT : ∀ k st m E ds y cols, ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    PlaysS T Said b := by
  have f1 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == J.p.place) =
      some (proverSideOfProximityTest J) := by
    have e : ((proverSideOfProximityTest J : Placed V W X).place == J.p.place) = true := beq_self_eq_true _
    simp [List.find?, e]
  have f2 : ([(proverSideOfProximityTest J : Placed V W X)].find? fun g => g.place == blk.place) =
      some (proverSideOfProximityTest J) := by
    rw [hseat.place]
    exact f1
  have P0 : PlaysOn T.φ Bk T.chain T.ft [proverSideOfProximityTest J] blk (ThrS T Said b) (fun _ _ _ _ => True) :=
    playsOn_k12 T.φ Bk T.chain T.ft _ blk J enter leave hseat _ _ s t rest hst hk f1 sent P
      (fun k st m E _ c u _ hc =>
        ⟨hA k st m E c u hc, by
          obtain ⟨⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩, -⟩ := u
          rw [h3, hsent], hold k st m E u⟩)
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  have P1 := playsOn_guarded (hs := T.hs) (proverSideOfProximityTest J) hf f2 hop P0
  intro blk' hblk' k st m E ds l u hd hs hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨y, cols, hy, hc, -⟩ := P1 k st m E ds l u hd hs hl
  have hMv : T.Moved blk k m E ds y cols := ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨y, cols, hMv, hT k st m E ds y cols u hd hMv⟩

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}
  {W₀ Rc X₀ Cl V Pb : Type} {Bk : ProverCoinCounts}

/-- The job's state on entry is the door's. -/
theorem rec_door (Zp : ProofFile.Pub) (Np : H2U.Places4) (pO : P12) (bs : List (Block St Unit))
    (wts : W₀ → Weights) (rnd : Rc → TableRand) :
    (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).rec₀ =
      doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U (fun w => w.key) colsOpened :=
  rfl

/-- **What the two statements ask of the thread and its letter.** -/
structure StandO (Zp : ProofFile.Pub) (Np : H2U.Places4) (pO : P12)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb) (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit)) (blk : Block St Cl) : Prop where
  member : T.bs[10]? = some blk
  seat : SeatOf blk (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest
    (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
    VerifiableInference.Desc.K12.Seat.leave
  half : (T.hs.find? fun g => g.place == blk.place) =
    some (proverSideOfProximityTest (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Placed V _ X₀).needsField
  front : List.Forall₂ Like (T.bs.take 10) (frontBlock c₀ ::
    (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf Np).U)]))
  ahead : T.ahead = []
  chain : T.chain = 1
  ft : T.ft = 0
  begun : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = first (K1.qAt Zp Np).codes w.key
  trees : treesTo T.bs 10 = 7
  taken : T.taken = []
  table : T.table = tableShared (K1.qAt Zp Np) wts rnd JU
    (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest own₀
  fixedOne : 1 ≤ T.fixed (.own 1)
  oneU : treesU (K1.qAt Zp Np) = 1
  cover : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true
  field : ∀ k s m E, ThrS T Said 10 k s m E → ∀ cols, T.colsTo 10 m E = .ok cols → m.opened = some cols

/-- Where the thread stands at 10 and the letter gives the field, the field is some. -/
theorem opened_at_ten {T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb}
    {Said : ℕ → Coins Bk → Mid _ X₀ → Prop}
    (hfield : ∀ k s m E, ThrS T Said 10 k s m E → ∀ cols, T.colsTo 10 m E = .ok cols →
      m.opened = some cols) (k : Coins Bk) (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env)
    (u : ThrS T Said 10 k s m E) : m.opened.isSome = true := by
  obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, -, hc, -⟩, -, -⟩ := u.1
  rw [hfield k s m E u cols hc]
  rfl

/-- **The job's numbers at the seated place**: two stages or more, k = h + g, round 1's tree, round 1 stands. -/
theorem door_numbers (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (bs : List (Block St Unit)) (wts : W₀ → Weights) (rnd : Rc → TableRand) :
    ∃ s₁ t₁ rest,
      (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages = s₁ :: t₁ :: rest ∧
      s₁.k = (sgOf s₁).h + (sgOf s₁).g ∧
      depthAt (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest 1 = some s₁.Z.a ∧
      1 < (proximityTestKind guardedProximityTestParts (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p :
        Block T12 Unit).rounds.length := by
  obtain ⟨s₁, t₁, rest, hs₀⟩ := stages_O
  have hst : pO.nums.stages = s₁ :: t₁ :: rest := by
    rw [nums_head_O h hO]
    exact hs₀
  have hstg : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages =
      s₁ :: t₁ :: rest := hst
  have hk : s₁.k = (sgOf s₁).h + (sgOf s₁).g := by
    have e := k_head_O h hO
    rw [hst] at e
    exact e
  have hfi : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.fresh.isNone = true := rfl
  refine ⟨s₁, t₁, rest, hstg, hk, ?_, ?_⟩
  · unfold depthAt
    rw [hstg, hfi]
    rfl
  · show 1 < (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds.length
    rw [rounds_head_O h hO]
    exact rounds_len_O

/-- The decision at the job, at a stand. -/
theorem accepts_door (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (bs : List (Block St Unit)) (hb : blocks (K1.qAt Zp Np) = some bs) (wts : W₀ → Weights)
    (rnd : Rc → TableRand) (w : Common W₀ Rc TableKey) (fr : Front X₀) (C : TestCoins)
    (ds : List Fmt.Drawn)
    (hd : drawsFit (proximityTestKind guardedProximityTestParts (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p : Block T12 Unit).rounds ds = true)
    (hs : SaysAt (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd) w fr C) :
    ∃ t', (proximityTestKind guardedProximityTestParts (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p : Block T12 Unit).decide
      ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.rec₀ w fr)
      ((testAll (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest w fr C (byNo ds)).rs.map noDigest)
      (testAll (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest w fr C (byNo ds)).gs = .ok t' := by
  have H := accepts_head_O h hO bs hb (W := Common W₀ Rc TableKey) (X := X₀) (fun w => w.key) colsOpened
    (fun c => wts c.w₀) (fun c => rnd c.rc) none w fr C ds hd hs
  exact H

/-- The seat's way in is the job's state on entry, at a stand. -/
theorem enters_door (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit))
    (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (hpre : List.Forall₂ Like (T.bs.take 10) (frontBlock c₀ ::
      (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf Np).U)])))
    (hah : T.ahead = []) (hft : T.ft = 0)
    (hbeg : ∀ k w hd s₀, T.begun k w hd s₀ → s₀ = first (K1.qAt Zp Np).codes w.key)
    {k : Coins Bk} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 10 k s m E)
    (hfield : ∀ cols, T.colsTo 10 m E = .ok cols → m.opened = some cols) :
    VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) s =
      .ok ((jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.rec₀ m.st.input (frontOf m)) := by
  have e : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.rec₀ =
      doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U (fun w => w.key) colsOpened := rfl
  rw [e]
  exact enters_at_ten T c₀ (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U hpre hah hft hbeg u
    hfield

/-- The count of the term's rounds. -/
theorem count_door (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (bs : List (Block St Unit)) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (s₁ : Fmt.M1.Stage) (l : List Fmt.M1.Stage)
    (hstg : (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p.nums.stages = s₁ :: l)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest w fr C D).rs.length =
      (proximityTestKind guardedProximityTestParts (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest.p : Block T12 Unit).rounds.length :=
  count_of_plan (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest s₁ l 7
    (planPlays_head_O h hO (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest rfl rfl s₁ l hstg) w fr C D

set_option maxHeartbeats 1000000 in
/-- **It is accepted, at member 10**, where `SaysAt` holds at every coin lent. -/
theorem acceptedS_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb) (Said : ℕ → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (wts : W₀ → Weights) (rnd : Rc → TableRand) (JU : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (c₀ : OnBytes.Model.Verify.Chains) (bs : List (Block St Unit))
    (hb : blocks (K1.qAt Zp Np) = some bs) {blk : Block St Cl}
    (H : StandO Zp Np pO T Said wts rnd JU own₀ c₀ bs blk)
    (fall : ℕ → St → List Fmt.Drawn → Option String)
    (hsay : ∀ k s m E (c : RowCoins
        [(firstPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Part V _ _),
        restPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest]),
      ThrS T Said 10 k s m E →
      lendRow Bk (Bk.rowsOf 1) (k.look 1) pO.place
        [(firstPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest : Part V _ _),
        restPart (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest] 0 = .ok c →
      SaysAt (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd) m.st.input (frontOf m)
        (restCoins (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest c.2.1)) :
    AcceptedS T Said fall 10 := by
  obtain ⟨s₁, t₁, rest, hstg, hk, h1, hr1⟩ := door_numbers (X₀ := X₀) h hO bs wts rnd
  have hcuts := bookCutsOmega_head h hO hB
  refine acceptedS_at_own T Said H.member _ _ _ H.seat s₁ t₁ rest hstg hk 2 s₁.Z.a h1 hr1 H.half
    (opened_at_ten H.field) fall ?_
  intro k s m E ds c u hd _ hc
  rw [H.chain] at hc
  obtain ⟨t', ht'⟩ := accepts_door (X₀ := X₀) h hO bs hb wts rnd m.st.input (frontOf m) _ ds hd
    (hsay k s m E c u hc)
  obtain ⟨depths, src₀, q1, q2, q3, q4⟩ := opens_head_O h hO T wts rnd JU
    (jobDoorO (X₀ := X₀) Zp Np pO bs wts rnd).toRun.toTest own₀
    (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U (fun w => w.key) colsOpened)
    H.trees H.taken H.table H.fixedOne H.oneU H.cover hcuts s₁ (t₁ :: rest) hstg u.1 c hc ds
  refine ⟨?_, ?_, ⟨depths, src₀, q1, q2, q3, q4⟩, ?_, ⟨t', ht', _, rfl⟩⟩
  · have H₀ := agree_head_O (V := V) (W := Common W₀ Rc TableKey) (X := X₀) h hO hB ⟨K1.qAt Zp Np, 0⟩
      (doorOmegaF (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U (fun w => w.key) colsOpened)
      (fun c => wts c.w₀) (fun c => rnd c.rc) none _ _ c hc m.st.input (frontOf m)
    exact H₀
  · exact count_door h hO bs wts rnd s₁ (t₁ :: rest) hstg _ _ _ _
  · exact enters_door T c₀ bs wts rnd H.front H.ahead H.ft H.begun u.1 (H.field k s m E u)

end

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.acceptedS_at_own
#print axioms ProofFile.Honest.K12.AtFile.playsS_at_own
#print axioms ProofFile.Honest.K12.AtFile.StandO
#print axioms ProofFile.Honest.K12.AtFile.rec_door
#print axioms ProofFile.Honest.K12.AtFile.door_numbers
#print axioms ProofFile.Honest.K12.AtFile.accepts_door
#print axioms ProofFile.Honest.K12.AtFile.enters_door
#print axioms ProofFile.Honest.K12.AtFile.count_door
#print axioms ProofFile.Honest.K12.AtFile.opened_at_ten
#print axioms ProofFile.Honest.K12.AtFile.acceptedS_head_O
