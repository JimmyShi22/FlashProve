-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OAccepted.lean: the frame's sentence «it is accepted» at the test on G_omega,
member 10 of the filled key thread, the half behind the guard, the first fold sending its own table.

  `acceptedS_of_own_test`   the sentence at any member at which such a test stands, from `K12AtO` at every lent coin
  `accepts_of_written`, `accepted_shape_written`   the decision accepts, and the state on entry has the one shape, at
                 any value that equals the written one
  `manyAtTen`               the many-member job of the test at these parts
  `acceptedS_at_ten_key`    the statement

The premises of `acceptedS_at_ten_key`, with who pays them. e: `par_sourced` with `later_sourced`. hK₀: `full_made`.
B: `Plan2.eight` through `plan_key`. hs: `send_keyOf`. hsp: the key prover in scope. hfield: the field holds the columns
that the thread's fold read: the letter's. hsay: `SaysAt` at every coin lent, at a stand: `says_at_ten_key`.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `acceptedS_of_own_test`, `acceptedS_at_ten_key` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
  Their ground: the thread's pair is a premise, `AcceptedS` the end.
- Of the state behind the member nothing is said but that there is one.
- That a stand is reached, or that any letter pays hfield or hsay, is not said here.
- At the readers that the parts hold.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OAccepts
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OEnters
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OTreesSentBeforeTest
import Johnson.Desc.ProofFile.Honest.K12.AtFile.AcceptedAtTest
import Johnson.Desc.ProofFile.Honest.K12.Own.SaysYesOwn
import Johnson.Desc.ProofFile.Honest.K12.PlanAtKeyKernel
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import E2E.KeyOmegaClosedKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block OpenedColumn noDigest)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey randKey)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyFixedLines (trees_key_O)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega jobKO wtOf rdOf hk_O)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full JO find_O)
open AtPublicFiles.TableFilled (TR ttF)
open AtPublicFiles.PlaysAtNine (mems_at fresh_at)
open AtPublicFiles.TreesAtTenKey (block_ten)
open AtPublicFiles.AtFiles.Full (QK PF)
open _root_.Desc.K14 (P14 St blocks)
open _root_.Desc.K14.Honest (Eight)
open H2K.Member (piKOFull piKUFull)
open H2K.JointK (keyOmega)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.Own (K12AtO saysYes_seat_guarded treeAt_own fresh_tree_atOmega)
open ProofFile.Honest.K12.AtFile (acceptedS_of_saysYes)
open ProofFile.Honest.K12.Light (ManyJob jobAtOmega doorOmegaF SaysAt sentOf)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **It is accepted, at a test whose first fold sends its own table, behind the guard**, where what is
said of the run gives the field and the pair gives `K12AtO`. -/
theorem acceptedS_of_own_test (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop)
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

end

/-- **The decision accepts**, at any value and places equal to the written ones. -/
theorem accepts_of_written {W X : Type} {Q : P14} {p q : P12} (hQ : Q = QK) (hp : p = piKOFull)
    (hq : q = piKUFull) (bs : List (Block St Unit)) (hb : blocks Q = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (C : TestCoins)
    (ds : List Fmt.Drawn) :
    let A := jobAtOmega ⟨Q, 0⟩ p (doorOmegaF Q (sentOf Q.S) bs q key cols) weights rand omega?
    drawsFit (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).rounds ds = true →
    SaysAt A w fr C →
    ∃ t', (proximityTestKind guardedProximityTestParts A.p : Block T12 Unit).decide (A.toRun.toTest.rec₀ w fr)
      ((testAll A.toRun.toTest w fr C (byNo ds)).rs.map noDigest)
      (testAll A.toRun.toTest w fr C (byNo ds)).gs = .ok t' := by
  subst hQ hp hq
  exact accepts_at_key bs hb key cols weights rand omega? w fr C ds

/-- **The state on entry has the one shape**, at any value and place equal to the written ones. -/
theorem accepted_shape_written {W X : Type} {Q : P14} {q : P12} (hQ : Q = QK) (hq : q = piKUFull)
    (bs : List (Block St Unit)) (hb : blocks Q = some bs) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    ProofFile.Honest.Sh.testSh (doorOmegaF Q (sentOf Q.S) bs q key cols w fr) =
      ProofFile.Honest.K12.Light.KeyDoorUClosed.shapeOm := by
  subst hQ hq
  exact shape_at_key bs hb key cols w fr

theorem rounds_at_key : 1 < (proximityTestKind guardedProximityTestParts piKOFull : Block T12 Unit).rounds.length := by decide +kernel

theorem depths_three : [ProofFile.Honest.K12.Light.depthOf piKOFull 0, ProofFile.Honest.K12.Light.depthOf piKOFull 1,
    (piKOFull.nums.stages.headD default).Z.a] = [22, 13, 13] := by decide +kernel

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

/-- The many-member job of the test on G_omega at these parts. -/
abbrev manyAtTen : ManyJob (Common W₀ Rc TableKey) X₀ :=
  jobKO (X := X₀) ⟨parKey Xs PF, 0⟩ pU pO [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
    (wtOf K₁) (rdOf K₁)

include hK₀ in
/-- **It is accepted, at member 10**, where the field holds the columns that the fold read and `SaysAt` holds
at every coin lent. -/
theorem acceptedS_at_ten_key (e : parKey Xs PF = QK) (hs : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String)
    (hsay : ∀ k s m E (c : RowCoins [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)]),
      ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JO Xs K₁ B).p.place
        [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)] 0 = .ok c →
      SaysAt (manyAtTen Xs K₁ B) m.st.input (frontOf m) (restCoins (JO Xs K₁ B) c.2.1)) :
    AcceptedS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said fall 10 := by
  have hP : (JO Xs K₁ B).p = piKOFull := pO_full
  have hseat : SeatOf (keyOmega (PF.O.getD PF.U)) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave := by
    have h := seatOf_inside (Cl := Unit) (JO Xs K₁ B)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  have hblk := block_ten Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd
    w B
  obtain ⟨st0, st1, st2, hs₀⟩ : ∃ a b r, piKOFull.nums.stages = a :: b :: r := ⟨_, _, _, rfl⟩
  have hst : (JO Xs K₁ B).p.nums.stages = st0 :: st1 :: st2 := by
    rw [hP]
    exact hs₀
  have hle : st0.h ≤ st0.k := by
    refine hk_O st0 ?_
    rw [hs₀]
    exact List.mem_cons_self
  have hk : st0.k = (sgOf st0).h + (sgOf st0).g := by
    show st0.k = st0.h + (st0.k - st0.h)
    omega
  have hfi : (JO Xs K₁ B).fresh.isNone = true := rfl
  have h1 : depthAt (JO Xs K₁ B) 1 = some st0.Z.a := by
    unfold depthAt
    rw [hst, hfi]
    rfl
  have hr1 : 1 < (proximityTestKind guardedProximityTestParts (JO Xs K₁ B).p : Block T12 Unit).rounds.length := by
    rw [hP]
    exact rounds_at_key
  have hop : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      m.opened.isSome = true := fun k s m E u => by
    obtain ⟨-, -, -, -, ⟨-, -, -, -, s₀, cols, -, hc, -⟩, -, -⟩ := u.1
    rw [hfield k s m E u cols hc]
    rfl
  refine acceptedS_of_own_test _ Said hblk (JO Xs K₁ B) _ _ hseat st0 st1 st2 hst hk 2 st0.Z.a h1 hr1
    (find_O Xs K₁ B hs hsp) hop fall ?_
  intro k s m E ds c u hd _ hc
  have e7 := trees_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w e B
  have hsent : E.sent = 7 := by
    have h := u.1.2.2.2.2.1.2.2.1
    exact h.trans e7
  have hc' : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JO Xs K₁ B).p.place
      [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)] 0 = .ok c := hc
  obtain ⟨t', ht'⟩ := accepts_of_written (W := Common W₀ Rc TableKey) (X := X₀) e pO_full place_full
    [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (by rw [B.made]) (fun v => v.key)
    ProofFile.Honest.K12.Light.colsOpened (wtOf K₁) (rdOf K₁) none m.st.input (frontOf m) _ ds hd
    (hsay k s m E c u hc')
  exact
    { agree := agree_at_O K₀ hK₀ (manyAtTen Xs K₁ B) pO_full (mems_at _ e _ _ _) (fresh_at _ e _ _ _) _ _
        c hc' _ _
      count := (length_test _ _ _ _ _).trans
        (PlanAtKey.planPlays_KO (JO Xs K₁ B) hP hfi st0 (st1 :: st2) hst).count
      opens := ⟨[22, 13, 13], fun j => [Fmt.TreeSource.own 1, .own 2, .own 7].getD j (.own 0), by
          show [ProofFile.Honest.K12.Light.depthOf pO 0, ProofFile.Honest.K12.Light.depthOf pO 1,
            (pO.nums.stages.headD default).Z.a] = [22, 13, 13]
          rw [pO_full]
          exact depths_three, by
          rw [hsent]
          refine opensFit_of_B _ _ _ _ _ ?_
          show opensFitB true pO.nums.stages (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds _ _ _ = true
          rw [pO_full]
          exact ProofFile.Honest.K12.Light.KeyOmegaClosed.opens_O,
        oldAtO_at_ten K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e u.1 c hc', fun x _ => by
          have e1 := fresh_tree_atOmega ⟨parKey Xs PF, 0⟩ pO
            (doorOmegaF (parKey Xs PF) (sentOf (parKey Xs PF).S)
              [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] pU (fun v => v.key)
              ProofFile.Honest.K12.Light.colsOpened) (wtOf K₁) (rdOf K₁) none m.st.input (frontOf m)
            (restCoins (JO Xs K₁ B) c.2.1).mem
            ((JO Xs K₁ B).first m.st.input (frontOf m) (restCoins (JO Xs K₁ B) c.2.1)) x
          have e2 := congrFun (treeAt_own (JO Xs K₁ B) m.st.input (frontOf m)
            (restCoins (JO Xs K₁ B) c.2.1) (byNo ds) st0 (st1 :: st2) hst hfi) x
          have es : (JO Xs K₁ B).s₀ = st0 := by
            unfold TestJob.s₀
            rw [hst]
            rfl
          refine e1.trans ?_
          rw [e2]
          show freshCol (sgOf (JO Xs K₁ B).s₀) _ x = _
          rw [es]⟩
      enters := enters_at_ten_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w B u.1
        (hfield k s m E u)
      accepts := ⟨t', ht', _, rfl⟩ }

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.acceptedS_of_own_test
#print axioms ProofFile.Honest.K12.AtKey.accepts_of_written
#print axioms ProofFile.Honest.K12.AtKey.accepted_shape_written
#print axioms ProofFile.Honest.K12.AtKey.rounds_at_key
#print axioms ProofFile.Honest.K12.AtKey.depths_three
#print axioms ProofFile.Honest.K12.AtKey.acceptedS_at_ten_key
