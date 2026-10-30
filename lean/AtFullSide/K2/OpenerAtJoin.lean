-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/OpenerAtJoin.lean: the kind "the code switch" (K2): OF THE THIRTEEN FIELDS OF THE
RECORD `OpenerAsks` (Honest/K2/Law/LockAsksAtStep.lean) EIGHT ARE LAID IN AT THE JOINED SCRIPT: hmS,
hpS, hmF, hpF, hN, hfx₀, hgl, hD by calls. Closed facts by Lean's kernel; statements with their
proofs.

WHICH SLOT IT IS FOR. `StepAsks` (Honest/K2/Law/StepLeft.lean) asks `OpenerAsks` at each switch past
the first.

  `placesCountsW`   BY LEAN's KERNEL: at each written switch the number `noAt` of the group in
                    front is at most the switch's own, and numbers rise with links;
                    `placesCountsW_can_fail`, a control
  `opener_at_join`  THE END: `OpenerAsks` from five things: h₀, hs, hf, hV, HL

By: `seam_at_head`, `seam_mask_at_head`, `mask_num_at_head`, `last_first`
(Honest/K2/Law/SeamAtHead.lean, of other authors) · `share_msgs_fit` (Honest/K2/JoinShare.lean) ·
`msgs_at_lot_data` (MsgsAtLotData.lean, of other authors) · `pads_at_join`
(Honest/K2/Law/TieAtJoin.lean, of other authors) · `heard_at_switches` (HeardAtSwitches.lean, of
other authors) · `roundsAhead_mono`, `roundsTo_eq_roundsAhead` (Honest/K13/).

Limits. AN IMPLICATION. LEFT, BINDERS: h₀: the frame hands p₀ its coins (`handed_at_book` has that
there are some) · hs, hf: two tests on the book · hV: the sender's laying at p₀ returned · HL: the
two later senders' SharedAsks · hlen: the heard challenges are at least as many as the rounds in
front of p · h1: p₀ is past the opening · hJ, hO: the proximity test's job, and which share the
others' list is · hR4, hI as in ExchangeFull.lean. It binds a run's coins k, c₀, c and V; entries
that hold coins: equations between two texts' values. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO
INDEPENDENT CHECKER. One run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS.
Nothing on any property.
-/
import AtFullSide.K2.ExchangeStep
import AtFullSide.K2.HeardAtSwitches
import Johnson.Desc.ProofFile.Honest.K2.Law.SeamAtHead
import Johnson.Desc.ProofFile.Honest.K13.PileIs
import Johnson.Desc.ProofFile.Honest.K13.ReachAtFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block KindName Strs)
open VerifiableInference.Desc.K2.Honest (carryExact Left)
open VerifiableInference.Desc.Sound (MsgT allOf EAll)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open OnBytes.Maker (WholeD)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open VerifiableInference.Desc.First.Close (seatK10 maskTree maskPart)
open VerifiableInference.Desc.LinkJoin (loAt)

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL. -/
theorem placesCountsW : (placesW.all fun q =>
    decide (VerifiableInference.Desc.First.K2Caller.noAt (q.link - 1) ≤ switchNo q) &&
    placesW.all fun q' => decide (q.link ≤ q'.link → switchNo q ≤ switchNo q')) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at some written switch the number of the next group is above the switch's. -/
theorem placesCountsW_can_fail : (placesW.all fun q =>
    decide (VerifiableInference.Desc.First.K2Caller.noAt q.link ≤ switchNo q)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X Y X₂ : Type} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- h, O, hA, hJ, hO, hR4, hI, hp₀, hp, e₀, h1, hlen, h₀, hs, hf, hV AND HL ARE PREMISES; the rest
are letters. One run's coins: never quoted for a law. **`OpenerAsks` AT THE JOINED SCRIPT.** -/
theorem opener_at_join {Wj Xj : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp
               Bs.G₀)
      (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ReadsLight Zp Bs.G₀ v.x)
    (hI : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → (wit v).x = v.x)
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = p.link - 1) (h1 : 1 ≤ p₀.link) (k : Coins A.B)
    (v : Local W₀ Rc ProofFile.Inst Tr) (hdL ds : List Fmt.Drawn)
    (hlen : roundsTo cF.blocksInOrder (switchNo p) ≤ hdL.length)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed 0 p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (V : Nat → Johnson.Prover.Send.Rows)
    (hs : carriedSame A.B p₀ p = true) (hf : carriedFits A.B (switchPlaces Zp Bs.G₀) p = true)
    (hV : switchRowsLaid (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R)
      (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀ v
      (hdL.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V)
    (HL : ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
      closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData Sz.ref (K1.lotData
        Sz.ref) Zp Bs.G₀ v.x)
        ((fun v => (wit v).R) v) hdL) hdL (Stretch.carried p.carries c.2.2)
        ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none = .ok y' →
      (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg →
      ∀ q, q < 2 → ∃ (wit' : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : K1.SendJob Wj Xj) (own' : Xj)
        (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
        (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
        SharedAsks Zp cF.blocksInOrder (VerifiableInference.Desc.K1.parL Zp Bs.G₀ (p.link - 1) (q == 1))
          (K1.rideOf none) (VerifiableInference.Desc.K1.noL (p.link - 1) (q == 1)) 0
          (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) 0 p k
          (lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ v.x)
            ((fun v => (wit v).R) v) hdL (0 + (p.link - 1))
            ((Sg.sent.headD #[]).size - 1 -
              (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
          (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth)
          (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid
          (0 + roundsTo cF.blocksInOrder (switchNo p₀)) v (hdL ++ ds) wit' J own' cs e dataK front) :
    OpenerAsks (W := Wj) (X := Xj) Zp Bs cF (p.link - 1) p₀ p (joinQ cF.blocksInOrder 0 cellsQ tokQ
      (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth)
      (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid
      (0 + roundsTo cF.blocksInOrder (switchNo p₀)) 0 (0 + roundsTo cF.blocksInOrder (switchNo p₀)) (withSwitchData
                          Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout k v hdL ds c₀ c V := by
  have hq₀ : p₀ ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp₀
  have hq : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have t := List.all_eq_true.1 placesCountsW p₀ hq₀
  simp only [Bool.and_eq_true, decide_eq_true_eq] at t
  obtain ⟨c2, c3⟩ := t
  have c4 : p₀.link ≤ p.link → switchNo p₀ ≤ switchNo p :=
    of_decide_eq_true (List.all_eq_true.1 c3 p hq)
  have hleN : switchNo p₀ ≤ switchNo p := c4 (by omega)
  have hmono : 0 + roundsTo cF.blocksInOrder (switchNo p₀) ≤ hdL.length := by
    rw [Nat.zero_add]
    exact Nat.le_trans (ProofFile.Honest.K13.roundsAhead_mono cF.blocksInOrder hleN) hlen
  have F := joinFit_full h O hA no (K1.lotData Sz.ref) Dd 0 wit own₀ (withSwitchData Sz.ref
    (K1.lotData Sz.ref) Zp Bs.G₀)
    (fun v => (wit v).R) rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂
  rw [← hO] at F
  have hin : ShareIn (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData
             Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) rest) Oth := by
    rw [hO]
    exact shareIn_add_left _ _
  have hB := pure_book_written h hA
  have M := msgs_at_lot_data h O hB Sz.ref no Dd F hin cellsQ tokQ _
    (fun p hp v hv => publicOk_of_reads h O (hR4 v hv) p hp)
    (fun p₀ hp₀ p hp _ v _ s m a hs ha => heard_at_switches h O Sz.ref p₀ hp₀ p hp v.x s m a hs ha)
    hI (fun _ _ => rfl)
  have hsz : ∀ n, n < (switchSent p₀.sizes p₀.others).size → n < (switchPar p₀).sent.size :=
    fun n hn => by
      show n < (sendingPar _ _).sent.size
      rw [sendingPar_sent]
      exact hn
  rw [← e₀]
  obtain ⟨c1', c1''⟩ := last_first h O hp₀
  have hin' := hin
  unfold switchShareAt at hin'
  refine ⟨?_, ?_, ?_, ?_, ?_, hmono, h₀, hs, hf, ?_, ?_, hV, ?_⟩
  · intro n i hn hi
    rw [seam_at_head h O hp₀ hn hi]
    exact M p₀ hp₀ n (hsz n (by omega))
  · intro n i hn hi
    rw [seam_at_head h O hp₀ hn hi]
    exact pads_at_join h O hp₀ F hin cellsQ tokQ _ n (hsz n (by omega))
  · have g := share_msgs_fit _ _ _ _ _ _ _ _ _ _ _ _ F hin' cellsQ tokQ
      (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid
      (0 + roundsTo cF.blocksInOrder (switchNo p₀)) hp₀ (by omega) c1''
    rw [mask_num_at_head h O hp₀, K1.borderNo_written h p₀.place] at g
    exact g
  · have em := seam_mask_at_head h O hp₀
    have t1 := congrArg Prod.fst em
    have t2 := congrArg Prod.snd em
    simp only at t1 t2
    rw [t1, t2]
    exact pads_at_join h O hp₀ F hin cellsQ tokQ _ _ (hsz _ (by omega))
  · exact Nat.le_trans hmono (by simp)
  · rw [Nat.zero_add, ProofFile.Honest.K13.roundsTo_eq_roundsAhead]
    exact ProofFile.Honest.K13.roundsAhead_mono cF.blocksInOrder c2
  · exact fun s i ad hs ha => heard_at_switches h O Sz.ref p₀ hp₀ p hp v.x s i ad hs ha
  · rw [e₀]
    exact HL

end AtFullSide.K2

#print axioms AtFullSide.K2.placesCountsW
#print axioms AtFullSide.K2.placesCountsW_can_fail
#print axioms AtFullSide.K2.opener_at_join
