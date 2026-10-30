-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FirstSenders.lean: the senders that the switch into the group 1 reads: the form
FirstSenders (JoinSenders.lean) at the joined Script.

1. The switch into the group 1 closes the first segment. No switch sent that segment: its messages
   in front of the fold's mask and the mask itself are the opening's, the job at number 2, and its
   two later messages are those of LaterAsks.lean.
2. firstOk, firstW: a public test at the written lists, by Lean's kernel: each message in front of
   the mask has the opening's address, its field, how much its data has heard, and the order of the
   rounds.
3. first_job_mem: the opening's job stands in the joined list at number 2.
4. first_sender, mask_sender: the opening's message n, and the fold's mask.
5. first_senders: the end, at N := 0: the ties on messages hold at every N.

Limits. The head, the opening, the maker's return and hJ are hypotheses. hI and hR tie the reader wit
to the input and to the readers of the closing. hlen says that the challenges heard reach the switch.
The closed fact runs in Lean's kernel and no independent checker replays it here. The controls bend
the address and the hearing; the limbs on the field and on the order of rounds have none. MaskAsks
says nothing of the mask's rows at the sender's data. The form stands at one run's coins and says
what is written where. The full size and the format's second hash function alone.
-/
import AtFullSide.K2.LaterAsks
import AtFullSide.K2.FirstSizeAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.K1SendersSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (maskTree maskPart)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (parGF firstPar gpOf)
open VerifiableInference.Desc.K2.Honest (Left)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (layoutFull)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3.Fit (seatsW)
open OnBytes.SendSim.Seat (wJobs)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (Others TreeLot JoinFit OwnMsgs OwnPads byNo headJ₂ joinQ
  join_tie_k1_fit k1Jobs byNo_at_head)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open P5J (AtMgA CellsM F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 The public test -/

/-- **A PUBLIC TEST** at a written place: at each message of the first segment's first sending in
front of the mask. da and dh bend the address and the hearing for a control; 0 in earnest. -/
def firstOk (da dh : Nat) (p : SwitchPlace) : Bool :=
  (segsW[0]?).any fun Sg => (List.range ((Sg.sent.headD #[]).size - 1)).all fun n =>
    decide (p.addrs 0 n = some ⟨K1.firstAddr, n + da⟩) &&
    (((Sg.ownShapes true).getD n {}).mainDeg == (shapeAt parGF n).mainDeg) &&
    decide (n < parGF.sent.size) &&
    decide (heardAll (seatsW "U3") (seatsW "BZ") layoutFull heardRngW ⟨K1.firstAddr, n⟩ + dh ≤
      roundsCutW 2) &&
    decide (roundsCutW 2 ≤ roundsCutW (switchNo p))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test says yes at the written place below link 2**; two controls: with the address bent,
and with the hearing bent, it says no; and one written place lies below link 2, so that none of the
three runs over nothing. -/
theorem firstW : ((placesW.filter fun p => decide (p.link < 2)).all fun p => firstOk 0 0 p) = true ∧
    ((placesW.filter fun p => decide (p.link < 2)).all fun p => !firstOk 1 0 p) = true ∧
    ((placesW.filter fun p => decide (p.link < 2)).all fun p => !firstOk 0 100000 p) = true ∧
    (placesW.filter fun p => decide (p.link < 2)).length = 1 := by
  decide +kernel

/-- What the test's yes gives. -/
theorem first_public {p : SwitchPlace} (hp : p ∈ placesW) (h2 : p.link < 2) {Sg : SegmentPub}
    (hS : segsW[0]? = some Sg) {n : Nat} (hn : n < (Sg.sent.headD #[]).size - 1) :
    p.addrs 0 n = some ⟨K1.firstAddr, n⟩ ∧
    ((Sg.ownShapes true).getD n {}).mainDeg = (shapeAt parGF n).mainDeg ∧
    n < parGF.sent.size ∧
    heardAll (seatsW "U3") (seatsW "BZ") layoutFull heardRngW ⟨K1.firstAddr, n⟩ ≤ roundsCutW 2 ∧
    roundsCutW 2 ≤ roundsCutW (switchNo p) := by
  have t : firstOk 0 0 p = true :=
    List.all_eq_true.1 firstW.1 p (List.mem_filter.2 ⟨hp, decide_eq_true h2⟩)
  unfold firstOk at t
  rw [hS] at t
  simp only [Option.any_some] at t
  have t' := List.all_eq_true.1 t n (List.mem_range.2 hn)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t'
  obtain ⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩ := t'
  exact ⟨t1, t2, t3, Nat.le_trans (Nat.le_add_right _ 0) t4, t5⟩

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Tr X₀ X Y X₂ Cells Tok : Type}

/-- **The opening's job stands in the joined list at number 2.** -/
theorem first_job_mem (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (no : Place → Nat) (Dt Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst) :
    (2, headJ₂ (X := Y) Zp Bs.G₀ no Dt) ∈
      byNo cF.blocksInOrder (K1.lotJobs (X := Y) no Dt Zp Bs.G₀ ++ wJobs (X := Y) no Dd Zp Bs.G₀) := by
  show _ ∈ byNo cF.blocksInOrder (k1Jobs (X := Y) no Dt Dd Zp Bs.G₀)
  rw [byNo_at_head h O no Dt Dd]
  exact K1.mem_k1MembersW.2 (Or.inl (K1.mem_k1Members.2 (Or.inl rfl)))

/-- **MaskAsks at a job of a fit list**, from facts on that job: the sister of shared_at_job. hseat:
the mask's seat is the seat of the job's message n. -/
theorem mask_at_job {Bk : ProverCoinCounts} {bs : List (Block S ProofFile.Cl)} {seats : List (Nat × Nat)}
    {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst} {own₀ : Y}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn ProofFile.Inst) Y)}
    {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (F : JoinFit bs 0 (P5J.At.arr Zp) seats wit own₀ jobs Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → Cells) (tok : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N : Nat) {b n ix : Nat}
    {P₀ : VerifiableInference.Desc.K1.Par} {ρ₀ : Nat → Option K1.Ride}
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) Y} (hx : (b, J) ∈ jobs) (hP : P₀ = J.P)
    (hρ : ρ₀ = J.ride) (hn : n < J.P.sent.size) {p : SwitchPlace} {e : Ahead}
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[ix]? = some e)
    (t1 : e.owner = ⟨J.P.place, 0⟩) (t2 : e.start = K1.startR J.P J.ride n)
    (t3 : e.count = K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n)) (k : Coins Bk)
    (hseat : (maskTree 0, maskPart 0) = K1.seatAtMember bs b J.P n) :
    ∃ cs : Cs (K1.dueR J.P J.ride),
      MaskAsks Zp P₀ ρ₀ n ix 0 p k (joinQ bs 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd N wit J
        own₀ cs e (0 + roundsTo bs b) := by
  subst hP hρ
  have hco : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = K1.dueR J.P J.ride := F.coins (b, J) hx
  have hcov : K1.bookCovers Bk 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true := by
    unfold K1.bookCovers
    rw [hco]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  obtain ⟨cs, hcut⟩ := Option.isSome_iff_exists.1
    ((K1.lentCut_isSome k 0 (by omega) ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride)).trans hcov)
  have hnum : P5J.At.arr Zp (maskTree 0) (maskPart 0) =
      P5J.At.arr Zp (K1.seatAtMember bs b J.P n).1 (K1.seatAtMember bs b J.P n).2 :=
    congrArg (fun s : Nat × Nat => P5J.At.arr Zp s.1 s.2) hseat
  refine ⟨cs, rfl, rfl, hcut, he, t1, t2, t3, ?_, ?_⟩
  · rw [hnum]
    exact join_msg_any (x := (b, J)) F cells tok Vd N hx hn
  · have t := (join_tie_k1_fit F cells tok Vd hx).2 n hn
    have t' : OwnPads (joinQ bs 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (K1.seatAtMember bs b J.P n).1 (K1.seatAtMember bs b J.P n).2
        (fun k _ => K1.padTxt 0 J n k) := t
    rw [← hseat] at t'
    exact t'

/-- h, O, hA, hJ, hO, hI, hR, hp, h1 AND hlen ARE PREMISES. **THE SENDERS THAT THE SWITCH INTO THE
GROUP 1 READS, AT THE JOINED SCRIPT.** -/
theorem first_senders (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hI : (wit w).x = w.x) (hR : (wit w).R = readers w) {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zp Bs.G₀) (h1 : p.link = 1) (k : Coins A.B)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hd ds : List Fmt.Drawn)
    (hlen : roundsTo cF.blocksInOrder (switchNo p) ≤ hd.length) :
    FirstSenders Zp Bs cF (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀))
      (lotOwn segsW p ((withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) w.x) (readers w) hd) p k c
      (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth)
      Vd 0 w hd ds wit own₀ := by
  intro y' Sg hy hS
  simp only [List.take_zero, closingFrom] at hy
  obtain rfl : ((none : Option (Left × List OnBytes.OracleShape)), 0) = y' := Except.ok.inj hy
  have hB := pure_book_written h hA
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hsegs := segments_at_head h.toAtMg O
  have hSW := hS
  rw [hsegs] at hSW
  have hm0 : p.link - 1 = 0 := by omega
  have h2 : p.link < 2 := by omega
  have hsz := first_size_at_head h O hS
  obtain ⟨J, hJe⟩ : ∃ J : K1.SendJob (K1.PlaceIn ProofFile.Inst) Y,
      J = headJ₂ Zp Bs.G₀ no (K1.lotData Sz.ref) := ⟨_, rfl⟩
  have hx : (2, J) ∈ byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
               wJobs (X := Y) no Dd Zp Bs.G₀) := by
    subst hJe
    exact first_job_mem h O no (K1.lotData Sz.ref) Dd
  have hP : firstPar Bs.G₀.first (gpOf Zp) = J.P := by
    subst hJe
    rfl
  have hρ : K1.rideOf (K1.firstFold Bs.G₀.first) = J.ride := by
    subst hJe
    rfl
  have hJd : ∀ (v : K1.PlaceIn ProofFile.Inst) (fr : Front Y) (n r j : Nat), J.data v fr n r j =
      (K1.lotData Sz.ref Zp Bs.G₀ v.x).at_ v.R fr.heard ⟨⟨J.P.place, 0⟩, n⟩ r j := by
    subst hJe
    intro v fr n r j
    rfl
  have hPw : J.P = parGF := hP.symm.trans (ProofFile.Honest.K11.par_at_head h O)
  have hA₀ : (⟨J.P.place, 0⟩ : Addr) = K1.firstAddr := by
    subst hJe
    rfl
  have hk : J.P.place.kind ≠ .K2 := by
    subst hJe
    show K1.firstAddr.place.kind ≠ .K2
    decide
  have F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth := by
    subst hO
    exact joinFit_full h O hA no (K1.lotData Sz.ref) Dd 0 wit own₀ _ readers rest ch Jt hJ own₂ n₀
      ok codes sh sh₁ rest₂
  -- the book's entry at the opening's message number n
  have hbook : ∀ n, n < (Sg.sent.headD #[]).size → ∃ e,
      ((A.B.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[n]? = some e ∧
      e.owner = ⟨J.P.place, 0⟩ ∧ e.start = K1.startR J.P J.ride n ∧
      e.count = K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n) := by
    intro n hn
    obtain ⟨e, he, u1, u2, u3⟩ := entryRunIs_gives (carried_opening_at_book h O hB hS hp hn)
    rw [carryE_is] at he
    refine ⟨e, he, ?_, ?_, ?_⟩
    · rw [hA₀]
      exact u1
    · rw [← hP, ← hρ]
      exact u2
    · rw [← hP, ← hρ]
      exact u3
  refine ⟨fun n hn => ?_, fun q hq => ?_, ?_⟩
  · -- the opening's message n
    obtain ⟨t1, t2, t3, t4, t5⟩ := first_public hpW h2 hSW hn
    obtain ⟨e, he, u1, u2, u3⟩ := hbook n (by omega)
    have he' : ((A.B.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[0 + n]? =
        some e := by
      rw [Nat.zero_add]
      exact he
    have hnP : n < J.P.sent.size := by
      rw [hPw]
      exact t3
    have ha : p.addrs (0 + 0) n = some ⟨⟨J.P.place, 0⟩, n⟩ := by
      rw [hA₀]
      exact t1
    have hb : (((((segsW[0 + 0]?).map fun (y : SegmentPub) => y.ownShapes (0 + 0 == 0)).getD []).getD
        n {}).mainDeg == 3) = ((shapeAt J.P n).mainDeg == 3) := by
      have e₀ : segsW[0 + 0]? = some Sg := hSW
      rw [e₀]
      show (((Sg.ownShapes true).getD n {}).mainDeg == 3) = _
      rw [t2, hPw]
    have hdat : dataAtOf Sg none
        (lotOwn segsW p ((withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) w.x) (readers w) hd (0 + 0)) n =
        fun r j => asRow ((shapeAt J.P n).mainDeg == 3)
          ((K1.lotData Sz.ref Zp Bs.G₀ w.x).at_ (readers w) hd ⟨⟨J.P.place, 0⟩, n⟩ r j) :=
      funext fun r => funext fun j => own_is_row Sz.ref Zp Bs.G₀ w.x (readers w) ha hb hk r j
    have hf1 : (K1.lotData Sz.ref Zp Bs.G₀ w.x).heardAt ⟨⟨J.P.place, 0⟩, n⟩ ≤
        0 + roundsTo cF.blocksInOrder 2 := by
      rw [← (with_other_kind Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ w.x ⟨⟨J.P.place, 0⟩, n⟩ hk).1]
      refine heard_at_later h O Sz.ref w.x _ _ ?_
      rw [Nat.zero_add, roundsTo_at_head h O, hA₀]
      exact t4
    have hf2 : 0 + roundsTo cF.blocksInOrder 2 ≤ hd.length := by
      rw [Nat.zero_add, roundsTo_at_head h O]
      exact Nat.le_trans t5 (by
        rw [← roundsTo_at_head h O (switchNo p)]
        exact hlen)
    obtain ⟨cs, dataK, B⟩ := shared_at_job F cellsQ tokQ Vd 0 w readers hI hR Sz.ref Bs.G₀ hx hP hρ
      hJd hnP he' u1 u2 u3 k ds hdat hf1 hf2
    unfold SharedAt
    exact ⟨(2, J), hx, rfl, cs, e, dataK, B⟩
  · -- the two later messages
    have hy2 : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p
        ((withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) w.x) (readers w) hd) hd
        (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none =
        .ok (none, 0) := by
      simp only [hm0, List.take_zero, closingFrom]
    have hS2 : (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg := by
      rw [hm0]
      exact hS
    have B := later_sender h O hA no Dd cellsQ tokQ wit own₀ readers rest ch Jt hJ own₂ n₀ ok codes
      sh sh₁ rest₂ Oth hO Vd 0 w hI hR hp k hd ds hlen hy2 hS2 hq
    rw [hm0, hsegs] at B
    exact B
  · -- the fold's mask
    have hnM : (Sg.sent.headD #[]).size - 1 < (Sg.sent.headD #[]).size := by omega
    obtain ⟨e, he, u1, u2, u3⟩ := hbook _ hnM
    have he' : ((A.B.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[0 +
        ((Sg.sent.headD #[]).size - 1)]? = some e := by
      rw [Nat.zero_add]
      exact he
    have T := mask_tie_at_head h O hS
    have hnP : (Sg.sent.headD #[]).size - 1 < J.P.sent.size := by
      rw [← hP]
      exact T.hq
    have hseat := (mask_seat_at_head h O hS).1
    rw [hP] at hseat
    obtain ⟨cs, B⟩ := mask_at_job F cellsQ tokQ Vd 0 (b := 2) hx hP hρ hnP he' u1 u2 u3 k hseat
    unfold MaskAt
    exact ⟨(2, J), hx, rfl, cs, e, B⟩

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.firstOk
#print axioms AtFullSide.K2.firstW
#print axioms AtFullSide.K2.first_public
#print axioms AtFullSide.K2.first_job_mem
#print axioms AtFullSide.K2.mask_at_job
#print axioms AtFullSide.K2.first_senders
