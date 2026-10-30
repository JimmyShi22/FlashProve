-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SymbolsTop.lean: SymbolsAre at each switch of the first chain, at the joined Script,
from JoinSenders.

  handed_lends         what the frame hands a part is what it lends
  shared_member        a member sent by a job of the joined list, from its record
  switch_member        a member sent by the switch in front
  switch_fresh         the fresh mask sent by the switch in front
  first_fresh          the fresh mask of the first segment, sent by the opening
  sendersBeforeW       by Lean's kernel, with a control: the senders stand in front of the switch
  symbols_closed       SymbolsAre at a front, from JoinSenders
  symbols_at_join      THE TOP: SymbolsAre at each switch, at the joined Script

Limits. The records are premises. Nothing on any property.
-/
import AtFullSide.K2.SymbolsAtJoin
import AtFullSide.K2.ExchangeLeft
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open OnBytes
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc (Block Chain roundsFit fieldPrimeWord noDigest)
open VerifiableInference.Desc.First.K2 (P2 AtYes frontAt rounds)
open VerifiableInference.Desc.K2.Honest (Left SymbolsAre carryExact sizesAt)
open VerifiableInference.Desc.K2.Honest.Returns (link_door head_door fin_door)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open VerifiableInference.Desc.First.Close (membersOf seatK10 maskTree maskPart)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.K2.Honest.Returns (fresh_of_closedBehind)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K2.Honest (Sizes GroupMember shapeOf)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.Sound (MsgT allOf EAll)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember treeTables treeTables_length)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {Bk : ProverCoinCounts}

/-- **What the frame hands a part is what it lends.** -/
theorem handed_lends {ch : Nat} {p : SwitchPlace} {k : Coins Bk}
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (h : handed ch p k = some c) :
    lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c := by
  unfold handed at h
  cases e : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) with
  | error s =>
    rw [e] at h
    cases h
  | ok c' =>
    rw [e] at h
    exact congrArg Except.ok (Option.some.inj h)

/-- **A member sent by a job of the joined list, from its record.** -/
theorem shared_member {Cells Tok V X' Pb Xj Y W₀ Rc Tr : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m nb : Nat}
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h m nb a s₁ x) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Yv rows G cd) (hft : q.firstTree = 0)
    (hlog : cd.logN = (Johnson.G.codesFull2.base.getD proofSizedFull.request.code default).logN)
    (hmk : x.f.rows.masks = 2) {arr : Nat → Nat → Nat} {seats : List (Nat × Nat)}
    {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn Xj} {own₀ : Y}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Y)} {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (F : JoinFit cF.blocksInOrder 0 arr seats wit own₀ jobs Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → Cells) (tok : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (T : Thread Bk TS ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = 0)
    (htab : T.table = (joinQ cF.blocksInOrder 0 cells tok arr wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder 0 cells tok arr wit own₀ jobs Oth).fixed)
    (k : Coins Bk) (mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X') (ds : List Fmt.Drawn) (Zs : Sizes)
    (hcodes : Zs.codes = Johnson.G.codesFull2) (hcode : Zs.code = proofSizedFull.request.code)
    (hmask : Zs.maskCode = proofSizedFull.request.maskCode)
    {P₀ : VerifiableInference.Desc.K1.Par} {ρ₀ : Nat → Option K1.Ride} {b n ix : Nat}
    {p : SwitchPlace} {dat : Nat → Nat → Cb.Gl.E}
    {Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) Cells Tok MsgT}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : Nat}
    (hP : SenderAt Zp Bs P₀ b) (hb : b < nb) (hn : n < P₀.sent.size)
    (hlen : 0 + roundsTo cF.blocksInOrder b ≤ mm.st.heard.length)
    (S₀ : SharedAt Zp cF.blocksInOrder jobs P₀ ρ₀ b n ix p k dat Q Vd N mm.st.input (mm.st.heard ++ ds) wit
      own₀)
    {w : Nat} {i : Fin (loAt m).length} (hi : (membersOf (loAt m))[w]? = some i)
    (hseat : seatK10 (loAt m) P5T.psFull m i = seatAtMember cF.blocksInOrder b P₀ n)
    (hshape : ((loAt m).get i).1 = shapeAt P₀ n) (R : GroupRows) (ms : List GroupMember)
    (hms : shapeOf ms w = ((loAt m).get i).1)
    (hrow : ∀ {J : K1.SendJob (K1.PlaceIn Xj) Y} {cs : Cs (K1.dueR J.P J.ride)}
      {dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)} {e : Ahead},
      SharedAsks Zp cF.blocksInOrder P₀ ρ₀ b n ix 0 p k dat Q Vd N mm.st.input (mm.st.heard ++ ds) wit J own₀
        cs e dataK (0 + roundsTo cF.blocksInOrder b) →
      R.rows.getD w zeroMessage = K1.rowsR J.P J.ride dataK cs n) :
    ∃ (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Johnson.Prover.Send.Rows) (kn : Nat) (Xo : Oracle)
      (pp : Nat × Nat) (tr : Tree),
      MemberSent T nb k mm q Zs x.f.rows z w P Vr kn Xo pp tr ∧
      MemberRow q Zs ms R w P Vr kn tr := by
  obtain ⟨y, hy, hy1, cs, e, dataK, B⟩ := S₀
  subst hy1
  obtain rfl : P₀ = y.2.P := B.plan
  obtain ⟨plan, hpc, blk, hblk, hcount⟩ := sender_plan h O hP
  obtain ⟨hτ, hτ'⟩ := tree_in_plan plan hn
  have er : (mm.st.heard ++ ds).take (0 + roundsTo cF.blocksInOrder y.1) =
      mm.st.heard.take (0 + roundsTo cF.blocksInOrder y.1) := List.take_append_of_le_length hlen
  have hr' : R.rows.getD w zeroMessage = K1.rowsLaid y.2 own₀ cs (wit mm.st.input)
      (mm.st.heard.take (0 + roundsTo cF.blocksInOrder y.1)) n := by
    rw [hrow B, B.rows, er]
  obtain ⟨Xo, tr, M1, M2⟩ := member_sent_at h O Ar A hft hlog hmk T hbs k mm Zs hcodes hcode hmask hP hb
    hblk hcount plan hpc hn hi hseat hshape R ms hms _
    (k1_table_at_join F cells tok T hbs hfr htab hfix hy k mm B.cut hτ') hr'
  exact ⟨_, _, _, _, _, _, M1, M2⟩

/-- **A member sent by the switch in front.** -/
theorem switch_member {Wt Rt Tt Cells Tok V X' Pb Xj Xo : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m nb : Nat}
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h m nb a s₁ x) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Yv rows G cd) (hft : q.firstTree = 0)
    (hlog : cd.logN = (Johnson.G.codesFull2.base.getD proofSizedFull.request.code default).logN)
    (hmk : x.f.rows.masks = 2) {wit : Local Wt Rt ProofFile.Inst Tt → K1.PlaceIn Xj} {own₀ : Xo}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Xo)}
    {Oth : Others Bk (Local Wt Rt ProofFile.Inst Tt)} {D : RowDataOf ProofFile.Inst}
    {readers : Local Wt Rt ProofFile.Inst Tt → Readers}
    {rest : Nat → TreeLot Bk (Local Wt Rt ProofFile.Inst Tt)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local Wt Rt ProofFile.Inst Tt → Cells) (tok : Local Wt Rt ProofFile.Inst Tt → Tok)
    (T : Thread Bk TS ProofFile.Cl V (Local Wt Rt ProofFile.Inst Tt) X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = 0)
    (htab : T.table = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).fixed)
    (k : Coins Bk) (mm : Mid (Local Wt Rt ProofFile.Inst Tt) X') (Zs : Sizes)
    (hcodes : Zs.codes = Johnson.G.codesFull2) (hcode : Zs.code = proofSizedFull.request.code)
    (hmask : Zs.maskCode = proofSizedFull.request.maskCode)
    {p₀ : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (e₀ : p₀.link = m)
    (hb : switchNo p₀ < nb) (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
    (h₀ : handed 0 p₀ k = some c₀) {V₀ : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀
      mm.st.input (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀)
    {w : Nat} (hw : w < (switchSent p₀.sizes p₀.others).size - 1) (R : GroupRows)
    (ms : List GroupMember)
    (hms : ∀ i : Fin (loAt m).length, (membersOf (loAt m))[w]? = some i →
      shapeOf ms w = ((loAt m).get i).1)
    (hrow : R.rows.getD w zeroMessage = V₀ w) :
    ∃ (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Johnson.Prover.Send.Rows) (kn : Nat) (Xo' : Oracle)
      (pp : Nat × Nat) (tr : Tree),
      MemberSent T nb k mm q Zs x.f.rows z w P Vr kn Xo' pp tr ∧
      MemberRow q Zs ms R w P Vr kn tr := by
  subst e₀
  have hP : SenderAt Zp Bs (switchPar p₀) (switchNo p₀) := Or.inr (Or.inr ⟨p₀, hp₀, rfl, rfl⟩)
  obtain ⟨plan, hpc, blk, hblk, hcount⟩ := sender_plan h O hP
  have hlt : w < (switchPar p₀).sent.size := by
    show w < (sendingPar _ _).sent.size
    rw [sendingPar_sent]
    omega
  obtain ⟨i, hi, es⟩ := first_shapes_at_head h.toAtMg O hp₀ Ar.below hw
  have hseat := seam_at_head h O hp₀ hw hi
  have hps : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.seats
  rw [hps] at hseat
  have hshape : ((loAt p₀.link).get i).1 = shapeAt (switchPar p₀) w := by
    rw [sendingPar_shape]
    exact es
  obtain ⟨hτ, hτ'⟩ := tree_in_plan plan hlt
  obtain ⟨Xo', tr, M1, M2⟩ := member_sent_at h O Ar A hft hlog hmk T hbs k mm Zs hcodes hcode hmask hP hb
    hblk hcount plan hpc hlt hi hseat hshape R ms (hms i hi) V₀
    (switch_table_at_join h O F hin cells tok T hbs hfr htab hfix hp₀ k mm c₀ (handed_lends h₀) hV
      hblk (by rw [hcount]; exact hτ') (by rw [treeTables_length]; exact hτ')) hrow
  exact ⟨_, _, _, _, _, _, M1, M2⟩

/-- **The fresh mask sent by the switch in front.** -/
theorem switch_fresh {Wt Rt Tt Cells Tok V X' Pb Xj Xo : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m nb : Nat}
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h m nb a s₁ x) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Yv rows G cd) (hft : q.firstTree = 0)
    (hmk : x.f.rows.masks = 2) {wit : Local Wt Rt ProofFile.Inst Tt → K1.PlaceIn Xj} {own₀ : Xo}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Xo)}
    {Oth : Others Bk (Local Wt Rt ProofFile.Inst Tt)} {D : RowDataOf ProofFile.Inst}
    {readers : Local Wt Rt ProofFile.Inst Tt → Readers}
    {rest : Nat → TreeLot Bk (Local Wt Rt ProofFile.Inst Tt)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local Wt Rt ProofFile.Inst Tt → Cells) (tok : Local Wt Rt ProofFile.Inst Tt → Tok)
    (T : Thread Bk TS ProofFile.Cl V (Local Wt Rt ProofFile.Inst Tt) X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = 0)
    (htab : T.table = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).fixed)
    (k : Coins Bk) (mm : Mid (Local Wt Rt ProofFile.Inst Tt) X') (Zs : Sizes)
    (hcodes : Zs.codes = Johnson.G.codesFull2)
    (hmask : Zs.maskCode = proofSizedFull.request.maskCode)
    {p₀ : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (e₀ : p₀.link = m)
    (hb : switchNo p₀ < nb) (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
    (h₀ : handed 0 p₀ k = some c₀) {V₀ : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀
      mm.st.input (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀)
    (hne : 0 < (switchSent p₀.sizes p₀.others).size)
    (hfc : ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape.maskRows ≠ 0 →
      ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape.maskCode = proofSizedFull.request.maskCode) (R : GroupRows)
    (hrow : R.fresh = some (V₀ ((switchSent p₀.sizes p₀.others).size - 1))) :
    ∃ (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Johnson.Prover.Send.Rows) (kn : Nat) (Xo' : Oracle)
      (pp : Nat × Nat) (tr : Tree),
      MemberSent T nb k mm q Zs x.f.rows z x.f.rows.layout.members.size P Vr kn Xo' pp tr ∧
      FreshRow x.f.rows R P Vr kn := by
  subst e₀
  have hP : SenderAt Zp Bs (switchPar p₀) (switchNo p₀) := Or.inr (Or.inr ⟨p₀, hp₀, rfl, rfl⟩)
  obtain ⟨plan, hpc, blk, hblk, hcount⟩ := sender_plan h O hP
  have hlt : (switchSent p₀.sizes p₀.others).size - 1 < (switchPar p₀).sent.size := by
    show _ < (sendingPar _ _).sent.size
    rw [sendingPar_sent]
    omega
  obtain ⟨e1, e2, -⟩ := fresh_of_closedBehind h Ar.below Ar.rch.2 a.2 Ar.closed
  have hshape : (a.1.2.st.oracles.getD x.f.rows.fresh default).shape =
      shapeAt (switchPar p₀) ((switchSent p₀.sizes p₀.others).size - 1) := by
    rw [sendingPar_shape, e1]
    exact mask_shape_getD h O a Ar.rch Ar.failed hp₀ Ar.below (by rw [← e1]; exact e2) rfl
  obtain ⟨hτ, hτ'⟩ := tree_in_plan plan hlt
  obtain ⟨Xo', tr, M, hrw⟩ := fresh_at h O Ar A hft hmk T hbs k mm Zs hcodes hmask hP hb hblk hcount
    plan hpc hlt (seam_mask_at_head h O hp₀) hshape
    (fun h0 => by
      rw [sendingPar_shape] at h0 ⊢
      exact hfc h0)
    V₀
    (switch_table_at_join h O F hin cells tok T hbs hfr htab hfix hp₀ k mm c₀ (handed_lends h₀) hV
      hblk (by rw [hcount]; exact hτ') (by rw [treeTables_length]; exact hτ'))
  refine ⟨_, _, _, _, _, _, M, hrw, ?_, ?_⟩
  · rw [hrow]
    rfl
  · rw [hrow]
    rfl

/-- **The fresh mask of the first segment, sent by the opening**, from its record. Of the rows the
fold reads the mask rows and their tails alone, which hang on the ride and the coins. -/
theorem first_fresh {Wl Cells Tok V X' Pb Xj Y : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {nb : Nat}
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h 0 nb a s₁ x) {q : P2} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ gs x z S3 Yv rows G cd) (hft : q.firstTree = 0)
    (hmk : x.f.rows.masks = 2) {arr : Nat → Nat → Nat} {seats : List (Nat × Nat)}
    {wit : Wl → K1.PlaceIn Xj} {own₀ : Y} {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Y)}
    {Oth : Others Bk Wl} (F : JoinFit cF.blocksInOrder 0 arr seats wit own₀ jobs Oth) (cells : Wl → Cells)
    (tok : Wl → Tok) (T : Thread Bk TS ProofFile.Cl V Wl X' Pb) (hbs : T.bs = cF.blocksInOrder) (hfr : T.front = 0)
    (htab : T.table = (joinQ cF.blocksInOrder 0 cells tok arr wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder 0 cells tok arr wit own₀ jobs Oth).fixed)
    (k : Coins Bk) (mm : Mid Wl X') (Zs : Sizes) (hcodes : Zs.codes = Johnson.G.codesFull2)
    (hmask : Zs.maskCode = proofSizedFull.request.maskCode)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg)
    (hfc : ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape.maskRows ≠ 0 →
      ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape.maskCode =
        proofSizedFull.request.maskCode)
    (hb : 2 < nb) {y : Nat × K1.SendJob (K1.PlaceIn Xj) Y} (hy : y ∈ jobs) (hy1 : y.1 = 2)
    (hplan : firstPar Bs.G₀.first (gpOf Zp) = y.2.P)
    {cs : Cs (K1.dueR y.2.P y.2.ride)}
    (ho : K1.lentCut k 0 ⟨y.2.P.place, 0⟩ (K1.dueR y.2.P y.2.ride) = some cs) (R : GroupRows)
    (hmask' : (R.fresh.getD zeroMessage).mask = (K1.rowsLaid y.2 own₀ cs (wit mm.st.input)
        (mm.st.heard.take (0 + roundsTo cF.blocksInOrder y.1)) ((Sg.sent.headD #[]).size - 1)).mask)
    (htail' : (R.fresh.getD zeroMessage).maskTl = (K1.rowsLaid y.2 own₀ cs (wit mm.st.input)
        (mm.st.heard.take (0 + roundsTo cF.blocksInOrder y.1)) ((Sg.sent.headD #[]).size - 1)).maskTl) :
    ∃ (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Johnson.Prover.Send.Rows) (kn : Nat) (Xo' : Oracle)
      (pp : Nat × Nat) (tr : Tree),
      MemberSent T nb k mm q Zs x.f.rows z x.f.rows.layout.members.size P Vr kn Xo' pp tr ∧
      FreshRow x.f.rows R P Vr kn := by
  have hP : SenderAt Zp Bs y.2.P y.1 := Or.inl ⟨hplan.symm, hy1⟩
  obtain ⟨plan, hpc, blk, hblk, hcount⟩ := sender_plan h O hP
  have T₀ := mask_tie_at_head h O hS
  rw [hplan] at T₀
  obtain ⟨e1, e2, -⟩ := fresh_of_closedBehind h Ar.below Ar.rch.2 a.2 Ar.closed
  have hshape : (a.1.2.st.oracles.getD x.f.rows.fresh default).shape =
      shapeAt y.2.P ((Sg.sent.headD #[]).size - 1) := by
    rw [e1, T₀.hs]
    exact mask0_shape_getD h O a Ar.rch Ar.failed hS (by rw [← e1]; exact e2) rfl
  have hseat : (maskTree 0, maskPart 0) =
      seatAtMember cF.blocksInOrder y.1 y.2.P ((Sg.sent.headD #[]).size - 1) := by
    rw [hy1, ← hplan]
    exact (mask_seat_at_head h O hS).1
  obtain ⟨hτ, hτ'⟩ := tree_in_plan plan T₀.hq
  have hb' : y.1 < nb := by
    rw [hy1]
    exact hb
  obtain ⟨Xo', tr, M, hrw⟩ := fresh_at h O Ar A hft hmk T hbs k mm Zs hcodes hmask hP hb' hblk hcount
    plan hpc T₀.hq hseat hshape
    (fun h0 => by
      rw [T₀.hs] at h0 ⊢
      exact hfc h0)
    _ (k1_table_at_join F cells tok T hbs hfr htab hfix hy k mm ho hτ')
  exact ⟨_, _, _, _, _, _, M, hrw, hmask', htail'⟩

/-- Of a sender's rows the mask rows and their tails read no data. -/
theorem rowsR_mask (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (d d' : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride)) (n : Nat) :
    (K1.rowsR P ride d c n).mask = (K1.rowsR P ride d' c n).mask ∧
      (K1.rowsR P ride d c n).maskTl = (K1.rowsR P ride d' c n).maskTl :=
  ⟨rfl, rfl⟩

set_option maxRecDepth 1000000 in
/-- **The senders stand in front of the switch that reads them**, by Lean's kernel, at the written
places; a control: at the switch's own number, no. -/
theorem sendersBeforeW : (placesW.all fun p => decide (2 < switchNo p) &&
      ([false, true].all fun d => decide (VerifiableInference.Desc.K1.noL (p.link - 1) d < switchNo p)) &&
      placesW.all fun p₀ => decide (p₀.link < p.link → switchNo p₀ < switchNo p)) = true ∧
    (placesW.all fun p => decide (switchNo p < switchNo p)) = false := by
  decide +kernel

/-- A member's shape among the true members. -/
theorem shapeOf_true (S : Statement) (old : SingleRows)
    (hk : old.layout.kept.size = old.layout.members.size) {w : Nat}
    (hw : w < old.layout.members.size) :
    shapeOf (VerifiableInference.Desc.K2.Honest.membersTrue S old) w =
      (S.oracles.getD (old.layout.members.getD w noId) default).shape := by
  have hw2 : w < old.layout.kept.size := by omega
  have hl : (old.layout.members.zip old.layout.kept).toList[w]? =
      some (old.layout.members[w], old.layout.kept[w]) := by
    rw [Array.toList_zip, List.getElem?_zip_eq_some]
    exact ⟨by simp [hw], by simp [hw2]⟩
  have e : old.layout.members.getD w noId = old.layout.members[w] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
    rfl
  unfold shapeOf VerifiableInference.Desc.K2.Honest.membersTrue
  rw [List.getElem?_map, hl, e]
  rfl

/-- **A written place's sizes are the written ones.** -/
theorem sizes_written {p : SwitchPlace} (hp : p ∈ placesW) :
    p.sizes.codes = Johnson.G.codesFull2 ∧ p.sizes.code = proofSizedFull.request.code ∧
      p.sizes.maskCode = proofSizedFull.request.maskCode := by
  have tk := List.all_eq_true.1 placeSizesW.1 p hp
  unfold placeSizesOk at tk
  obtain ⟨rr, -, hrr⟩ := (Option.any_eq_true _ _).1 tk
  simp only [Bool.and_eq_true, beq_iff_eq] at hrr
  obtain ⟨⟨⟨⟨k1, k2⟩, k3⟩, -⟩, -⟩ := hrr
  exact ⟨k1, k2, k3⟩

/-- **SymbolsAre at a front, from JoinSenders.** The closing's return is hW; the first chain's way in
is hf₀; p₀ is the switch in front, where there is one. -/
theorem symbols_closed {W₀ Rc Tr Cells Tok V X' Pb Y : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} {p : SwitchPlace} (hpS : p ∈ switchPlaces Zp Bs.G₀) (el : p.link = m + 1)
    {a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str}
    {s₁ t : TS} {x : _root_.Tw.K2.Front} (Ar : ArmAt h m (switchNo p) a s₁ x)
    {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst} {own₀ : Y}
    {jobs : List (Nat × K1.SendJob (K1.PlaceIn ProofFile.Inst) Y)}
    {Oth : Others Bk (Local W₀ Rc ProofFile.Inst Tr)} {D : RowDataOf ProofFile.Inst}
    {rest : Nat → TreeLot Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D (fun v => (wit v).R) rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → Cells) (tok : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (T : Thread Bk TS ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) X' Pb) (hbs : T.bs = cF.blocksInOrder)
    (hfr : T.front = 0)
    (htab : T.table = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).fixed)
    {blk : Block TS ProofFile.Cl} {q : P2} (hrd : blk.rounds = rounds q) (hft : q.firstTree = 0)
    (hftT : T.ft = 0) (rs : List Fmt.RoundView) {cols : List VerifiableInference.Desc.OpenedColumn}
    (hF : blk.Fits q.firstTree rs cols) (ps : List Played) (R1 R2 : Fmt.Drawn) {En : Env}
    {k : Coins Bk} {s : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    (hA : Thr T (switchNo p) k s mm En)
    (hfill : fillCols (readsOf T.chain T.ft (En.add ps).stored (En.add ps).tree blk.rounds [R1, R2])
      [] = .ok cols)
    {r₁ r₂ : Fmt.RoundView} {z : _root_.Tw.K2.Sent} {S3 : Statement} {Yv : Array E}
    {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ (blk.shown q.firstTree rs cols) x z S3 Yv rows G cd)
    (hrf : roundsFit (rounds q) [r₁, r₂] = true)
    (hZ : VerifiableInference.Desc.K2.Honest.sizesAt x.st x.f.rows x.T = p.sizes)
    (hlog : cd.logN = (Johnson.G.codesFull2.base.getD proofSizedFull.request.code default).logN)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hc : handed 0 p k = some c)
    {Wl : VerifiableInference.Desc.K2.Honest.Left}
    (hW : lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p (D mm.st.input.x)
      ((wit mm.st.input).R) mm.st.heard (ProofFile.Honest.K2.Stretch.carried p.carries c.2.2) = .ok Wl)
    {zp : ProofFile.InstPub} {seen R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (hf₀ : VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take (switchNo p)) (ProofFile.startS Zp zp) seen
      C = .ok (a.1.2, R₀, C₀)) (hseen : seen.map (·.drawn) = mm.st.heard)
    (ds : List Fmt.Drawn) {Qs : Script Bk (Local W₀ Rc ProofFile.Inst Tr) Cells Tok MsgT}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    (S₀ : JoinSenders Zp Bs cF jobs D (fun v => (wit v).R) p k c Qs Vd mm.st.input mm.st.heard ds wit
      own₀) (hpW : p ∈ placesW) (hlenp : roundsTo cF.blocksInOrder (switchNo p) ≤ mm.st.heard.length)
    (hOp : 1 ≤ m → ∃ (p₀ : SwitchPlace) (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
      (V₀ : Nat → Johnson.Prover.Send.Rows), p₀ ∈ switchPlaces Zp Bs.G₀ ∧ p₀.link = m ∧ handed 0 p₀ k = some c₀ ∧
      carriedSame Bk p₀ p = true ∧ carriedFits Bk (switchPlaces Zp Bs.G₀) p = true ∧
      VerifiableInference.Desc.K13.Honest.roundsAhead cF.blocksInOrder
        (VerifiableInference.Desc.First.K2Caller.noAt (m - 1)) ≤ 0 + roundsTo cF.blocksInOrder (switchNo p₀) ∧
      (∀ s i ad, s < p₀.link → p.addrs s i = some ad →
        (D mm.st.input.x).heardAt ad ≤ 0 + roundsTo cF.blocksInOrder (switchNo p₀)) ∧
      switchRowsLaid D (fun v => (wit v).R) (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀))
        p₀ c₀ mm.st.input (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀) :
    VerifiableInference.Desc.K2.Honest.SymbolsAre p.sizes x.f.rows Wl
      (Positions.ofDraws q.logN r₂.drawn.poss) Yv := by
  have eS := segments_at_head h.toAtMg O
  have hW' := hW
  rw [eS] at hW'
  obtain ⟨y, hy, ey⟩ := lotClosingAt_kept hW'
  rw [el] at hy
  obtain ⟨Sg, y', W', kept', hSg, hC, hy1, hLeft, hMem⟩ := Ar.last hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hy1.symm.trans ey))
  obtain ⟨R, eR, -, -⟩ := ProofFile.Honest.K2.segmentLeft_inv hLeft
  have L := Ar.lay x.T
  rw [hZ] at L
  obtain ⟨G₀, HL⟩ := Ar.facts.ties.lay
  obtain ⟨g1, g2, g3, g4⟩ := VerifiableInference.Desc.K2.Honest.groupLayout_true x.st G₀ x.f.rows
    HL.members HL.kept HL.sizes
  have hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg := by
    rw [eS]
    exact hSg
  obtain ⟨c1, c2, c3⟩ := segmentsOf_at_front O Ar.facts.ties (List.mem_of_getElem? hS)
  have z1 : p.sizes.codes = x.st.codes := by
    rw [← hZ]
    rfl
  have z2 : p.sizes.code = x.f.rows.code := by
    rw [← hZ]
    rfl
  have z3 : p.sizes.maskCode = x.f.rows.maskCode := by
    rw [← hZ]
    rfl
  obtain ⟨k1, k2, k3⟩ := sizes_written hpW
  have hkk : x.f.rows.layout.kept.size = x.f.rows.layout.members.size := by
    rw [HL.kept, HL.members]
    exact HL.sizes
  have hsz := members_size_facts h O Ar.facts hS
  have hmk := L.masks
  have hmsz : ∀ {w : Nat} {i : Fin (loAt m).length},
      (membersOf (loAt m))[w]? = some i →
      shapeOf (VerifiableInference.Desc.K2.Honest.membersTrue x.st x.f.rows) w =
        ((loAt m).get i).1 := by
    intro w i hi
    obtain ⟨h1, -, h3⟩ := member_at_facts Ar.facts hi
    exact (shapeOf_true _ _ hkk h1).trans h3
  have hsb := List.all_eq_true.1 sendersBeforeW.1 p hpW
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hsb
  obtain ⟨⟨h2b, hlb0, hlb1⟩, hpb⟩ := hsb
  have hlenb : ∀ b, b ≤ switchNo p → 0 + roundsTo cF.blocksInOrder b ≤ mm.st.heard.length := fun b hb => by
    rw [Nat.zero_add, ProofFile.Honest.K13.roundsTo_eq_roundsAhead]
    refine Nat.le_trans (ProofFile.Honest.K13.roundsAhead_mono cF.blocksInOrder hb) ?_
    rw [← ProofFile.Honest.K13.roundsTo_eq_roundsAhead]
    exact hlenp
  have hlate : ∀ {q' : Nat}, q' < 2 → VerifiableInference.Desc.K1.noL (p.link - 1) (q' == 1) <
      switchNo p := by
    intro q' hq'
    cases hd : (q' == 1) with
    | false => exact hlb0
    | true => exact hlb1
  refine symbols_of_closing T hA blk q hrd (hftT.trans hft.symm) rs cols hF ps R1 R2 hfill A p.sizes
    (VerifiableInference.Desc.K2.Honest.membersTrue x.st x.f.rows) (x.f.rows.gamma.map OnBytes.Slice.readE)
    L (positions_below hrf) hLeft eR ?_ ?_ ?_ (hMem R eR) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [z1]
    exact c1
  · rw [z2]
    exact c2
  · rw [z3]
    exact c3
  · rw [← hseen]
    exact Ar.gamma hf₀ hSg
  · rw [z1, z2, z3]
    exact g1.trans HL.k.symm
  · rw [z1, z2, z3]
    exact g2.trans HL.h.symm
  · rw [z1, z2, z3]
    exact g3.trans HL.mainFirst.symm
  · rw [z1, z2, z3]
    exact g4.trans HL.maskFirst.symm
  · intro a' ha
    have hl : a' < ((List.range (VerifiableInference.Desc.K2.Honest.membersTrue x.st x.f.rows).length).filter
        fun w => VerifiableInference.Desc.K2.Honest.keptOf
          (VerifiableInference.Desc.K2.Honest.membersTrue x.st x.f.rows) w).length := by
      rw [L.keptNos]
      rw [L.keptShapes, List.length_map] at ha
      exact ha
    unfold VerifiableInference.Desc.K2.Honest.keptNo
    rw [List.getD_eq_getElem _ _ hl]
    exact List.mem_range.1 (List.mem_filter.1 (List.getElem_mem hl)).1
  · have eR' := eR
    rw [← eS] at eR'
    have hC' := hC
    rw [← eS] at hC'
    have hfcS : ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape.maskRows ≠ 0 →
        ((Sg.sent.headD #[]).getD ((Sg.sent.headD #[]).size - 1) default).shape.maskCode =
          proofSizedFull.request.maskCode := by
      intro h0
      have t := List.all_eq_true.1 fresh_codes_written.1 Sg (List.mem_of_getElem? hSg)
      simp only [Bool.or_eq_true, beq_iff_eq, Nat.add_zero] at t
      exact t.resolve_left h0
    -- the switch in front, where there is one: what the closing lays is what it sent
    have Key : 1 ≤ m → ∃ (p₀ : SwitchPlace)
        (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (V₀ : Nat → Johnson.Prover.Send.Rows),
        p₀ ∈ switchPlaces Zp Bs.G₀ ∧ p₀.link = m ∧ handed 0 p₀ k = some c₀ ∧
        switchNo p₀ < switchNo p ∧ Sg.sent.headD #[] = switchSent p₀.sizes p₀.others ∧
        switchRowsLaid D (fun v => (wit v).R)
          (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀ mm.st.input
          (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀ ∧
        (∀ n, n < (switchSent p₀.sizes p₀.others).size - 1 → R.rows[n]? = some (V₀ n)) ∧
        R.fresh = some (V₀ ((switchSent p₀.sizes p₀.others).size - 1)) := by
      intro hm1
      obtain ⟨p₀, c₀, V₀, hp₀, e₀, h₀, hs, hf, hgl, hD, hV⟩ := hOp hm1
      have hq₀ : p₀ ∈ placesW := by
        rw [← places_at_head h.toAtMg O]
        exact hp₀
      have hlt₀ : switchNo p₀ < switchNo p := hpb p₀ hq₀ (by omega)
      have hln : (mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))).length =
          0 + roundsTo cF.blocksInOrder (switchNo p₀) := by
        rw [List.length_take]
        exact Nat.min_eq_left (hlenb _ (Nat.le_of_lt hlt₀))
      obtain ⟨Sg₂, hSg₂, hK⟩ := key_of_lots h.toAtMg O 0 D (fun v => (wit v).R)
        Bs.G₀.first.layout hp₀ hpS (by omega) k c₀ h₀ c hc hs hf mm.st.input
        (hd₀ := mm.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) (hd := mm.st.heard)
        (List.take_prefix _ _)
        (fun Sg' hSg' g hg => by
          rw [hln]
          have hb25 := Ar.below
          exact Nat.lt_of_lt_of_le (gamma_below_at_head h.toAtMg O (m := p₀.link - 1) (by omega) Sg'
            (by rwa [show p₀.link - 1 + 1 = p₀.link by omega]) g hg) (by rw [e₀]; exact hgl))
        (fun s' i' ad h1 h2 => by
          rw [hln]
          exact hD s' i' ad h1 h2) hV (by rw [e₀]; exact hC')
      obtain rfl : Sg₂ = Sg := Option.some.inj (by rw [e₀] at hSg₂; exact hSg₂.symm.trans hS)
      obtain ⟨⟨Sg₃, -, hS₃, -, -, eS₃, -⟩, -⟩ := switchTies_at_head h.toAtMg O hp₀ hpS (by omega)
      obtain rfl : Sg₃ = Sg₂ := Option.some.inj (hS₃.symm.trans hSg₂)
      have hK' := hK R (by rw [e₀]; exact eR')
      exact ⟨p₀, c₀, V₀, hp₀, e₀, h₀, hlt₀, eS₃, hV, hK'.1, hK'.2⟩
    intro w hw
    rw [hsz] at hw
    have em : p.link - 1 = m := by omega
    by_cases hlast : w = (Sg.sent.headD #[]).size - 1 + 2
    · -- the fresh mask
      have e1 : w = x.f.rows.layout.members.size := by
        rw [hsz]
        exact hlast
      subst e1
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · obtain ⟨N, -, Fs⟩ := S₀.first (by omega)
        obtain ⟨-, -, y₂, hy₂, hy1', cs, e, B⟩ := Fs y' Sg (by rw [eS]; exact hC) hS
        have eF := copyShared_mask_at_head h O 0 p k c hc hS eR' B.plan B.ride ⟨y₂.2.P.place, 0⟩ B.cut
          e rfl B.entry B.owner B.start B.count
          (fun n => asShared (shapeAt y₂.2.P n) fun _ _ => VerifiableInference.Desc.K2.Honest.zeroG)
          rfl
        obtain ⟨P', Vr, kn, Xo, pp, tr, M, Fr⟩ := first_fresh h O Ar A hft hmk F cells tok T hbs hfr
          htab hfix k mm p.sizes k1 k3 hS hfcS h2b hy₂ hy1' B.plan B.cut R
          (by rw [eF]; rfl) (by rw [eF]; rfl)
        exact ⟨P', Vr, kn, Xo, pp, tr, M, fun e' => absurd e' (Nat.lt_irrefl _), fun _ => Fr⟩
      · obtain ⟨p₀, c₀, V₀, hp₀, e₀, h₀, hlt₀, eS₃, hV, -, hFr⟩ := Key hm1
        have hne : 0 < (switchSent p₀.sizes p₀.others).size := (last_first h O hp₀).1
        obtain ⟨P', Vr, kn, Xo, pp, tr, M, Fr⟩ := switch_fresh h O Ar A hft hmk F hin cells tok T hbs
          hfr htab hfix k mm p.sizes k1 k3 hp₀ e₀ hlt₀ c₀ h₀ hV hne
          (by rw [← eS₃]; exact hfcS) R hFr
        exact ⟨P', Vr, kn, Xo, pp, tr, M, fun e' => absurd e' (Nat.lt_irrefl _), fun _ => Fr⟩
    · have hlt : w < x.f.rows.layout.members.size := by
        rw [hsz]
        omega
      by_cases hfirst : w < (Sg.sent.headD #[]).size - 1
      · -- a message of the first sending
        rcases Nat.eq_zero_or_pos m with rfl | hm1
        · obtain ⟨N, -, Fs⟩ := S₀.first (by omega)
          obtain ⟨a1, -, -⟩ := Fs y' Sg (by rw [eS]; exact hC) hS
          obtain ⟨i, hi, es, eseat, -⟩ := first_seats_at_head h O hS hfirst
          have hps : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.seats
          rw [hps] at eseat
          have Tt := first_ties_at_head h O hS hfirst
          obtain ⟨P', Vr, kn, Xo, pp, tr, M1, M2⟩ := shared_member h O Ar A hft hlog hmk F cells tok T
            hbs hfr htab hfix k mm ds p.sizes k1 k2 k3 (Or.inl ⟨rfl, rfl⟩) h2b Tt.hq
            (hlenb 2 (Nat.le_of_lt h2b)) (a1 w hfirst) hi eseat es R _ (hmsz hi)
            (fun {J cs dataK e} B => by
              have eRow := copyShared_first_at_head h O 0 p k c hc hS eR' hfirst B.plan B.ride
                ⟨J.P.place, 0⟩ B.cut e rfl B.entry B.owner B.start B.count dataK
                (by rw [eS]; exact B.data)
              rw [List.getD_eq_getElem?_getD, eRow]
              rfl)
          exact ⟨P', Vr, kn, Xo, pp, tr, M1, fun _ => M2, fun e' => absurd e' (by omega)⟩
        · obtain ⟨p₀, c₀, V₀, hp₀, e₀, h₀, hlt₀, eS₃, hV, hRows, -⟩ := Key hm1
          have hw₀ : w < (switchSent p₀.sizes p₀.others).size - 1 := by
            rw [← eS₃]
            exact hfirst
          obtain ⟨P', Vr, kn, Xo, pp, tr, M1, M2⟩ := switch_member h O Ar A hft hlog hmk F hin cells tok
            T hbs hfr htab hfix k mm p.sizes k1 k2 k3 hp₀ e₀ hlt₀ c₀ h₀ hV hw₀ R _
            (fun i hi => hmsz hi)
            (by
              rw [List.getD_eq_getElem?_getD, hRows w hw₀]
              rfl)
          exact ⟨P', Vr, kn, Xo, pp, tr, M1, fun _ => M2, fun e' => absurd e' (by omega)⟩
      · -- a later sender
        obtain ⟨q', rfl⟩ : ∃ q', w = (Sg.sent.headD #[]).size - 1 + q' :=
          ⟨w - ((Sg.sent.headD #[]).size - 1), by omega⟩
        have hq' : q' < 2 := by omega
        obtain ⟨i, hi, es, eseat, -⟩ := later_seats_at_head h O hS hq'
        have hps : P5J.At.pseats Zp = P5T.psFull := h.toAtMg.seats
        rw [hps] at eseat
        obtain ⟨hl2, hties⟩ := later_ties_at_head h O hS
        have hlq : q' < ((Sg.sent.drop 1).flatMap (·.toList)).length := by
          rw [hl2]
          exact hq'
        have Tt := hties q' _ (List.getElem?_eq_getElem hlq)
        have hPs : SenderAt Zp Bs (VerifiableInference.Desc.K1.parL Zp Bs.G₀ m (q' == 1))
            (VerifiableInference.Desc.K1.noL m (q' == 1)) :=
          Or.inr (Or.inl ⟨m, q' == 1, Ar.below, rfl, rfl⟩)
        have hnb : VerifiableInference.Desc.K1.noL m (q' == 1) < switchNo p := by
          have := hlate hq'
          rwa [em] at this
        have hrowL : ∀ {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) Y} {cs : Cs (K1.dueR J.P J.ride)}
            {dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)} {e : Ahead} {dat}, K1.rideOf none = J.ride →
            VerifiableInference.Desc.K1.parL Zp Bs.G₀ m (q' == 1) = J.P →
            K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs →
            ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[
              y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q']? = some e →
            e.owner = ⟨J.P.place, 0⟩ → e.start = K1.startR J.P J.ride 0 →
            e.count = K1.dueMsg J.P.codes (shapeAt J.P 0) (J.ride 0) →
            dataK 0 = asShared (shapeAt J.P 0) dat →
            dat = lotOwn (segmentsOf Zp Bs.G₀) p (D mm.st.input.x) ((wit mm.st.input).R) mm.st.heard
              (0 + m) ((Sg.sent.headD #[]).size - 1 -
                (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q') →
            R.rows.getD ((Sg.sent.headD #[]).size - 1 + q') zeroMessage =
              K1.rowsR J.P J.ride dataK cs 0 := by
          intro J cs dataK e dat hρ hPl hcut hent ho' hst' hco hda hdt
          subst hdt
          have eRow := copyShared_later_at_head h O 0 p k c hc hS eR' (List.getElem?_eq_getElem hlq)
            hPl hρ ⟨J.P.place, 0⟩ hcut e rfl hent ho' hst' hco dataK hda
          rw [List.getD_eq_getElem?_getD, eRow]
          rfl
        rcases Nat.eq_zero_or_pos m with rfl | hm1
        · obtain ⟨N, -, Fs⟩ := S₀.first (by omega)
          obtain ⟨-, a2, -⟩ := Fs y' Sg (by rw [eS]; exact hC) hS
          obtain ⟨P', Vr, kn, Xo, pp, tr, M1, M2⟩ := shared_member h O Ar A hft hlog hmk F cells tok T
            hbs hfr htab hfix k mm ds p.sizes k1 k2 k3 hPs hnb Tt.hq
            (hlenb _ (Nat.le_of_lt hnb)) (a2 q' hq') hi eseat es R _ (hmsz hi)
            (fun {J cs dataK e} B => hrowL B.ride B.plan B.cut B.entry B.owner B.start
              B.count B.data (by rw [eS]))
          exact ⟨P', Vr, kn, Xo, pp, tr, M1, fun _ => M2, fun e' => absurd e' (by omega)⟩
        · obtain ⟨p₀, c₀, V₀, hp₀, e₀, -, -, -, -, -, -⟩ := Key hm1
          have a2 := S₀.later p₀ hp₀ (by omega) (by omega) y' Sg (by rw [em]; exact hC')
            (by rw [em]; exact hS) q' hq'
          rw [em] at a2
          obtain ⟨P', Vr, kn, Xo, pp, tr, M1, M2⟩ := shared_member h O Ar A hft hlog hmk F cells tok T
            hbs hfr htab hfix k mm ds p.sizes k1 k2 k3 hPs hnb Tt.hq
            (hlenb _ (Nat.le_of_lt hnb)) a2 hi eseat es R _ (hmsz hi)
            (fun {J cs dataK e} B => hrowL B.ride B.plan B.cut B.entry B.owner B.start
              B.count B.data rfl)
          exact ⟨P', Vr, kn, Xo, pp, tr, M1, fun _ => M2, fun e' => absurd e' (by omega)⟩

/-- **THE TOP: SymbolsAre at each switch, at the joined Script, from JoinSenders.** Premises: the
head, the opening, onlineProverFromPublicFiles's return, the letters of stepAsks_of_join, that the input is typed, and
JoinSenders at the run's coins, input and challenges. -/
theorem symbols_at_join {W₀ Rc Tr X₀ X Y X₂ : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → P5J.CellsM OnBytes.Flat.numsFull)
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
               Bs.G₀) (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → ReadsLight Zp Bs.G₀ v.x)
    {p : SwitchPlace} (hp : p ∈ placesW)
    {blk : Block TS ProofFile.Cl} {Pp : P1K2.Prep} {n : P1K2.Nums} {nm : String}
    {st : VerifiableInference.Desc.First.K2.At} {before : TS → Except String TS}
    {after : TS → TS → Except String TS}
    (hb : (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).bs[switchNo p]? = some blk)
    (hP : P1K2.prepOf Zp Bs.G₀ = some Pp) (hn : P1K2.numsAt Pp p.place.link = some n)
    (hArm : SwitchArm Zp Bs.G₀ p st before after)
    {k : Coins A.B} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : ThrS (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread Said (switchNo p) k s m En)
    (hd : drawsFit blk.rounds ds = true)
    (hS : (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.Stepped blk k s m En ds y cols s')
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} {Wl : Left}
    {r₁ r₂ : Fmt.RoundView} {s₁ t : TS} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Yv : Array E} {rows : List OnBytes.Row} {Gr : Group} {cd : Code}
    (hc : handed 0 p k = some c)
    (hW : lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ m.st.input.x) ((wit m.st.input).R)
      (m.st.heard.take (m.st.heard.length - 0)) (ProofFile.Honest.K2.Stretch.carried p.carries c.2.2) = .ok Wl)
    (hr : (roundsOf y.1).map noDigest = [r₁, r₂]) (hbf : before s = .ok s₁)
    (Ay : AtYes (IM.k2P Zp p.place nm st n) s₁ t r₁ r₂
      (shownGroups (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.ft blk (roundsOf y.1) cols) x z S3 Yv rows Gr cd)
    (hty : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub)
    (S₀ : JoinSenders Zp Bs cF (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) p k c (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth)
      (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid m.st.input m.st.heard ds wit own₀) :
    SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl
      (Positions.ofDraws (IM.k2P Zp p.place nm st n).logN r₂.drawn.poss) Yv := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hB := pure_book_written h hA
  have F := joinFit_full h O hA no (K1.lotData Sz.ref) Dd 0 wit own₀ (withSwitchData Sz.ref
    (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R) rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂
  rw [← hO] at F
  have hin : ShareIn (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData
               Sz.ref) Zp Bs.G₀) (fun v => (wit v).R) rest) Oth := by
    rw [hO]
    exact shareIn_add_left _ _
  have hmem : cF.blocksInOrder[switchNo p]? = some blk := hb
  have hlenb : switchNo p ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hmem).1
  have y₀ := anyStrings (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))
  have hR := rch_at_head h A.H _ test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk
    hst hlenb hT hty y₀
  have hsz := sizes_at_yes h O hpS hArm hR.1 hbf nm Ay
  have hsf := sizes_front_at_yes h O hpS hArm hR.1 hbf nm Ay
  have hZ : sizesAt x.st x.f.rows x.T = p.sizes := hsf.symm.trans hsz
  rw [hsz]
  have hft : (IM.k2P Zp p.place nm st n).firstTree = 0 :=
    congrArg (·.firstTree) (VerifiableInference.Desc.K13.Law.gpOf_in_scope h.scope h.laid.pub
      (VerifiableInference.Desc.K1.pin1_atAll h))
  obtain ⟨Pp', n', nm', st', -, -, hP', hn', -, ⟨-, hrd, -⟩, -, -⟩ := k2_block_at_head h O hpS hmem
  have ePp : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
  rw [ePp] at hn'
  have en : n' = n := Option.some.inj (hn'.symm.trans hn)
  rw [en] at hrd
  have hrd' : blk.rounds = rounds (IM.k2P Zp p.place nm st n) := hrd
  obtain ⟨hFits, -, -⟩ := (VerifiableInference.Desc.step_iff _ _ _ _ _ _ _).1 hS.2
  have hF : blk.Fits (IM.k2P Zp p.place nm st n).firstTree (roundsOf y.1) cols := by
    rw [hft]
    exact hFits
  have A' : AtYes (IM.k2P Zp p.place nm st n) s₁ t r₁ r₂
      (blk.shown (IM.k2P Zp p.place nm st n).firstTree (roundsOf y.1) cols) x z S3 Yv rows Gr cd := by
    rw [hft]
    exact Ay
  have hrf : roundsFit (rounds (IM.k2P Zp p.place nm st n)) [r₁, r₂] = true := by
    rw [← hr, VerifiableInference.Desc.roundsFit_noDigest, ← hrd']
    exact hFits.1
  obtain ⟨d₁, d₂, hq⟩ : ∃ d₁ d₂, rounds (IM.k2P Zp p.place nm st n) = [d₁, d₂] := ⟨_, _, rfl⟩
  rw [hrd', hq] at hd
  obtain ⟨R1, R2, rfl, -⟩ := draws_two d₁ d₂ ds hd
  have hfill := hS.1.2
  obtain ⟨hseen, -, -, -, s₀, cols₀, hbeg, -, hfold⟩ := hT.1.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hfold
  obtain ⟨k1, k2, -⟩ := sizes_written hp
  have z1 : x.st.codes = Johnson.G.codesFull2 := by
    rw [← k1, ← hZ]
    rfl
  have z2 : x.f.rows.code = proofSizedFull.request.code := by
    rw [← k2, ← hZ]
    rfl
  have hlog : cd.logN =
      (Johnson.G.codesFull2.base.getD proofSizedFull.request.code default).logN := by
    have e := Ay.code
    rw [Ay.sent.codes, z1, z2] at e
    rw [Array.getD_eq_getD_getElem?, e]
    rfl
  have hW' : lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ m.st.input.x) ((wit m.st.input).R)
      m.st.heard (ProofFile.Honest.K2.Stretch.carried p.carries c.2.2) = .ok Wl := by
    simpa using hW
  have hlenp : roundsTo cF.blocksInOrder (switchNo p) ≤ m.st.heard.length := by
    have e := drawsFit_length _ _ hT.1.2.1
    rw [e, List.length_append]
    exact Nat.le_add_left _ _
  have hOp : ∀ m', p.link = m' + 1 → 1 ≤ m' → ∃ (p₀ : SwitchPlace)
      (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (V₀ : Nat → Johnson.Prover.Send.Rows),
      p₀ ∈ switchPlaces Zp Bs.G₀ ∧ p₀.link = m' ∧ handed 0 p₀ k = some c₀ ∧
      carriedSame A.B p₀ p = true ∧ carriedFits A.B (switchPlaces Zp Bs.G₀) p = true ∧
      VerifiableInference.Desc.K13.Honest.roundsAhead cF.blocksInOrder
        (VerifiableInference.Desc.First.K2Caller.noAt (m' - 1)) ≤
          0 + roundsTo cF.blocksInOrder (switchNo p₀) ∧
      (∀ s i ad, s < p₀.link → p.addrs s i = some ad →
        (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ m.st.input.x).heardAt ad ≤
          0 + roundsTo cF.blocksInOrder (switchNo p₀)) ∧
      switchRowsLaid (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R)
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀ m.st.input
        (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀ := by
    intro m' el h1
    have hW0 := List.all_eq_true.1 frontSwitchW p hp
    rw [Bool.or_eq_true] at hW0
    obtain ⟨p₀, hq₀, hl₀⟩ : ∃ p₀ ∈ placesW, p₀.link + 1 = p.link := by
      rcases hW0 with q | q
      · exact absurd (of_decide_eq_true q) (by omega)
      · obtain ⟨p₀, a, b⟩ := List.any_eq_true.1 q
        exact ⟨p₀, a, of_decide_eq_true b⟩
    have hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀ := by
      rw [places_at_head h.toAtMg O]
      exact hq₀
    have e₀ : p₀.link = m' := by omega
    obtain ⟨c₀, h₀⟩ := Option.isSome_iff_exists.1 (handed_at_book h O hB hp₀ k)
    have hval := hT.1.2.2.2.2.2.2
    have hr₀ := rows_isSome (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p₀
      (closing_at_head h.toAtMg O p₀ hp₀) c₀ m.st.input
      (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀)))
    rw [serves_at_head h.toAtMg O p₀ hp₀, roomy_at_head h.toAtMg O p₀ hp₀,
      publicOk_of_reads h O (hR4 m.st.input hval) p₀ hp₀, fits_at_head h.toAtMg O p₀ hp₀] at hr₀
    obtain ⟨V₀, hV₀⟩ : ∃ V₀, switchRowsLaid (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
        (fun v => (wit v).R) (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀
        m.st.input (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀ := by
      cases e : switchRowsLaid (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
        (fun v => (wit v).R) (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀
        m.st.input (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) with
      | ok V' => exact ⟨V', rfl⟩
      | error _ =>
        rw [e] at hr₀
        cases hr₀
    obtain ⟨hf, hs⟩ := book_tests_at_head h hB hq₀ hp hl₀
    have hf' : carriedFits A.B (switchPlaces Zp Bs.G₀) p = true := by
      rw [places_at_head h.toAtMg O]
      exact hf
    have t := List.all_eq_true.1 placesCountsW p₀ hq₀
    simp only [Bool.and_eq_true, decide_eq_true_eq] at t
    refine ⟨p₀, c₀, V₀, hp₀, e₀, h₀, hs, hf', ?_, ?_, hV₀⟩
    · rw [Nat.zero_add, ProofFile.Honest.K13.roundsTo_eq_roundsAhead, ← e₀]
      exact ProofFile.Honest.K13.roundsAhead_mono cF.blocksInOrder t.1
    · exact fun s i ad hs' ha => heard_at_switches h O Sz.ref p₀ hp₀ p hpS m.st.input.x s i ad hs' ha
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hp)
  have hfold' : VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take (switchNo p))
      (ProofFile.startS Zp m.st.input.x.pub) m.seen cols₀ = .ok (s, [], []) := hfold
  have hArm' := hArm
  rcases hArm' with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hbf
    have h23 : p.link - 1 < 23 := by omega
    have el : p.link = (p.link - 1) + 1 := by omega
    have eno : switchNo p = 14 * ((p.link - 1) + 1) + 2 := by
      rw [show switchNo p = 14 * p.link + 2 from ei, ← el]
    have hR' : h.toAtMg.rch (14 * ((p.link - 1) + 1) + 2) ((m.st.input.x.pub, s), y₀) := by
      rw [← eno]
      exact hR
    obtain ⟨hstd, -⟩ := link_door h h23 _ hR'
    have hf : frontAt (ProofFile.pAtK2 Zp (p.link - 1)) s = some x :=
      (frontAt_stands (q := IM.k2P Zp p.place nm .link n) hstd s).trans Ay.front
    have Ar : ArmAt h (p.link - 1) (switchNo p) ((m.st.input.x.pub, s), y₀) s x := by
      rw [eno]
      exact link_arm h h23 _ hR' hf
    exact symbols_closed h O hpS el Ar F hin cellsQ tokQ _ rfl rfl rfl rfl hrd' hft rfl (roundsOf y.1)
      hF y.1 R1 R2 hT.1 hfill A' hrf hZ hlog hc hW' hfold' hseen [R1, R2] S₀ hp hlenp
      (hOp _ el)
  · obtain rfl : s = s₁ := Except.ok.inj hbf
    have e24 : p.link = 23 + 1 := by
      rw [hlk, ep]
      rfl
    have eno : switchNo p = 339 := ei
    have hR' : h.toAtMg.rch 339 ((m.st.input.x.pub, s), y₀) := by
      rw [← eno]
      exact hR
    obtain ⟨hstd, -⟩ := head_door h _ hR'
    have hf : frontAt (ProofFile.pAtK2 Zp 23) s = some x :=
      (frontAt_stands (q := IM.k2P Zp p.place nm .head n) hstd s).trans Ay.front
    have Ar : ArmAt h 23 (switchNo p) ((m.st.input.x.pub, s), y₀) s x := by
      rw [eno]
      exact head_arm h _ hR' hf
    exact symbols_closed h O hpS e24 Ar F hin cellsQ tokQ _ rfl rfl rfl rfl hrd' hft rfl
      (roundsOf y.1) hF y.1 R1 R2 hT.1 hfill A' hrf hZ hlog hc hW' hfold' hseen [R1, R2] S₀ hp hlenp
      (hOp _ e24)
  · have e25 : p.link = 24 + 1 := by
      rw [hlk, ep]
      rfl
    have eno : switchNo p = 353 := ei
    have hR' : h.toAtMg.rch 353 ((m.st.input.x.pub, s), y₀) := by
      rw [← eno]
      exact hR
    obtain ⟨hstd, -⟩ := fin_door h _ hR' hbf
    have hf : frontAt (ProofFile.pAtK2 Zp 24) s₁ = some x :=
      (frontAt_stands (q := IM.k2P Zp p.place nm .finish n) hstd s₁).trans Ay.front
    have Ar : ArmAt h 24 (switchNo p) ((m.st.input.x.pub, s), y₀) s₁ x := by
      rw [eno]
      exact fin_arm h _ hR' hbf hf
    exact symbols_closed h O hpS e25 Ar F hin cellsQ tokQ _ rfl rfl rfl rfl hrd' hft rfl
      (roundsOf y.1) hF y.1 R1 R2 hT.1 hfill A' hrf hZ hlog hc hW' hfold' hseen [R1, R2] S₀ hp hlenp
      (hOp _ e25)

end AtFullSide.K2

#print axioms AtFullSide.K2.handed_lends
#print axioms AtFullSide.K2.shared_member
#print axioms AtFullSide.K2.switch_member
#print axioms AtFullSide.K2.switch_fresh
#print axioms AtFullSide.K2.first_fresh
#print axioms AtFullSide.K2.rowsR_mask
#print axioms AtFullSide.K2.sendersBeforeW
#print axioms AtFullSide.K2.shapeOf_true
#print axioms AtFullSide.K2.sizes_written
#print axioms AtFullSide.K2.symbols_closed
#print axioms AtFullSide.K2.symbols_at_join
