-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsHead.lean: VecTie (ReadsCore.lean) AT THE OUTPUT HEAD's READS: at a stand behind member 342 the maker of the head's vector of reads returns at what was heard, and its vector is the reading at the state's own tables.

  headVals_vec_ok    the maker's vector returns where its heard record, its tables and the parts' test do
  head_tables_cov    the head's tables return, and their list is the record's; the state in front has its covered positions; the record's matrices are the plan's
  vecTie_head_of     the statement, under its public premises

The stand's list of challenges is read as far as the seat's number heardOf. Public premises on the plans and the numbers are handed on; hPhi, that each table of the record has as many weights as its length, stands as a premise on a stand, to be paid with phi_sizes_at_reads.

This letter is for the honest run's own forms alone. NEVER ON SOUNDNESS's ROAD.
NO PROPERTY IS CLAIMED. -/
import AtFullSide.K1.VecTie
import Johnson.Desc.ProofFile.Honest.K1.Law.HeadRecord
import Johnson.Desc.ProofFile.Honest.K1.Law.ReqAtStand
import Johnson.Desc.ProofFile.Honest.K1.Law.U3ValHead
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.Thread.MemberFrom
import Johnson.Desc.ProofFile.Honest.K6.HeardAtYes
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat
import Johnson.P4R.FreeAt341N
import Johnson.Desc.K1.Law.LaterAtRecord
import Johnson.Desc.ProofFile.Honest.K1.Law.HeadSentence
import Johnson.Desc.K8.Honest.HeadShapes
import Johnson.HonestTrace.U3Fit.ReturnsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.CoveredAtReturns
import Johnson.Desc.ProofFile.Honest.K1.Law.HeadLook
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.K8.ReadsQuiet (head)
open VerifiableInference.Desc.Kinds (Head.Par Head.Request)
open VerifiableInference.Desc.Kinds.Head (requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6 readsOf K6MemberIs)
open VerifiableInference.Desc.K1 (commitAtS_here commitAtS_slots commit_head)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace.U3 (covOf u3Seats placeIn SegVals valsAt headVals headAt partsFit partsOf sizesOf)
open ProofFile (Spot spotsOf)
open ProofFile.Honest.K4 (k4LookOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K6 (headHeardWhole headHeardWholeAt headHearingOf headParAt headInFront
  tables_nine tables_heardOf tables_at_accept)
open ProofFile.Honest.FirstThread
open OnBytes.HonestTrace (parOfMats)
open OnBytes.Tie.Pv.Tail.Closed (headShapes shapesOf)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K8 (cellsAtOf)

/-- **The maker's vector returns where its three steps do.** -/
theorem headVals_vec_ok {Z : ProofFile.Pub} {G : ProofFile.Ground} {cov : Head.Covered} {sps : List Spot} {seg : ℕ}
    {SV : SegVals} (h : headVals Z G cov sps seg = .ok SV) {k6 k3 : Spot × ℕ}
    (p6 : placeIn Z sps seg .K6 = .ok k6) (p3 : placeIn Z sps seg .K3 = .ok k3)
    {hd : List Fmt.Drawn} {x : Head.Heard} {t : Head.Tables}
    (hx : headHeardWholeAt (headParAt G) (requestOf Z.s₀) 0 (k4LookOf G.W.HLy.fs k3.2 hd) k6.2 hd = .ok x)
    (ht : ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t)
    (hp : partsFit (sizesOf G.W.H.tl.mats) (OnBytes.HonestTrace.U3.partsOf t.funs) (G.W.H.nU.getD 2 0) = .ok ()) :
    ∃ vec, SV.vec hd = .ok vec := by
  unfold headVals at h
  obtain ⟨k6', hk6, h⟩ := bind_eq_ok h
  obtain ⟨k3', hk3, h⟩ := bind_eq_ok h
  obtain rfl : k6' = k6 := Except.ok.inj (hk6.symm.trans p6)
  obtain rfl : k3' = k3 := Except.ok.inj (hk3.symm.trans p3)
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain rfl := Except.ok.inj h
  have hA : headAt G.W.hS G.W.HLy G.W.H cov x = .ok fun cell =>
      VerifiableInference.Desc.First.K8.Honest.readAt (parOfMats G.W.H.tl.mats) t.funs.toList cell := by
    unfold headAt
    rw [ht]
    show (match partsFit (sizesOf G.W.H.tl.mats) (OnBytes.HonestTrace.U3.partsOf t.funs) (G.W.H.nU.getD 2 0) with
      | .error e => (Except.error e : Except String _)
      | .ok _ => .ok fun cell => VerifiableInference.Desc.First.K8.Honest.readAt (parOfMats G.W.H.tl.mats) t.funs.toList cell) = _
    rw [hp]
  refine ⟨fun C => VerifiableInference.Desc.First.K8.Honest.readAt (parOfMats G.W.H.tl.mats) t.funs.toList (cellsAtOf C (matsOwn G.W seg)), ?_⟩
  show (do
    let x ← headHeardWholeAt (headParAt G) (requestOf Z.s₀) 0 (k4LookOf G.W.HLy.fs k3'.2 hd) k6'.2 hd
    let v ← headAt G.W.hS G.W.HLy G.W.H cov x
    pure fun C => v (cellsAtOf C (matsOwn G.W seg))) = _
  rw [hx]
  show (do
    let v ← headAt G.W.hS G.W.HLy G.W.H cov x
    pure fun C => v (cellsAtOf C (matsOwn G.W seg))) = _
  rw [hA]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The tables return, and their list is the record's.** -/
theorem head_tables_cov (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Zq : ProofFile.Pub} {G : ProofFile.Ground} {Xl : LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    (hGW : G.W = P5J.At.X Zp) (hquiet : IM.k1Quiet G 24 Xl = head (p8K6 G.W 24))
    (hTT : G.W.hS.T = G.W.T) (hVV : G.W.hS.V = G.W.P.h.V)
    {blk : Block TS ProofFile.Cl}
    (hU : blk.UnderR ((IM.k1Reads Zq G 24 Xl pr reads).retype : Block TS ProofFile.Cl))
    (hb : 342 ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 342 k s m E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
      cols s')
    {tl : HTailF2} (htl : s'.tl? = some tl) {N base : ℕ}
    (hbase : base =
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front + roundsTo cF.blocksInOrder 341)
    (hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt G) 8 = b₆.rounds.length)
    (hcut : base + headInFront (headParAt G) 8 ≤ N) {g₂ : Forest.Heard}
    (hLook : ∀ o g₁, s.here = .head o → o.lookHeard = some g₁ →
      g₁.zx = g₂.zx ∧ g₁.zk = g₂.zk ∧ g₁.zb0 = g₂.zb0 ∧ g₁.zb1 = g₂.zb1 ∧ g₁.shape = g₂.shape)
    {q : Head.Request} {xm : Head.Heard}
    (hx : headHeardWholeAt (headParAt G) q 0 g₂ base (m.st.heard.take N) = .ok xm) :
    ∃ t c, ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
      ((covOf Zq G m.st.input.x).toOption.getD default) xm = .ok t ∧ tl.funs = t.funs ∧
      s.covered G.W.T G.W.P.h.V = .ok c ∧ tl.mats = G.W.H.tl.mats := by
  -- (1) K6's member, and the one state in front of it
  obtain ⟨b₆, hb₆, M₀⟩ := P4.k6_member_at_mg h.toAtMg
  have M : K6MemberIs G.W 24 ProofFile.sameReply IM.k6Place b₆ := by
    rw [hGW]
    exact M₀
  have hM : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Made 342 k s m E := by
    have hT' := hT
    unfold Thr at hT'
    exact hT'.2.2.2.2.1
  obtain ⟨sj, sj', rs, c, n, rs', c', hR, hst, hdr, hfold⟩ :=
    made_member_reach (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ProofFile.startS Zp) m.st.input.x.pub (b := 342) (j := 341) (by omega) hb hb₆ (fun _ h0 => h0) hM
  -- (2) the fold behind it is empty
  have hnil : ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.take 342).drop
      (341 + 1) = [] := List.drop_eq_nil_of_le (by rw [List.length_take]; omega)
  rw [hnil] at hfold
  obtain rfl : s = sj' := congrArg Prod.fst (foldBlocks_nil _ _ _ _ _ hfold)
  -- (3) the ledger in front is well laid
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have hWL := P4.wellLaid_341 h.scope h.reads O
    (fun b hb' => P5J.flat_ok h.toAtMg b (List.mem_of_getElem? hb')) hR G.W.hS
    (VerifiableInference.Desc.Kinds.Head.Law.readsOf G.W)
  -- (4) what the member's yes leaves
  obtain ⟨o, x₀, g₁, yk, hso, hox, hol, -, -, -, -, -, -, htab⟩ := tables_at_accept M hst hWL
  -- (5) through the reads' member
  obtain ⟨r₁, r₂, gs, gs₁, rs₂, gs₂, s₁, a, cov, x₁, t₁, -, h1, -, ha, hcov, hx₁, ht₁, hmats, -,
    hfun⟩ := head_record hquiet hU hS htl
  obtain ⟨-, -, hh⟩ := commitAtS_here _ _ _ _ s s₁ _ _ h1
  have hop : o.opened = true := by
    rcases hh with ⟨a', _, e, _⟩ | ⟨a', _, e, _⟩ | ⟨a', _, e, _, e2, _⟩
    · rw [hso] at e
      cases e
    · rw [hso] at e
      cases e
    · rw [hso] at e
      cases e
      exact e2
  obtain ⟨_, _, _, yy, _, _, _, e1, _⟩ := commitAtS_slots h1
  have hs₁ := e1.trans (commit_head hso hop _ _ _)
  rw [hs₁] at ha hcov
  have hax : a.x = o.x := by
    cases ha
    rfl
  have hxx : x₁ = x₀ := by
    rw [hax, hox] at hx₁
    exact (Option.some.inj hx₁).symm
  subst hxx
  have hcs : s.covered G.W.T G.W.P.h.V = .ok cov := by
    rw [← hTT, ← hVV]
    exact hcov
  -- (6) the spelling
  have hxm : xm = headHeardWhole (headParAt G) q 0 g₂
      (((m.st.heard.take N).drop base).take (headInFront (headParAt G) 8)) := by
    unfold headHeardWholeAt at hx
    dsimp only at hx
    split at hx
    · exact (Except.ok.inj hx).symm
    · cases hx
  have hown : ((m.st.heard.take N).drop base).take (headInFront (headParAt G) 8) =
      rs.map (·.drawn) := by
    rw [hdr, List.drop_take, List.take_take, Nat.min_eq_left (by omega), hbase, hlen b₆ hb₆]
    rfl
  -- (7) one answer
  obtain ⟨k0, k1, k2, k3, k4⟩ := hLook o g₁ hso hol
  have E1 : ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x₁ =
      ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov xm := by
    rw [htab, hxm, hown]
    exact tables_whole _ _ _ _ (headParAt G) _ q _ 0 _ k0 k1 k2 k3 k4
  have E2 := tables_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT Zq G hcs G.W.hS
    G.W.HLy G.W.H xm
  have E4 : ReadsQuiet.tables G.W.hS G.W.HLy G.W.H
      ((covOf Zq G m.st.input.x).toOption.getD default) xm = .ok t₁ := E2.trans (E1.symm.trans ht₁)
  exact ⟨t₁, cov, E4, hfun, hcs, hmats⟩


/-- **VecTie at the output head's reads, under its public premises.** -/
theorem vecTie_head_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} {pr : ℕ}
    {reads : Option (List ℕ)} (hquiet : IM.k1Quiet G 24 Xl = head (p8K6 G.W 24))
    (hGW : G.W = P5J.At.X Zp) (hTT : G.W.hS.T = G.W.T) (hVV : G.W.hS.V = G.W.P.h.V)
    {blk₁ : Block TS ProofFile.Cl} (hblk₁ : cF.blocksInOrder[342]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Zp G 24 Xl pr reads).retype : Block TS ProofFile.Cl))
    {sps : List Spot} (hsps : spotsOf Zp.cuts = some sps) {Y : LinkH} (hY : G.built[24]? = some Y)
    (hkind : Y.kind = 2) {k6 k3 : Spot × ℕ}
    (p6 : placeIn Zp sps 24 .K6 = .ok k6) (p3 : placeIn Zp sps 24 .K3 = .ok k3)
    (hbase : k6.2 = roundsTo cF.blocksInOrder 341) (hbase3 : k3.2 = roundsTo cF.blocksInOrder 340)
    (hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt G) 8 = b₆.rounds.length)
    {A : MsgAddr} (hcut : k6.2 + headInFront (headParAt G) 8 ≤
      OnBytes.HonestTrace.heardOf (u3Seats Zp G) A)
    (hfull : k6.2 + headInFront (headParAt G) 8 ≤ roundsTo cF.blocksInOrder 342)
    (hfs : ProofFile.Honest.K3.Law.AtThr.headCallsShape Zp = G.W.HLy.fs)
    (hPF : ∀ funs : Array HFun, shapesOf funs = headShapes G.W.hS G.W.H.tl.mats →
      (∀ Fn ∈ funs.toList, Fn.phi.size = Fn.len) →
      partsFit (sizesOf G.W.H.tl.mats) (OnBytes.HonestTrace.U3.partsOf funs) (G.W.H.nU.getD 2 0) = .ok ())
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} (hwit : ∀ v, (wit v).x = v.x)
    (hPhi : ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[342]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 342 k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl → ∀ Fn ∈ tl.funs.toList, Fn.phi.size = Fn.len) :
    VecTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said 342 wit Zp G 24
      (G.W.H.nU.getD 2 0) A := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain rfl : blk₁ = blk := Option.some.inj (hblk₁.symm.trans hb)
  have hThr := hT.1
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      342 k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hb342 : 342 ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1.le
  -- the list heard, as far as the seat
  have hlenH : μ.st.heard.length = roundsTo cF.blocksInOrder 342 := by
    have q' := drawsFit_length _ _ hT.1.2.1
    have h0 : μ.st.heard.length =
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
          roundsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 342 := by
      rw [q', List.length_append]
      rfl
    have hf0 : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front = 0 := rfl
    rw [hf0, Nat.zero_add] at h0
    exact h0
  have hdl : k6.2 + headInFront (headParAt G) 8 ≤
      (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zp G) A)).length := by
    rw [List.length_take, hlenH]
    omega
  have hxm : ∃ xm, headHeardWholeAt (headParAt G) (requestOf Zp.s₀) 0
      (k4LookOf G.W.HLy.fs k3.2 (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zp G) A))) k6.2
      (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zp G) A)) = .ok xm := by
    refine ⟨headHeardWhole (headParAt G) (requestOf Zp.s₀) 0
      (k4LookOf G.W.HLy.fs k3.2 (μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zp G) A)))
      (((μ.st.heard.take (OnBytes.HonestTrace.heardOf (u3Seats Zp G) A)).drop k6.2).take
        (headInFront (headParAt G) 8)), ?_⟩
    unfold headHeardWholeAt
    dsimp only
    rw [if_pos (by
      rw [List.length_take, List.length_drop]
      simp only [beq_iff_eq]
      omega)]
  obtain ⟨xm, hx⟩ := hxm
  have hN341 : roundsTo cF.blocksInOrder 341 ≤ OnBytes.HonestTrace.heardOf (u3Seats Zp G) A := by
    rw [← hbase]
    omega
  have hLook := head_look h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb342 hThr hfs hbase3 hN341
  obtain ⟨t, c, ht, hfun, hcs, hmats⟩ := head_tables_cov h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (Zq := Zp) hGW hquiet hTT hVV hU hb342 hThr hS htl (base := k6.2) (by rw [hbase]; exact (Nat.zero_add _).symm)
    hlen hcut hLook hx
  obtain ⟨c', h1, -⟩ := cov_at_stand h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb342 hThr Zp G hcs
  have hcv : (covOf Zp G μ.st.input.x).toOption.getD default = c' := by
    rw [h1]
    rfl
  have hsz : c'.sized G.W.hS.T = true := by
    have q' := h1
    unfold covOf at q'
    rw [hTT]
    exact ProofFile.Honest.K2.Law.coveredAt_sized q'
  obtain ⟨V, hV⟩ := OnBytes.HonestTrace.U3.Fit.head_returns_at_head h hG hsz
  have hV' : headVals Zp G c' sps 24 = .ok V := by
    rw [← OnBytes.HonestTrace.U3.Fit.valsAt_head hsps hY hkind c']
    exact hV
  rw [hcv] at ht
  have hpf := hPF t.funs (VerifiableInference.Desc.First.K8.Honest.tables_shapes ht) (by
    rw [← hfun]
    exact hPhi _ hb k s μ E ds y cols s' hT hd hS tl htl)
  obtain ⟨vec, hvec⟩ := headVals_vec_ok hV' p6 p3 hx ht hpf
  obtain ⟨en, k6', k3', x', t', q6, q3, qx, qt, qv⟩ := head_vec Zp G c' sps 24 hV' hvec
  obtain rfl : k6' = k6 := by
    have := q6.symm.trans p6
    exact Except.ok.inj this
  obtain rfl : k3' = k3 := by
    have := q3.symm.trans p3
    exact Except.ok.inj this
  obtain rfl : x' = xm := Except.ok.inj (qx.symm.trans hx)
  obtain rfl : t' = t := Except.ok.inj (qt.symm.trans ht)
  refine ⟨V, vec, by rw [hwit, hcv]; exact hV, hvec, en, fun C j _ => ?_⟩
  rw [qv C j, hfun, hmats]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.headVals_vec_ok
#print axioms ProofFile.Honest.K1.head_tables_cov
#print axioms ProofFile.Honest.K1.vecTie_head_of
