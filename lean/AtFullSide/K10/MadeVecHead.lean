-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/MadeVecHead.lean: at a stand of the first chain's thread behind the output head's reads, at
any later border: the maker of the head's vector of reads returns at what was heard, cut at a seat of the array "U3" of
segment 24. The law `vecTie_head` (AtFullSide/K1/ReadsHeadAll.lean) says this at a stand just in front of the reads' member;
here the members' own steps are read off the thread's clause Made at the later border (`made_cuts`, Honest/K10/Pay/MadeVecChain.lean).

  `head_record_step`   `head_record` (Honest/K1/Law/HeadRecord.lean) from the member's step alone
  `req_reached`        a reached state bears the request's words where the first state bears no mark
  `cov_of_req`         where a state with the instance's words has covered positions, so has the filler
  `headSeatS`, `headSeatS_ok`   by Lean's kernel: each written seat of "U3" of segment 24 stands behind the head's own rounds
  `head_vec_of`        the return, from public premises
  `head_vec_at`        the return, under the head

Limits. A statement on what returns: nothing on the vector's entries. The head is a premise. That a run stands at the border is
not said.
-/
import AtFullSide.K1.ReadsHeadPhi
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeVecChain
import Johnson.LTPileR.AtGate

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads commitAtS_here commitAtS_slots commit_head)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.K8.ReadsQuiet (PH head head_ok closed_ok)
open VerifiableInference.Desc.Kinds (Head.Par Head.Request)
open VerifiableInference.Desc.Kinds.Head (requestOf)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6 K6MemberIs)
open VerifiableInference.Desc.Kinds.Head.Honest (k6_keeps_of_member_step)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace.U3 (covOf u3Seats placeIn SegVals valsAt headVals partsFit sizesOf)
open OnBytes.HonestTrace.U3.Fit
open ProofFile (Spot spotsOf)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K1 (head_record headVals_vec_ok headFs_at_head partsFit_head row341_ok tables_whole)
open ProofFile.Honest.K3.Law.AtThr (headCallsShape head_calls_tie)
open ProofFile.Honest.K6 (headHeardWhole headHeardWholeAt headParAt headInFront tables_at_accept)
open ProofFile.Honest.FirstThread
open OnBytes.Tie.Pv.Tail.Closed (headShapes shapesOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

variable {Bk : ProverCoinCounts}

/-- **`head_record` from the member's step alone.** -/
theorem head_record_step {Z : ProofFile.Pub} {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {Ph : PH}
    (hquiet : IM.k1Quiet G 24 X = head Ph) {ft n : ℕ} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {Cl : Type} {blk : Block S Cl} (hU : blk.UnderR ((IM.k1Reads Z G 24 X pr reads).retype : Block S Cl))
    (hS : blk.step ft s rs cols = .ok (s', n)) {tl : HTailF2} (htl : s'.tl? = some tl) :
    ∃ (r₁ r₂ : Fmt.RoundView) (gs₁ : List (List (ℕ × List UInt64))) (s₁ : S) (a : First.HeadOwn)
      (cov : OnBytes.Model.Head.Covered) (x : OnBytes.Model.Head.Heard) (t : OnBytes.Model.Head.Tables),
      (K1.laterAt (Cl := Unit) G.first (K1.gpOf Z) 24 pr 1 reads).decide s [r₁, r₂] gs₁ = .ok s₁ ∧
      s₁.here = .head a ∧ s₁.covered Ph.h.T Ph.h.V = .ok cov ∧ a.x = some x ∧
      VerifiableInference.Desc.K8.ReadsQuiet.tables Ph.h Ph.L Ph.hp cov x = .ok t ∧ tl.funs = t.funs := by
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS)
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G 24 X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G 24 X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G 24 X) s s' r₁ r₂ _ hdec
  rw [hquiet] at h3
  obtain ⟨a, cov, x, t, tl', ha, hop, hcov, hx, ht, hc, e'⟩ := head_ok h3
  subst e'
  obtain ⟨-, rfl, -, -⟩ := closed_ok hc
  have e : some ({ Ph.hp.tl with funClosed := true, funs := t.funs } : HTailF2) = some tl := by
    rw [← htl]
    show _ = (if a.opened then some _ else none)
    rw [if_pos hop]
  obtain rfl := Option.some.inj e
  exact ⟨r₁, r₂, gs₁, s₁, a, cov, x, t, h1, ha, hcov, hx, ht, rfl⟩

/-- A reached state bears the request's words, where the first state bears no mark. -/
theorem req_reached {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {ft k : ℕ} {a : ProofFile.InstPub × S} (h : Reach ft c.blocksInOrder (ProofFile.startS Z) k a)
    (h0 : (ProofFile.startS Z a.1).failed = none) : a.2.req = Verify.words32 a.1.request := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  have q : Meaning.K2.ReqStays (ProofFile.startS Z a.1) a.2 :=
    Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial (fun _ _ _ => trivial) hp k hf
  rw [q.1]
  exact Meaning.K2.req_start Z a.1 h0

/-- The first state bears no mark, where a later state reached from it bears none. -/
theorem start_clean {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    {ft k : ℕ} {a : ProofFile.InstPub × S} (h : Reach ft c.blocksInOrder (ProofFile.startS Z) k a) (hm : a.2.failed = none) :
    (ProofFile.startS Z a.1).failed = none := by
  obtain ⟨-, rs, cols, hf⟩ := h.fold
  have q : Meaning.K2.ReqStays (ProofFile.startS Z a.1) a.2 :=
    Meaning.K2.open_fold_all Meaning.K2.seatKeeps_req Meaning.K2.seatBack_req O trivial (fun _ _ _ => trivial) hp k hf
  exact q.2 hm

/-- Where a state with the instance's words has covered positions, so has the filler, with the same costs. -/
theorem cov_of_req {Zq : ProofFile.Pub} {G : ProofFile.Ground} {s : S} {p : ProofFile.InstPub} {xi : ProofFile.Inst}
    (hx : xi.pub = p) (e : s.req = Verify.words32 p.request) {c : Head.Covered}
    (hc : s.covered G.W.T G.W.P.h.V = .ok c) : ∃ c', covOf Zq G xi = .ok c' ∧ c'.hOnC = c.hOnC := by
  subst hx
  unfold S.covered at hc
  cases hy : s.replyTok? with
  | none =>
    rw [hy] at hc
    cases hc
  | some y =>
    rw [hy] at hc
    obtain ⟨c', h1, h2⟩ := coveredAt_cost (y' := 0) hc (Nat.lt_of_le_of_lt (Nat.zero_le y) (coveredAt_tok hc))
    refine ⟨c', ?_, h2⟩
    unfold covOf
    rw [Johnson.AtFull.Shape.coveredAt_same (s := s)
      (show (Zq.s₀.withReq (Verify.words32 xi.pub.request)).req = s.req from e.symm)]
    exact h1

/-- At the written seats: each seat of segment 24 stands behind the head's own rounds. -/
def headSeatS : Bool :=
  match placeBy cutWritten spotsWritten 24 .K6 with
  | .ok k6 => (seatsW "U3").all fun s => s.seg != 24 || decide (k6.2 + 82 ≤ s.heard)
  | .error _ => false

set_option maxRecDepth 1000000 in
theorem headSeatS_ok : headSeatS = true := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **The return, from public premises.** -/
theorem head_vec_of {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Xl : LinkH} {pr : ℕ}
    {reads : Option (List ℕ)} (hquiet : IM.k1Quiet G 24 Xl = head (p8K6 G.W 24))
    (hGW : G.W = P5J.At.X Zp) (hTT : G.W.hS.T = G.W.T) (hVV : G.W.hS.V = G.W.P.h.V)
    {blk₁ : Block TS ProofFile.Cl} (hblk₁ : cF.blocksInOrder[342]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Zp G 24 Xl pr reads).retype : Block TS ProofFile.Cl))
    {sps : List Spot} (hsps : spotsOf Zp.cuts = some sps) {Y : LinkH} (hY : G.built[24]? = some Y)
    (hkind : Y.kind = 2) {k6 k3 : Spot × ℕ}
    (p6 : placeIn Zp sps 24 .K6 = .ok k6) (p3 : placeIn Zp sps 24 .K3 = .ok k3)
    (hbase : k6.2 = roundsTo cF.blocksInOrder 341) (hbase3 : k3.2 = roundsTo cF.blocksInOrder 340)
    (hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt G) 8 = b₆.rounds.length)
    {N : ℕ} (hcut : k6.2 + headInFront (headParAt G) 8 ≤ N)
    (hfull : k6.2 + headInFront (headParAt G) 8 ≤ roundsTo cF.blocksInOrder 342)
    (hfs : headCallsShape Zp = G.W.HLy.fs)
    (hPF : ∀ funs : Array HFun, shapesOf funs = headShapes G.W.hS G.W.H.tl.mats →
      (∀ Fn ∈ funs.toList, Fn.phi.size = Fn.len) →
      partsFit (sizesOf G.W.H.tl.mats) (OnBytes.HonestTrace.U3.partsOf funs) (G.W.H.nU.getD 2 0) = .ok ())
    {B : ℕ} (hB : 343 ≤ B) (hBl : B ≤ cF.blocksInOrder.length) {k : Coins Bk} {sB : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr 𝕋 B k sB m E) {V : SegVals}
    (hVv : valsAt Zp G ((covOf Zp G m.st.input.x).toOption.getD default) 24 = .ok V) :
    ∃ v, V.vec (m.st.heard.take N) = .ok v := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hflat : ∀ b ∈ cF.blocksInOrder, b.planOk = true := fun b hb => P5J.flat_ok h.toAtMg b hb
  -- the thread's fold, cut at the members
  have hT' := hT
  unfold Thr at hT'
  have hM : (𝕋).Made B k sB m E := hT'.2.2.2.2.1
  have hseen : m.seen.map (·.drawn) = m.st.heard := by
    have hM' := hM
    unfold Thread.Made at hM'
    exact hM'.1
  obtain ⟨s₀, cols, hbeg, C⟩ := made_cuts (𝕋) hM
  have hs₀ : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  subst hs₀
  obtain ⟨b₆, hb₆, M₀⟩ := P4.k6_member_at_mg h.toAtMg
  have M : K6MemberIs Bs.G₀.W 24 ProofFile.sameReply IM.k6Place b₆ := by
    rw [hGW]
    exact M₀
  obtain ⟨sj, s2, c, n, f1, st1, f2, dr⟩ := C 341 b₆ (by omega) hb₆
  obtain ⟨s2', s3, c2, n2, g1, st2, g2, -⟩ := C 342 blk₁ (by omega) hblk₁
  obtain rfl : s2 = s2' := congrArg Prod.fst (cut_meets f2 g1)
  have hR341 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 341 (m.st.input.x.pub, sj) :=
    reach_of_fold 341 (by omega) sj _ _ _ _ f1
  have hR342 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 342 (m.st.input.x.pub, s2) :=
    reach_of_fold 342 (by omega) s2 _ _ _ _ g1
  have hR343 : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 343 (m.st.input.x.pub, s3) :=
    reach_of_fold 343 (by omega) s3 _ _ _ _ g2
  -- K6's member: what its yes leaves
  have hWL := P4.wellLaid_341 h.scope h.reads O (fun b hb' => hflat b (List.mem_of_getElem? hb')) hR341 Bs.G₀.W.hS
    (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)
  obtain ⟨o, x₀, g₁, yk, hso, hox, hol, -, -, -, -, -, -, htab⟩ := tables_at_accept M st1 hWL
  -- the reads' member
  obtain ⟨xh, t₃, -, -, tl, etl, -, -, -, -⟩ :=
    P1K8.headList_at_343 _ _ _ _ _ _ _ _ _ _ h.scope h.reads O _ _ _ _ hR343
  obtain ⟨r₁, r₂, gs₁, s₁, a, cov, x₁, t₁, h1, ha, hcov, hx₁, ht₁, hfun⟩ := head_record_step hquiet hU st2 etl
  obtain ⟨-, -, hh⟩ := commitAtS_here _ _ _ _ s2 s₁ _ _ h1
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
  have hcs : s2.covered Bs.G₀.W.T Bs.G₀.W.P.h.V = .ok cov := by
    rw [← hTT, ← hVV]
    exact hcov
  -- what was heard, as far as the seat
  have hlenH : m.st.heard.length = roundsTo cF.blocksInOrder B := by
    have q' := drawsFit_length _ _ hT'.2.1
    have h0 : m.st.heard.length = (𝕋).front + roundsTo (𝕋).bs B := by
      rw [q', List.length_append]
      rfl
    have hf0 : (𝕋).front = 0 := rfl
    rw [hf0, Nat.zero_add] at h0
    exact h0
  have hmono : roundsTo cF.blocksInOrder 342 ≤ roundsTo cF.blocksInOrder B := by
    have e : cF.blocksInOrder.take 342 = (cF.blocksInOrder.take B).take 342 := by
      rw [List.take_take, Nat.min_eq_left (by omega)]
    have e2 : cF.blocksInOrder.take B = (cF.blocksInOrder.take B).take 342 ++ (cF.blocksInOrder.take B).drop 342 :=
      (List.take_append_drop _ _).symm
    unfold roundsTo declsTo
    rw [e, e2, List.flatMap_append, List.length_append, ← e2]
    omega
  have hdl : k6.2 + headInFront (headParAt Bs.G₀) 8 ≤ (m.st.heard.take N).length := by
    rw [List.length_take, hlenH]
    omega
  obtain ⟨xm, hx⟩ : ∃ xm, headHeardWholeAt (headParAt Bs.G₀) (requestOf Zp.s₀) 0
      (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N)) k6.2 (m.st.heard.take N) = .ok xm := by
    refine ⟨headHeardWhole (headParAt Bs.G₀) (requestOf Zp.s₀) 0
      (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N))
      (((m.st.heard.take N).drop k6.2).take (headInFront (headParAt Bs.G₀) 8)), ?_⟩
    unfold headHeardWholeAt
    dsimp only
    rw [if_pos (by
      rw [List.length_take, List.length_drop]
      simp only [beq_iff_eq]
      omega)]
  -- the lookup's copy
  have hN341 : roundsTo cF.blocksInOrder 341 ≤ N := by
    rw [← hbase]
    omega
  have K := k6_keeps_of_member_step M st1
  obtain ⟨o₀, o', ho₀, ho', e⟩ := K.own
  obtain ⟨-, -, o1, -, h1', -, hop', -⟩ := K
  rw [hso] at ho'
  cases ho'
  rw [ho₀] at h1'
  cases h1'
  have el : o.lookHeard = o₀.lookHeard := by rw [e]
  have hH : sj.lookHeard? = some g₁ := by
    unfold S.lookHeard?
    rw [ho₀]
    show (if o₀.opened then o₀.lookHeard else none) = some g₁
    rw [if_pos hop', ← el]
    exact hol
  have T := head_calls_tie h _ _ cols sj _ c g₁ ((m.st.heard.take N).drop (roundsTo cF.blocksInOrder 341)) f1 hH
  have hlist : ((m.seen.drop (𝕋).front).take ((cF.blocksInOrder.take 341).flatMap (·.rounds)).length).map (·.drawn) ++
      (m.st.heard.take N).drop (roundsTo cF.blocksInOrder 341) = m.st.heard.take N := by
    show ((m.seen.drop 0).take (roundsTo cF.blocksInOrder 341)).map (·.drawn) ++ _ = _
    rw [List.drop_zero, List.map_take, hseen,
      show m.st.heard.take (roundsTo cF.blocksInOrder 341) =
        (m.st.heard.take N).take (roundsTo cF.blocksInOrder 341) by
          rw [List.take_take, Nat.min_eq_left hN341]]
    exact List.take_append_drop _ _
  rw [hlist] at T
  have k0 : g₁.zx = (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N)).zx := by
    rw [← hfs, hbase3]
    exact T.zx
  have k1 : g₁.zk = (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N)).zk := by
    rw [← hfs, hbase3]
    exact T.zk
  have k2 : g₁.zb0 = (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N)).zb0 := by
    rw [← hfs, hbase3]
    exact T.zb0
  have k3' : g₁.zb1 = (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N)).zb1 := by
    rw [← hfs, hbase3]
    exact T.zb1
  have k4 : g₁.shape = (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N)).shape := by
    rw [← hfs, hbase3]
    exact T.shape
  -- one answer
  have hxm : xm = headHeardWhole (headParAt Bs.G₀) (requestOf Zp.s₀) 0
      (k4LookOf Bs.G₀.W.HLy.fs k3.2 (m.st.heard.take N))
      (((m.st.heard.take N).drop k6.2).take (headInFront (headParAt Bs.G₀) 8)) := by
    unfold headHeardWholeAt at hx
    dsimp only at hx
    split at hx
    · exact (Except.ok.inj hx).symm
    · cases hx
  have hown : ((m.st.heard.take N).drop k6.2).take (headInFront (headParAt Bs.G₀) 8) =
      (((m.seen.drop (𝕋).front).drop (roundsTo (𝕋).bs 341)).take b₆.rounds.length).map (·.drawn) := by
    rw [dr, List.drop_take, List.take_take, Nat.min_eq_left (by omega), hbase, hlen b₆ hb₆,
      show (𝕋).front + roundsTo (𝕋).bs 341 = roundsTo cF.blocksInOrder 341 from Nat.zero_add _]
    rfl
  have E1 : VerifiableInference.Desc.K8.ReadsQuiet.tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H cov x₁ =
      VerifiableInference.Desc.K8.ReadsQuiet.tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H cov xm := by
    rw [htab, hxm, hown]
    exact tables_whole _ _ _ _ (headParAt Bs.G₀) _ _ _ 0 _ k0 k1 k2 k3' k4
  -- the filler's cover
  have hclean : (ProofFile.startS Zp m.st.input.x.pub).failed = none :=
    start_clean O hflat (a := (m.st.input.x.pub, sB))
      (thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hBl hT)
      (head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT)
  have hreq := req_reached O hflat (a := (m.st.input.x.pub, s2)) hR342 hclean
  obtain ⟨c', e1', e2'⟩ := cov_of_req (Zq := Zp) (G := Bs.G₀) (xi := m.st.input.x) rfl hreq hcs
  have hcv : (covOf Zp Bs.G₀ m.st.input.x).toOption.getD default = c' := by
    rw [e1']
    rfl
  have hsz : c'.sized Bs.G₀.W.hS.T = true := by
    have q' := e1'
    unfold covOf at q'
    rw [hTT]
    exact ProofFile.Honest.K2.Law.coveredAt_sized q'
  have ht : VerifiableInference.Desc.K8.ReadsQuiet.tables Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H c' xm = .ok t₁ := by
    rw [tables_cost _ _ _ e2' xm]
    exact E1.symm.trans ht₁
  have hV' : headVals Zp Bs.G₀ c' sps 24 = .ok V := by
    rw [← valsAt_head hsps hY hkind c', ← hcv]
    exact hVv
  have hphi := Johnson.AtFull.Shape.Phi.phi_sizes_head h hR343 etl
  have hpf := hPF t₁.funs (VerifiableInference.Desc.First.K8.Honest.tables_shapes ht) (by
    rw [← hfun]
    exact hphi)
  obtain ⟨vec, hvec⟩ := headVals_vec_ok hV' p6 p3 hx ht hpf
  exact ⟨vec, hvec⟩

/-- **The return, under the head**, at a seat of the array "U3" of segment 24, at a border behind the reads' member. -/
theorem head_vec_at {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr}
    {st : OnBytes.HonestTrace.Seat} (hst : OnBytes.HonestTrace.seatAt (u3Seats Zp G) Ad = some st)
    (hseg : st.seg = 24) {B : ℕ} (hB : 343 ≤ B) (hBl : B ≤ cF.blocksInOrder.length) {k : Coins Bk} {sB : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr 𝕋 B k sB m E) {V : SegVals}
    (hVv : valsAt Zp G ((covOf Zp G m.st.input.x).toOption.getD default) st.seg = .ok V) :
    ∃ v, V.vec (m.st.heard.take st.heard) = .ok v := by
  rw [hseg] at hVv
  have hmem : st ∈ u3Seats Zp G := List.mem_of_find?_eq_some hst
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O 24 (by omega)
  have he' : cF.blocksInOrder[342]? = some e := he
  obtain ⟨m2, f2, k2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).2
  obtain rfl : m2 = Xl := Option.some.inj (f2.symm.trans hX)
  have hq := VerifiableInference.Desc.K1.quiet_of_kind Bs.G₀ 24 m2 hX k2
  have hW := IM.ground_publicK h.laid.pub hG
  have hGW : Bs.G₀.W = P5J.At.X Zp := ProofFile.Law.blankBy_W hG
  have q6 := placeIn_by Zp spotsWritten 24 .K6
  have q3 := placeIn_by Zp spotsWritten 24 .K3
  rw [cuts_at_head h] at q6 q3
  have hw := List.all_eq_true.1 lookPlacesW_yes 24 (List.mem_range.2 (by omega))
  cases e3 : placeBy cutWritten spotsWritten 24 .K3 with
  | error w' =>
    rw [e3] at hw
    cases hw
  | ok k3 =>
    cases e6 : placeBy cutWritten spotsWritten 24 .K6 with
    | error w' =>
      have : ownOf 24 = .K6 := rfl
      simp [this, e3, e6] at hw
    | ok k6 =>
      have : ownOf 24 = .K6 := rfl
      simp only [this, e6, e3, Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨w3, w6⟩ := hw
      rw [e6] at q6
      rw [e3] at q3
      have h82 := headInFront_at_head h hG
      have hb6 : k6.2 = roundsTo cF.blocksInOrder 341 := by
        rw [roundsTo_at_head h]
        exact w6
      have hb3 : k3.2 = roundsTo cF.blocksInOrder 340 := by
        rw [roundsTo_at_head h]
        exact w3
      have hlen : ∀ b₆, cF.blocksInOrder[341]? = some b₆ → headInFront (headParAt Bs.G₀) 8 = b₆.rounds.length := by
        intro b₆ hb₆
        have hc := First.Close.hc_at_laid h.scope h.laid
        have e1 : ((VerifiableInference.PlanWritten.cutOf cF.blocksInOrder)[341]?).map (·.2.2.1) = some b₆.rounds.length := by
          unfold VerifiableInference.PlanWritten.cutOf
          rw [List.getElem?_map, hb₆]
          rfl
        rw [hc, row341_ok.1] at e1
        rw [h82]
        exact Option.some.inj e1
      have hsw : u3Seats Zp Bs.G₀ = seatsW "U3" := seats_at_head h hG "U3"
      have hcut : k6.2 + headInFront (headParAt Bs.G₀) 8 ≤ st.heard := by
        have k := headSeatS_ok
        unfold headSeatS at k
        rw [e6] at k
        have k' := List.all_eq_true.1 k st (hsw ▸ hmem)
        simp only [hseg, bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at k'
        rw [h82]
        exact k'
      have hfull : k6.2 + headInFront (headParAt Bs.G₀) 8 ≤ roundsTo cF.blocksInOrder 342 := by
        rw [h82, roundsTo_at_head h]
        have := row341_ok.2
        have e0 : k6.2 = rowsBeforeW 341 := w6
        omega
      exact head_vec_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hG hq hGW
        (_root_.Fo.Pub.public_T hW).symm (_root_.Fo.Pub.public_V hW).symm he' (IM.alone_underR hu)
        (spots_at_head h) hX k2 q6 q3 hb6 hb3 hlen hcut hfull (headFs_at_head h hG)
        (fun funs a b => partsFit_head h hG funs a b) hB hBl hT hVv

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.head_record_step
#print axioms ProofFile.Honest.K10.req_reached
#print axioms ProofFile.Honest.K10.start_clean
#print axioms ProofFile.Honest.K10.cov_of_req
#print axioms ProofFile.Honest.K10.headSeatS
#print axioms ProofFile.Honest.K10.headSeatS_ok
#print axioms ProofFile.Honest.K10.head_vec_of
#print axioms ProofFile.Honest.K10.head_vec_at
