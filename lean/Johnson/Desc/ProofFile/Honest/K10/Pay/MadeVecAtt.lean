-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeVecAtt.lean: at an attention's segment: the honest maker of the vector of reads (`attVals`, Johnson/HonestTrace/U3Rows.lean)
returns at the challenges in front of its sending, FROM THE VERIFIER's FOLD AT ANY LATER BORDER: the thread's two clauses `Made`
and `Fit` at a border B behind the reads' own sub-protocol. No stand at the reads' own border is asked, and no step of a prover.

  `roundsTo_le`       the count of rounds in front of a border grows with the border
  `att_record_step`   what the reads' sub-protocol's own yes holds at an attention's segment: `att_record`
                     (Honest/K1/Law/AttRecord.lean) from the verifier's step alone
  `attRun_later`      `attRun` (Honest/K1/Law/AttFunsAtHead.lean) from `Made` and `Fit` at B: the three neighbouring sub-protocols
                     (the lookup on the calls, attention's own rounds, the reads) by `made_cuts` (MadeVecChain.lean)
  **`vec_att_later`**   the maker's vector returns at `heard.take s.heard`

The two longer proofs follow the texts of `attRun` and of the first half of `vec_att_head` (Honest/K1/Law/AttVecAtHead.lean), whose
lemmas they call; what is new is where the states and the rounds come from.

Limits. The head is a hypothesis. That a thread stands anywhere is not shown. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.AttVecAtHead
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeVecChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (funBack tabsBack)
open VerifiableInference.Desc.First.Att.P (Pts TablesP)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open OnBytes.Model (HTailF2 Head.Covered)
open OnBytes.Model.Stages (LinkH)
open OnBytes.HonestTrace (pairOf heardOf Seat)
open OnBytes.HonestTrace.U3 (SegVals valsAt u3Seats placeIn sizesOf)
open OnBytes.HonestTrace.U3.Fit (rowsBeforeW seatsW)
open H2K5.Honest (PtsTo Pub5)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1
open ProofFile.Honest.K3 (lookHeardAt OpenSame)
open ProofFile.Honest.K4 (k4LookOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

/-- The count of rounds in front of a border grows with the border. -/
theorem roundsTo_le {S' Cl' : Type} (bs : List (Block S' Cl')) {a b : ℕ} (h : a ≤ b) :
    roundsTo bs a ≤ roundsTo bs b := by
  have e : bs.take b = bs.take a ++ (bs.take b).drop a := by
    conv_rhs => rw [← take_le bs h]
    exact (List.take_append_drop a _).symm
  unfold roundsTo declsTo
  rw [e, List.flatMap_append, List.length_append]
  exact Nat.le_add_right _ _

/-- **What the reads' sub-protocol's own yes holds at an attention's segment**, from the verifier's
step alone. -/
theorem att_record_step {Cl' : Type} {m : ℕ} {Z : ProofFile.Pub} {G : ProofFile.Ground} {X : LinkH} {pr : ℕ}
    {reads : Option (List ℕ)} {A : OnBytes.Attention.Plan} (hk : X.kind = 1)
    (hA : G.W.A[X.g]? = some A) {ft : ℕ} {s s' : S} {rs : List Fmt.RoundView} {c : List OpenedColumn} {n : ℕ}
    {blk : Block S Cl'}
    (hU : blk.UnderR ((IM.k1Reads Z G m X pr reads).retype : Block S Cl'))
    (hS : blk.step ft s rs c = .ok (s', n)) :
    ∃ (r₁ r₂ : Fmt.RoundView) (gs₁ : List (List (ℕ × List UInt64))) (s₁ : S) (a : First.AttOwn)
      (hh : First.Att.P.Heard) (g : OnBytes.Model.Forest.Heard) (p : First.Att.P.Pts)
      (t : First.Att.P.TablesP),
      (K1.laterAt (Cl := Unit) G.first (K1.gpOf Z) m pr 1 reads).decide s [r₁, r₂] gs₁ = .ok s₁ ∧
      s₁.here = .att a ∧ s₁.heard5? = some hh ∧ a.g = some g ∧
      First.Att.P.ptsFrom (First.Att.P.parCOf A).geo g.zk hh a.F = some p ∧
      First.Att.P.tablesP (First.Att.P.parCOf A).geo (First.Att.P.parCOf A).mats
        (First.Att.P.parCOf A).nW (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb g) p =
        some t := by
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS)
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G m X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G m X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G m X) s s' r₁ r₂ _ hdec
  rw [H2K5.Honest.quiet_is G m X hk hA] at h3
  obtain ⟨a, hh, g, p, t, ha, h5, hg, -, hp, ht, -, -, -⟩ :=
    (H2K5.Honest.readsAtSO_iff A s₁ s').1 h3
  exact ⟨r₁, r₂, gs₁, s₁, a, hh, g, p, t, h1, ha, h5, hg, hp, ht⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)

set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

/-- **What the reads' sub-protocol of an attention's segment holds, from the verifier's fold at a later
border.** -/
theorem attRun_later {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, am)) {B : ℕ}
    (hB : 14 * (2 * g + 1) + 4 + 1 < B) {k : Coins Bk} {sB : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hM : (𝕋).thread.Made B k sB μ E) (hFit : (𝕋).thread.Fit B μ)
    {A : OnBytes.Attention.Plan} (hA : G.W.A[g]? = some A) :
    ∃ (k5 k3 : Spot × ℕ) (Hh : OnBytes.Model.Forest.Heard) (hd : First.Att.P.Heard)
      (Lf : First.Att.P.Left) (pv : First.Att.P.Pts) (t₀ : First.Att.P.TablesP) (nx : ℕ),
      placeIn Zp Johnson.AtFull.Desc.spotsWritten (2 * g + 1) .K5 = .ok k5 ∧
      placeIn Zp Johnson.AtFull.Desc.spotsWritten (2 * g + 1) .K3 = .ok k3 ∧
      OpenSame Hh (lookHeardAt A.fs k3.2 (μ.st.heard.take (heardOf (u3Seats Zp G) Ad))) ∧
      First.Att.P.pointsOf (First.Att.P.geoOf A.S) Hh.zk hd Lf = some pv ∧
      (∀ q, H2K5.Honest.SameTo A.own q hd (H2K5.Honest.heardAt ⟨A.S, A.own⟩
        ⟨Hh.zk, (μ.st.heard.take (heardOf (u3Seats Zp G) Ad)).drop k5.2⟩ fun _ => none)) ∧
      First.Att.P.tablesP (First.Att.P.parCOf A).geo (First.Att.P.parCOf A).mats
        (First.Att.P.parCOf A).nW (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh) pv =
        some t₀ ∧
      First.Shape.heard5Sh hd = H2K5.Honest.heard5At A.own nx := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hl2 : 2 * g + 1 < 25 := by omega
  have i1 : K1.noL (2 * g + 1) false = 14 * (2 * g + 1) + 4 + 1 := by
    have : IM.k1Ix (2 * g + 1) false = 3 := by
      show (if false = true then 5 else 3) + (if 2 * g + 1 = 24 then 1 else 0) = 3
      rw [if_neg (fun e => nomatch e), if_neg (by omega)]
    show 14 * (2 * g + 1) + IM.k1Ix (2 * g + 1) false + 2 = _
    omega
  obtain ⟨blk, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O (2 * g + 1) hl2
  obtain ⟨m0, m1, -, -, -, -, f2, k2, g2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : m1 = Xl := Option.some.inj (f2.symm.trans hX)
  have hU := IM.alone_underR hu
  have hAg : Bs.G₀.W.A[m1.g]? = some A := by
    rw [g2]
    exact hA
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hAX : (P5J.At.X Zp).A[g]? = some A := hW ▸ hA
  obtain ⟨blk₅, a₅, hb₅, Pl, Dc⟩ := K5.k5_member h hg
  obtain rfl : A = a₅ := Option.some.inj (hAX.symm.trans Pl.plan)
  have hb₅' : (𝕋).thread.bs[14 * (2 * g + 1) + 4]? = some blk₅ := hb₅
  have hb₅c : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some blk₅ := hb₅
  have hlt : 14 * (2 * g + 1) + 4 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb₅').1
  obtain ⟨blk₃, hb₃⟩ : ∃ b, cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some b :=
    ⟨cF.blocksInOrder[14 * (2 * g + 1) + 3], List.getElem?_eq_getElem (by omega)⟩
  have hb₃' : (𝕋).thread.bs[14 * (2 * g + 1) + 3]? = some blk₃ := hb₃
  have hb₁ : (𝕋).thread.bs[14 * (2 * g + 1) + 4 + 1]? = some blk := by
    rw [← i1]
    exact he
  -- the three neighbours, off one fold
  obtain ⟨s₀, colsA, hbeg, cut⟩ := made_cuts (𝕋).thread hM
  obtain ⟨sj, sj', c, n, -, hst, G3, hrs⟩ := cut _ blk₃ (by omega) hb₃'
  obtain ⟨t5, s, c5, n5, F5, hs5, G5, hr5⟩ := cut _ blk₅ (by omega) hb₅'
  obtain ⟨t1, s', c1, n1, F1, hs1, -, -⟩ := cut _ blk hB hb₁
  obtain rfl : sj' = t5 := congrArg Prod.fst (cut_meets G3 F5)
  obtain rfl : s = t1 := congrArg Prod.fst (cut_meets G5 F1)
  obtain ⟨r₁, r₂, gs₁, s₁, a, hh, gl, p, t₀, hlater, ha, h5', hgl, hp, ht₀⟩ :=
    att_record_step k2 hAg hU hs1
  obtain ⟨F₅, G₅, hd5, hh5, h5s⟩ := K5.k5_step_lays Dc hs5
  obtain rfl : hd5 = hh := Option.some.inj ((K5.heard5_sent hlater h5s).symm.trans h5')
  -- the lookup on the calls
  obtain ⟨pp, hps, Hb⟩ := ProofFile.Honest.K3.Law.AtThr.att_back_head h g hg A blk₃ hAX hb₃
  obtain ⟨F, Hh, G₁, hv, hgH⟩ := Hb (𝕋).thread.ft sj sj' _ c n hst
  obtain ⟨a₄, hd₄, G₄, ea, -, -⟩ := K5.k5_step_is Dc hs5
  have hga := hgH a₄ ea
  obtain ⟨a₂, ea₂, eg₂⟩ := K5.k5_step_keeps_g Dc (𝕋).thread.ft Hh sj' _ _ s _ hs5 ⟨a₄, ea, hga⟩
  obtain ⟨a₃, ea₃, eg₃⟩ := K5.g_sent hlater ⟨a₂, ea₂, eg₂⟩
  obtain rfl : a = a₃ := VerifiableInference.Desc.First.Here.att.inj (ha.symm.trans ea₃)
  obtain rfl : Hh = gl := Option.some.inj (eg₃.symm.trans hgl)
  -- the numbers
  obtain ⟨k5', k3', a', q5, q3, w5, w3, -⟩ := OnBytes.HonestTrace.U3.Att.attDeclared_at_head h hG hg
  have er3 : roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3) = k3'.2 := by
    rw [OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h, w3]
  have er5 : roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 4) = k5'.2 := by
    rw [OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h, w5]
  have er6 : roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 4 + 1) = k5'.2 + blk₅.rounds.length := by
    rw [← er5]
    unfold roundsTo
    rw [declsTo_succ hb₅c, List.length_append]
  have er4 : k3'.2 + blk₃.rounds.length = k5'.2 := by
    rw [← er3, ← er5]
    unfold roundsTo
    rw [declsTo_succ hb₃, List.length_append]
  have hHn : k5'.2 + blk₅.rounds.length ≤ heardOf (u3Seats Zp Bs.G₀) Ad := by
    have q' := heard_att h hG hg hPair
    have e6 : rowsBeforeW (14 * (2 * g + 1) + 5) = k5'.2 + blk₅.rounds.length := by
      rw [← er6]
      exact (OnBytes.HonestTrace.U3.Fit.roundsTo_at_head h _).symm
    omega
  have hlenH : k5'.2 + blk₅.rounds.length ≤ μ.st.heard.length := by
    have q' := (𝕋).thread.heard_length hFit
    rw [q', ← er6]
    show _ ≤ 0 + roundsTo cF.blocksInOrder B
    rw [Nat.zero_add]
    exact roundsTo_le cF.blocksInOrder (Nat.le_of_lt hB)
  have hrs' : ((((μ.seen.drop (𝕋).thread.front).drop (roundsTo (𝕋).thread.bs (14 * (2 * g + 1) + 3))).take
      blk₃.rounds.length).map (·.drawn)) = (μ.st.heard.drop k3'.2).take blk₃.rounds.length := by
    rw [hrs]
    show (μ.st.heard.drop (0 + roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3))).take _ = _
    rw [Nat.zero_add, er3]
  have Op := open_of_slice pp A.fs hps hv (Hn := heardOf (u3Seats Zp Bs.G₀) Ad) hrs' (by omega)
    (by omega)
  -- the verifier's points
  obtain ⟨Lf, -, hpv⟩ := Option.bind_eq_some_iff.1 hp
  have hpv' : First.Att.P.pointsOf (First.Att.P.geoOf A.S) Hh.zk hd5 Lf = some p := hpv
  have hI : (𝕋).thread.front + roundsTo (𝕋).thread.bs (14 * (2 * g + 1) + 4) = k5'.2 := by
    show 0 + roundsTo cF.blocksInOrder _ = _
    rw [Nat.zero_add, er5]
  have hSame : ∀ q, H2K5.Honest.SameTo A.own q hd5 (H2K5.Honest.heardAt ⟨A.S, A.own⟩
      ⟨Hh.zk, (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad)).drop k5'.2⟩ fun _ => none) := by
    intro q
    have hc := K5.reads_of_slice (H := heardOf (u3Seats Zp Bs.G₀) Ad) hr5
      (by rw [hI]; exact hHn) Hh.zk
    rw [hI] at hc
    exact H2K5.Honest.heard_is_ours ⟨A.S, A.own⟩ _ hh5 hc q
  -- the shape of what was heard
  have hbl : 14 * (2 * g + 1) + 4 + 1 ≤ cF.blocksInOrder.length := hlt
  have e0 : s₀ = ProofFile.startS Zp μ.st.input.x.pub := hbeg
  rw [e0] at G5
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 4 + 1) (μ.st.input.x.pub, s) :=
    reach_of_fold _ hbl s _ _ _ _ G5
  obtain ⟨t₁, b₄, hr₁, hb₄, y₄⟩ := H2K5.Honest.reach_last (k := 14 * (2 * g + 1) + 4) hr
  obtain rfl : blk₅ = b₄ := Option.some.inj (hb₅c.symm.trans hb₄)
  obtain ⟨R₄, c₄, -, e₄⟩ := y₄
  obtain ⟨a₆, hd₆, G₆, ea₆, hh₆, rfl⟩ := K5.k5_step_is Dc e₄
  obtain ⟨-, rs₀, cols₀, f₀⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 hr₁
  have hz := VerifiableInference.OnPublicFiles.sized_upTo h.scope h.reads O h.laid.planOk (2 * g + 1) (by omega) 1 (by omega) f₀
  obtain ⟨G₇, hG₇, hz₇⟩ := hz
  obtain rfl : a₆.F = G₇ := by
    have : t₁.fork? = some a₆.F := by
      unfold First.S.fork?
      rw [ea₆]
    exact Option.some.inj (this.symm.trans hG₇)
  have hsh := H2K5.Honest.heard5_sh hh₆ ⟨hz₇.1, hz₇.2.1, hz₇.2.2⟩
  obtain rfl : hd₆ = hd5 := Option.some.inj h5s
  exact ⟨k5', k3', Hh, hd₆, Lf, p, t₀, _, q5, q3, Op, hpv', hSame, ht₀, hsh⟩

/-- **AT AN ATTENTION's SEGMENT THE HONEST MAKER's VECTOR RETURNS AT THE CHALLENGES IN FRONT OF ITS SENDING**,
from the verifier's fold at any later border. -/
theorem vec_att_later {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {st : Seat}
    (hst : OnBytes.HonestTrace.seatAt (u3Seats Zp G) Ad = some st) (hseg : st.seg = 2 * g + 1) {B : ℕ}
    (hB : 14 * (2 * g + 1) + 4 + 1 < B) {k : Coins Bk} {sB : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hM : (𝕋).thread.Made B k sB μ E) (hFit : (𝕋).thread.Fit B μ) (cov : Head.Covered) :
    ∀ V', valsAt Zp G cov st.seg = .ok V' → ∃ v, V'.vec (μ.st.heard.take st.heard) = .ok v := by
  intro V' hV'
  have hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, st.array.message) := by
    unfold pairOf
    rw [hst, ← hseg]
    rfl
  have hHe : heardOf (u3Seats Zp G) Ad = st.heard := by
    unfold heardOf
    rw [hst]
    rfl
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨V, hV, hVn, -⟩ := OnBytes.HonestTrace.U3.Att.attVals_at_head h hG hg
  obtain rfl : V = V' := by
    rw [hseg, OnBytes.HonestTrace.U3.Fit.valsAt_att_at_head h hG hg] at hV'
    exact Except.ok.inj (hV.symm.trans hV')
  obtain ⟨A, k5₂, k3₂, hA, e5₂, e3₂, en₂, -⟩ := K5.attVals_vec hV
  obtain ⟨k5, k3, Hh, hd5, Lf, pv, t₀, nx, q5, q3, Op, hpv, hSame, ht₀, hsh⟩ :=
    attRun_later h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hg hG hPair hB hM hFit hA
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hAX : (P5J.At.X Zp).A[g]? = some A := hW ▸ hA
  -- the honest points return
  have pa := K5Law.points_are hpv
  have nL : Lf.scores.size = (H2K5.Honest.blankLeft A.own.score.length).scores.size := by
    have e1 := pa.nL.symm.trans (pa.nH.trans (hSame 0).nS)
    simpa [H2K5.Honest.heardAt, H2K5.Honest.blankLeft] using e1
  obtain ⟨p₀, hp₀, -⟩ := H2K5.Honest.points_congr (hSame 0).nR (hSame 0).nS nL hpv
  have hp₀' : H2K5.Honest.ptsOf ⟨A.S, A.own⟩
      ⟨Hh.zk, (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad)).drop k5.2⟩ = some p₀ := hp₀
  have K : ∀ n, PtsTo A.own n p₀ pv := fun n =>
    H2K5.Honest.points_same ⟨A.S, A.own⟩ (hSame n) hp₀' hpv
  -- the honest tables return
  have hok : K5Law.placeOk (First.Att.P.parCOf A).geo (First.Att.P.parCOf A).mats (First.Att.P.parCOf A).nW
      (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh) pv = true := by
    rw [← K5Law.tablesP_isSome, ht₀]
    rfl
  obtain ⟨t, ht⟩ := K5Law.tablesP_some (placeOk_same K hok)
  have hfun : t.funs = t₀.funs := H2K5.Honest.funs_same
    (H2K5.Honest.points_laid K _ _) ht ht₀
  -- as many weights as rows
  have hpl : (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh).planesOk = true := by
    unfold K5Law.placeOk at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.2
  have hsz := ProofFile.Honest.K3.Law.AtThr.lookHeardAt_sizes A.fs k3.2
    (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad))
  have hG' : H2K5.Honest.tabsFitB (First.Att.P.parCOf A).geo (First.Shape.heard5Sh hd5)
      (First.Shape.heardAll Hh) = true := by
    rw [hsh, H2K5.Honest.tabsFitB_at]
    have hlook : First.Look.planesOk Hh.shape A.S.cf.lmb = true := hpl
    rw [Op.shape] at hlook
    refine planFit_att h hg hAX ?_ ?_ ?_ ?_ hlook
    · exact Op.shape
    · show Hh.zx.size = _
      rw [Op.zx]
      exact hsz.1
    · show Hh.zb0.size = _
      rw [Op.zb0]
      exact (zb_sizes _ _ _).1
    · show Hh.zb1.size = _
      rw [Op.zb1]
      exact (zb_sizes _ _ _).2
  have hfit : First.Att.P.fit (First.Att.P.parCOf A).geo
      (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh) pv = true := by
    rw [K5Law.fit_eq_ten hok]
    exact H2K5.Honest.fitTen_of hpv hG' hpl
  have hphi : ∀ f ∈ t.funs.toList, f.phi.size = f.len := fun f hf => by
    rw [hfun] at hf
    exact (H2K5.Honest.funs_fit ht₀ hfit f hf).2
  have hzk : (k4LookOf A.fs k3.2 (μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad))).zk = Hh.zk := Op.zk.symm
  have hvec := attVals_vec_returns hV hA q5 q3
    (heard := μ.st.heard.take (heardOf (u3Seats Zp Bs.G₀) Ad)) (p := p₀) (t := t)
    (by rw [hzk]; exact hp₀')
    (by rw [lookOf_of_open Op]; exact ht)
    (partsFit_of_tables (mats := A.mats) ht hphi)
  rw [← hHe]
  exact ⟨_, hvec⟩

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.roundsTo_le
#print axioms ProofFile.Honest.K10.att_record_step
#print axioms ProofFile.Honest.K10.attRun_later
#print axioms ProofFile.Honest.K10.vec_att_later
