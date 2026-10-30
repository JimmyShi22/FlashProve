-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/GAtFirstEnd.lean: THE ROW WEIGHTS AT THE FIRST CHAIN's END. The row (Dot) of the last
chain reads the row weights g off the first chain's last state, and the prover makes W of weights
that it computes from the challenges heard. At the border 356 the two are tied by
k13_g_at_356_pileAnyK3 (GAt356AnyK3.lean of this folder). Here the same tie stands at the chain's
last border, where the door between the chains reads it. It spends of the thread what that theorem
spends: how the state was made, the number of the challenges, no mark.

  k13_m4_member_place  the member number 356 stands at W's sending
  k13_tail_step        the state behind the last two sub-protocols is what W's sending makes
  k13_tail_keeps       so they leave the rows, what the parts hand on and the mark as they were
  k13_g_at_first_end   the weights that the filling of W's main rows makes are the row's at the end
  k13_evalLaid_at_end  the row (Eval) is laid at the end

What these are. Conditional lemmas under the library's one hypothesis at the full size, h, and a
base. None is one of the library's goals. They say nothing of soundness, completeness or hiding.

Limits.
  * That the thread stands at any run is not said.
  * The premise on the reply is kept, as in GAt356.lean: the row weights hold one value that was
    sent, the reply as heard. The premise s.rows = [row] is kept too.
-/
import AtFullSide.K13.GAt356AnyK3
import Johnson.IMR.LastFour
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4Proof
import Johnson.Desc.Sound.Gather
import Johnson.AtFull.Shape.Numbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open OnBytes OnBytes.Model
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block foldBlocks noDigest OpenedColumn)
open VerifiableInference.Desc.K13 (battRounds whereOf atM4)
open VerifiableInference.Desc.K13.Honest (rowReads PileIs roundsAhead roundsAhead_succ
  foldCutAt atM3_return_tied sampledRV sampledRV_noDigest)
open VerifiableInference.Desc.K13.Law (atM4_rec StepM4 StepM4.decide)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.AtPlace (k13_m4_alone k13_at_m4 alone_gives)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **The place of number 356.** -/
theorem k13_m4_member_place (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[356]? = some blk) :
    blk.place = ⟨1, none, 4, .K1⟩ := by
  have e := P5J.At.places_paid h.scope h.reads h.laid
  have q : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[356]? = some blk.place := by
    unfold VerifiableInference.Desc.First.blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  rw [e, m4_place] at q
  exact (Option.some.inj q).symm

/-- **The last two sub-protocols of the first chain**: the state behind them is what W's sending
makes of the state in front. -/
theorem k13_tail_step (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {t s : TS}
    {rs z₁ : List Fmt.RoundView} {cols z₂ : List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.drop 356) t rs cols = .ok (s, z₁, z₂)) :
    ∃ P' r₁ r₂ gs, (atM4 (Cl := Unit) (whereOf Zp)
      (VerifiableInference.Desc.K1.sendAtS P')).decide t [r₁, r₂] gs = .ok s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hl : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  obtain ⟨b₆, h₆⟩ : ∃ b, cF.blocksInOrder[356]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨b₇, h₇⟩ : ∃ b, cF.blocksInOrder[357]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have e : cF.blocksInOrder.drop 356 = [b₆, b₇] := by
    have g₆ := List.getElem?_eq_some_iff.1 h₆
    have g₇ := List.getElem?_eq_some_iff.1 h₇
    rw [List.drop_eq_getElem_cons g₆.1, List.drop_eq_getElem_cons g₇.1, g₆.2, g₇.2,
      List.drop_eq_nil_of_le (by omega)]
  rw [e] at hf
  obtain ⟨s₁, n₁, -, st₁, f₁⟩ :=
    VerifiableInference.Desc.Sound.foldBlocks_cons_ok 0 b₆ _ t rs cols _ hf
  obtain ⟨s₂, n₂, -, st₂, f₂⟩ :=
    VerifiableInference.Desc.Sound.foldBlocks_cons_ok 0 b₇ _ s₁ _ _ _ f₁
  have es : s₂ = s := by
    unfold foldBlocks at f₂
    exact congrArg Prod.fst (Except.ok.inj f₂)
  have e7 : s₂ = s₁ := IM.at_357 h.scope h.reads O h₇ st₂
  obtain ⟨P', hw, -⟩ := k13_at_m4 _ _ _ _ _ _ _ _ _ _ _ O
  obtain ⟨x, hF, hA⟩ := k13_m4_alone O hw (List.mem_of_getElem? h₆) (k13_m4_member_place h h₆)
  have hb := ((alone_gives ProofFile.sameReply x b₆ _ _ _ hF hA).2.2.2.2.2.2 _ t s₁ _ _ cols).1 st₁
  have hst : (atM4 (Cl := Unit) (whereOf Zp)
      (VerifiableInference.Desc.K1.sendAtS P')).step 0 t _ cols = .ok (s₁, n₁) := hb.1
  have hM4 : StepM4 Unit (whereOf Zp) P' (((), t) : Unit × TS) ((), s₁) :=
    ⟨rfl, _, _, _, _, hst⟩
  obtain ⟨r₁, r₂, gs, hdec⟩ := hM4.decide
  subst es
  rw [e7]
  exact ⟨P', r₁, r₂, gs, hdec⟩

/-- **So they leave** the rows, what the parts hand on and the mark as they were. -/
theorem k13_tail_keeps (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {t s : TS}
    {rs z₁ : List Fmt.RoundView} {cols z₂ : List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.drop 356) t rs cols = .ok (s, z₁, z₂)) :
    s.rows = t.rows ∧ s.out = t.out ∧ s.failed = t.failed := by
  obtain ⟨P', r₁, r₂, gs, hdec⟩ := k13_tail_step h hf
  obtain ⟨-, -, hfl, ho, hr⟩ := atM4_rec hdec
  exact ⟨hr, ho, hfl⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE ROW WEIGHTS THAT THE FILLING OF W's MAIN ROW MAKES ARE THE ROW's AT THE FIRST CHAIN's
END**: under h and a base, from the thread at the chain's last border, the reply as asked, and the
one row on the state's table. -/
theorem k13_g_at_first_end (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ k s m En,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k s m En →
      ReplyIs ProofFile.Inst.asked m.st.input.x s → ∀ row : TensorRow, s.rows = [row] →
      wG Zp.first.lin (wHeard Zp) (pileAnyK3 Zp Bs.G₀) m.st.input.x
        (m.st.heard.take (wHeard Zp)) = row.g := by
  intro k s m En hT hR row hrow
  have hPile := k13_pileIs_pileAnyK3 h Bs hB
  unfold Thr at hT
  obtain ⟨-, hF, hP, -, hM, -, -⟩ := hT
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, hb, -, hf⟩ := hM
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  subst hb'
  have hf0 : foldBlocks 0 (cF.blocksInOrder.take cF.blocksInOrder.length) (ProofFile.startS Zp m.st.input.x.pub) m.seen
      cols = .ok (s, [], []) := hf
  rw [List.take_length] at hf0
  have hfail : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hlen : m.st.heard.length = roundsTo cF.blocksInOrder cF.blocksInOrder.length := drawsFit_length _ _ hF
  have n356 : roundsTo cF.blocksInOrder 356 = 48290 :=
    (k13_wHeard_is_rounds h).symm.trans (k13_wHeard_at_head h)
  have n355 : roundsAhead cF.blocksInOrder 355 = 48270 := k13_rounds355_at_head h
  have hl : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  obtain ⟨blk, hblk⟩ : ∃ blk, cF.blocksInOrder[355]? = some blk :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨sj, sj', c₀, n, h1, h2, h3⟩ := foldCutAt 0 cF.blocksInOrder 355 blk hblk _ m.seen cols _ hf0
  rw [n355] at h1 h2
  obtain ⟨hkr, hko, hkf⟩ := k13_tail_keeps h h3
  obtain ⟨gs, hdec⟩ := VerifiableInference.Desc.stepOk h2
  obtain ⟨t, msg, x, hd, o, -, -, hfit, hrun, hs', hsamp⟩ :=
    atM3_return_tied ((k13_memberIs_at h).back blk hblk sj _ gs _ hdec)
  have hbl : blk.rounds.length = 20 := by
    rw [(k13_memberIs_at h).rounds blk hblk]
    unfold battRounds
    rw [List.length_cons, List.length_cons, List.length_replicate, m3_kCol h]
  have hB' : (battRounds h.𝔇.P13).length = 20 := by
    rw [← (k13_memberIs_at h).rounds blk hblk]
    exact hbl
  have hsl : 48290 ≤ m.seen.length := by
    have a : m.seen.length = m.st.heard.length := by rw [← hseen, List.length_map]
    have b : roundsTo cF.blocksInOrder 356 ≤ roundsTo cF.blocksInOrder cF.blocksInOrder.length := by
      unfold roundsTo declsTo
      rw [List.take_length]
      have : cF.blocksInOrder = cF.blocksInOrder.take 356 ++ cF.blocksInOrder.drop 356 := (List.take_append_drop _ _).symm
      conv_rhs => rw [this]
      simp
      have := List.sum_take_add_sum_drop (cF.blocksInOrder.map fun a => a.rounds.length) 356
      omega
    omega
  have hRlen : ((m.seen.drop 48270).take 20).length = 20 := by
    rw [List.length_take, List.length_drop]
    omega
  rw [hbl, List.take_of_length_le (by rw [List.length_map, hRlen, hB']),
    sampledRV_noDigest] at hsamp
  have hown : drawnE (((m.seen.drop 48270).take 20).map (·.drawn)) =
      x :: hd.eps :: hd.rounds.map (·.2) := by
    have e : drawnE (((m.seen.drop 48270).take 20).map (·.drawn)) =
        (sampledRV ((m.seen.drop 48270).take 20)).map fun l => l.head?.getD zeroE := by
      unfold drawnE sampledRV
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun a _ => ?_
      show ((a.drawn.elems.head?.map E.ofTriple).getD zeroE) =
        ((a.drawn.elems.map E.ofTriple).head?).getD zeroE
      rw [List.head?_map]
    rw [e, hsamp, List.map_cons, List.map_cons, List.map_map]
    rfl
  have hfj : sj.failed = none := by
    have q : sj'.failed = none := hkf ▸ hfail
    rw [hs'] at q
    exact q
  have hrj : sj.out.reply = some (ProofFile.Inst.asked m.st.input.x) := by
    have q : ReplyIs ProofFile.Inst.asked m.st.input.x sj' := by
      show sj'.out.reply = _
      rw [← hko]
      exact hR
    rw [hs'] at q
    exact q
  have hq := hPile m.st.input.x m.seen cols sj _ _ h1 hfj hrj ((m.st.heard.drop 48270).take 1)
  have hrw : row.g = (Batt.rowOf sj.out.pending o).g := by
    rw [hkr, hs'] at hrow
    have q := (List.cons.inj hrow).1
    rw [← q]
    rfl
  rw [hrw, (claimG_eq hfit hrun).1]
  have hk : Zp.first.lin.kCol = 18 := (k13_wRow_at_head h).2.2.2
  unfold wG wOwn wFront
  rw [k13_wHeard_at_head h, hk]
  have e4 : (m.st.heard.take 48290).drop 48270 = ((m.seen.drop 48270).take 20).map (·.drawn) := by
    rw [List.map_take, List.map_drop, hseen, List.drop_take]
  show claimG (pileAnyK3 Zp Bs.G₀ m.st.input.x ((m.st.heard.take 48290).take 48271))
    ((drawnE ((m.st.heard.take 48290).drop 48270)).getD 0 zeroE)
    ((drawnE ((m.st.heard.take 48290).drop 48270)).getD 1 zeroE)
    ((drawnE ((m.st.heard.take 48290).drop 48270)).drop 2) = _
  rw [e4, hown]
  show claimG (pileAnyK3 Zp Bs.G₀ m.st.input.x ((m.st.heard.take 48290).take 48271)) x hd.eps
    (hd.rounds.map (·.2)) = _
  apply claimG_congr
  have e5 : (m.st.heard.take 48290).take 48271 =
      (m.seen.take 48270).map (·.drawn) ++ (m.st.heard.drop 48270).take 1 := by
    rw [List.take_take, List.map_take, hseen]
    exact List.take_add (l := m.st.heard) (i := 48270) (j := 1)
  rw [e5]
  rw [n355] at hq
  exact hq

/-- **THE ROW (Eval) IS LAID AT THE FIRST CHAIN's END**: from the thread at its last border, off the
verifier's fold. F, y₀: any frame with any string of it: idle arguments of the library's lemma. -/
theorem k13_evalLaid_at_end {F : VerifiableInference.Desc.Sound.Frame} (y₀ : F.E.Str) :
    ∀ k s m En,
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cF.blocksInOrder.length k s m En →
      VerifiableInference.Desc.K13.Law.EvalLaid (whereOf Zp) s := by
  intro k s m En hT
  unfold Thr at hT
  obtain ⟨-, -, -, -, hM, -, -⟩ := hT
  unfold Thread.Made at hM
  obtain ⟨-, -, -, -, s₀, cols, hb, -, hf⟩ := hM
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  subst hb'
  have hf0 : foldBlocks 0 (cF.blocksInOrder.take cF.blocksInOrder.length) (ProofFile.startS Zp m.st.input.x.pub) m.seen
      cols = .ok (s, [], []) := hf
  rw [List.take_length] at hf0
  have hl : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  obtain ⟨blk, hblk⟩ : ∃ blk, cF.blocksInOrder[355]? = some blk :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨sj, sj', c₀, n, -, h2, h3⟩ := foldCutAt 0 cF.blocksInOrder 355 blk hblk _ m.seen cols _ hf0
  obtain ⟨gs, hdec⟩ := VerifiableInference.Desc.stepOk h2
  have hm3 := (k13_memberIs_at h).back blk hblk sj _ gs _ hdec
  have hroom := VerifiableInference.Desc.K13.Law.atM3_fits hm3
  obtain ⟨t, msg, x, hd, o, -, -, -, -, hs', -⟩ := atM3_return_tied hm3
  have hon : VerifiableInference.Desc.K13.Law.FrontOk (whereOf Zp)
      ((sj', y₀) : TS × F.E.Str) := by
    intro l hl'
    have hhere : sj'.here = .mem ⟨msg, #[], some { claim := memberClaim (Batt.rowOf sj.out.pending o) }⟩ := by
      rw [hs']
    unfold VerifiableInference.Desc.K13.Law.linAt at hl'
    simp only [hhere] at hl'
    obtain rfl := Option.some.inj hl'
    exact ⟨⟨_, rfl⟩, hroom⟩
  obtain ⟨P', r₁, r₂, gs', hd'⟩ := k13_tail_step h h3
  exact (VerifiableInference.Desc.K13.Law.atM4_laid hd' y₀ y₀ hon).1

end AtFullSide.K13

#print axioms AtFullSide.K13.k13_tail_step
#print axioms AtFullSide.K13.k13_evalLaid_at_end
#print axioms AtFullSide.K13.k13_m4_member_place
#print axioms AtFullSide.K13.k13_tail_keeps
#print axioms AtFullSide.K13.k13_g_at_first_end
