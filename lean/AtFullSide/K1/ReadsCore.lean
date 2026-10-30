-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsCore.lean: behind the reads' member of a segment, at a stand of the first chain's
thread under the head: what the law on the vector of reads asks of the state, of every sort of
segment alike. Public data and the walk alone; no coin and no witness is read.

  reach_behind   the state behind the member's step is reached
  book_behind    its book fits and its trees bear their numbers

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.IMR.AtReach
import Johnson.IMR.ArraysOpen
import Johnson.P5J.K8U3Named
import Johnson.K8Q47R.MultipliedArraysNamedAndFound
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsVecS
import Johnson.Desc.ProofFile.Honest.K1.Law.UnderAtReads
import Johnson.Desc.ProofFile.Honest.K1.Law.FrontAtReads
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import AtFullSide.K1.ReadsPublic
import AtFullSide.K1.VecTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open OnBytes OnBytes.Params
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Seat parOfMats seatAt seatsOf)
open OnBytes.HonestTrace.U3 (SegVals valsAt covOf u3Seats)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K8 (cellsAtOf)

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

/-- **The state behind a member's step is reached.** -/
theorem reach_behind {b : Nat} {blk : Block TS ProofFile.Cl}
    (hblk : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y
      cols s') :
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (b + 1) (μ.st.input.x.pub, s') := by
  have hb : b ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1.le
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  obtain ⟨hfit, -⟩ := Block.step_ok.1 hS.2
  exact Reach.succ hr hblk ⟨roundsOf y.1, cols, roundsFit_len _ _ hfit, hS.2⟩

/-- **Behind a member's step the book fits and its trees bear their numbers.** -/
theorem book_behind {b : Nat} {blk : Block TS ProofFile.Cl}
    (hblk : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[b]? = some blk)
    {k : Coins Bk} {s s' : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y
      cols s') :
    Book.BookFits s'.book ∧
      ∀ (z : ℕ) (T' : OnBytes.Tree), s'.book.trees[z]? = some T' → T'.number = z := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := P5J.flat_ok h.toAtMg
  have hr := reach_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hblk hT hS
  have e1 := Meaning.K2.atFirstFits_all O hp hr
  have e2 := Meaning.K2.atFirstBook_all O hp hr
  refine ⟨(VerifiableInference.Desc.Sound.bookFitsB_iff _).1 e1, fun z T' hz => ?_⟩
  unfold K12.Door.atFirstBook K12.Door.bookInOrderB at e2
  simp only [Bool.and_eq_true] at e2
  have hlt := (Array.getElem?_eq_some_iff.1 hz).1
  have q := List.all_eq_true.1 e2.2 z (List.mem_range.2 hlt)
  rw [hz] at q
  simpa using q
end

set_option maxRecDepth 100000 in
/-- Where the reads' cut lies. -/
theorem reads_cut : (List.range 25).all (fun l =>
    decide (14 * l + 3 + (if l = 24 then 1 else 0) ≤ K1.noL l false + 1) &&
      decide (K1.noL l false + 1 ≤ 14 * l + (if l = 24 then 10 else 14)) &&
      decide (IM.k1Ix l false + 1 ≤ 11)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- In front of a reads' member one moment has been sent. -/
theorem reads_moment : (List.range 25).all (fun l =>
    decide (VerifiableInference.Desc.First.momentAt
      (VerifiableInference.Desc.First.shiftAt P5J.At.links l) (IM.k1Ix l false + 1) ≤ 1)) = true := by
  decide +kernel

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
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)

include hSaid in
/-- **VecPlanS FROM THE ONE CLAUSE.** All else is read off the walk and the written plan. -/
theorem vecPlanS_of_tie {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {l first₁ : ℕ} (hl : l < 25) {Sz₀ : OnBytes.HonestTrace.Sz} {blk₁ : Block TS ProofFile.Cl}
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} {own₁ : X} {sort₁ : K1Sort}
    {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List VerifiableInference.Desc.Sound.Mem}
    {rad : ℕ → ℕ}
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) (K1.noL l false) blk₁ wit
      (laterJobAt G.first (K1.gpOf Zp) l (IM.k1Ix l false + 1) 1 first₁ (lotData Sz₀ Zp G)) own₁
      sort₁ arr seats₀ ms rad)
    {st : Seat} {n : ℕ} (hs : st ∈ u3Seats Zp G) (hseg : st.seg = l)
    (hsa : st.addr = ⟨⟨(K1.parLater G.first (K1.gpOf Zp) l (IM.k1Ix l false + 1) 1).place, 0⟩, n⟩)
    (hn : n < (K1.parLater G.first (K1.gpOf Zp) l (IM.k1Ix l false + 1) 1).sent.size)
    (hsh : Johnson.Prover.Send.shapeAt (K1.parLater G.first (K1.gpOf Zp) l (IM.k1Ix l false + 1) 1) n =
      st.shape) {nR : ℕ} (hCn : nR ≤ st.array.sizeC)
    (hix : ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[K1.noL l false]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false) k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl → u3Of tl = 0)
    (T : VecTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (K1.noL l false) wit
      Zp G l nR st.addr) :
    VecPlanS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said (K1.noL l false) wit Zp G
      n l nR st.addr := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain rfl : blk₁ = blk := Option.some.inj (R.member.symm.trans hb)
  obtain ⟨hFits, hNum⟩ := book_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT.1 hS
  obtain ⟨SV, vec, hv, hvec, hnR, hE⟩ := T _ hb k s μ E ds y cols s' hT hd hS tl htl
  have hu3 := hix _ hb k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨Ap, p, hAp, hp, -, -⟩ := front_at_reads h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    hSaid hl hb hT hS
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  have eG : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨Xl, reads, hX₀, hU₀⟩ := underR_reads h.scope h.reads O hl hb
  have hr' := reach_behind h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT.1 hS
  obtain ⟨-, rs, cs', f⟩ := hr'.fold
  have hcut := List.all_eq_true.1 reads_cut l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcut
  obtain ⟨L', hL', hlk, harr, hlay, -⟩ :=
    Meaning.K2.arrays_open h.scope h.reads O hl hX₀ hcut.1.1 hcut.1.2 f
  have hX : G.built[l]? = some Xl := eG ▸ hX₀
  have hU : Block.UnderR blk₁ ((IM.k1Reads Zp G l Xl (IM.k1Ix l false + 1) reads).retype : Block TS ProofFile.Cl) :=
    eG ▸ hU₀
  rw [eG] at hlay
  obtain ⟨tl₀, hpL, -, -, hbk⟩ := K1.segAt_some hp
  obtain rfl : p.L = L' := Option.some.inj (hpL.symm.trans hL')
  obtain ⟨c1, ⟨M, hM, eMs, hans⟩, cpair, cname, csz, claid, ccount⟩ := seat_clauses h hG hs
  rw [hseg] at c1 hM cpair ccount
  have hmsg : st.addr.msg = n := by rw [hsa]
  rw [hmsg] at ccount
  -- the array
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public h.laid.pub
  have hP := K8Q47.built_plan h.scope h.reads h.laid.pub hG (Nat.lt_succ_iff.1 hl) hX
  rw [ProofFile.Law.blankBy_W hG] at hP
  have eU := K8Q47.U_of_plan hpub hP
  have hU3 := P5J.K8N.u3_at_ground h.laid.pub hG hX 0 (by rw [eU]; rfl)
  -- the step
  obtain ⟨-, r₁', r₂', gs', -, hdec', -⟩ := step_at_block R Said hT hd hS
  have hB := R.books _ _ _ _ _ hdec'
  obtain ⟨ecodes, xm, hxm, hshape, -⟩ := msg_at_block _ R.isSend hdec' hB n hn
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact K1.rounds_k1Reads Zp G l Xl _ reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec2 : (IM.k1Reads Zp G l Xl (IM.k1Ix l false + 1) reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ :=
    K1.joined_yes _ _ _ _ _ (IM.k1Quiet G l Xl) s s' r₁ r₂ _ hdec2
  obtain ⟨LA, L1, a1, a2, e, -⟩ := K1.commitAtS_frame _ _ _ _ s s₁ r₁ r₂ gs₁ h1
  have hq := (K1.quietP_orLoud _ _ _ G l Xl _) s₁ s' _ _ h3
  have eL : s'.link? = some L1 := hq.2.2.2.1.trans a2
  have eL1 : p.L = L1 := Option.some.inj (hpL.symm.trans eL)
  -- the frame in front
  have hIn := inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT
  have σ : (Sound.frameAt (D.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (D.at OnBytes.Slice.frS.P.T.a))
      (D.at OnBytes.Slice.frS.P.T.a).key₁ 0).E.Str := (fun _ => default, fun _ => default)
  have hu : s.failed = none := (hIn (Sound.strsOf _ σ)).2
  have FF := foldFacts_thr (X := X) h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  have hbl : K1.noL l false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1.le
  obtain ⟨-, f2, -, f4⟩ := FF.frameIs (K1.noL l false) (μ.st.input.x.pub, s)
    ⟨1, some l, IM.k1Ix l false + 1, .K1⟩ l LA ⟨hbl, k, μ, E, hT.1, rfl⟩ hu R.placeAt rfl a1
  obtain ⟨hlk2, hnext⟩ := f4 (Nat.le_trans hcut.2 (Nat.le_add_right _ _))
  have hsz : LA.check.frame.own.size + n = st.array.message := by
    have hm1 := List.all_eq_true.1 reads_moment l (List.mem_range.2 hl)
    simp only [decide_eq_true_eq] at hm1
    have eOwn : (P5J.At.foldD Zp cF VerifiableInference.Desc.K13.Law.LFull).ownAt l
        (VerifiableInference.Desc.First.momentAt
          (VerifiableInference.Desc.First.shiftAt P5J.At.links l) (IM.k1Ix l false + 1)) =
        (VerifiableInference.Desc.First.FillSent.sentDataAt (P5J.At.shape Zp) (P5J.At.N Zp cF)
          P5J.At.links P5J.At.ps Zp.made.p.built.links).own l := by
      show VerifiableInference.Desc.First.FillSent.ownAt _ _ _ _ _ l _ = _
      unfold VerifiableInference.Desc.First.FillSent.ownAt
      rw [if_pos hm1]
    have eShape : P5J.At.shape Zp = G.first.shape := by
      rw [Meaning.K2.blank_first hG]
      rfl
    rw [f2, eOwn]
    simp only [VerifiableInference.Desc.First.FillSent.sentDataAt,
      VerifiableInference.Desc.First.FillSent.sentDataOf, Array.size_map, Array.size_range]
    rw [eShape]
    exact ccount
  have ho : p.L.check.frame.whereIs l st.array.message = some (s.st.oracles.size + n) := by
    rw [eL1, e]
    simp only [ReqFrame.whereIs, hnext, hlk2, bne_self_eq_false, Bool.false_eq_true, if_false,
      beq_self_eq_true, if_true]
    rw [← hsz, Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact K1.idsOf_get _ _ _ hn
  have hok : laidMatrixOk st.array
      (p.d.st.rowBits (s.st.oracles.size + n) .main)
      (p.d.st.placeBits (s.st.oracles.size + n) .main) = true := by
    rw [K1.segAt_st hp]
    have hx : xm.shape = st.shape := hshape.trans hsh
    have e1 : s'.st.rowBits (s.st.oracles.size + n) .main =
        ceilLog2 (st.shape.rows .main) := by
      unfold Statement.rowBits
      rw [hxm]
      show ceilLog2 (xm.shape.rows .main) = _
      rw [hx]
    have e2 : s'.st.placeBits (s.st.oracles.size + n) .main =
        (if st.shape.rows .main == 0 then 0
          else (G.first.codes.base.getD st.shape.code default).logEll) := by
      unfold Statement.placeBits
      rw [hxm]
      show (if xm.shape.rows .main == 0 then 0
        else (s'.st.codes.base.getD xm.shape.code default).logEll) = _
      rw [hx, ecodes]
      rfl
    rw [e1, e2]
    exact claid
  refine ⟨hFits, hNum, p, hp, (l, "U3"), st.array, "U3", M, SV, vec, ?_, ?_, ho, hok, c1, hM, hans,
    ?_, cname, csz, hCn, hv, hvec, hnR, hE⟩
  · rw [hu3, harr]
    exact hU3
  · rw [hlay]
    exact c1
  · rw [hsa] at cpair
    rw [hsa]
    exact cpair
end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.book_behind
#print axioms ProofFile.Honest.K1.vecPlanS_of_tie
