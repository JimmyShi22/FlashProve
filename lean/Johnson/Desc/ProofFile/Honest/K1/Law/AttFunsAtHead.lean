-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/AttFunsAtHead.lean: THE LAST CLAUSE OF AttPlanS (TieReadsAttS.lean) AT AN
ATTENTION's READS, AT THE HEAD: the list of tables that the state behind the reads' member closes is the list that
tablesP gives at the points that the honest ptsOf makes of what was heard. From Thr's clause Made alone.

  attSeatsB, attSeatsB_yes, attSeatsB_can_fail   a closed test on the written seats of "U3"; the kernel's yes; a control
  heard_att       under the head: the seat of an odd segment's "U3" stands behind the segment's K5 rounds and its sending's
  open_of_slice   where the hearing returns on rounds whose challenges are the slice from i on: OpenSame at heard.take H
  phiB_same, lookOf_of_open   what lookOf reads of a heard record: shape, zx, zb0, zb1
  take_one        a list's take (j + 1) drop j is its element j
  attRun          what the reads' member holds, from Thr's Made alone
  attFuns_head    THE CLAUSE

NO PROPERTY IS CLAIMED.
IDLE WHERE ThrS HOLDS OF NOTHING (at Vd := False, through the thread's clause valid).
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieReadsAttS
import Johnson.Desc.ProofFile.Honest.K5.Law.HeardAtMade
import Johnson.Desc.ProofFile.Honest.K5.Law.AttValsAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.HeardWholeLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AttBackHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.First.Att.LookOAgrees
import Johnson.Desc.K5.Honest.Law.TabsAtReach
import Johnson.Desc.K5.Honest.Law.TabsShape
import Johnson.Desc.K5.Honest.Law.PointsTable
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.HonestTrace.U3Fit.Slice

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (funBack tabsBack)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (pairOf heardOf seatAt Seat)
open OnBytes.HonestTrace.U3 (u3Seats placeIn sizesOf)
open OnBytes.HonestTrace.U3.Fit (rowsBeforeW seatsW)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3 (lookHeardAt OpenSame)
open ProofFile.Honest.K4 (k4LookOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The seats -/

/-- On the written seats of "U3": at an odd segment below 24 the seat stands behind the rows up to the reads' own row. -/
def attSeatsB (c : ℕ) : Bool :=
  (seatsW "U3").all fun s =>
    s.seg % 2 != 1 || decide (24 ≤ s.seg) || decide (rowsBeforeW (14 * s.seg + c) ≤ s.heard)

set_option maxRecDepth 1000000 in
/-- The kernel's yes. -/
theorem attSeatsB_yes : attSeatsB 5 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the test says no a row further on. -/
theorem attSeatsB_can_fail : attSeatsB 6 = false := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The seat of an odd segment's "U3" stands behind the segment's K5 rounds.** -/
theorem heard_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : ℕ} (hg : g < 12) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, am)) :
    rowsBeforeW (14 * (2 * g + 1) + 5) ≤ heardOf (u3Seats Zp G) Ad := by
  unfold pairOf at hPair
  obtain ⟨st, hst, e⟩ := Option.map_eq_some_iff.1 hPair
  have eS : st.seg = 2 * g + 1 := congrArg Prod.fst e
  have hm : st ∈ seatsW "U3" := by
    have q : st ∈ u3Seats Zp G := List.mem_of_find?_eq_some hst
    unfold u3Seats at q
    rwa [OnBytes.HonestTrace.U3.Fit.seats_at_head h hG] at q
  have w := List.all_eq_true.1 (show (seatsW "U3").all _ = true from attSeatsB_yes) st hm
  rw [eS] at w
  unfold heardOf
  rw [hst]
  have h1 : ((2 * g + 1) % 2 != 1) = false := by
    have : (2 * g + 1) % 2 = 1 := by omega
    rw [this]
    rfl
  have h2 : decide (24 ≤ 2 * g + 1) = false := decide_eq_false (by omega)
  rw [h1, h2] at w
  simpa using w

end

/-! ## 2 On lists and on what was heard -/

/-- A list's element j, by take and drop. -/
theorem take_one {α : Type} {l : List α} {j : ℕ} {a : α} (h : l[j]? = some a) :
    (l.take (j + 1)).drop j = [a] := by
  obtain ⟨hlt, e⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.drop_take, show j + 1 - j = 1 by omega, List.drop_eq_getElem_cons hlt, e]
  rfl

/-- **Where the hearing returns on rounds whose challenges are the slice from i on, its record is lookHeardAt at what was
heard, cut anywhere behind the slice.** -/
theorem open_of_slice (p : VerifiableInference.Desc.First.Look.P) (fs : OnBytes.Model.Forest.Shape)
    (hs : p.shape = some fs) {F G₁ : OnBytes.Model.Fork} {rs : List Fmt.RoundView}
    {Hh : OnBytes.Model.Forest.Heard}
    (hv : VerifiableInference.Desc.K3.Law.hearVia p F rs = some (Hh, G₁))
    {heard : List Fmt.Drawn} {i n Hn : ℕ} (hr : rs.map (·.drawn) = (heard.drop i).take n)
    (hin : i + n ≤ Hn) (hlen : i + n ≤ heard.length) :
    OpenSame Hh (lookHeardAt fs i (heard.take Hn)) := by
  have e := ProofFile.Honest.K3.Law.heardWhole_of_hearVia p fs hs F G₁ rs Hh ((heard.take Hn).take i)
    ((heard.take Hn).drop (i + n)) hv
  have l1 : ((heard.take Hn).take i).length = i := by
    rw [List.length_take, List.length_take]
    omega
  have e1 : (heard.drop i).take n = ((heard.take Hn).drop i).take n := by
    rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
  have e2 : (heard.take Hn).take i ++ rs.map (·.drawn) ++ (heard.take Hn).drop (i + n) =
      heard.take Hn := by
    rw [hr, e1, List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  rw [l1, e2] at e
  exact e

/-- phiBOwn reads the shape and the two points zb alone. -/
theorem phiB_same {g g' : OnBytes.Model.Forest.Heard} (es : g.shape = g'.shape) (e0 : g.zb0 = g'.zb0)
    (e1 : g.zb1 = g'.zb1) (lm e : ℕ) :
    VerifiableInference.Desc.First.Look.phiBOwn g lm e =
      VerifiableInference.Desc.First.Look.phiBOwn g' lm e := by
  unfold VerifiableInference.Desc.First.Look.phiBOwn OnBytes.Model.Forest.Heard.zb
  simp only [es, e0, e1]

/-- **What lookOf makes of the honest side's record is what lookOfO makes of the hearing's.** -/
theorem lookOf_of_open {fs : OnBytes.Model.Forest.Shape} {i : ℕ} {L : List Fmt.Drawn}
    {Hh : OnBytes.Model.Forest.Heard} (O : OpenSame Hh (lookHeardAt fs i L)) (lmb : ℕ) :
    First.Att.P.lookOf lmb (k4LookOf fs i L) = First.Att.P.lookOfO lmb Hh := by
  rw [← First.Att.P.lookOfO_eq]
  have es : (k4LookOf fs i L).shape = Hh.shape := O.shape.symm
  have ex : (k4LookOf fs i L).zx = Hh.zx := O.zx.symm
  have e0 : (k4LookOf fs i L).zb0 = Hh.zb0 := O.zb0.symm
  have e1 : (k4LookOf fs i L).zb1 = Hh.zb1 := O.zb1.symm
  unfold First.Att.P.lookOfO
  rw [phiB_same es e0 e1, phiB_same es e0 e1, ex, es]

/-! ## 3 The clause -/

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

set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)

/-- **What the reads' member of an attention's segment holds, from Thr's Made alone.** H' below: what was heard, cut at
the seat's own count. k5, k3: the places' first rounds. Hh: what the lookup on the calls returned, in the state and as
lookHeardAt of H'. hd, Lf, pv: the verifier's points. t₀: the state's tables. -/
theorem attRun {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, am)) {blk : Block TS ProofFile.Cl}
    (hb : (𝕋).bs[K1.noL (2 * g + 1) false]? = some blk) {k : Coins Bk} {s s' : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X} {cols : List OpenedColumn}
    (hT : ThrS (𝕋).thread Said (K1.noL (2 * g + 1) false) k s μ E)
    (hS : (𝕋).thread.Stepped blk k s μ E ds y cols s')
    {A : OnBytes.Attention.Plan} (hA : G.W.A[g]? = some A) :
    ∃ (k5 k3 : Spot × ℕ) (Hh : OnBytes.Model.Forest.Heard) (hd : First.Att.P.Heard)
      (Lf : First.Att.P.Left) (pv : First.Att.P.Pts) (t₀ : First.Att.P.TablesP) (a : First.AttOwn)
      (nx : ℕ),
      placeIn Zp Johnson.AtFull.Desc.spotsWritten (2 * g + 1) .K5 = .ok k5 ∧
      placeIn Zp Johnson.AtFull.Desc.spotsWritten (2 * g + 1) .K3 = .ok k3 ∧
      OpenSame Hh (lookHeardAt A.fs k3.2 (μ.st.heard.take (heardOf (u3Seats Zp G) Ad))) ∧
      First.Att.P.pointsOf (First.Att.P.geoOf A.S) Hh.zk hd Lf = some pv ∧
      (∀ q, H2K5.Honest.SameTo A.own q hd (H2K5.Honest.heardAt ⟨A.S, A.own⟩
        ⟨Hh.zk, (μ.st.heard.take (heardOf (u3Seats Zp G) Ad)).drop k5.2⟩ fun _ => none)) ∧
      First.Att.P.tablesP (First.Att.P.parCOf A).geo (First.Att.P.parCOf A).mats
        (First.Att.P.parCOf A).nW (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb Hh) pv = some t₀ ∧
      s'.tl? = some { a.tl with funClosed := true, funs := (tabsBack t₀).funs } ∧
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
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O (2 * g + 1) hl2
  obtain ⟨m0, m1, -, -, -, -, f2, k2, g2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
  obtain rfl : m1 = Xl := Option.some.inj (f2.symm.trans hX)
  have hU := IM.alone_underR hu
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have hAg : Bs.G₀.W.A[m1.g]? = some A := by
    rw [g2]
    exact hA
  obtain ⟨r₁, r₂, gs, gs₁, s₁, a, hh, gl, p, t₀, -, hlater, -, ha, h5', hgl, hp, ht₀, -, htl'⟩ :=
    att_record (L := 𝕋) k2 hAg hU hS
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hAX : (P5J.At.X Zp).A[g]? = some A := hW ▸ hA
  obtain ⟨blk₅, a₅, hb₅, Pl, Dc⟩ := K5.k5_member h hg
  obtain rfl : A = a₅ := Option.some.inj (hAX.symm.trans Pl.plan)
  have hb₅' : (𝕋).thread.bs[14 * (2 * g + 1) + 4]? = some blk₅ := hb₅
  have hb₅c : cF.blocksInOrder[14 * (2 * g + 1) + 4]? = some blk₅ := hb₅
  have hM : (𝕋).thread.Made (14 * (2 * g + 1) + 4 + 1) k s μ E := by
    have q' := hT.1.2.2.2.2.1
    rwa [i1] at q'
  obtain ⟨F₅, G₅, hd5, rs₅, hh5, hr5, h5s⟩ := K5.heard5_next (𝕋).thread Dc hb₅' hM
  obtain rfl : hd5 = hh := Option.some.inj ((K5.heard5_sent hlater h5s).symm.trans h5')
  -- the lookup on the calls
  have hlt : 14 * (2 * g + 1) + 4 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb₅').1
  obtain ⟨blk₃, hb₃⟩ : ∃ b, cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some b :=
    ⟨cF.blocksInOrder[14 * (2 * g + 1) + 3], List.getElem?_eq_getElem (by omega)⟩
  have hb₃' : (𝕋).thread.bs[14 * (2 * g + 1) + 3]? = some blk₃ := hb₃
  obtain ⟨pp, hps, Hb⟩ := ProofFile.Honest.K3.Law.AtThr.att_back_head h g hg A blk₃ hAX hb₃
  obtain ⟨sj, sj', rs, c, n, rs', c', hst, hrs, hf⟩ := made_member (𝕋).thread (j := 14 * (2 * g + 1) + 3)
    (by omega) hb₃' hM
  obtain ⟨F, Hh, G₁, hv, hgH⟩ := Hb (𝕋).thread.ft sj sj' rs c n hst
  have edrop : ((𝕋).thread.bs.take (14 * (2 * g + 1) + 4 + 1)).drop (14 * (2 * g + 1) + 3 + 1) = [blk₅] :=
    take_one hb₅'
  rw [edrop] at hf
  obtain ⟨s₅, k', -, hs5, hf'⟩ := foldBlocks_cons (𝕋).thread.ft blk₅ [] sj' rs' c' _ hf
  obtain rfl : s₅ = s := (congrArg Prod.fst (foldBlocks_nil _ _ _ _ _ hf')).symm
  obtain ⟨a₄, hd₄, G₄, ea, -, -⟩ := K5.k5_step_is Dc hs5
  have hga := hgH a₄ ea
  obtain ⟨a₂, ea₂, eg₂⟩ := K5.k5_step_keeps_g Dc (𝕋).thread.ft Hh sj' _ _ s₅ _ hs5 ⟨a₄, ea, hga⟩
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
  have hlenH : μ.st.heard.length = k5'.2 + blk₅.rounds.length := by
    have q' := (𝕋).thread.heard_length hT.1.2.1
    rw [i1] at q'
    rw [q']
    show 0 + roundsTo cF.blocksInOrder _ = _
    rw [Nat.zero_add]
    exact er6
  have hrs' : rs.map (·.drawn) = (μ.st.heard.drop k3'.2).take blk₃.rounds.length := by
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
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl
    (by rw [← i1]; exact hT.1)
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
  exact ⟨k5', k3', Hh, hd₆, Lf, p, t₀, a, _, q5, q3, Op, hpv', hSame, ht₀, htl', hsh⟩

/-- **AttPlanS' last clause at an attention's reads, at the head.** -/
theorem attFuns_head {g : ℕ} (hg : g < 12) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Ad : MsgAddr} {am : ℕ}
    (hPair : pairOf (u3Seats Zp G) Ad = some (2 * g + 1, am)) :
    ∀ blk, (𝕋).bs[K1.noL (2 * g + 1) false]? = some blk → ∀ k s μ E ds y cols s',
      ThrS (𝕋).thread Said (K1.noL (2 * g + 1) false) k s μ E →
      drawsFit blk.rounds ds = true → (𝕋).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl →
      ∀ (sps : List Spot) (A' : OnBytes.Attention.Plan) (k5 k3 : Spot × ℕ)
        (q : First.Att.P.Pts) (t : First.Att.P.TablesP),
        spotsOf Zp.cuts = some sps → G.W.A[g]? = some A' →
        placeIn Zp sps (2 * g + 1) .K5 = .ok k5 → placeIn Zp sps (2 * g + 1) .K3 = .ok k3 →
        H2K5.Honest.ptsOf ⟨A'.S, A'.own⟩
          ⟨(k4LookOf A'.fs k3.2 (μ.st.heard.take (heardOf (u3Seats Zp G) Ad))).zk,
            (μ.st.heard.take (heardOf (u3Seats Zp G) Ad)).drop k5.2⟩ = some q →
        First.Att.P.tablesP (⟨A'.S, A'.own⟩ : H2K5.Honest.Pub5).g (sizesOf A'.mats) A'.nW
          (First.Att.P.lookOf A'.S.cf.lmb
            (k4LookOf A'.fs k3.2 (μ.st.heard.take (heardOf (u3Seats Zp G) Ad)))) q = some t →
        tl.funs = t.funs.map funBack := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl sps A' k5 k3 q t hsp hA' e5 e3 hq ht
  obtain ⟨k5', k3', Hh, hd5, Lf, pv, t₀, a, nx, q5, q3, Op, hpv, hSame, ht₀, htl', -⟩ :=
    attRun h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hg hG hPair hb hT hS hA'
  have esp : sps = Johnson.AtFull.Desc.spotsWritten := Option.some.inj
    (hsp.symm.trans (OnBytes.HonestTrace.U3.Fit.spots_at_head h))
  subst esp
  obtain rfl : k5' = k5 := Except.ok.inj (q5.symm.trans e5)
  obtain rfl : k3' = k3 := Except.ok.inj (q3.symm.trans e3)
  obtain rfl := Option.some.inj (htl.symm.trans htl')
  have ez : (k4LookOf A'.fs k3'.2
      (μ.st.heard.take (heardOf (u3Seats Zp G) Ad))).zk = Hh.zk := Op.zk.symm
  rw [ez] at hq
  rw [lookOf_of_open Op] at ht
  have PS := H2K5.Honest.points_laid (fun n => H2K5.Honest.points_same ⟨A'.S, A'.own⟩ (hSame n) hq hpv)
    (⟨A'.S, A'.own⟩ : H2K5.Honest.Pub5).g (First.Att.P.lookOfO (First.Att.P.parCOf A').geo.lmb Hh)
  have ef : t.funs = t₀.funs := H2K5.Honest.funs_same PS ht ht₀
  show t₀.funs.map funBack = _
  rw [ef]

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.attSeatsB_yes
#print axioms ProofFile.Honest.K1.attSeatsB_can_fail
#print axioms ProofFile.Honest.K1.heard_att
#print axioms ProofFile.Honest.K1.take_one
#print axioms ProofFile.Honest.K1.open_of_slice
#print axioms ProofFile.Honest.K1.phiB_same
#print axioms ProofFile.Honest.K1.lookOf_of_open
#print axioms ProofFile.Honest.K1.attRun
#print axioms ProofFile.Honest.K1.attFuns_head
