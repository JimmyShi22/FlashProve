-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/AtChainPays.lean: THE LAYERS' OWN ROUNDS (K4): THE SEATED DECISION
RETURNS, FROM A TEST ON THE PLAN, A GUARD ON THE SHAPE IN FRONT AND NAMED TESTS ON VALUES; AND WHAT
OF THE SHAPE BEHIND IS A FUNCTION OF THE PLAN AND THE SHAPE IN FRONT. General laws: nothing is
evaluated.

  roomB, room_of_B   the ledger has room, on its shape.
  shapeB, shapeFits_sh, zkB, zkFits_sh   two tests on the lookup's record, on its shape.
  lookB, LookFacts, look_of_B   THE GUARD ON THE LOOKUP's RECORD's SHAPE AND THE LEDGER's: its
                  numbers are the layout's; its points have the coordinates that are read; its
                  calls, weights, trees and padding counts are the layout's; the planes' matrix
                  fits; every slot of its end form lies below the next slot and is filled.
  k4PlanB         THE TEST ON THE PLAN ALONE: covers; the ten comparisons (planNumsB); another
                  file's test on six groups of pure functions with the test on the points (hearPB,
                  Johnson/Desc/First/K4/Returns/Pub/JoinPoints.lean); the test on the join (joinB).
  k4FrontB        THE GUARD ON THE CHAIN's SHAPE: a layers' link; roomB; lookB.
  k4U             THE UPDATE: the ledger's shape by hearLedU; what the hearing leaves; the tables'
                  shapes; no count of rows owed.
  MergedAt        the test on values "internal-g-merged-point", at the lookup's record.
  OwnNums, hearNums_tokv, ownNums_of   the sizes and the slots by number, on the shape.
  OwnKnown        the fields of the shape of what the hearing leaves that are a function of the plan
                  and the shape in front (the list below).
  **k4_returns**  k4PlanB; the host's count of the padding keys is the layout's own; k4FrontB at the
                  shape in front; stretchB; AND THREE NAMED TESTS ON VALUES (the request's tokens;
                  MergedAt; the coin, coinB): heardAt returns some (o, G); the decision says yes and
                  the shape behind is k4U at o's shape and its tables' shapes; room is left;
                  OwnKnown.

THE SHAPE OF WHAT THE HEARING LEAVES (OwnSh, Johnson/Desc/First/Shape/Own.lean), FIELD BY FIELD.
  A FUNCTION OF THE PLAN AND THE SHAPE IN FRONT, BY OwnKnown: g · iU3 · K3 · tab · zk · H.fo (whole)
  · H.tT is there · H.wpl.r · hd.r · hd2 is there, with its r · H.tV.p.first · H.tV.sEnd ·
  wo.p.first · wo.sFv · AND, BY ITS FIELD nums (OwnNums): EVERY OTHER SIZE AND SLOT: H.PV · H.ZE ·
  H.tkh · H.ztF · H.gp · H.omV · H.sW · H.sPv · H.wpl.sL | sR · H.tV.sCl | r · the second token
  sumcheck's sCl | sEnd | r · K.rs · K.sA0 | sH1 | sB0 | sV · K.wD · hd.sL | sR · hd2's sL | sR ·
  wo.rm · sVE IN THE FIRST GROUP ALONE (in a later group nothing is said of it).
  READ OFF heardAt, OWED: of each sumcheck (H.tV.p · H.tT's p · wo.p) all but what stands above:
  the two marks in front, the degrees, the number of challenges, the start form's shape, the mark
  "ended"; the second token sumcheck's p.first · EVERY FORM's SHAPE: H.wpl.row · hd.row · hd2's row
  · the two rowU · H.KT · K.Alin · K.Blin · K.rowS · wo.recs · AND THE TABLES' SHAPES (k4U's third
  argument).

Limits. A CONDITIONAL LAW. NOT A STEP ON THE SHAPE ALONE: k4U's second and third arguments are read
off heardAt, which reads the state and the rounds' values. That k4PlanB is true at a plan, that the
host's count is the layout's, and that a shape which the chain reaches passes k4FrontB are not shown
here. k4FrontB IS NOT ALL THAT IS ASKED OF THE SHAPE IN FRONT. Neither k4PlanB nor k4FrontB reads
rowsOwed, and k4U lays it to none. So rows owed do not stop the two Bools, while stretchB's first
clause (s.noneWaits) then fails. Whoever takes the two as the member's test on shapes must carry
that clause. The title names the plan, the shape and values; k4_returns asks besides the host's
count (hL) and stretchB (hS). "SEATED" means: the field decide of blockAtC p at the state that the
first chain carries; the block's planOk, the rounds' test and its place in the run are not in it.
From a yes alone nothing is concluded: "carries" is had under the same three tests on values.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.AtChain
import Johnson.Desc.First.K4.Returns.JoinSkel
import Johnson.Desc.First.K4.Returns.Needs
import Johnson.Desc.First.K4.Returns.Pub.JoinPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own TableAt TableAsk)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4.RtPub (hearPB zkFits zkSize tokensFit tablesAt hear_returns_of_PB)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.Shape

/-! ## The ledger's room, on its shape -/

/-- The arrays on the slots have their size; n more slots fit; every slot from the next on is free.
-/
def roomB (L : LedSh) (n : Nat) : Bool :=
  sizedB L && decide (L.next + n ≤ L.ns) && (L.got.drop L.next).all (!·)

theorem room_of_B {F : Fork} {n : Nat} (h : roomB (ledSh F) n = true) : Room F n := by
  unfold roomB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨sized_of_B h1, h2, fun j hj hf => ?_⟩
  have hf' : F.gotF.getD j false = true := hf
  by_cases hl : j < F.gotF.size
  · have hm : F.gotF[j] ∈ F.gotF.toList.drop F.next :=
      List.mem_iff_getElem.2 ⟨j - F.next, by simp; omega, by
        simp only [List.getElem_drop, Array.getElem_toList]
        congr 1
        omega⟩
    have := List.all_eq_true.1 h3 _ hm
    simp [Array.getD, hl] at hf'
    rw [hf'] at this
    cases this
  · simp [Array.getD, hl] at hf'

/-! ## What the lookup hands over, on its record's shape -/

/-- The lookup's numbers are the layout's (shapeFits), on the lookup's shape. -/
def shapeB (P : Pub) (s : Forest.Shape) : Bool :=
  s.dT == P.y.fo.dT && s.kT == P.y.fo.kT && s.NT == P.y.fo.NT && s.rK == P.y.fo.rK &&
    s.first == P.y.fo.first && s.iota == P.y.fo.iota && s.callOf == P.y.fo.callOf

theorem shapeFits_sh (P : Pub) (fo : Forest.Heard) : shapeFits P fo = shapeB P fo.shape := rfl

/-- Each call has a point, of the plan's number of coordinates: on the sizes. -/
def zkB (P : Pub) (l : List Nat) : Bool :=
  l.length == P.y.fo.NC && (List.range P.y.fo.NC).all fun q => l.getD q 0 == zkSize P q

theorem zkFits_sh (P : Pub) (zk : Array (Array E)) :
    zkFits P zk = zkB P (zk.toList.map (·.size)) := by
  unfold zkFits zkB
  congr 1
  · simp
  · refine List.all_congr rfl fun q => ?_
    congr 1
    by_cases hq : q < zk.size
    · simp [Array.getD, List.getD, hq]
    · simp [Array.getD, List.getD, hq]

/-- **THE GUARD ON THE LOOKUP's RECORD's SHAPE AND THE LEDGER's.** -/
def lookB (P : Pub) (h : HeardAll) (L : LedSh) : Bool :=
  shapeB P h.shape && decide (P.y.h.la ≤ h.shape.dT) && decide (P.y.h.la ≤ h.zx) &&
    decide (P.y.h.lt ≤ h.zx) && h.zk.all (fun n => decide (P.y.h.la ≤ n)) && zkB P h.zk &&
    h.shape.calls.size == P.y.calls.size && h.e == P.y.calls.size &&
    Forest.noPub h.shape == Forest.noPub P.y.fo && h.shape.pub == P.y.fo.pub &&
    (Forest.planeCols h.shape P.y.h.lmb).toBool &&
    h.cEnd.slots.all fun j => decide (j < L.next) && L.got.getD j false

/-- What the guard gives, at the lookup's record and the ledger. -/
structure LookFacts (P : Pub) (fo : Forest.Heard) (F : Fork) : Prop where
  fits : shapeFits P fo = true
  zk : zkFits P fo.zk = true
  calls : fo.shape.calls.size = P.y.calls.size
  e : fo.e.size = P.y.calls.size
  noPub : Forest.noPub fo.shape = Forest.noPub P.y.fo
  pub : fo.shape.pub = P.y.fo.pub
  planes : (Forest.planeCols fo.shape P.y.h.lmb).toBool = true
  hands : ∃ Z ztF ends, K3Hands P fo F Z ztF ends

theorem look_of_B {P : Pub} {fo : Forest.Heard} {F : Fork}
    (h : lookB P (heardAll fo) (ledSh F) = true) : LookFacts P fo F := by
  unfold lookB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := h
  obtain ⟨Z, hZ, -⟩ := lastOf_some fo.zx P.y.h.la a3
  obtain ⟨ztF, hzt, hzs⟩ := lastOf_some fo.zx P.y.h.lt a4
  obtain ⟨ends, he⟩ := mapM_some (fun zk : Array E => (lastOf zk P.y.h.la).toOption) fo.zk.toList
    fun zk hzk => by
      have := List.all_eq_true.1 a5 zk.size (List.mem_map.2 ⟨zk, hzk, rfl⟩)
      obtain ⟨b, hb, -⟩ := lastOf_some zk P.y.h.la (by simpa using this)
      exact ⟨b, hb⟩
  refine ⟨a1, by rw [zkFits_sh]; exact a6, a7, a8, a9, a10, a11, Z, ztF, ends.toArray,
    a2, hZ, ?_, hzt, hzs, fun j hj => ?_⟩
  · rw [Array.mapM_eq_mapM_toList, he]
    rfl
  · have := List.all_eq_true.1 a12 j hj
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    refine ⟨this.1, ?_⟩
    show F.gotF.getD j false = true
    have h2 : F.gotF.toList.getD j false = true := this.2
    by_cases hl : j < F.gotF.size
    · simpa [Array.getD, List.getD, hl] using h2
    · simp [List.getD, hl] at h2

/-! ## The test on the plan, the guard on the chain's shape, the update -/

/-- **THE TEST ON THE PLAN ALONE.** -/
def k4PlanB (p : Par) : Bool :=
  covers p.P && planNumsB p.P p.hp p.g && hearPB p.P p.hp p.g &&
    (p.hp.tl.ix.U.getD 2 none).any fun iU3 =>
      (RtPub.tablesAt p.P p.g).any fun r => joinB p.P p.hp p.g iU3 r.1

/-- **THE GUARD ON THE CHAIN's SHAPE.** k: the slots that are to be left behind the hearing. It does
not read rowsOwed: "no count of rows waits" stands in stretchB (AtChain.lean), at the state. -/
def k4FrontB (p : Par) (k : Nat) (a : ChainSh) : Bool :=
  a.here == 1 &&
    match a.led, a.look with
    | some L, some h => roomB L (k4Takes p.P p.hp p.g + k) && lookB p.P h L
    | _, _ => false

/-- **THE UPDATE ON THE CHAIN's SHAPE.** ow: the shape of what the hearing leaves; fs: the shapes
of its list of tables. It lays rowsOwed := none whatever stood there; where no ledger's shape is
there it hands a on as it is (under k4FrontB one is there). -/
def k4U (p : Par) (ow : OwnSh) (fs : List FunSh) (a : ChainSh) : ChainSh :=
  match a.led with
  | some L =>
    (((a.setLed (hearLedU p.P p.hp p.g L)).layOwn (some ow)).layTables (some fs)).setRowsOwed none
  | none => a

/-- The test on sampled values under the refusal's name "internal-g-merged-point", at the lookup's
record. -/
def MergedAt (P : Pub) (fo : Forest.Heard) : Prop :=
  ∀ Z ends, (lastOf fo.zx P.y.h.la).toOption = some Z →
    (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption) = some ends → ends.all (· == Z) = true

/-- The update on the ledger's shape does not read the request's tokens. -/
theorem hearLedU_tokv (P : Pub) (t : Array Nat) (hp : HPlan2) (g : Nat) (L : LedSh) :
    hearLedU { P with tokv := t } hp g L = hearLedU P hp g L := rfl

/-- The sizes and the slots of the shape of what the hearing leaves, by number (HearNums,
Johnson/Desc/First/K4/Returns/Whole.lean, on the shape). n: the next slot in front. -/
structure OwnNums (P : Pub) (hp : HPlan2) (g n : Nat) (ow : OwnSh) : Prop where
  pv : ow.H.PV = P.y.h.lt
  ze : ow.H.ZE = if (g == 0) = true then P.y.ls + P.y.h.lt else 0
  tkh : ow.H.tkh = if (g == 0) = true then P.y.lPd - P.y.ls else 0
  ztF : ow.H.ztF = P.y.h.lt
  gp : ow.H.gp = ledNS P.y.h.xl
  omV : ow.H.omV = ledNP P.y.h.xl * P.y.NI
  sW : ow.H.sW = n
  wplL : ow.H.wpl.sL = n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + 2))
  wplR : ow.H.wpl.sR = ow.H.wpl.sL + 1
  sPv : ow.H.sPv = n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2)))
  tvCl : ow.H.tV.sCl = ow.H.sPv + ledNP P.y.h.xl * P.y.NI
  tvR : ow.H.tV.r = P.y.h.lt
  tT : (ow.H.tT.map fun t => (t.sCl, t.sEnd, t.r)) =
    some (n + slotsNorms P, n + slotsNorms P + (1 + (1 + (2 * P.y.h.lt + 1))), P.y.h.lt)
  rs : ow.K.rs = hp.lamS
  sA0 : ow.K.sA0 = n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2))
  sH1 : ow.K.sH1 = ow.K.sA0 + 1
  sB0 : ow.K.sB0 = ow.K.sH1 + (1 + P.y.LamM)
  sV : ow.K.sV = ow.K.sB0 + 1
  wD : ow.K.wD = P.y.h.ll + P.y.lPf
  hdL : ow.hd.sL = n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
    (1 + (2 * P.rd.muH + 2))
  hdR : ow.hd.sR = ow.hd.sL + 1
  hd2 : (ow.hd2.map fun l => (l.sL, l.sR)) =
    some (n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)),
      n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)) + 1)
  sVE : (g == 0) = true → ow.sVE = n + slotsNorms P + slotsTerms P +
    slotsStack P hp.lamS (nclp hp g) + slotsGated P
  rm : ow.wo.rm = P.wsLay.lk

/-- The sizes and slots do not read the request's tokens. -/
theorem hearNums_tokv {P : Pub} {t : Array Nat} {hp : HPlan2} {g n : Nat} {o : Own}
    (h : HearNums { P with tokv := t } hp g n o) : HearNums P hp g n o :=
  ⟨h.pv, h.ze, h.tkh, h.ztF, h.gp, h.omV, h.sW, h.wplL, h.wplR, h.sPv, h.tvCl, h.tvR, h.tT, h.rs,
    h.sA0, h.sH1, h.sB0, h.sV, h.wD, h.hdL, h.hdR, h.hd2, h.sVE, h.rm⟩

theorem ownNums_of {P : Pub} {hp : HPlan2} {g n : Nat} {o : Own} (h : HearNums P hp g n o) :
    OwnNums P hp g n (ownSh o) :=
  { pv := h.pv, ze := h.ze, tkh := h.tkh, ztF := h.ztF, gp := h.gp, omV := h.omV, sW := h.sW
    wplL := h.wplL, wplR := h.wplR, sPv := h.sPv, tvCl := h.tvCl, tvR := h.tvR
    tT := by
      show ((o.H.tT.map tscSh).map fun t => (t.sCl, t.sEnd, t.r)) = _
      rw [Option.map_map]
      exact h.tT
    rs := h.rs, sA0 := h.sA0, sH1 := h.sH1, sB0 := h.sB0, sV := h.sV, wD := h.wD, hdL := h.hdL
    hdR := h.hdR
    hd2 := by
      show ((o.hd2.map levelSh).map fun l => (l.sL, l.sR)) = _
      rw [Option.map_map]
      exact h.hd2
    sVE := h.sVE, rm := h.rm }

/-- **What of the shape of what the hearing leaves is a function of the plan and the shape in
front.** L, h: the ledger's shape and the lookup's record's shape in front. -/
structure OwnKnown (p : Par) (L : LedSh) (h : HeardAll) (ow : OwnSh) : Prop where
  g : ow.g = p.g
  unit : p.hp.tl.ix.U.getD 2 none = some ow.iU3
  K3 : ow.K3 = ((p.hp.Fp.trees[ow.iU3]?).map (·.K)).getD 0
  tab : ((RtPub.tablesAt p.P p.g).map fun r => r.1.map fun x => (x.name, x.first, x.len)) =
    some ow.tab
  zk : ow.zk = h.zk
  look : ow.H.fo = h
  tT : ow.H.tT.isSome = true
  wpl : ow.H.wpl.r = p.P.rd.muV
  hd : ow.hd.r = p.P.rd.muH
  hd2 : ow.hd2.map (·.r) = some p.P.rd.muH2
  tvFirst : ow.H.tV.p.first = tvFirstOf p.P L.next
  tvEnd : ow.H.tV.sEnd = tvFirstOf p.P L.next + (1 + (2 * p.P.y.h.lt + 2))
  woFirst : ow.wo.p.first + slotsMerge p.P.wsLay.lk = L.next + k4Takes p.P p.hp p.g
  sFv : ow.wo.sFv = ow.wo.p.first + (1 + (2 * p.P.wsLay.lk + 1))
  nums : OwnNums p.P p.hp p.g L.next ow

theorem here_lay {x : VerifiableInference.Desc.First.Here} (h : hereNo x = 1) :
    ∃ a, x = .lay a := by
  cases x with
  | lay a => exact ⟨a, rfl⟩
  | head a =>
    simp only [hereNo] at h
    split at h <;> cases h
  | _ => cases h

/-- **K4's SEATED DECISION RETURNS, AND THE SHAPE BEHIND IS THE UPDATE**: from the test on the plan,
the host's count of the padding keys, the guard on the shape in front, K4's three tests in front of
the hearing, and three named tests on values. -/
theorem k4_returns (p : Par) (k : Nat) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hP : k4PlanB p = true)
    (hL : VerifiableInference.Desc.First.Look.laidLayers p.P = some p.P.y.fo.pub)
    (hF : k4FrontB p k (chainSh s) = true) (hS : stretchB p s rs = true)
    -- the three tests on values: the request's tokens; the merged point; the coin
    (vT : tokensFit { p.P with tokv := s.tokv } p.g = true)
    (vM : ∀ fo, s.look? = some fo → MergedAt p.P fo)
    (vE : coinB p.P p.g (paired rs (entries p.P p.hp p.g)) = true) :
    ∃ o G, heardAt p s rs = some (o, G) ∧
      ((blockAtC p).decide s rs gs).toOption.map chainSh =
        some (k4U p (ownSh o) (o.funs.toList.map funSh) (chainSh s)) ∧ Room G k ∧
      ∀ L h, (chainSh s).led = some L → (chainSh s).look = some h → OwnKnown p L h (ownSh o) := by
  -- where the chain stands, and the two parts that the guard reads
  unfold k4FrontB at hF
  rw [Bool.and_eq_true, beq_iff_eq] at hF
  obtain ⟨a, hh⟩ := here_lay (x := s.here) hF.1
  have hled : (chainSh s).led = some (ledSh a.F) := by
    show s.fork?.map ledSh = _
    unfold S.fork?
    rw [hh]
    rfl
  have hlook : s.look? = a.fo := by
    unfold S.look?
    rw [hh]
  have hlk : (chainSh s).look = a.fo.map heardAll := by
    show s.look?.map heardAll = _
    rw [hlook]
  have hF2 := hF.2
  rw [hled, hlk] at hF2
  cases hfo : a.fo with
  | none =>
    rw [hfo] at hF2
    cases hF2
  | some fo =>
    rw [hfo] at hF2
    have hF3 : (roomB (ledSh a.F) (k4Takes p.P p.hp p.g + k) &&
        lookB p.P (heardAll fo) (ledSh a.F)) = true := hF2
    rw [Bool.and_eq_true] at hF3
    have hR := room_of_B hF3.1
    have hK := look_of_B hF3.2
    obtain ⟨Z, ztF, ends, hH⟩ := hK.hands
    -- the plan's tests
    unfold k4PlanB at hP
    simp only [Bool.and_eq_true] at hP
    obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hP
    unfold stretchB at hS
    simp only [Bool.and_eq_true] at hS
    obtain ⟨⟨s0, s1⟩, s2⟩ := hS
    obtain ⟨iU3, tab, laid, n, hu, ht, hret⟩ :=
      hear_returns_of_PB (P := { p.P with tokv := s.tokv }) (hp := p.hp) (g := p.g) p3 vT
    have ht' : RtPub.tablesAt p.P p.g = some (tab, laid, n) := ht
    rw [hu, ht'] at p4
    have hJ : joinB p.P p.hp p.g iU3 tab = true := p4
    have hN := planNums_of_B p2
    obtain ⟨o, G, e, a1, a2, a3, a4⟩ := hret fo (F := a.F) (k := k)
      (t := paired rs (entries p.P p.hp p.g)) (Z := Z) (ztF := ztF) (ends := ends) p1 hK.fits hR
      (tape_of_fits (rounds p.P p.hp p.g) rs s1 s2)
      ⟨hN.ns, hN.np, hN.no, hN.muV, hN.endT, hN.muH9, hN.muH29, hN.muH, hN.muH2, hN.ncl⟩
      ⟨hH.depth, hH.z, hH.ends, hH.zt, hH.ztSize, hH.cEnd⟩ hK.zk hK.planes
      (join_pay (P := { p.P with tokv := s.tokv }) hL hJ hK.calls hK.e hK.noPub hK.pub)
      (vM fo (by rw [hlook, hfo]) Z ends hH.z hH.ends) (coin_of_B vE)
    have hv : heardAt p s rs = some (o, G) := by
      unfold heardAt
      rw [hh]
      dsimp only
      rw [hfo]
      show (match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
          (paired rs (entries p.P p.hp p.g)) with
        | some (o, G, []) => some (o, G)
        | _ => none) = _
      rw [e]
    have hl0 : ledSh G = hearLedU { p.P with tokv := s.tokv } p.hp p.g (ledSh a.F) :=
      hear_ledSh (P := { p.P with tokv := s.tokv }) e hR a1 a2 a3 a4
    have hl : ledSh G = hearLedU p.P p.hp p.g (ledSh a.F) := by
      rw [hl0]
      exact hearLedU_tokv p.P s.tokv p.hp p.g _
    refine ⟨o, G, hv, ?_, a1, fun L h eL eh => ?_⟩
    case refine_2 =>
      rw [hled] at eL
      rw [hlk, hfo] at eh
      obtain rfl := Option.some.inj eL
      obtain rfl := Option.some.inj eh
      have ev := a4.v
      have t1 := a4.tvFirst
      have t2 := a4.tvEnd
      have t3 := a4.woFirst
      exact
        { g := by show o.v.g = p.g; rw [ev]; rfl
          unit := by show _ = some o.v.iU3; rw [ev]; exact hu
          K3 := by show o.v.K3 = ((p.hp.Fp.trees[o.v.iU3]?).map (·.K)).getD 0; rw [ev]; rfl
          tab := by
            show _ = some (o.v.tab.map fun x => (x.name, x.first, x.len))
            rw [ev, ht']
            rfl
          zk := by show o.v.zk.toList.map (·.size) = fo.zk.toList.map (·.size); rw [ev]; rfl
          look := by show heardAll o.H.fo = heardAll fo; rw [a4.fo]
          tT := by
            show (o.H.tT.map tscSh).isSome = true
            rw [Option.isSome_map]
            exact a4.tT
          wpl := a4.wpl
          hd := a4.hd
          hd2 := by
            show (o.hd2.map levelSh).map (·.r) = _
            rw [Option.map_map]
            exact a4.hd2
          tvFirst := t1
          tvEnd := by
            show o.H.tV.sEnd = _
            rw [t2, t1]
            rfl
          woFirst := by
            show o.wo.p.first + _ = _
            rw [t3, a3]
            rfl
          sFv := a4.sFv
          nums := ownNums_of (hearNums_tokv a4.nums) }
    have hS' : stretchB p s rs = true := by
      unfold stretchB
      rw [s0, s1, s2]
      rfl
    rw [k4_seat, if_pos hS', hv]
    unfold k4U
    rw [hled]
    show some (((((chainSh s).setLed (ledSh G)).layOwn (some (ownSh o))).layTables
      (some (o.funs.toList.map funSh))).setRowsOwed none) =
      some (((((chainSh s).setLed (hearLedU p.P p.hp p.g (ledSh a.F))).layOwn
        (some (ownSh o))).layTables (some (o.funs.toList.map funSh))).setRowsOwed none)
    rw [hl]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.room_of_B
#print axioms OnBytes.Desc.First.K4.Rt.shapeFits_sh
#print axioms OnBytes.Desc.First.K4.Rt.zkFits_sh
#print axioms OnBytes.Desc.First.K4.Rt.look_of_B
#print axioms OnBytes.Desc.First.K4.Rt.hearLedU_tokv
#print axioms OnBytes.Desc.First.K4.Rt.hearNums_tokv
#print axioms OnBytes.Desc.First.K4.Rt.ownNums_of
#print axioms OnBytes.Desc.First.K4.Rt.here_lay
#print axioms OnBytes.Desc.First.K4.Rt.k4_returns
#print axioms OnBytes.Desc.First.K4.Rt.roomB
#print axioms OnBytes.Desc.First.K4.Rt.shapeB
#print axioms OnBytes.Desc.First.K4.Rt.zkB
#print axioms OnBytes.Desc.First.K4.Rt.lookB
#print axioms OnBytes.Desc.First.K4.Rt.LookFacts
#print axioms OnBytes.Desc.First.K4.Rt.k4PlanB
#print axioms OnBytes.Desc.First.K4.Rt.k4FrontB
#print axioms OnBytes.Desc.First.K4.Rt.k4U
#print axioms OnBytes.Desc.First.K4.Rt.MergedAt
#print axioms OnBytes.Desc.First.K4.Rt.OwnNums
#print axioms OnBytes.Desc.First.K4.Rt.OwnKnown
