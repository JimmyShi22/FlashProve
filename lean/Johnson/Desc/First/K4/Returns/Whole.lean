-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Whole.lean: THE LAYERS' OWN ROUNDS (K4): THE HEARING RETURNS (hear,
OnBytes/Desc/First/K4/Hear.lean; hearFl, OnBytes/Desc/First/K4/Plain.lean), with the whole tape used
up. A general law: nothing is evaluated.

  nclp, rowsMerge, rounds_eq, k4Takes   K4's table, part by part; the slots that the hearing takes.
  optClaim_tape   the embedding's value, in the first group alone.
  envOf           the environment of the forms, as the hearing lays it.
  PlanNums        THE PLAN's NUMBERS: ten comparisons of public numbers.
  K3Hands         WHAT THE LOOKUP (the kind K3, heard in front of K4) HANDS OVER, on sizes and
                  marks: the depth; the three readings of its points return; the token point's
                  length; every slot of its end form has been shown.
  HearPub         THE READINGS OF PURE FUNCTIONS, AS PREMISES: six fields for the hearing's other
                  "get"s and "must"s and the merge's three tests on the claims. THREE OF THE SIX
                  (stack, claims, points) ARE ASKED AT THE LOOKUP's RECORD fo, WHICH HOLDS DRAWN
                  VALUES, and for all arrays that are drawn or shown later, of the lengths that the
                  table of rounds fixes: so these three are no tests on public data. Its field
                  claims holds THE ONE TEST THAT READS THE REQUEST (inside claimE: in the first
                  group there are T tokens, each below the vocabulary's size).
  **hear_returns**   covers (the plan is one for which K4 is written:
                  OnBytes/Desc/First/K4/Rounds.lean), shapeFits (seven numbers of the lookup's shape
                  fo.shape are the layout's: OnBytes/Desc/First/K4/Hear.lean: ONE MORE PREMISE THAT
                  READS fo), room for k4Takes, a tape of the table's shape, PlanNums, K3Hands,
                  HearPub, AND THE TWO TESTS ON SAMPLED VALUES, by the names of their
                  refusals: "internal-g-merged-point" and "coin-zero": the hearing returns, nothing
                  is left of the tape, the room behind is left, nothing below has turned, the next
                  slot is k4Takes further, and HearLeft.
  HearNums        THE SIZES AND THE SLOTS OF WHAT THE HEARING LEAVES, BY NUMBER: of the plan's
                  numbers and the next slot in front.
  HearLeft        WHAT THE HEARING LEAVES: what a later listing's return hangs on (the environment;
                  the lookup's record; the second token sumcheck is there; three sizes); the two
                  sumchecks that are still open, with their windows by number; AND WHICH SLOTS ARE
                  FILLED: of those that the hearing takes all but these two windows.

Of the two tests on values the first is no chance event, by a reading of the lookup's own text
(OnBytes/Model/Look.lean lays each call's point as a part of one point followed by the lookup's
own): it should hold at every record that the lookup returns; no law says so here.

Limits. A CONDITIONAL LAW. HearPub IS A BUNDLE OF PREMISES ON PURE FUNCTIONS' RETURNS: THAT IT HOLDS
AT ANY PLAN IS NOT SHOWN IN THIS FILE, nor that these returns hang on sizes and the layout alone: so
this file does not show that the law's premises can be met together. Of the returned record HearLeft
says a part (the parts' laws say more, part by part). That the ledger's other fields stay is not
said.
Nothing on what a form is worth. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled)

/-- The panels' weight claims by the plan. -/
def nclp (hp : HPlan2) (g : Nat) : Nat := hp.NCL - (if (g == 0) = true then 1 else 0)

/-- The rows of K4's table that the merge hears: its number 7. -/
def rowsMerge (P : Pub) (hp : HPlan2) (g : Nat) : List Rd :=
  [batchRd (if (g == 0) = true then 1 else 0) hp.NCL] ++ masked P.wsLay.lk 1 1 1

/-- K4's table, part by part. -/
theorem rounds_eq (P : Pub) (hp : HPlan2) (g : Nat) :
    rounds P hp g = rowsNorms P g ++ (rowsTerms P ++ (rowsStack P hp.lamS (nclp hp g) ++
      (rowsGated P ++ rowsMerge P hp g))) := by
  unfold rounds rowsNorms rowsTerms rowsStack rowsGated rowsMerge nclp
  cases (g == 0) <;> simp [List.append_assoc]

/-- The slots that K4's hearing takes. -/
def k4Takes (P : Pub) (hp : HPlan2) (g : Nat) : Nat :=
  slotsNorms P + (slotsTerms P + (slotsStack P hp.lamS (nclp hp g) + (slotsGated P +
    ((if (g == 0) = true then 1 else 0) + slotsMerge P.wsLay.lk))))

/-- The embedding's value, in the first group alone; what is left is the merge's batching round with
nothing more to take. -/
theorem optClaim_tape (b : Bool) {F : Fork} {rows k : Nat}
    (hR : Room F ((if b = true then 1 else 0) + k)) {t : Tape}
    (hT : TapeOf [batchRd (if b = true then 1 else 0) rows] t) (u : Tape) :
    ∃ j G x, (if b = true then engFl.claimsIn 1 else pure 0) F (t ++ u) =
        some (j, G, ⟨some RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u) ∧
      Room G k ∧ Below F G ∧ G.next = F.next + (if b = true then 1 else 0) ∧
      (b = true → j = F.next ∧ Filled G j) := by
  obtain ⟨s, d, t', rfl, a1, a2, a3⟩ := tape_cons hT
  obtain rfl := tape_nil a3
  obtain ⟨x, rfl⟩ := len_one a2
  cases b with
  | true =>
    obtain ⟨G, b1, b2, b3, b4, b5, b6⟩ := claimsInR (n := 1) hR (some RoundName.batSigma.name) 0
      rows s [] [x] u a1
    rw [List.append_nil] at b1
    have f0 := b5 0 (by omega)
    exact ⟨F.next, G, x, b1, b2, ⟨b4, fun _ => b2.sized, by omega, b6⟩, b3, fun _ => ⟨rfl, f0⟩⟩
  | false =>
    obtain rfl := len_zero a1
    exact ⟨0, F, x, rfl, by simpa using hR, Below.refl F, rfl, fun h => by cases h⟩

/-- The environment of the forms, as the hearing lays it. -/
def envOf (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (iU3 : Nat) (tab : List TableAt) :
    Env :=
  { y := P.y, sc := P.sc, g := g, iU3 := iU3, K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0,
    tab := tab, zk := fo.zk }

/-- **THE PLAN's NUMBERS**: comparisons of public numbers that the layers' orders, the batching
rounds and the sumchecks want. -/
structure PlanNums (P : Pub) (hp : HPlan2) (g : Nat) : Prop where
  ns : ledNS P.y.h.xl ≠ 0
  np : ledNP P.y.h.xl * P.y.NI ≠ 0
  no : 1 ≤ ledNO P.y.h.xl * P.y.NI
  muV : P.rd.muV ≤ P.rd.lNI + P.y.lPd + P.y.h.lt
  endT : 1 ≤ nEndT P.y
  muH9 : 9 ≤ P.rd.muH
  muH29 : 9 ≤ P.rd.muH2
  muH : P.rd.muH ≤ min (P.y.h.ll + P.y.lPf) hp.lamS + P.y.h.lt
  muH2 : P.rd.muH2 ≤ (P.y.h.ll - 1) + min P.y.lfe hp.lamS + P.y.h.lt
  ncl : (g == 0) = true → 1 ≤ hp.NCL

/-- **WHAT THE LOOKUP HANDS OVER**, on sizes and marks. Z, ends, ztF: what the three readings of its
points return. -/
structure K3Hands (P : Pub) (fo : Forest.Heard) (F : Fork) (Z ztF : Array E)
    (ends : Array (Array E)) : Prop where
  depth : P.y.h.la ≤ fo.shape.dT
  z : (lastOf fo.zx P.y.h.la).toOption = some Z
  ends : (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption) = some ends
  zt : (lastOf fo.zx P.y.h.lt).toOption = some ztF
  ztSize : ztF.size = P.y.h.lt
  cEnd : Shown F fo.cEnd

/-- **THE READINGS OF PURE FUNCTIONS**, as premises: stack, claims and points are asked at the
lookup's record, which holds drawn values, and for all arrays that are drawn or shown later, of the
lengths that the table of rounds fixes. -/
structure HearPub (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (ztF : Array E)
    (iU3 : Nat) (tab : List TableAt) (laid : List (TableAsk × List (Nat × Nat))) : Prop where
  unit : hp.tl.ix.U.getD 2 none = some iU3
  funOpen : hp.tl.funOpen = true
  tables : ∃ nU3, layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
      (tableAsks P.y P.rd g) 0 = some (tab, laid, nU3) ∧ (nU3 == hp.nU.getD 2 0) = true
  stack : ∀ H : Heard, H.fo = fo → H.ztF = ztF →
    StackPub P (envOf P hp g fo iU3 tab) H hp.lamS (nclp hp g)
  claims : ∃ TS, callsTS P = some TS ∧ ∀ (rs rt ZE tkh : Array E), rs.size = hp.lamS →
    rt.size = P.y.h.lt → ZE.size = (if (g == 0) = true then P.y.ls + P.y.h.lt else 0) →
    tkh.size = (if (g == 0) = true then P.y.lPd - P.y.ls else 0) →
    ∃ claimsP claimsE,
      ({ v := envOf P hp g fo iU3 tab, wsLay := P.wsLay, rope := P.rope, rs := rs, rt := rt } :
        ClaimEnv).weightClaims TS = some claimsP ∧
      (if (g == 0) = true then
        (({ v := envOf P hp g fo iU3 tab, wsLay := P.wsLay, rope := P.rope, rs := rs, rt := rt } :
          ClaimEnv).claimE ZE tkh P.V P.tokv).map ([·]) else some []) = some claimsE ∧
      ((claimsP ++ claimsE).toArray.size == hp.NCL) = true ∧
      (!(claimsP ++ claimsE).toArray.isEmpty && decide ((claimsP ++ claimsE).toArray.size ≤ 4096)) =
        true ∧
      ((claimsP ++ claimsE).toArray.all fun c => decide (c.ui < P.wsLay.U.size)) = true ∧
      ((claimsP ++ claimsE).toArray.all fun c => (wsClaimShape P.wsLay c).isOk) = true
  points : ∀ (H : Heard) (hd hd2 : Level) (tT : Tsc), H.fo = fo → H.ztF = ztF → H.tT = some tT →
    tT.r.size = P.y.h.lt → H.PV.size = P.y.h.lt →
    H.ZE.size = (if (g == 0) = true then P.y.ls + P.y.h.lt else 0) → H.wpl.r.size = P.rd.muV →
    H.tV.r.size = P.y.h.lt → hd.r.size = P.rd.muH → hd2.r.size = P.rd.muH2 →
    ∃ pts funs, pointsOf P.y H hd (some hd2) = some pts ∧ funsOf P.y fo pts laid = some funs

/-- **THE SIZES AND THE SLOTS OF WHAT THE HEARING LEAVES, BY NUMBER.** n: the next slot in front. -/
structure HearNums (P : Pub) (hp : HPlan2) (g n : Nat) (o : Own) : Prop where
  pv : o.H.PV.size = P.y.h.lt
  ze : o.H.ZE.size = if (g == 0) = true then P.y.ls + P.y.h.lt else 0
  tkh : o.H.tkh.size = if (g == 0) = true then P.y.lPd - P.y.ls else 0
  ztF : o.H.ztF.size = P.y.h.lt
  gp : o.H.gp.size = ledNS P.y.h.xl
  omV : o.H.omV.size = ledNP P.y.h.xl * P.y.NI
  sW : o.H.sW = n
  wplL : o.H.wpl.sL = n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + 2))
  wplR : o.H.wpl.sR = o.H.wpl.sL + 1
  sPv : o.H.sPv = n + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2)))
  tvCl : o.H.tV.sCl = o.H.sPv + ledNP P.y.h.xl * P.y.NI
  tvR : o.H.tV.r.size = P.y.h.lt
  tT : (o.H.tT.map fun t => (t.sCl, t.sEnd, t.r.size)) =
    some (n + slotsNorms P, n + slotsNorms P + (1 + (1 + (2 * P.y.h.lt + 1))), P.y.h.lt)
  rs : o.K.rs.size = hp.lamS
  sA0 : o.K.sA0 = n + slotsNorms P + slotsTerms P + (1 + (2 * hp.lamS + 2))
  sH1 : o.K.sH1 = o.K.sA0 + 1
  sB0 : o.K.sB0 = o.K.sH1 + (1 + P.y.LamM)
  sV : o.K.sV = o.K.sB0 + 1
  wD : o.K.fin.wD = P.y.h.ll + P.y.lPf
  hdL : o.hd.sL = n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
    (1 + (2 * P.rd.muH + 2))
  hdR : o.hd.sR = o.hd.sL + 1
  hd2 : (o.hd2.map fun l => (l.sL, l.sR)) =
    some (n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)),
      n + slotsNorms P + slotsTerms P + slotsStack P hp.lamS (nclp hp g) +
      (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2)) + 1)
  sVE : (g == 0) = true → o.sVE = n + slotsNorms P + slotsTerms P +
    slotsStack P hp.lamS (nclp hp g) + slotsGated P
  rm : o.wo.rm.size = P.wsLay.lk

/-- **WHAT THE HEARING LEAVES**: what a later listing's return hangs on, the two sumchecks that are
still open with their windows by number, WHICH SLOTS ARE FILLED, and the sizes and slots by number.
F: the ledger in front; G: behind. -/
structure HearLeft (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (iU3 : Nat)
    (tab : List TableAt) (F G : Fork) (o : Own) : Prop where
  v : o.v = envOf P hp g fo iU3 tab
  fo : o.H.fo = fo
  tT : o.H.tT.isSome = true
  wpl : o.H.wpl.r.size = P.rd.muV
  hd : o.hd.r.size = P.rd.muH
  hd2 : o.hd2.map (·.r.size) = some P.rd.muH2
  tvOpen : Open o.H.tV.p G
  tvFirst : o.H.tV.p.first = F.next + ledNS P.y.h.xl * P.y.NI + (1 + (2 * P.rd.muV + (2 + 2))) +
    ledNP P.y.h.xl * P.y.NI + 1
  tvEnd : o.H.tV.sEnd = o.H.tV.p.first + (1 + (2 * P.y.h.lt + 2))
  woOpen : Open o.wo.p G
  woFirst : o.wo.p.first + slotsMerge P.wsLay.lk = G.next
  sFv : o.wo.sFv = o.wo.p.first + (1 + (2 * P.wsLay.lk + 1))
  /-- of the slots that the hearing takes just the two open sumchecks' own are free -/
  marks : ∀ j, F.next ≤ j → j < G.next →
    (Filled G j ↔ ¬ (o.H.tV.p.first ≤ j ∧ j < o.H.tV.sEnd) ∧ ¬ (o.wo.p.first ≤ j ∧ j < o.wo.sFv))
  nums : HearNums P hp g F.next o

/-- **K4's HEARING RETURNS.** -/
theorem hear_returns (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) {F : Fork} {k : Nat}
    {t : Tape} {Z ztF : Array E} {ends : Array (Array E)} {iU3 : Nat} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))}
    (hc : covers P = true) (hs : shapeFits P fo = true) (hR : Room F (k4Takes P hp g + k))
    (hT : TapeOf (rounds P hp g) t) (hN : PlanNums P hp g) (hK : K3Hands P fo F Z ztF ends)
    (hP : HearPub P hp g fo ztF iU3 tab laid)
    -- the two tests on sampled values
    (vM : ends.all (· == Z) = true)
    (vE : ∀ t₁ s0 eps t₂, TapeOf (rowsNorms P g) t₁ →
      t = t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false) :
    ∃ o G, hearFl P hp g fo F t = some (o, G, []) ∧ Room G k ∧ Below F G ∧
      G.next = F.next + k4Takes P hp g ∧ HearLeft P hp g fo iU3 tab F G o := by
  rw [rounds_eq] at hT
  unfold k4Takes at hR
  obtain ⟨t1, r1, rfl, h1, hT⟩ := tape_append hT
  obtain ⟨t2, r2, rfl, h2, hT⟩ := tape_append hT
  obtain ⟨t3, r3, rfl, h3, hT⟩ := tape_append hT
  obtain ⟨t4, t5, rfl, h4, h5⟩ := tape_append hT
  unfold rowsMerge at h5
  obtain ⟨t6, t7, rfl, h6, h7⟩ := tape_append h5
  -- 1 to 3
  obtain ⟨H1, G1, a1, a2, a3, a4, a5⟩ := hearNorms_returns P g fo (F := F)
    (k := slotsTerms P + (slotsStack P hp.lamS (nclp hp g) + (slotsGated P +
      ((if (g == 0) = true then 1 else 0) + slotsMerge P.wsLay.lk))) + k)
    (by refine hR.mono ?_; omega) h1 (t2 ++ (t3 ++ (t4 ++ (t6 ++ t7)))) hN.ns hN.np hN.no hN.muV
    hK.depth hK.z hK.ends hK.zt vM
  -- 4, its first part
  obtain ⟨H2, G2, tT, b1, b2, b3, b4, b5⟩ := hearTerms_returns P H1 (F := G1)
    (k := slotsStack P hp.lamS (nclp hp g) + (slotsGated P +
      ((if (g == 0) = true then 1 else 0) + slotsMerge P.wsLay.lk)) + k)
    (by refine a2.mono ?_; omega) h2 (t3 ++ (t4 ++ (t6 ++ t7)))
    (by rw [a5.ztF, hK.ztSize]) hN.endT
    (fun s0 eps t' e => vE t1 s0 eps (t' ++ (t3 ++ (t4 ++ (t6 ++ t7)))) h1 (by rw [e]; simp))
  have eFo : H2.fo = fo := by rw [b5.rest]; exact a5.fo
  have eZt : H2.ztF = ztF := by rw [b5.rest]; exact a5.ztF
  have ePV : H2.PV.size = P.y.h.lt := by rw [b5.rest]; exact a5.pv
  have eZE : H2.ZE.size = if (g == 0) = true then P.y.ls + P.y.h.lt else 0 := by
    rw [b5.rest]; exact a5.ze
  have eTk : H2.tkh.size = if (g == 0) = true then P.y.lPd - P.y.ls else 0 := by
    rw [b5.rest]; exact a5.tkh
  have eWp : H2.wpl.r.size = P.rd.muV := by rw [b5.rest]; exact a5.wplR
  have eTV : H2.tV.r.size = P.y.h.lt := by rw [b5.rest]; exact a5.tvR
  have b4' : G2.next = G1.next + (1 + (1 + (2 * P.y.h.lt + (1 + nEndT P.y)))) := b4
  have hcl := b5.cl
  have hse := b5.sEnd
  -- 4, its end, and 5
  obtain ⟨K, G3, c1, c2, c3, c4, c5⟩ := hearStack_returns P (envOf P hp g fo iU3 tab) H2 hp.lamS
    (nclp hp g) (F := G2)
    (k := slotsGated P + ((if (g == 0) = true then 1 else 0) + slotsMerge P.wsLay.lk) + k)
    (by refine b2.mono ?_; omega) h3 (t4 ++ (t6 ++ t7)) (hP.stack H2 eFo eZt) b5.some
    (by omega) b5.clF (fun i hi => ⟨by omega, b5.ends i hi⟩)
    (by rw [eFo]; exact hK.cEnd.below (a3.trans b3)) b5.kt
  have c4' : G3.next = G2.next + (1 + (2 * hp.lamS + (2 + (2 + (1 + P.y.LamM) + nclp hp g)))) := c4
  have hA0 := c5.sA0
  have hH1 := c5.sH1
  have hB0 := c5.sB0
  have hsV := c5.sV
  -- 6
  obtain ⟨hd, hd2, G4, d1, d2, d3, d4, d5⟩ := hearGated_returns P H2 K (F := G3)
    (k := (if (g == 0) = true then 1 else 0) + slotsMerge P.wsLay.lk + k)
    (by refine c2.mono ?_; omega) h4 (t6 ++ t7) b5.some hN.muH9 hN.muH29
    (by rw [c5.wD, c5.rs, eZt, hK.ztSize]; exact hN.muH)
    (by rw [c5.rs, b5.r]; exact hN.muH2)
    (fun i hi => ⟨by omega, by
      have := c5.ends (1 + i) (by omega)
      rw [← Nat.add_assoc, ← hH1] at this
      exact this⟩)
  -- 7
  obtain ⟨TS, hTS, hcl'⟩ := hP.claims
  obtain ⟨claimsP, claimsE, e1, e2, e3, e4, e5, e6⟩ := hcl' K.rs ((H2.tT.map (·.r)).getD #[]) H2.ZE
    H2.tkh c5.rs (by rw [b5.some]; exact b5.r) eZE eTk
  obtain ⟨sVE, G5, x, f1, f2, f3, f4, f5⟩ := optClaim_tape (g == 0) (F := G4) (rows := hp.NCL)
    (k := slotsMerge P.wsLay.lk + k) (by refine d2.mono ?_; omega) h6 t7
  have hsize : ((Array.range (nclp hp g)).map (K.sV + ·) ++
      (if (g == 0) = true then #[sVE] else #[])).size = hp.NCL := by
    rw [Array.size_append, Array.size_map, Array.size_range]
    unfold nclp
    by_cases hg : (g == 0) = true
    · have := hN.ncl hg
      rw [if_pos hg, if_pos hg]
      show hp.NCL - 1 + 1 = _
      omega
    · rw [if_neg hg, if_neg hg]
      rfl
  have B35 : Below G3 G5 := d3.trans f3
  have hsv : ∀ j ∈ ((Array.range (nclp hp g)).map (K.sV + ·) ++
      (if (g == 0) = true then #[sVE] else #[])).toList, j < G5.next ∧ Filled G5 j := by
    intro j hj
    rw [Array.toList_append] at hj
    rcases List.mem_append.1 hj with h | h
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < nclp hp g ∧ K.sV + i = j := by simpa using h
      have hf := c5.ends (2 + (1 + P.y.LamM) + i) (by omega)
      have e : K.sA0 + (2 + (1 + P.y.LamM) + i) = K.sV + i := by omega
      rw [e] at hf
      have hl : K.sV + i < G3.next := by omega
      exact ⟨Nat.lt_of_lt_of_le hl B35.next, (B35.same _ hl).2 hf⟩
    · by_cases hg : (g == 0) = true
      · rw [if_pos hg] at h
        obtain rfl : j = sVE := by simpa using h
        obtain ⟨q1, q2⟩ := f5 hg
        rw [if_pos hg] at f4
        exact ⟨by omega, q2⟩
      · rw [if_neg hg] at h
        simp at h
  obtain ⟨wo, G6, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10⟩ := forkEnd_returns P.wsLay
    (claimsP ++ claimsE).toArray
    ((Array.range (nclp hp g)).map (K.sV + ·) ++ (if (g == 0) = true then #[sVE] else #[]))
    (F := G5) (k := k) f2 x h7 []
    (by rw [Bool.and_eq_true]; exact ⟨e4, by rw [hsize, beq_iff_eq]; exact (beq_iff_eq.1 e3).symm⟩)
    e5 e6 hsv
  rw [hsize, List.append_nil] at w1
  obtain ⟨pts, funs, p1, p2⟩ := hP.points H2 hd hd2 tT eFo eZt b5.some b5.r ePV eZE eWp eTV d5.r
    d5.r2
  obtain ⟨nU3, hlay, hnU⟩ := hP.tables
  refine ⟨{ v := envOf P hp g fo iU3 tab, H := H2, K := K, hd := hd, hd2 := some hd2, sVE := sVE,
            wo := wo, funs := funs }, G6, ?_, w2,
    ((((a3.trans b3).trans c3).trans d3).trans f3).trans w3, by unfold k4Takes; omega, ?_⟩
  rotate_left
  · have eTVp : H2.tV = H1.tV := by rw [b5.rest]
    have B16 : Below G1 G6 := ((((b3.trans c3).trans d3).trans f3).trans w3)
    have B26 : Below G2 G6 := (((c3.trans d3).trans f3).trans w3)
    have B36 : Below G3 G6 := ((d3.trans f3).trans w3)
    have B46 : Below G4 G6 := f3.trans w3
    have q1 := a5.tvFirst
    have q2 := a5.tvCl
    have q3 := a5.sPv
    have q4 := a5.tvEnd
    have q5 := a5.tvIn
    have a4' : G1.next = F.next + (ledNS P.y.h.xl * P.y.NI + ((1 + (2 * P.rd.muV + (2 + 2))) +
      (ledNP P.y.h.xl * P.y.NI + (1 + (1 + (2 * P.y.h.lt + (2 + ledNO P.y.h.xl * P.y.NI))))))) :=
      a4
    have w4' : G6.next = G5.next + (1 + (2 * P.wsLay.lk + (1 + 1))) := w4
    exact
      { v := rfl, fo := eFo, tT := by show H2.tT.isSome = true; rw [b5.some]; rfl, wpl := eWp
        hd := d5.r, hd2 := by show some hd2.r.size = _; rw [d5.r2]
        tvOpen := by
          show Open H2.tV.p G6
          rw [eTVp]
          exact a5.tvOpen.below B16 q5
        tvFirst := by show H2.tV.p.first = _; rw [eTVp]; omega
        tvEnd := by show H2.tV.sEnd = H2.tV.p.first + _; rw [eTVp]; omega
        woOpen := w7
        woFirst := by show wo.p.first + slotsMerge _ = _; unfold slotsMerge; omega
        sFv := by show wo.sFv = wo.p.first + _; omega
        nums :=
          { pv := ePV, ze := eZE, tkh := eTk
            ztF := by show H2.ztF.size = _; rw [eZt]; exact hK.ztSize
            gp := by show H2.gp.size = _; rw [b5.rest]; exact a5.gp
            omV := by show H2.omV.size = _; rw [b5.rest]; exact a5.omV
            sW := by show H2.sW = _; rw [b5.rest]; exact a5.sW
            wplL := by show H2.wpl.sL = _; rw [b5.rest]; exact a5.wplL
            wplR := by show H2.wpl.sR = H2.wpl.sL + 1; rw [b5.rest]; exact a5.wplS
            sPv := by show H2.sPv = _; rw [b5.rest]; exact a5.sPv
            tvCl := by show H2.tV.sCl = H2.sPv + _; rw [b5.rest]; exact a5.tvCl
            tvR := eTV
            tT := by
              show (H2.tT.map fun t => (t.sCl, t.sEnd, t.r.size)) = _
              rw [b5.some]
              show some (tT.sCl, tT.sEnd, tT.r.size) = _
              rw [hcl, hse, b5.r, a4]
            rs := c5.rs
            sA0 := by show K.sA0 = _; rw [hA0, b4, a4]
            sH1 := hH1, sB0 := hB0, sV := hsV, wD := c5.wD
            hdL := by show hd.sL = _; rw [d5.sL.1, c4, b4, a4]
            hdR := d5.sR.1
            hd2 := by
              show some (hd2.sL, hd2.sR) = _
              rw [d5.sR.2, d5.sL.2, c4, b4, a4]
            sVE := fun hg => by
              show sVE = _
              rw [(f5 hg).1, d4, c4, b4, a4]
            rm := w8 }
        marks := fun j h1 h2 => by
          show Filled G6 j ↔ ¬ (H2.tV.p.first ≤ j ∧ j < H2.tV.sEnd) ∧
            ¬ (wo.p.first ≤ j ∧ j < wo.sFv)
          rw [eTVp]
          by_cases r1 : j < G1.next
          · rw [B16.same j r1, a5.marks j h1 r1]
            exact ⟨fun h => ⟨h, fun hc => by omega⟩, fun h => h.1⟩
          · have nV : ¬ (H1.tV.p.first ≤ j ∧ j < H1.tV.sEnd) := fun hc => by omega
            by_cases r2 : j < G2.next
            · exact ⟨fun _ => ⟨nV, fun hc => by omega⟩, fun _ =>
                (B26.same j r2).2 (b5.marks j (by omega) r2)⟩
            · by_cases r3 : j < G3.next
              · exact ⟨fun _ => ⟨nV, fun hc => by omega⟩, fun _ =>
                  (B36.same j r3).2 (c5.marks j (by omega) r3)⟩
              · by_cases r4 : j < G4.next
                · exact ⟨fun _ => ⟨nV, fun hc => by omega⟩, fun _ =>
                    (B46.same j r4).2 (d5.marks j (by omega) r4)⟩
                · by_cases r5 : j < G5.next
                  · by_cases hg : (g == 0) = true
                    · obtain ⟨z1, z2⟩ := f5 hg
                      rw [if_pos hg] at f4
                      obtain rfl : j = sVE := by omega
                      exact ⟨fun _ => ⟨nV, fun hc => by omega⟩, fun _ => (w3.same _ r5).2 z2⟩
                    · rw [if_neg hg] at f4
                      omega
                  · rw [w10 j (by omega) h2]
                    exact ⟨fun h => ⟨nV, fun hc => by omega⟩, fun h => by
                      have := h.2
                      omega⟩ }
  unfold hearFl hear
  refine bindR (mustR hc _ _) ?_
  refine bindR (mustR hs _ _) ?_
  refine bindR (needR hP.unit _ _) ?_
  refine bindR a1 ?_
  refine bindR b1 ?_
  refine bindR (mustR hP.funOpen _ _) ?_
  refine bindR (needR hlay _ _) ?_
  refine bindR (mustR hnU _ _) ?_
  refine bindR c1 ?_
  refine bindR d1 ?_
  refine bindR (needR hTS _ _) ?_
  refine bindR (needR e1 _ _) ?_
  refine bindIte (a := claimsE) (G := G4) (u := t6 ++ t7) ?_ ?_
  · by_cases hg : (g == 0) = true
    · rw [if_pos hg] at e2 ⊢
      exact needR e2 _ _
    · rw [if_neg hg] at e2 ⊢
      obtain rfl := Option.some.inj e2
      rfl
  refine bindR (mustR e3 _ _) ?_
  refine bindIte f1 ?_
  refine bindR w1 ?_
  refine bindR (needR p1 _ _) ?_
  refine bindR (needR p2 _ _) ?_
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.rounds_eq
#print axioms OnBytes.Desc.First.K4.Rt.optClaim_tape
#print axioms OnBytes.Desc.First.K4.Rt.hear_returns
