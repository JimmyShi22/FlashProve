-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SlotsUnder.lean: CONDITIONAL on a return of the verifier's
function `hearFl` (OnBytes/Desc/First/K4/, "the hearing"). A LAW ON THE VERIFIER's TEXT: the honest
prover is not in it.

What is here. What the ledger holds, behind a return of the hearing of the layers' own rounds
(sub-protocol K4), under every slot of a value that is sent with a mask entry of the segment's mask
row: the scalars sent outside a sumcheck, the two claimed sums, and the end values of six sumchecks;
and these slots by number. Numbers, definitions of propositions, and five statements with their
proofs: calls, among others, of the library's `own_ledG` (Johnson/Road/K4/OwnLedgersG.lean),
`hear_fills` (Johnson/Road/K4/Slots/HearFills.lean), `level_shown`, `tsc_shown`
(OnBytes/Desc/First/P1/Heard.lean), `stackVals_shown`, `stack_factor`, `hideRun_shown`,
`hideRun_factor` (OnBytes/Desc/First/K4/), `hear_slots`, `hear_slots_right`, `hear_end_first`
(Johnson/Road/K4/HearSlots.lean, HearSlotsEnd.lean), and of `hear_rows_under`, `tsc_cl_filled`,
`tcP_drop` (Law/RowsLedger.lean).

  `rJ1` … `rJ6`, `rE`   the numbers, in K4's stretch of rounds, from 0, of the first rounds of the
      six sumchecks and of the round that sends the embedding's value (`rowsRound`,
      Law/RowsLedger.lean, is the round of the row products)
  `nStack`   how many end values the batched sumcheck has
  `ownOf`   how many slots a sumcheck takes in front of its end values
  `EndsUnder`, `level_under`, `tsc_under`, `cuts`   a sumcheck's end values under their slots
      ("later" is the library's `Fo.Later` there); the library's seven names for the tape from a
      given round on: five are a sumcheck's first round, two the batching rounds in front of the
      batched sumcheck and of the merge
  `K4Under P hp g o G t`   one field for each run of slots: slot, shown word, factor: an end value's
      factor is the element that the round in the further variable sampled
  `hear_under`   a return of the hearing gives it
  `K4Nums P hp g o n`, `hear_nums`   the first slot of each run as n, the ledger's next slot in
      front, plus a number; that the second token sumcheck and the second gated level have been
      heard; the ties among the hearing's names for slots of one run

Not shown here. From a return of the hearing alone, from a ledger whose arrays have their sizes:
that it returns is not shown. WORDS ALONE: what the ledger shows under a slot is the word as it was
sent; nothing on the value behind it. NOT HERE: the merge's end value (its mask entry lies in
another message); the slots of the sumchecks' hiding polynomials; what the runs "front" and "back"
lay. Free of the honest side's frame: no part, no coin, no thread. WHAT IT IMPORTS, by a walk
over import lines: no module under Johnson/Goal/, Johnson/D/ or Johnson/RecCompile/. Nothing on
soundness, on completeness or on any other property.

Kin. `cuts`' SEVEN EQUATIONS ARE INSTANCES, UP TO HOW THE SUMS ARE SPELT (two of them with one step
more), OF SIX STATEMENTS OF Law/PtsHear.lean (no part of the library yet) (`ks_tc1`, `ks_tcP`,
`ks_tc4`, `ks_tc5`, `ks_tc6`, `ks_tcW`: the library's six cuts of a tape at every value of its
structure `Ks` and every number): that file stands higher than this one; here the library's cuts are
unfolded again, in this file's own names for the rounds. The library's `level_fills` | `tsc_fills`
(Johnson/Road/K4/Slots/Fills.lean, beneath this file already) have a level's and a token sumcheck's
end values' slots filled in the ledger that the sumcheck left; `level_under` and `tsc_under` go that
walk again. Sought: by statement, to the letter and up to the bound letters, and by short name,
among the theorems of the library and of files that are no part of it yet, as they lay with the
writer; by the names of the library's cuts and of its laws on a level and on a token sumcheck, in
OnBytes/Desc/First/K4, OnBytes/Desc/First/P1, Johnson/Road/K4 and Johnson/Desc/K4. Not sought: twins
of the twelve definitions in other letters.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RowsLedger
import Johnson.Road.K4.HearSlotsEnd
import Johnson.Road.K4.Slots.HearFills

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.K.Kc (Tape)
open OnBytes.Model (Fork Reading ledNS ledNP ledNO)
open OnBytes.Model.Layer (Pub HPlan2 Own nEndT)
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.K4 (hearFl hear engFl k0 drop_drop' hideRun_shown hideRun_factor
  tsc_cl_factor later_fo stack_factor stackVals_shown hear_slots hear_slots_right hear_end_first
  mergeFront k4Slots)
open OnBytes.Desc.First.K4.Slots (hear_fills)
open OnBytes.Desc.First.P1 (sentOf tapeEps tapeCl Ks tscIn_heard levelIn_heard level_shown
  tsc_shown claimsIn_spec)
open OnBytes.Desc.First.Grow (Grows)
open OnBytes.Road.K4 (own_ledG ksOf tsc_cl_shown)

/-! ## 1 The rounds' numbers -/

/-- The first round of the squares' sumcheck. -/
def rJ1 (g : Nat) : Nat := k0 g + 2

/-- The first round of the token sumcheck on the row products. -/
def rJ2 (P : Pub) (g : Nat) : Nat := rowsRound P g + 1

/-- The first round of the second token sumcheck. -/
def rJ3 (P : Pub) (g : Nat) : Nat := rJ2 P g + (P.y.h.lt + 3)

/-- The first round of the batched sumcheck; the batching round stands in front of it. -/
def rJ4 (P : Pub) (g : Nat) : Nat := rJ3 P g + (P.y.h.lt + 3) + 1

/-- The first round of the first gated product level. -/
def rJ5 (P : Pub) (hp : HPlan2) (g : Nat) : Nat := rJ4 P g + (hp.lamS + 3)

/-- The first round of the second gated product level. -/
def rJ6 (P : Pub) (hp : HPlan2) (g : Nat) : Nat := rJ5 P hp g + (P.rd.muH + 5)

/-- The batching round in front of the merge: in the first group it sends the embedding's value. -/
def rE (P : Pub) (hp : HPlan2) (g : Nat) : Nat := rJ6 P hp g + (P.rd.muH2 + 4)

/-- How many end values the batched sumcheck has. -/
def nStack (P : Pub) (hp : HPlan2) (g : Nat) : Nat :=
  2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))

/-! ## 2 What lies under the slots -/

/-- The n end values of a sumcheck of nv variables that begins at round r of the tape t, from the
slot j on: each shows what the values' round sent; its factor is the element that the round in the
further variable sampled. -/
def EndsUnder (G : Fork) (t : Tape) (r nv j n : Nat) : Prop :=
  ∀ e, e < n → Under G (j + e) ((sentOf (t.drop (r + (nv + 2)))).getD e zeroE)
    (tapeEps (t.drop (r + (nv + 1))))

/-- **A product level's two end values**, where its rounds begin at round r of the tape T. -/
theorem level_under {mu : Nat} {rho : Array E} {C : OnBytes.Model.Aff} {order : List Nat}
    {F G : Fork} {T u : Tape} {r : Nat} {L : OnBytes.Model.Level} (hF : Sized F)
    (h : OnBytes.K.Kc.Fl.levelIn mu rho C order F (T.drop r) = some (L, G, u)) (Hl : Fork)
    (hL : Fo.Later G Hl) : EndsUnder Hl T r mu L.sL 2 := by
  intro e he
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, G1, hv, hG1, _, hG⟩ :=
    levelIn_heard h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) := hF
  obtain ⟨_, hS1, hin, _⟩ := hideRun_ok _ G1 L.sL v _ hF' hG1
  have l2 := Fo.hideRun_later hS1 hG
  have he' : e < v.size := by
    rw [hv]
    exact he
  refine ⟨((l2.trans hL).keep _ (hin e he').2.2.1).1, ?_, ?_⟩
  · rw [← drop_drop']
    exact level_shown hF h Hl hL e he
  · rw [← drop_drop']
    exact hideRun_factor hF' hG1 (l2.trans hL) e he'

/-- **A token sumcheck's end values**, where its rounds begin at round r of the tape T. -/
theorem tsc_under {P : Array E} {lt n dY : Nat} {F G : Fork} {T u : Tape} {r : Nat}
    {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : OnBytes.K.Kc.Fl.tscIn P lt n dY F (T.drop r) = some (o, G, u)) (Hl : Fork)
    (hL : Fo.Later G Hl) : EndsUnder Hl T r lt o.sEnd n := by
  intro e he
  obtain ⟨hlt, _, _, _, _, _, _, _, _, _, _, _, _, v, G0, hG0, _, _, _, hvn, hG⟩ := tscIn_heard h
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  obtain ⟨_, hS0, _, _⟩ := hideRun_ok _ G0 F.next _ oneE hF' hG0
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } :
      Fork) := hS0
  obtain ⟨_, _, hin, _⟩ := hideRun_ok _ G o.sEnd v _ hS0' hG
  have he' : e < v.size := by
    rw [hvn]
    exact he
  have l : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  refine ⟨(hL.keep _ (hin e he').2.2.1).1, ?_, ?_⟩
  · have q := tsc_shown hF h Hl hL e he
    unfold OnBytes.Desc.First.P1.tscVals at q
    rw [l, drop_drop'] at q
    exact q
  · have q : Hl.mf.getD (o.sEnd + e) zeroE =
        tapeEps ((T.drop r).drop ((P.toList.take lt).length + 1)) :=
      hideRun_factor hS0' hG hL e he'
    rw [l, drop_drop'] at q
    exact q

/-- The library's seven names for the tape from a given round on: the fourth is the batching round
in front of the batched sumcheck, the last the batching round in front of the merge; the others are
a sumcheck's first round. -/
theorem cuts (P : Pub) (hp : HPlan2) (g : Nat) (t : Tape) :
    (ksOf P hp).tc1 (t.drop (k0 g)) = t.drop (rJ1 g) ∧
    ((ksOf P hp).tcP (t.drop (k0 g))).drop 1 = t.drop (rJ2 P g) ∧
    (((ksOf P hp).tcP (t.drop (k0 g))).drop 1).drop (P.y.h.lt + 3) = t.drop (rJ3 P g) ∧
    (ksOf P hp).tc4 (t.drop (k0 g)) = t.drop (rJ3 P g + (P.y.h.lt + 3)) ∧
    (ksOf P hp).tc5 (t.drop (k0 g)) = t.drop (rJ5 P hp g) ∧
    (ksOf P hp).tc6 (t.drop (k0 g)) = t.drop (rJ6 P hp g) ∧
    (ksOf P hp).tcW (t.drop (k0 g)) = t.drop (rE P hp g) := by
  have c1 : (ksOf P hp).tc1 (t.drop (k0 g)) = t.drop (rJ1 g) := by
    unfold Ks.tc1 rJ1
    rw [drop_drop', drop_drop']
  have cP := tcP_drop P hp g t
  have c2 : ((ksOf P hp).tcP (t.drop (k0 g))).drop 1 = t.drop (rJ2 P g) := by
    rw [cP, drop_drop']
    rfl
  have c3 : (((ksOf P hp).tcP (t.drop (k0 g))).drop 1).drop (P.y.h.lt + 3) =
      t.drop (rJ3 P g) := by
    rw [c2, drop_drop']
    rfl
  have c4 : (ksOf P hp).tc4 (t.drop (k0 g)) = t.drop (rJ3 P g + (P.y.h.lt + 3)) := by
    unfold Ks.tc4
    show ((((ksOf P hp).tcP (t.drop (k0 g))).drop 1).drop (P.y.h.lt + 3)).drop (P.y.h.lt + 3) = _
    rw [c3, drop_drop']
  have c5 : (ksOf P hp).tc5 (t.drop (k0 g)) = t.drop (rJ5 P hp g) := by
    unfold Ks.tc5
    show (((ksOf P hp).tc4 (t.drop (k0 g))).drop 1).drop (hp.lamS + 3) = _
    rw [c4, drop_drop', drop_drop']
    congr 1
    unfold rJ5 rJ4
    omega
  have c6 : (ksOf P hp).tc6 (t.drop (k0 g)) = t.drop (rJ6 P hp g) := by
    unfold Ks.tc6
    show ((((ksOf P hp).tc5 (t.drop (k0 g))).drop (P.rd.muH + 3)).drop 1).drop 1 = _
    rw [c5, drop_drop', drop_drop', drop_drop']
    rfl
  have cW : (ksOf P hp).tcW (t.drop (k0 g)) = t.drop (rE P hp g) := by
    unfold Ks.tcW
    show (((ksOf P hp).tc6 (t.drop (k0 g))).drop (P.rd.muH2 + 3)).drop 1 = _
    rw [c6, drop_drop', drop_drop']
    rfl
  exact ⟨c1, c2, c3, c4, c5, c6, cW⟩

/-- **What lies under the slots**, one field for each run of slots. -/
structure K4Under (P : Pub) (hp : HPlan2) (g : Nat) (o : Own) (G : Fork) (t : Tape) : Prop where
  /-- the norms' sums -/
  sums : ∀ i, i < ledNS P.y.h.xl * P.y.NI →
    Under G (o.H.sW + i) ((sentOf (t.drop (k0 g))).getD i zeroE) oneE
  /-- the squares' level's two end values -/
  sq : EndsUnder G t (rJ1 g) P.rd.muV o.H.wpl.sL 2
  /-- the row products -/
  prods : ∀ i, i < ledNP P.y.h.xl * P.y.NI →
    Under G (o.H.sPv + i) ((sentOf (t.drop (rowsRound P g))).getD i zeroE) oneE
  /-- their claimed batch -/
  cl8 : Under G o.H.tV.sCl (tapeCl (t.drop (rJ2 P g))) oneE
  /-- the end values of their sumcheck -/
  ends8 : EndsUnder G t (rJ2 P g) P.y.h.lt o.H.tV.sEnd (ledNO P.y.h.xl * P.y.NI)
  /-- the second token sumcheck's claimed sum and end values -/
  terms : ∀ tT, o.H.tT = some tT → Under G tT.sCl (tapeCl (t.drop (rJ3 P g))) oneE ∧
    EndsUnder G t (rJ3 P g) P.y.h.lt tT.sEnd (nEndT P.y)
  /-- the batched sumcheck's end values -/
  stack : EndsUnder G t (rJ4 P g) hp.lamS o.K.sA0 (nStack P hp g)
  /-- the first gated level's end values -/
  lv1 : EndsUnder G t (rJ5 P hp g) P.rd.muH o.hd.sL 2
  /-- the second gated level's end values -/
  lv2 : ∀ o2, o.hd2 = some o2 → EndsUnder G t (rJ6 P hp g) P.rd.muH2 o2.sL 2
  /-- in the first group: the embedding's value -/
  emb : (g == 0) = true → Under G o.sVE ((sentOf (t.drop (rE P hp g))).getD 0 zeroE) oneE

/-- **A return of the hearing gives it.** -/
theorem hear_under {P : Pub} {hp : HPlan2} {g : Nat} {fo : OnBytes.Model.Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own} (hF : Sized F)
    (h : hearFl P hp g fo F t = some (o, G, u)) : K4Under P hp g o G t := by
  have h' : hear engFl P hp g fo F t = some (o, G, u) := h
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hF h'
  have Fi := hear_fills hF h'
  obtain ⟨r1, r2, _⟩ := hear_rows_under hF h
  obtain ⟨C1, C2, C3, C4, C5, C6, CW⟩ := cuts P hp g t
  obtain ⟨vW, hwl, hws, hrunW⟩ := L.runW
  obtain ⟨v1, c1⟩ := L.c1
  obtain ⟨v2, c2⟩ := L.c2
  obtain ⟨v5, c5⟩ := L.c5
  have c3 := L.c3
  have c4 := L.c4
  have c6 := L.c6
  rw [C1] at c1
  rw [C2] at c2
  rw [C3] at c3
  rw [C4] at c4
  rw [C5] at c5
  rw [C6] at c6
  have hF0 : Sized ({ F with next := F.next + ledNS P.y.h.xl * P.y.NI } : Fork) := hF
  have l4 : Fo.Later F4 G := (later_fo (Grows.later c1)).trans L.g7
  refine
    { sums := fun i hi => ?_
      sq := ?_
      prods := r1
      cl8 := r2
      ends8 := ?_
      terms := fun tT' hT' => ?_
      stack := fun e he => ?_
      lv1 := level_under L.s3 c5 G L.g3'
      lv2 := fun o2 h2 => ?_
      emb := fun hg => ?_ }
  · have hi' : i < vW.size := by
      rw [hws]
      exact hi
    refine ⟨Fi.sW i hi, ?_, ?_⟩
    · rw [L.kSW, L.sW]
      exact hideRun_shown hF0 hrunW hwl l4 i hi'
    · rw [L.kSW, L.sW]
      exact hideRun_factor hF0 hrunW l4 i hi'
  · rw [L.kWpl]
    exact level_under L.s4 c1 G L.g7
  · rw [L.kTV]
    exact tsc_under L.s8 c2 G L.g1
  · obtain rfl : ({ tT with p := { tT.p with rowMade := true } } : OnBytes.Model.Tsc) = tT' :=
      Option.some.inj (L.kTT.symm.trans hT')
    exact ⟨⟨tsc_cl_filled L.s1 c3 G L.g1', tsc_cl_shown L.s1 c3 G L.g1',
      tsc_cl_factor L.s1 c3 G L.g1'⟩, tsc_under L.s1 c3 G L.g1'⟩
  · have e1 : rJ3 P g + (P.y.h.lt + 3) + (hp.lamS + 3) = rJ4 P g + (hp.lamS + 2) := by
      unfold rJ4
      omega
    have e2 : rJ3 P g + (P.y.h.lt + 3) + (hp.lamS + 2) = rJ4 P g + (hp.lamS + 1) := by
      unfold rJ4
      omega
    refine ⟨Fi.stack e he, ?_, ?_⟩
    · have q := stackVals_shown L.s2 c4 G L.g3 e he
      unfold OnBytes.Desc.First.K4.stackVals at q
      rw [drop_drop', e1] at q
      exact q
    · have q : G.mf.getD (o.K.sA0 + e) zeroE =
          tapeEps ((t.drop (rJ3 P g + (P.y.h.lt + 3))).drop (hp.lamS + 2)) :=
        stack_factor L.s2 c4 G L.g3 e he
      rw [drop_drop', e2] at q
      exact q
  · obtain rfl : hd2 = o2 := Option.some.inj (L.eHd2.symm.trans h2)
    exact level_under L.s3' c6 G L.g4
  · have fr : OnBytes.K.Kc.Fl.claimsIn 1 G4 ((ksOf P hp).tcW (t.drop (k0 g))) =
        some (o.sVE, G5, u5) := by
      have q := L.front
      unfold mergeFront at q
      rw [if_pos hg] at q
      exact q
    obtain ⟨eE, vE, hvE, _, _, hrE⟩ := claimsIn_spec fr
    have hS4 : Sized ({ G4 with next := G4.next + 1 } : Fork) := L.sG4
    refine ⟨Fi.sVE hg, ?_, ?_⟩
    · rw [← CW]
      exact (L.emb hg).2 G L.g5
    · have q := hideRun_factor hS4 hrE L.g5 0 (by rw [hvE]; exact Nat.one_pos)
      rw [Nat.add_zero, ← eE] at q
      exact q

/-! ## 3 The slots by number -/

/-- How many slots a sumcheck takes in front of its end values: lead claimed sums, the sum of the
hiding polynomial, two for each of nv variables, dY for the further variable. -/
def ownOf (lead nv dY : Nat) : Nat := lead + (1 + 2 * nv + dY)

/-- **The first slot of each run**, counted from n. -/
structure K4Nums (P : Pub) (hp : HPlan2) (g : Nat) (o : Own) (n : Nat) : Prop where
  /-- the norms' sums -/
  sW : o.H.sW = n
  /-- the squares' level's left end value, and the right one -/
  sL : o.H.wpl.sL = n + (ledNS P.y.h.xl * P.y.NI + ownOf 0 P.rd.muV 2)
  sR : o.H.wpl.sR = o.H.wpl.sL + 1
  /-- the row products; their claimed batch; the end values of their sumcheck -/
  sPv : o.H.sPv = o.H.wpl.sL + 2
  sCl : o.H.tV.sCl = o.H.sPv + ledNP P.y.h.xl * P.y.NI
  sEnd : o.H.tV.sEnd = o.H.tV.sCl + ownOf 1 P.y.h.lt 2
  /-- the second token sumcheck has been heard -/
  hasT : ∃ tT, o.H.tT = some tT
  /-- its claimed sum; its end values; the batched sumcheck's first end value -/
  terms : ∀ tT, o.H.tT = some tT → tT.sCl = o.H.tV.sEnd + ledNO P.y.h.xl * P.y.NI ∧
    tT.sEnd = tT.sCl + ownOf 1 P.y.h.lt 1 ∧ o.K.sA0 = tT.sEnd + nEndT P.y + ownOf 0 hp.lamS 2
  /-- the batched sumcheck's end values by the hearing's four names -/
  sH1 : o.K.sH1 = o.K.sA0 + 1
  sB0 : o.K.sB0 = o.K.sA0 + (1 + (1 + P.y.LamM))
  sV : o.K.sV = o.K.sB0 + 1
  /-- the first gated level's left end value, and the right one -/
  hL : o.hd.sL = o.K.sA0 + nStack P hp g + ownOf 0 P.rd.muH 2
  hR : o.hd.sR = o.hd.sL + 1
  /-- the second gated level has been heard -/
  has2 : ∃ o2, o.hd2 = some o2
  /-- its two end values; in the first group the embedding's value -/
  lv2 : ∀ o2, o.hd2 = some o2 → o2.sL = o.hd.sL + 2 + ownOf 0 P.rd.muH2 2 ∧ o2.sR = o2.sL + 1 ∧
    ((g == 0) = true → o.sVE = o2.sL + 2)

/-- **A return of the hearing gives them**, at the ledger's next slot in front. -/
theorem hear_nums {P : Pub} {hp : HPlan2} {g : Nat} {fo : OnBytes.Model.Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own} (hF : Sized F)
    (h : hearFl P hp g fo F t = some (o, G, u)) : K4Nums P hp g o F.next := by
  have h' : hear engFl P hp g fo F t = some (o, G, u) := h
  obtain ⟨a1, a2, a3, a4, _, a6, ⟨tT, hT, b1, _, b3⟩, a8, a9, a10, a11, a12, hd2, h2, a13⟩ :=
    hear_slots Reading.gl hF h'
  obtain ⟨q1, q2, hd2', h2', q3⟩ := hear_slots_right Reading.gl hF h'
  obtain rfl : hd2 = hd2' := Option.some.inj (h2.symm.trans h2')
  simp only [k4Slots, OnBytes.Desc.First.K4.sPvAt, OnBytes.Desc.First.K4.sClAt,
    OnBytes.Desc.First.K4.tClAt, OnBytes.Desc.First.K4.kPAt, OnBytes.Desc.First.K4.hPAt]
    at a1 a2 a3 a4 a6 b1 b3 a8 a9 a10 a11 a12 a13 q1 q2 q3
  refine
    { sW := a1
      sL := by rw [a2]; unfold ownOf; omega
      sR := by rw [q1, a2]
      sPv := by rw [a3, a2]
      sCl := by rw [a4, a3]
      sEnd := by rw [a6, a4]; unfold ownOf; omega
      hasT := ⟨tT, hT⟩
      terms := fun tT' hT' => ?_
      sH1 := by rw [a9, a8]
      sB0 := by rw [a10, a8]; omega
      sV := by rw [a11, a10]
      hL := by rw [a12, a8]; unfold ownOf nStack; omega
      hR := by rw [q2, a12]
      has2 := ⟨hd2, h2⟩
      lv2 := fun o2 ho2 => ?_ }
  · obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans hT')
    refine ⟨by rw [b1, a6], ?_, ?_⟩
    · rw [b3, b1]
      unfold ownOf
      omega
    · rw [a8, b3]
      unfold ownOf
      omega
  · obtain rfl : hd2 = o2 := Option.some.inj (h2.symm.trans ho2)
    refine ⟨by rw [a13, a12]; unfold ownOf; omega, by rw [q3, a13], fun hg => ?_⟩
    have e := (hear_end_first Reading.gl hF h' hg).1
    simp only [k4Slots, OnBytes.Desc.First.K4.sPvAt, OnBytes.Desc.First.K4.sClAt,
      OnBytes.Desc.First.K4.tClAt, OnBytes.Desc.First.K4.kPAt, OnBytes.Desc.First.K4.hPAt] at e
    rw [e, a13]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.rJ1
#print axioms ProofFile.Honest.K4.rJ2
#print axioms ProofFile.Honest.K4.rJ3
#print axioms ProofFile.Honest.K4.rJ4
#print axioms ProofFile.Honest.K4.rJ5
#print axioms ProofFile.Honest.K4.rJ6
#print axioms ProofFile.Honest.K4.rE
#print axioms ProofFile.Honest.K4.nStack
#print axioms ProofFile.Honest.K4.EndsUnder
#print axioms ProofFile.Honest.K4.level_under
#print axioms ProofFile.Honest.K4.tsc_under
#print axioms ProofFile.Honest.K4.cuts
#print axioms ProofFile.Honest.K4.K4Under
#print axioms ProofFile.Honest.K4.hear_under
#print axioms ProofFile.Honest.K4.ownOf
#print axioms ProofFile.Honest.K4.K4Nums
#print axioms ProofFile.Honest.K4.hear_nums
