-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/SumTruth.lean: ONE MASKED SUMCHECK OF THE OUTPUT HEAD'S OWN ROUNDS,
PLAYED BY THE JOB pairJob (Honest/K6/Part.lean) AND HEARD BY THE VERIFIER'S TEXT: WHAT THE SLOTS OF
ITS LEAD SCALARS AND END VALUES ARE THEN WORTH, IN THE WORLD OF A LATER LEDGER AND OF A MASK ROW
THAT READS AS THE PROVER'S COINS (the job's lead values; the sum's end values at the challenges),
AND WHAT THE SUMCHECK'S OWN FORM IS WORTH THERE. One law for the four calls: general in the sum of
weighted products of pairs of maps (Johnson/Desc/K6/Honest/Pairs.lean: PairSum) and in the number of
lead scalars.
WHAT IT IS NOT. CONDITIONAL THROUGHOUT: THAT THE VERIFIER'S HEARING RETURNS IS A PREMISE (from
heardBy_truth on: and leaves no round); so are: the ties between the mask row and the prover's coins
(mLead, mOwn, mEnd); that the verifier's point is the sum's, word for word (hz); that this point has
n coordinates, n being the number of variables in the job's shape (hn); that the sum has as many
maps as the call has end values (hm); the test on the challenges' counts (hd); that the ledger in
front of the hearing is well laid (WellLaid; in the core: Sized); that the part, played alone,
returns (ha). The part is played alone (SumLaw/Terms.lean: alone), not in a run of the frame.
Nothing on whether the verifier accepts, on soundness, on completeness or on what a proof hides.
Equations in the field: nothing on canonical writing. No example.
  call_eq         the job's call in the run is the call that the verifier's text makes, as data.
  lastD_getD      the last of n + 1 elements is number n.
  heard_truth     THE CORE, at the part's own hearing (Johnson/Desc/Part/MaskedSum4.lean: hear) and
                  the laying of its own slots (rowLaid): the challenges are the run's; under end
                  value j's slot lies the sum's end value j at the challenges; what is read as shown
                  is that value plus beta times the coin; and where the start form is worth the sum,
                  and S0 reads as the summand at the challenges, rowForm is worth 0. In the world of
                  every ledger later than the one behind rowLaid.
  lead_sent       the lead as the verifier reads it: each scalar reads as the job's lead value plus
                  its coin.
  heardBy_truth   THE LIKE AT THE VERIFIER'S heardBy (Johnson/Desc/Kinds/HeadParts.lean), with the
                  lead: under lead scalar i's slot lies the job's lead value i. IT PARTS FROM THE
                  CORE IN FOUR THINGS, and so do the two below: the challenges are the run's first
                  n, without the further variable's; the clause on what is read as shown is gone;
                  S0 is to read as the summand on the end values AS SHOWN (onK), not at the
                  challenges; the form that is worth 0 is S.left S0.
  sumcheck_truth | level_truth   at the verifier's sumcheck (one lead scalar: the claimed sum) and
                  level (none; line: its last round, which another part plays).
CALLED. The law of the masked sumcheck's honest part (Honest/SumLaw/): heard_spec, sumEnds,
sumFirst, ends_reads, drawn_vars, varsOf_cons, all_some, withPoints_length, take_getD,
rounds_count, rowForm_worth. PairSumsTo.lean: headPair_sumsTo_job, head_withPoints_replicate.
LaidLaw.lean: hide_truth, shown_endK. The library: heardBy_spec, heardBy_ends, heardBy_cut,
hiddenFrom_get, hiddenFrom_hidsAt, hidsAt_spec, hide_unfold, hideRun_frame, leadScalars_len,
worldE_eq, vW_slot, getD_zero, sized_of (Johnson/Desc/Kinds/Law/), ledger_ownLaid, hear_keeps,
roundOf_spec (Johnson/Desc/Part/), hideRun_keeps, Later.trans.
-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.ProofFile.Honest.K6.PairSumsTo
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds
import Johnson.Desc.ProofFile.Honest.SumLaw.Counts
import Johnson.Desc.K6.Honest.LaidLaw
import Johnson.Desc.Kinds.Law.HeardEnds
import Johnson.Desc.Kinds.Law.WorldTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Reading)
open OnBytes.PscRun (Later Sized)
open VerifiableInference.Desc.Part.MaskedSum (Call Var Heard hear rowLaid rowForm ownSlots readAll
  leadScalars challenges)
open VerifiableInference.Desc.Kinds (Point Form Hid Sum sumcheck level heardBy)
open VerifiableInference.Desc.Kinds.Head.Law (rd worldE noEnt WellLaid callOf)
open VerifiableInference.Desc.Kinds.Head.Law.Came (val)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum)
open VerifiableInference.Desc.Kinds.Head (Law.vW)
open SumLaw (alone SumCoins firstRun endRun frontOf drawsOk varsOf hidingCoin)

variable {V W X : Type}

/-- The job's call in the run is the call that the verifier's text makes, as data. -/
theorem call_eq (lead n e : Nat) (sumAt : W → Front X → PairSum) (leadAt : W → Front X → List E)
    (w : W) (fr : Front X) (z : Point) (hz : z.toList = (sumAt w fr).z) (hn : z.size = n) :
    (pairJob (pointShape lead n e) sumAt leadAt).callAt w fr = callOf lead z e := by
  have hl : n = (sumAt w fr).z.length := by rw [← hz, Array.length_toList, hn]
  show ({ lead := lead, vs := withPoints (List.replicate n (Var.point zeroE 3)) (sumAt w fr).z,
          ends := some ⟨2, e⟩ } : Call) =
    { lead := lead, vs := z.toList.map (.point · 3), ends := some ⟨2, e⟩ }
  rw [hl, head_withPoints_replicate, hz]

/-- The last of n + 1 elements is number n. -/
theorem lastD_getD (l : List E) (n : Nat) (h : l.length = n + 1) :
    l.getLastD zeroE = l.getD n zeroE := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, h, List.getD_eq_getElem?_getD]
  rfl

/-- **THE CORE, at the part's own hearing.** Its fifth conjunct is spent in heardBy_truth alone. -/
theorem heard_truth (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (Cf : Aff)
    (Fa Gh F1 G : Fork) (h : Heard) (mask : Nat → E)
    (hn : (sumAt t.input (frontOf t seen)).z.length = n)
    (hd : drawsOk ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)) ds
      = true)
    (ha : alone (sumPart (V := V) name endName (pairJob (pointShape lead n e) sumAt leadAt)) c t
      seen ds = some rounds)
    (hh : hear Cf ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)) Fa
      rounds = some (h, Gh))
    (hS : Sized Fa) (hw : rowLaid h Gh = some F1) (hL : Later F1 G)
    (mOwn : ∀ i, i < ownSlots
        ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)).all →
      rd (mask (Fa.next + i)) = hidingCoin c i)
    (mEnd : ∀ j, j < e → rd (mask (Fa.next + ownSlots
        ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)).all + j)) =
      rd ((endRun c).getD j zeroE)) :
    h.r = varsOf ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)) ds ∧
    h.r.length = n + 1 ∧
    h.sEnd = Fa.next + ownSlots
      ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)).all ∧
    (∀ j, j < e → (worldE G mask noEnt).slot (h.sEnd + j) =
      rd (((sumAt t.input (frontOf t seen)).ends (h.r.take n)).getD j zeroE)) ∧
    (∀ R, readAll ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen))
        rounds = some R → ∀ j, j < e → rd (R.values.getD j zeroE) =
      rd (((sumAt t.input (frontOf t seen)).ends (h.r.take n)).getD j zeroE) +
        rd (h.r.getD n zeroE) * rd ((endRun c).getD j zeroE)) ∧
    (val (worldE G mask noEnt) Cf = rd (sumAt t.input (frontOf t seen)).total →
      ∀ S0 : E, rd S0 = (sumAt t.input (frontOf t seen)).endK (h.r.take n) (endRun c)
          (h.r.getD n zeroE) →
        val (worldE G mask noEnt) (rowForm h S0 {}) = 0) := by
  obtain ⟨d0, dv, dl, T, hds, hv, _, hR, hh'⟩ := SumLaw.heard_spec hd ha hh
  have hvs : (pairJob (pointShape lead n e) sumAt leadAt).shape.vs.length = n :=
    List.length_replicate
  have hall : ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input
      (frontOf t seen)).all.length = n + 1 := by
    rw [SumLaw.all_some _ _ _ ⟨2, e⟩ rfl, List.length_append, SumLaw.withPoints_length, hvs]
    rfl
  have hrr : h.r = dv.map SumLaw.elemOf := by rw [hh']
  have hsEnd : h.sEnd = Fa.next + ownSlots
      ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)).all := by
    rw [hh']
  have hvars' := SumLaw.varsOf_cons
    ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)) d0 dv dl hv
  have hlen : h.r.length = n + 1 := by rw [hrr, List.length_map, hv, hall]
  have hLG : Later Gh G := (OnBytes.PscRun.hideRun_keeps hw).trans hL
  refine ⟨by rw [hrr, hds, hvars'], hlen, hsEnd, ?_, ?_, ?_⟩
  · intro j hj
    have key := SumLaw.sumEnds V W X name endName _ c t seen ds Cf Fa Gh G rounds h ⟨2, e⟩
      (fun j => rd (mask j)) (fun a b i => rd (noEnt a b i)) rfl hS hd ha hh hLG j hj
      (by rw [hsEnd]; exact mEnd j hj)
    rw [VerifiableInference.Desc.Kinds.Head.Law.worldE_eq, key, hds, hvars', ← hrr, hvs]
    rfl
  · intro R hRR j hj
    have hRe : R = SumLaw.readOf _ c t seen d0 dv := by
      rw [hR] at hRR
      exact (Option.some.inj hRR).symm
    have hvals :
        (SumLaw.readOf (pairJob (pointShape lead n e) sumAt leadAt) c t seen d0 dv).values =
        (SumLaw.saidEnds (pairJob (pointShape lead n e) sumAt leadAt) ⟨2, e⟩
          ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)).all
          (frontOf t seen) (firstRun c) (endRun c) (drawnE (d0 :: dv)) t.input).map
            SumLaw.canon := rfl
    have hpos : 0 < dv.length := by rw [hv, hall]; omega
    obtain ⟨e1, e2⟩ := SumLaw.drawn_vars
      ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)) d0 dv dl hv
      hpos
      (pairJob (pointShape lead n e) sumAt leadAt).shape.vs.length
    rw [hRe, hvals]
    show Reading.gl.val _ = _
    rw [SumLaw.ends_reads _ ⟨2, e⟩ _ _ _ _ _ _ j hj, e1, e2, hvars', ← hrr, hvs,
      lastD_getD h.r n hlen]
    rfl
  · intro hC S0 hS0
    have hm : ∀ i, i < ownSlots
        ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)).all →
        (worldE G mask noEnt).slot (h.first + i) = hidingCoin c i := by
      intro i hi
      rw [VerifiableInference.Desc.Kinds.Head.Law.worldE_eq,
        VerifiableInference.Desc.Part.MaskedSum.ledger_ownLaid Reading.gl _ _ hh
          ((VerifiableInference.Desc.Part.MaskedSum.hear_keeps hh).sized hS) hw hL i hi]
      exact mOwn i hi
    have hST := headPair_sumsTo_job (pairJob (pointShape lead n e) sumAt leadAt) t.input
      (frontOf t seen) (sumAt t.input (frontOf t seen)) zeroE e (endRun c) h.r (by rw [hn]; rfl)
      rfl rfl rfl rfl (by rw [hlen, hn])
    rw [hn] at hST
    have hC' : Cf.value Reading.gl (worldE G mask noEnt) =
        Reading.gl.val (sumAt t.input (frontOf t seen)).total := hC
    have key := SumLaw.rowForm_worth (V := V) name endName _ c t seen ds rounds Cf Fa Gh h S0 {}
      (worldE G mask noEnt) _ hd ha hh hm (by rw [hC']; exact hST)
    show (rowForm h S0 {}).value Reading.gl (worldE G mask noEnt) = 0
    have hS0' : Reading.gl.val S0 = (sumAt t.input (frontOf t seen)).endK (h.r.take n) (endRun c)
        (h.r.getD n zeroE) := hS0
    rw [key, Aff.value_empty, hS0']
    ring

/-- **The lead as the verifier reads it.** -/
theorem lead_sent (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds) (k : Call)
    (hk : k.lead = J.shape.lead) (ld : List E) (hl : leadScalars k rounds = some ld) :
    ∀ i, i < J.shape.lead → rd (ld.getD i zeroE) =
      rd ((J.lead t.input (frontOf t seen)).getD i zeroE) + rd ((firstRun c).getD i zeroE) := by
  obtain ⟨r, rest, sc, hr0, hsc, _, hread⟩ :=
    SumLaw.sumFirst V W X name endName J c t seen ds rounds ha
  rw [hr0] at hl
  simp only [leadScalars, List.head?_cons, Option.bind_some] at hl
  cases hq : VerifiableInference.Desc.Part.MaskedSum.roundOf (k.lead + 1) 1 r with
  | none => simp [VerifiableInference.Desc.Part.MaskedSum.firstRound, hq] at hl
  | some x =>
    obtain ⟨s', dr⟩ := x
    have hs' := (VerifiableInference.Desc.Part.MaskedSum.roundOf_spec hq).1
    rw [hsc] at hs'
    obtain rfl := Option.some.inj hs'
    simp only [VerifiableInference.Desc.Part.MaskedSum.firstRound, hq, Option.map_some,
      Option.some.injEq] at hl
    intro i hi
    rw [← hl, SumLaw.take_getD sc _ i (by rw [hk]; exact hi)]
    exact hread i hi

/-- **ONE MASKED SUMCHECK, PLAYED BY THE JOB pairJob (Honest/K6/Part.lean), HEARD BY THE VERIFIER'S
heardBy.** -/
theorem heardBy_truth (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (z : Point)
    (C : Array Hid → Form) (F0 F1 G : Fork) (cA : Array Hid) (S : Sum) (mask : Nat → E)
    (hz : z.toList = (sumAt t.input (frontOf t seen)).z) (hn : z.size = n)
    (hm : (sumAt t.input (frontOf t seen)).maps.length = e)
    (hd : drawsOk ((pairJob (pointShape lead n e) sumAt leadAt).callAt t.input (frontOf t seen)) ds
      = true)
    (ha : alone (sumPart (V := V) name endName (pairJob (pointShape lead n e) sumAt leadAt)) c t
      seen ds = some rounds)
    (hW : WellLaid F0) (hv : heardBy lead C z e F0 rounds = some ((cA, S), F1, []))
    (hL : Later F1 G)
    (mLead : ∀ i, i < lead → rd (mask (F0.next + i)) = rd ((firstRun c).getD i zeroE))
    (mOwn : ∀ i, i < ownSlots (callOf lead z e).all →
      rd (mask (F0.next + lead + i)) = hidingCoin c i)
    (mEnd : ∀ j, j < e → rd (mask (F0.next + lead + ownSlots (callOf lead z e).all + j)) =
      rd ((endRun c).getD j zeroE)) :
    S.r.toList = (varsOf (callOf lead z e) ds).take n ∧
    (∀ i, i < lead → val (worldE G mask noEnt) (cA.getD i {}).var =
      rd ((leadAt t.input (frontOf t seen)).getD i zeroE)) ∧
    (∀ j, j < e → val (worldE G mask noEnt) (S.end_ j).var =
      rd (((sumAt t.input (frontOf t seen)).ends S.r.toList).getD j zeroE)) ∧
    (val (worldE G mask noEnt) (C cA) = rd (sumAt t.input (frontOf t seen)).total →
      ∀ S0 : E, rd S0 = (sumAt t.input (frontOf t seen)).onK (fun j => rd (S.end_ j).shown) →
        val (worldE G mask noEnt) (S.left S0) = 0) := by
  have hk := call_eq lead n e sumAt leadAt t.input (frontOf t seen) z hz hn
  have hzn : (sumAt t.input (frontOf t seen)).z.length = n := by
    rw [← hz, Array.length_toList, hn]
  obtain ⟨ld, Fa, Gh, h, es, _, a2, a3, a4, a5, a6, hSS⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.heardBy_spec hv
  have hll : ld.length = lead := VerifiableInference.Desc.Kinds.Head.Law.leadScalars_len a2
  obtain ⟨run1, _⟩ := VerifiableInference.Desc.Kinds.Head.Law.hide_unfold a3
  obtain ⟨wFa, _, nFa, _, _⟩ := VerifiableInference.Desc.Kinds.Head.Law.hideRun_frame
    (F := ({ F0 with next := F0.next + ld.length } : Fork)) hW run1
  have hFa : Fa.next = F0.next + lead := by rw [← hll]; exact nFa
  rw [← hk] at a4 mOwn mEnd
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := heard_truth (V := V) name endName lead n e sumAt leadAt c t
    seen ds rounds (C cA) Fa Gh F1 G h mask hzn hd ha a4
    (VerifiableInference.Desc.Kinds.Head.Law.sized_of wFa) a5 hL
    (fun i hi => by rw [hFa]; exact mOwn i hi) (fun j hj => by rw [hFa]; exact mEnd j hj)
  have hLa : Later Fa G :=
    ((VerifiableInference.Desc.Part.MaskedSum.hear_keeps a4).trans
      (OnBytes.PscRun.hideRun_keeps a5)).trans hL
  have hr : S.r.toList = h.r.take n := by
    rw [hSS]
    show ((challenges (callOf lead z e) h).toArray).toList = _
    rw [List.toList_toArray]
    show h.r.take (z.toList.map (Var.point · 3)).length = _
    rw [List.length_map, Array.length_toList, hn]
  have hend : ∀ j, j < e → S.end_ j =
      { var := Aff.slot (h.sEnd + j), shown := F1.vp.getD (h.sEnd + j) zeroE } := by
    intro j hj
    rw [hSS]
    exact VerifiableInference.Desc.Kinds.Head.Law.Came.hiddenFrom_get a6 j hj
  refine ⟨by rw [hr, c1, hk], ?_, ?_, ?_⟩
  · intro i hi
    have key := VerifiableInference.Desc.Kinds.Head.Honest.hide_truth hW a3 hLa mask
      (leadAt t.input (frontOf t seen)) (fun i hi => by
        rw [VerifiableInference.Desc.Kinds.Head.Law.getD_zero, mLead i (by rw [← hll]; exact hi)]
        exact lead_sent (V := V) name endName _ c t seen ds rounds ha (callOf lead z e) rfl ld a2 i
          (by rw [← hll]; exact hi)) i (by rw [hll]; exact hi)
    rw [key, VerifiableInference.Desc.Kinds.Head.Law.getD_zero]
  · intro j hj
    rw [hend j hj, hr]
    show Law.vW (worldE G mask noEnt) (Aff.slot (h.sEnd + j)) = _
    rw [VerifiableInference.Desc.Kinds.Head.Law.vW_slot]
    exact c4 j hj
  · intro hC S0 hS0
    have hleft : S.left S0 = rowForm h S0 {} := by
      rw [hSS]
      rfl
    rw [hleft]
    refine c6 hC S0 ?_
    rw [hS0]
    obtain ⟨_, R, _, _, b2, _, _, _, _, _, _, b9⟩ :=
      VerifiableInference.Desc.Kinds.Head.Law.heardBy_ends hW hv mask
    rw [← hk] at b2
    have hsz : es.size = e := (VerifiableInference.Desc.Kinds.Head.Law.hidsAt_spec
      (VerifiableInference.Desc.Kinds.Head.Law.hiddenFrom_hidsAt a6)).1
    refine VerifiableInference.Desc.Kinds.Head.Honest.shown_endK _ (h.r.take n) (endRun c)
      (h.r.getD n zeroE)
      (by rw [List.length_take, c2, Nat.min_eq_left (Nat.le_succ n), hzn])
      (fun j => (S.end_ j).shown) (fun j hj => ?_) fun j hj => ?_
    · rw [hm] at hj
      show rd (S.end_ j).shown = _
      rw [(b9 j hj).1]
      exact c5 R b2 j hj
    · have hdef : S.end_ j = {} := by
        rw [hSS]
        show es.getD j {} = {}
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [hsz, ← hm]; exact hj)]
        rfl
      show rd (S.end_ j).shown = 0
      rw [hdef]
      exact Reading.gl.zero

/-- **AT THE VERIFIER'S sumcheck**: one lead scalar, the claimed sum. -/
theorem sumcheck_truth (name endName : String) (n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape 1 n e) sumAt leadAt)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (z : Point)
    (F0 F1 G : Fork) (S : Sum) (mask : Nat → E)
    (hz : z.toList = (sumAt t.input (frontOf t seen)).z) (hn : z.size = n)
    (hm : (sumAt t.input (frontOf t seen)).maps.length = e)
    (hd : drawsOk ((pairJob (pointShape 1 n e) sumAt leadAt).callAt t.input (frontOf t seen)) ds
      = true)
    (ha : alone (sumPart (V := V) name endName (pairJob (pointShape 1 n e) sumAt leadAt)) c t
      seen ds = some rounds)
    (hW : WellLaid F0) (hv : sumcheck z e F0 rounds = some (S, F1, [])) (hL : Later F1 G)
    (mLead : rd (mask F0.next) = rd ((firstRun c).getD 0 zeroE))
    (mOwn : ∀ i, i < ownSlots (callOf 1 z e).all →
      rd (mask (F0.next + 1 + i)) = hidingCoin c i)
    (mEnd : ∀ j, j < e → rd (mask (F0.next + 1 + ownSlots (callOf 1 z e).all + j)) =
      rd ((endRun c).getD j zeroE)) :
    S.r.toList = (varsOf (callOf 1 z e) ds).take n ∧
    val (worldE G mask noEnt) S.claimed.var =
      rd ((leadAt t.input (frontOf t seen)).getD 0 zeroE) ∧
    (∀ j, j < e → val (worldE G mask noEnt) (S.end_ j).var =
      rd (((sumAt t.input (frontOf t seen)).ends S.r.toList).getD j zeroE)) ∧
    (rd ((leadAt t.input (frontOf t seen)).getD 0 zeroE) =
        rd (sumAt t.input (frontOf t seen)).total →
      ∀ S0 : E, rd S0 = (sumAt t.input (frontOf t seen)).onK (fun j => rd (S.end_ j).shown) →
        val (worldE G mask noEnt) (S.left S0) = 0) := by
  unfold sumcheck at hv
  obtain ⟨cs, F, left, h1, h2⟩ := VerifiableInference.Desc.Kinds.Head.Law.bind_some hv
  obtain ⟨cA, s'⟩ := cs
  dsimp only at h2
  obtain ⟨hS, rfl, rfl⟩ := VerifiableInference.Desc.Kinds.Head.Law.pure_some h2
  obtain ⟨a, b, cc, dd⟩ := heardBy_truth (V := V) name endName 1 n e sumAt leadAt c t seen ds
    rounds z (fun c => (c.getD 0 {}).var) F0 F G cA s' mask hz hn hm hd ha hW h1 hL
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact mLead) mOwn mEnd
  subst hS
  exact ⟨a, b 0 (by omega), cc, fun hq => dd ((b 0 (by omega)).trans hq)⟩

/-- **AT THE VERIFIER'S level**: no lead scalar; start: the form that the sum must equal; line: the
level's last round, which another part plays. -/
theorem level_truth (name endName : String) (n : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape 0 n 2) sumAt leadAt)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (line : Fmt.RoundView) (z : Point)
    (start : Form) (F0 F1 G : Fork) (S : Sum) (mask : Nat → E)
    (hz : z.toList = (sumAt t.input (frontOf t seen)).z) (hn : z.size = n)
    (hm : (sumAt t.input (frontOf t seen)).maps.length = 2)
    (hd : drawsOk ((pairJob (pointShape 0 n 2) sumAt leadAt).callAt t.input (frontOf t seen)) ds
      = true)
    (ha : alone (sumPart (V := V) name endName (pairJob (pointShape 0 n 2) sumAt leadAt)) c t
      seen ds = some rounds)
    (hW : WellLaid F0) (hv : level z start F0 (rounds ++ [line]) = some (S, F1, []))
    (hL : Later F1 G)
    (mOwn : ∀ i, i < ownSlots (callOf 0 z 2).all → rd (mask (F0.next + i)) = hidingCoin c i)
    (mEnd : ∀ j, j < 2 → rd (mask (F0.next + ownSlots (callOf 0 z 2).all + j)) =
      rd ((endRun c).getD j zeroE)) :
    S.r.toList = (varsOf (callOf 0 z 2) ds).take n ∧
    (∀ j, j < 2 → val (worldE G mask noEnt) (S.end_ j).var =
      rd (((sumAt t.input (frontOf t seen)).ends S.r.toList).getD j zeroE)) ∧
    (val (worldE G mask noEnt) start = rd (sumAt t.input (frontOf t seen)).total →
      ∀ S0 : E, rd S0 = (sumAt t.input (frontOf t seen)).onK (fun j => rd (S.end_ j).shown) →
        val (worldE G mask noEnt) (S.left S0) = 0) := by
  have hlen : rounds.length = z.size + 3 := by
    rw [SumLaw.rounds_count (V := V) name endName _ c t seen ds rounds ha, hn]
    show (List.replicate n _).length + 3 = _
    rw [List.length_replicate]
  unfold level at hv
  obtain ⟨cs, G1, l1, h1, k1⟩ := VerifiableInference.Desc.Kinds.Head.Law.bind_some hv
  obtain ⟨cA, s'⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := VerifiableInference.Desc.Kinds.Head.Law.bind_some k1
  obtain ⟨a0, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := VerifiableInference.Desc.Kinds.Head.Law.bind_some k2
  obtain ⟨_, rfl, rfl⟩ := VerifiableInference.Desc.Kinds.Head.Law.need_some h3
  obtain ⟨hS, rfl, rfl⟩ := VerifiableInference.Desc.Kinds.Head.Law.pure_some k3
  have hG : G1 = G2 := VerifiableInference.Desc.Kinds.Head.Law.Came.round_some h2
  subst hG
  obtain ⟨e1, _, _⟩ := VerifiableInference.Desc.Kinds.Head.Law.Came.heardBy_cut h1
  rw [← hlen, List.take_left] at e1
  obtain ⟨a, _, cc, dd⟩ := heardBy_truth (V := V) name endName 0 n 2 sumAt leadAt c t seen ds
    rounds z (fun _ => start) F0 G1 G cA s' mask hz hn hm hd ha hW e1 hL
    (fun i hi => absurd hi (Nat.not_lt_zero i)) mOwn mEnd
  subst hS
  exact ⟨a, cc, dd⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.call_eq
#print axioms ProofFile.Honest.K6.lastD_getD
#print axioms ProofFile.Honest.K6.heard_truth
#print axioms ProofFile.Honest.K6.lead_sent
#print axioms ProofFile.Honest.K6.heardBy_truth
#print axioms ProofFile.Honest.K6.sumcheck_truth
#print axioms ProofFile.Honest.K6.level_truth
