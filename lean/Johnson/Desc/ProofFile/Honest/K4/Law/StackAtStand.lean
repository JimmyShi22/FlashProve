-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackAtStand.lean: CONDITIONAL. Statements with their proofs.

Not shown here. No property is claimed. That the premises can be met: no example is known. WHAT
STAYS A HYPOTHESIS ON WHAT IS SUMMED: `JoinWorth` (Law/StackStart.lean), at the factors that the
verifier's text makes: THE BATCHED SUMCHECK's FIRST PASS IS THE LOOKUP's JOIN: nothing here shows
it. In `ownBack_join` besides: the start of the merge's sumcheck, which is that job's own content.
That the step of K4's member accepts is a premise. Nothing on the law of any coin. Nothing on
soundness, on completeness or on any other property.

What is here: at a stand (`K4Stand`, Law/SlotsTrue.lean) of the layers' own rounds (the sub-protocol
K4), under the premises below, the batched sumcheck's own claim is worth 0 in the world of every
ledger later than the one that the step leaves: the field stack of the hypothesis `OwnBack`
(Johnson/Road/K4/W/Join.lean), which Law/OwnAtStand.lean's `ownBack_stand` takes as a premise. A
call of `stack_whole` (Law/StackWhole.lean), which says so of a return of the hearing where the
second token sumcheck's part and the batched sumcheck's part have both played honestly; here its
premises on the two parts, on the hearing, on what was seen and on the makers are shown at a stand.

THE PREMISES: `K4Stand` · `Thr`, the proposition of `Thread` on a stand (Honest/Thread/Thr.lean):
with it `K4Seated.fits` is spent: at shapes that do not fit these statements say nothing ·
`K4LookTieAt` (Law/ScriptAt.lean), all three fields. BESIDES:
  hP: `TermsPub` (Law/TermsAll.lean), on public data, at what the two jobs share:
      `termsPub_of_plan` (Law/TermsPubOf.lean) has it from `K4Plan` and the weights' layout;
  hnE: the second token sumcheck has an end value: where the public test `planNumsB` accepts,
      `planNums_of_B` has it (Johnson/Desc/First/K4/Returns/Needs.lean, which this file does not
      import); a lower bound on the number of end values from `K4Plan`: `halvesNums_of_plan`
      (Law/W/HalvesNums.lean, field ends);
  hok: the three words of that sumcheck's first challenge lie below the prime: the library has it
      of a tape of small words (`small_eps`, Johnson/Road/K4/OwnCoin.lean); at a stand, from
      `drawsFit`: `stand_ok` (Law/OkAtStand.lean);
  hz0: the lookup's point is not empty: `stand_z0` (Law/OkAtStand.lean), where the layout has a
      token coordinate;
  hJW: `JoinWorth`, at the data that the batched sumcheck's maker returns at the stand:
      `join_stand` (Law/W/JoinAtFoot.lean) has it from the lookup's own sentence and further
      hypotheses.

  `jobTermsOn_lead`   the second token sumcheck's job leads with its cube's total
  `scalars_leading`, `last_of_cut`   two small steps on lists
  `stack_stand`   **THE BATCHED SUMCHECK's OWN CLAIM IS WORTH 0 AT A STAND**: `OwnBack.stack`
  `ownBack_join`   **`OwnBack` whole**, from these and the merge's start

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackWhole
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SeenTerms
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Aff Fork Tsc wsForkStart powers)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.PscRun (Later)
open OnBytes.K.Kc (leading)
open OnBytes.Desc.First.K4 (Par k0 mergeSlots formsBack)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.SumLaw (alone drawsOk frontOf sumGs SumCoins)
open ProofFile.Honest.K4.SlotsOwn (SumAt worldBehind sumAt_some terms_hs stack_hs)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- The second token sumcheck's job leads with its cube's total. -/
theorem jobTermsOn_lead {S : OnBytes.Desc.First.K4.Honest.Sides} {j : Job}
    (h : jobTermsOn S = some j) : j.lead = [j.cube.total] := by
  unfold jobTermsOn at h
  obtain ⟨rows, _, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    rfl

/-- A message that is scalars alone: its leading scalars are all of them. -/
theorem scalars_leading : ∀ (l : List Fmt.ItemValue) (s : List OnBytes.E),
    VerifiableInference.Desc.Part.MaskedSum.scalars l = some s → leading l = s := by
  intro l
  induction l with
  | nil =>
    intro s h
    obtain rfl := Option.some.inj h
    rfl
  | cons x l ih =>
    intro s h
    cases x with
    | e v =>
      obtain ⟨s', hs', rfl⟩ := Option.map_eq_some_iff.mp h
      show OnBytes.E.ofTriple v :: leading l = _
      rw [ih s' hs']
    | _ => cases h

/-- The last member of n members cut out of a list from number R on. -/
theorem last_of_cut {α : Type} (l : List α) (R n : Nat) (h : R + (n + 1) ≤ l.length) :
    ((l.drop R).take (n + 1)).getLast? = l[R + n]? := by
  have hl : ((l.drop R).take (n + 1)).length = n + 1 := by
    rw [List.length_take, List.length_drop]
    omega
  rw [List.getLast?_eq_getElem?, hl, Nat.add_sub_cancel, List.getElem?_take_of_lt (by omega),
    List.getElem?_drop]

/-- **THE BATCHED SUMCHECK's OWN CLAIM IS WORTH 0 AT A STAND**: `OwnBack.stack`. F: any ledger later
than the one that the step leaves. CONDITIONAL on the named premises; hJW: the lookup's join. -/
theorem stack_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) (F : Fork)
    (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hP : ∀ S, OnBytes.Desc.First.K4.Honest.Sides.of Q
        (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some S → TermsPub S)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hok : ∀ tT, o.H.tT = some tT → OnBytes.okE tT.p.eps = true)
    (hz0 : o.H.fo.zx.isEmpty = false)
    (hJW : ∀ D, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt (seenAt m y (rJ4 Q.P Q.g)).rounds (k4TermsEnds Q)) = some D →
      ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
        o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' →
        JoinWorth o.H tT' parts (worldBehind T own rdOf k y A ds' F entry) D) :
    o.K.rowS.value Reading.gl (worldBehind T own rdOf k y A ds' F entry) = 0 := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, ha, L⟩ := stand_led_tape Z
  obtain ⟨_, c, _, _, _, Pl, _⟩ := stand_ground Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  -- the hearing's return, at the ledgers of L
  obtain ⟨a', _, fo, ha', _, _, _, hh0, _⟩ := step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain rfl : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh0
  -- what the lookup has sampled
  have el := stand_look Z
  obtain ⟨g, _, h2, hzx, hzk, he⟩ := hLk
  rw [h2] at el
  obtain rfl := Option.some.inj el
  -- how far the challenges reach
  have hr := stand_reach Z
  obtain ⟨_, _, e2, e3, _, _, _⟩ := k4StartAt_eq Q
  have hl3 : k4StartAt Q 3 ≤ ds.length := by
    refine Nat.le_trans ?_ hr
    simp only [k4StartAt]
    omega
  have hlen : rJ3 Q.P Q.g + (Q.P.y.h.lt + 2 + 1) ≤ (roundsOf y.1).length := by
    rw [played_length hy, ← e2]
    refine Nat.le_trans ?_ hr
    simp only [k4StartAt]
    omega
  -- the second token sumcheck's part
  have hp3 := k4RowIn_at Q 6
  obtain ⟨c3, hc3⟩ := sumAt_some c (k0 Q.g + 6) _ _ (termsSum Q) hp3
  have ha3 := k4_alone (V := Unit) Pl (k0 Q.g + 6) _ _ (termsSum Q) hp3 c3 hc3
  have hn3 : ∀ a b : String, (sumGs a b (termsSum Q)).length = Q.P.y.h.lt + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.P.y.h.lt) _).length + 3 = _
    rw [List.length_replicate]
  have hdr3 := k4_draws (stand_elems Z) 6 (Q.P.y.h.lt) rfl
    ((termsSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rJ3 Q.P Q.g)) (seenAt m y (rJ3 Q.P Q.g))))
    (by
      show (withPoints (List.replicate (Q.P.y.h.lt) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn3, (k4_row_nums Q).m3] at ha3
  rw [(k4_row_nums Q).m3] at hdr3
  -- the batched sumcheck's part
  have hp4 := k4RowIn_at Q 8
  obtain ⟨c4, hc4⟩ := sumAt_some c (k0 Q.g + 8) _ _ (stackSum Q) hp4
  have ha4 := k4_alone (V := Unit) Pl (k0 Q.g + 8) _ _ (stackSum Q) hp4 c4 hc4
  have hn4 : ∀ a b : String, (sumGs a b (stackSum Q)).length = Q.hp.lamS + 3 := fun a b => by
    rw [SumLaw.sumGs_count]
    show (List.replicate (Q.hp.lamS) _).length + 3 = _
    rw [List.length_replicate]
  have hdr4 := k4_draws (stand_elems Z) 8 (Q.hp.lamS) rfl
    ((stackSum Q).callAt (k4Wit Q cells weights tokens (look Q) m.st.input)
      (frontOf (entryAt Q cells weights tokens look m ds (rJ4 Q.P Q.g)) (seenAt m y (rJ4 Q.P Q.g))))
    (by
      show (withPoints (List.replicate (Q.hp.lamS) _) _).length = _
      rw [SumLaw.withPoints_length, List.length_replicate]) rfl
  rw [hn4, (k4_row_nums Q).m4] at ha4
  rw [(k4_row_nums Q).m4] at hdr4
  -- the makers
  obtain ⟨S, j, hS, hJ, hfit3⟩ := W.termsJob_at Z hT
  obtain ⟨D, _, hDt, _, hfit4⟩ := W.stackJob_at Z hT
    (k4SentAt (seenAt m y (rJ4 Q.P Q.g)).rounds (k4TermsEnds Q))
  -- the first slot of the batched sumcheck's own run
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsA0,
    _⟩ := OnBytes.Desc.First.K4.hearStack_tape L.c4
  have hj4 : G2.next + ownOf 0 Q.hp.lamS 2 = o.K.sA0 := by
    rw [hsA0]
    unfold ownOf
    omega
  -- the start of the second token sumcheck: its claimed sum's slot holds its cube's total
  have hj' : jobTerms Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some j := by
    unfold jobTerms
    rw [show OnBytes.Desc.First.K4.Honest.Sides.of Q
      (k4Wit Q cells weights tokens (look Q) m.st.input)
      (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some S from hS]
    exact hJ
  have hσ3 : (Aff.slot G1.next).value Reading.gl (worldBehind T own rdOf k y A ds' F entry) =
      Reading.gl.val j.cube.total := by
    rw [OnBytes.Model.Aff.value_slot, ← (led_sCl L).2]
    refine ((opened_left Z ds' F hL entry).terms _ L.kTT).1.trans ?_
    unfold leadWord
    rw [hj']
    show Reading.gl.val ((j.lead).getD 0 zeroE) = _
    rw [jobTermsOn_lead hJ]
    rfl
  have hok' : OnBytes.okE tT.p.eps = true :=
    hok { tT with p := { tT.p with rowMade := true } } L.kTT
  exact stack_whole (V := Unit) m.st.heard hh0 L ds (stand_drawn hy _) hl3
    (k4_heard_front Z.seat hT) (worldBehind T own rdOf k y A ds' F entry)
    (k4Wit Q cells weights tokens (look Q) m.st.input) hzx he hzk
    _ _ c3 (entryAt Q cells weights tokens look m ds (rJ3 Q.P Q.g)) (seenAt m y (rJ3 Q.P Q.g)) _ _
    rfl (by rw [e2]; rfl) hdr3 ha3
    (fun i hi => by
      rw [← (led_sCl L).2]
      exact terms_hs Z c Pl.lent _ _ (termsSum Q) rfl c3 hc3 ds' F hL entry _ L.kTT _ _ i hi)
    S hS (hP S hS) j hJ hfit3 hnE hσ3 (by rw [e2]; exact tapeIs_paired_drop _ _ _ _)
    hok'
    _ _ c4 (entryAt Q cells weights tokens look m ds (rJ4 Q.P Q.g)) (seenAt m y (rJ4 Q.P Q.g)) _ _
    rfl (by rw [e3]; rfl) hdr4 ha4
    (stack_hs Z c Pl.lent _ _ (stackSum Q) rfl c4 hc4 ds' F hL entry G2.next hj4 _ _)
    D hDt hfit4 (by rw [e3]; exact tapeIs_paired_drop _ _ _ _)
    (fun rv sv g1 g2 => by
      have g1' : (roundsOf y.1)[rJ3 Q.P Q.g + (Q.P.y.h.lt + 2)]? = some rv :=
        (last_of_cut (roundsOf y.1) (rJ3 Q.P Q.g) (Q.P.y.h.lt + 2) hlen).symm.trans g1
      refine (stand_terms_seen Z hT).trans ?_
      unfold sentAt
      rw [g1']
      show (leading rv.vals).toArray = _
      rw [scalars_leading _ _ g2])
    (fun tT' a' g1 g3 => stand_terms_run Z hT tT' g1 G2 a' L.g2 g3)
    hz0 (hJW D hDt)

/-- **`OwnBack` WHOLE AT A STAND**, in the world of every ledger later than the one that "back"
leaves, run from a ledger later than the one that the step leaves. CONDITIONAL on the named
premises; hJW: the lookup's join; hσ: the start of the merge's sumcheck. -/
theorem ownBack_join
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) {F₁ F₂ : Fork}
    {fs₂ : Array Aff} (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂)) (F : Fork)
    (hL : Later F₂ F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hP : ∀ S, OnBytes.Desc.First.K4.Honest.Sides.of Q
        (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some S → TermsPub S)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hok : ∀ tT, o.H.tT = some tT → OnBytes.okE tT.p.eps = true)
    (hz0 : o.H.fo.zx.isEmpty = false)
    (hJW : ∀ D, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt (seenAt m y (rJ4 Q.P Q.g)).rounds (k4TermsEnds Q)) = some D →
      ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
        o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' →
        JoinWorth o.H tT' parts (worldBehind T own rdOf k y A ds' F entry) D)
    (hσ : ∀ cls, mergeClaimsAt Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))) = some cls →
      (wsForkStart (mergeSlots Q.hp Q.g o)
          (powers ((ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE)
            (mergeSlots Q.hp Q.g o).size)).value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (mergeJobOf Q.P.wsLay
          (k4Wit Q cells weights tokens (look Q) m.st.input).w cls
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))).rhoW).cube.total) :
    OnBytes.Road.K4.W.OwnBack Reading.gl (worldBehind T own rdOf k y A ds' F entry) o := by
  exact ownBack_stand Z hT ds' h1 hb F hL entry
    (stack_stand Z hT hLk ds' F
      ((h1.trans (OnBytes.Desc.First.K4.formsBack_later hb)).trans hL) entry hP hnE hok hz0 hJW) hσ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.jobTermsOn_lead
#print axioms ProofFile.Honest.K4.scalars_leading
#print axioms ProofFile.Honest.K4.last_of_cut
#print axioms ProofFile.Honest.K4.stack_stand
#print axioms ProofFile.Honest.K4.ownBack_join
