--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ChainMet.lean: an honest run of the eight sub-protocols of the linear
claim's shared rounds, written out: all premises of eight_hold
(Johnson/Desc/K14/Honest/ChainHolds.lean) are met together at one member.

eight_hold says: the eight return; and, under two premises on the committed table, if the OOD
answers shown are the honest ones at the states that the run reaches, and the scalar is the honest
one, then all that the statement claims behind the eight holds of the honest words. Its premises on
what is shown speak of states of the run itself. This file builds such a run: the answers of a
sending are chosen when the state in front of that sending is there. Two runs that share their first
rounds share their first states, since each place is a function.

The run. The committed table's rows are 0, with the key and the column of
Johnson/Desc/K14/Honest/ChainWitness.lean: there the two premises on the committed table hold. The
words in front and the random values of the four messages are arbitrary. The challenges are
ChainWitness.lean's. The statement (HonestW) shows the key, the challenges and the column written
out, and the three equations on what is shown.

Main names:
  sum_filter_nz, shapes_by_number, answers_length, items_answersAt   a sending's honest second round
                      shows as many answers as the place has
  rounds8_at          Rounds8 at the witness's challenges, whatever answers and scalar are shown
  Returned.front_eq   two runs that share the rounds up to "LOC" share the states up to there
  inputs0, HonestW    what the prover holds at rows that are 0; an honest run at the witness's key,
                      challenges and column
  holds_met           **there is an honest run**
  holds_key, holds_real   at the two typed shapes

What is assumed, as premises: PlanFacts; the two sendings pass their kind's test on the plan. At the
two typed shapes: nothing.
What is not claimed. More than "not empty": eight_hold is general, this file is one member, at a
committed table that is 0, at one location, at challenges that are written and not sampled, at a key
that is no committer's (what ChainWitness.lean's head says of the witness holds here). That a
decision accepts: in terms of the format's step see ChainStepsMet.lean. Nothing on the two proximity
tests, on soundness or on hiding. This is not completeness of the protocol or of a program.

-/
import Johnson.Desc.K14.Honest.ChainWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G Desc.Plain
open OnBytes.Means (Words)
open OnBytes.Slice (rdE)
open Johnson.Prover.Send (Rows answers shapeAt)
open VerifiableInference.Desc (itemOf)
open VerifiableInference.Desc.K1 (planOkOwn shapesOf realSized)
open Lk6.AtPlan (keyFull)
open Desc.K14.Law (parU parO)

/-! ## How many answers an honest second round shows -/

/-- Summands that are 0 may be left out. -/
theorem sum_filter_nz (f : ℕ → ℕ) : ∀ l : List ℕ,
    ((l.filter fun k => f k != 0).map f).sum = (l.map f).sum
  | [] => rfl
  | a :: l => by
    by_cases h : f a = 0
    · simp [h, sum_filter_nz f l]
    · simp [h, sum_filter_nz f l]

/-- A place's shapes, by number. -/
theorem shapes_by_number (Q : VerifiableInference.Desc.K1.Par) :
    (shapesOf Q).map (·.answers) =
      (List.range Q.sent.size).map fun k => (shapeAt Q k).answers := by
  refine List.ext_getElem (by simp [shapesOf]) fun i h1 h2 => ?_
  have hi : i < Q.sent.size := by simpa [shapesOf] using h1
  simp [shapesOf, shapeAt, Array.getD_eq_getD_getElem?, hi]

/-- **The honest answers of a sending are as many as the place has.** -/
theorem answers_length (Q : VerifiableInference.Desc.K1.Par) (S' : Statement) (first : ℕ)
    (w' : Words Cb.Gl.E) (seeds : List (List E × E)) :
    (answers Q S' first w' seeds).length = Q.answers := by
  unfold answers
  rw [List.length_flatMap, VerifiableInference.Desc.K1.answers_sum, shapes_by_number]
  simp only [List.length_map, List.length_range]
  exact sum_filter_nz (fun k => (shapeAt Q k).answers) _

/-- So its second round shows the items that the plan cuts. -/
theorem items_answersAt (Q : VerifiableInference.Desc.K1.Par) (T : Statement) (r : Fmt.RoundView)
    (w : Words Cb.Gl.E) (V : ℕ → Rows) :
    (answersAt Q T r w V).map itemOf = List.replicate Q.answers .answer := by
  unfold answersAt
  rw [List.map_map]
  have e : (itemOf ∘ Fmt.ItemValue.answer) = fun _ => Fmt.Item.answer := rfl
  rw [e, List.map_const', answers_length]

/-! ## The view -/

/-- **Rounds8 at the witness's challenges, whatever answers and scalar are shown.** -/
theorem rounds8_at (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (v2 v5 : List Fmt.ItemValue)
    (h2 : v2.map itemOf = List.replicate (parU P sentU).answers .answer)
    (h5 : v5.map itemOf = List.replicate (parO P).answers .answer) (x : Fmt.Ext) :
    Rounds8 P.par (parU P sentU) (parO P) (pointW P) (seedsW (parU P sentU)) (rvVals v2)
      (rvPoss P.par.S.fold.columns) (seedsW (parO P)) (rvVals v5) (zetaW P) (rvVals [.e x])
      (colsW P.par.S.fold.index.rows) := by
  have hlen : P.codes.lengthsOk = true := hP.lengths
  have fU := fits_send (parU P sentU) v2 h2
  have fO := fits_send (parO P) v5 h5
  have z := rounds8_met P sentU layO hP hBU hBO
  exact ⟨z.point, seeds_nz _ _ _ fU, fitB_of_rounds _ _ _ hBU hlen fU, z.columns,
    seeds_nz _ _ _ fO, fitB_of_rounds _ _ _ hBO hlen fO, z.zeta, ⟨x, rfl⟩⟩

/-- **Two runs that share the rounds up to "LOC" share the states up to there.** -/
theorem Returned.front_eq {P : P14} {sentU : Array OracleNotice} {d0 : St}
    {r1 r2a r2b r4 r5a r5b r7 r8 r5a' r5b' r7' r8' : Fmt.RoundView} {cols : List (Nat × List UInt64)}
    {rs3 rs6 rs6' : List Fmt.RoundView} {d1 d2 d3 d4 d5 d6 d7 d8 e1 e2 e3 e4 e5 e6 e7 e8 : St}
    {x2 x5 y2 y5 : DState (Array Nat)} {ids2 ids5 jds2 jds5 : Array Nat}
    (h : Returned P sentU d0 r1 r2a r2b r4 r5a r5b r7 r8 cols rs3 rs6
      d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5)
    (k : Returned P sentU d0 r1 r2a r2b r4 r5a' r5b' r7' r8' cols rs3 rs6'
      e1 e2 e3 e4 e5 e6 e7 e8 y2 y5 jds2 jds5) : d1 = e1 ∧ d4 = e4 := by
  obtain rfl : d1 = e1 := Option.some.inj (h.k1.symm.trans k.k1)
  have a : (ids2, x2) = (jds2, y2) := Except.ok.inj (h.s2.sent.symm.trans k.s2.sent)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj a
  obtain rfl : d2 = e2 := Option.some.inj (h.s2.noted.symm.trans k.s2.noted)
  obtain rfl : d3 = e3 := Option.some.inj (h.k3.symm.trans k.k3)
  obtain rfl : d4 = e4 := Option.some.inj (h.k4.symm.trans k.k4)
  exact ⟨rfl, rfl⟩

/-- What an honest prover holds where the committed table's rows are 0. -/
def inputs0 (w₀ : Words Cb.Gl.E) (cU cMask cOmega cSp : MsgCoins) : Inputs :=
  ⟨w₀, fun _ _ => 0, cU, cMask, cOmega, cSp⟩

/-- **An honest run at the witness's key, challenges and column**: the eight have returned; the OOD
answers shown at the two sendings are the honest ones at the states reached; the scalar shown is the
honest one; and all that the statement claims behind the eighth holds of the honest words. H: what
the prover holds. -/
def HonestW (P : P14) (sentU : Array OracleNotice) (H : Inputs) (rs3 rs6 : List Fmt.RoundView) : Prop :=
  ∃ (r2b r5b r8 : Fmt.RoundView) (d1 d2 d3 d4 d5 d6 d7 d8 : St) (x2 x5 : DState (Array Nat))
    (ids2 ids5 : Array Nat),
    ReturnedW P sentU r2b r5b r8 rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5 ∧
    r2b.vals = answersAt (parU P sentU) d1.st (seedsW (parU P sentU)) H.w₀
      (rowsU P (firstW P) (pointW P) H) ∧
    r5b.vals = answersAt (parO P) d4.st (seedsW (parO P))
      (words1 P sentU (firstW P) (pointW P) H) (rowsO P (firstW P) (pointW P) H) ∧
    r8.vals = [.e (Slice.ofE (muRun P (firstW P) (pointW P) (zetaW P) H))] ∧
    Means.AllMet rdE d8.st (words2 P sentU (firstW P) (pointW P) H)

/-- **There is an honest run**, at rows that are 0, whatever words lie in front and whatever the
random values of the four messages are. -/
theorem holds_met (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (w₀ : Words Cb.Gl.E) (cU cMask cOmega cSp : MsgCoins)
    (rs3 rs6 : List Fmt.RoundView) : HonestW P sentU (inputs0 w₀ cU cMask cOmega cSp) rs3 rs6 := by
  -- the state in front of the first sending
  obtain ⟨c1, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := returned_met P sentU layO hP hBU hBO rs3 rs6
  -- a run with the first sending's honest answers: it reaches the state in front of the second
  have i2 := items_answersAt (parU P sentU) c1.st (seedsW (parU P sentU)) w₀
    (rowsU P (firstW P) (pointW P) (inputs0 w₀ cU cMask cOmega cSp))
  obtain ⟨e1, _, _, e4, _, _, _, _, _, _, _, _, he⟩ := eight_return P sentU layO hP (firstW P) rfl
    rfl (key_fits _) (key_beta _) _ _ _ _ _ _ _ _ _
    (rounds8_at P sentU layO hP hBU hBO _ _ i2 (items_zero (parO P).answers) (0, 0, 0)) rs3 rs6
  obtain rfl : c1 = e1 := Option.some.inj (hc.k1.symm.trans he.k1)
  -- the honest run
  have i5 := items_answersAt (parO P) e4.st (seedsW (parO P))
    (words1 P sentU (firstW P) (pointW P) (inputs0 w₀ cU cMask cOmega cSp))
    (rowsO P (firstW P) (pointW P) (inputs0 w₀ cU cMask cOmega cSp))
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, x2, x5, ids2, ids5, h⟩ := eight_return P sentU layO hP
    (firstW P) rfl rfl (key_fits _) (key_beta _) _ _ _ _ _ _ _ _ _
    (rounds8_at P sentU layO hP hBU hBO _ _ i2 i5
      (Slice.ofE (muRun P (firstW P) (pointW P) (zetaW P) (inputs0 w₀ cU cMask cOmega cSp))))
    rs3 rs6
  obtain ⟨rfl, rfl⟩ := h.front_eq he
  exact ⟨_, _, _, d1, d2, d3, d4, d5, d6, d7, d8, x2, x5, ids2, ids5, h, rfl, rfl, rfl,
    returned_holds P sentU layO hP _ _ _ _ _ _ _ _ _ _ rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2
      ids5 h (inputs0 w₀ cU cMask cOmega cSp) hBU hBO (fits_send _ _ i2) (fits_send _ _ i5)
      (first_kept rdE P.codes _ w₀) (rec_zero P.par.S.fold.index) (col_zero P.par _) rfl rfl rfl⟩

/-- **At the typed sizes of a key of full size.** -/
theorem holds_key : ∃ sentU : Array OracleNotice, withU keyFull.once.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
    ∀ (w₀ : Words Cb.Gl.E) (cU cMask cOmega cSp : MsgCoins) (rs3 rs6 : List Fmt.RoundView),
      HonestW ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (inputs0 w₀ cU cMask cOmega cSp) rs3 rs6 := by
  obtain ⟨sentU, layO, hf⟩ := planFacts_key
  refine ⟨sentU, (hf 0 [(0, 0)] (by simp)).goes,
    fun item bp hbp w₀ cU cMask cOmega cSp rs3 rs6 => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (Law.k14_key item bp hbp) (hf item bp hbp).goes
  exact holds_met _ sentU layO (hf item bp hbp) hBU hBO w₀ cU cMask cOmega cSp rs3 rs6

/-- **At the typed sizes over a proof file's own codes.** -/
theorem holds_real : ∃ (x : LinSized) (sentU : Array OracleNotice),
    realSized = some (x, codesFull2) ∧ withU x.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
    ∀ (w₀ : Words Cb.Gl.E) (cU cMask cOmega cSp : MsgCoins) (rs3 rs6 : List Fmt.RoundView),
      HonestW ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ sentU
        (inputs0 w₀ cU cMask cOmega cSp) rs3 rs6 := by
  obtain ⟨x, sentU, layO, a1, _, hf⟩ := planFacts_real
  obtain ⟨x', b1, _, hC⟩ := Law.k14_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (a1.symm.trans b1))
  refine ⟨x, sentU, a1, (hf 0 [(0, 0)] (by simp)).goes,
    fun item bp hbp w₀ cU cMask cOmega cSp rs3 rs6 => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (hC item bp hbp) (hf item bp hbp).goes
  exact holds_met _ sentU layO (hf item bp hbp) hBU hBO w₀ cU cMask cOmega cSp rs3 rs6

end Desc.K14.Honest

#print axioms Desc.K14.Honest.sum_filter_nz
#print axioms Desc.K14.Honest.shapes_by_number
#print axioms Desc.K14.Honest.answers_length
#print axioms Desc.K14.Honest.items_answersAt
#print axioms Desc.K14.Honest.rounds8_at
#print axioms Desc.K14.Honest.Returned.front_eq
#print axioms Desc.K14.Honest.holds_met
#print axioms Desc.K14.Honest.holds_key
#print axioms Desc.K14.Honest.holds_real
