-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumEnd.lean: CONDITIONAL.

What is here. THE END OF THE CHAIN, ON THE VALUES AS THEY ARE SENT. The last message of the masked
sumcheck's honest part, at a caller's job that is made of a `Job` (`k4SumJob`), reads as the job's
end values masked (`maskedEnds`); so the job's summand on the SENT values reads as the value at
which the chain of `SumsTo` ends (CubeSum.lean); and so the form that is left (`rowForm`), made with
that summand on the sent values, is worth the first challenge times what is kept. Statements and
proofs.

  `map_eq_of_getD`, `maskedEnds_length`, `getLastD_eq`   lists
  `vars_length`   a challenge for each of the cube's variables, and Y's
  `k4_sent`   **the last message reads as the masked end values**
  `k4_sent_summand`   the summand on the sent values reads as the chain's end
  `k4_rowForm_sent`   **the form that is left, made on the sent values**
  `rowsSummand_congr`   the row products' summand reads of what was heard the powers omV alone

Limits. At the reading `Reading.gl` alone. THE VERIFIER's TEXT HERE IS THE PART's (`hear`,
Johnson/Desc/Part/MaskedSum4.lean; `rowForm`, Johnson/Desc/Part/MaskedSumMore.lean), not the flat
text that the layers' own rounds run. That the part's moves answer, that the challenges have the
call's shape and, for the form that is left, that `hear` accepts, are premises, as in the law that
is called; so are the world's two (SumCall.lean) and the tie's on the job (CubeSum.lean), with the
turn that SumCall.lean's head says: that the job has as many end values as the call states is a
premise still. THAT A VERIFIER's OWN SUMMAND IS THE JOB's `atEnds` is by reading alone for the
product levels and the merge (a product of two; the first): no statement says that a verifier's step
hands just that to its row; for the row products it wants besides that the verifier has heard the
powers that the maker lays (`rowsSummand_congr`). No example of the premises together is known to us
at the full size. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumCall
import Johnson.Desc.ProofFile.Honest.K4.Law.SumRows
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends Heard hear rowForm ownSlots scalars)
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-! ## 1 Lists -/

/-- Two lists of one length that read alike entry by entry read alike. -/
theorem map_eq_of_getD : ∀ (a b : List E), a.length = b.length →
    (∀ i, i < a.length → Reading.gl.val (a.getD i zeroE) = Reading.gl.val (b.getD i zeroE)) →
    a.map Reading.gl.val = b.map Reading.gl.val
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: a, y :: b, h, hi => by
    rw [List.map_cons, List.map_cons, map_eq_of_getD a b (by simpa using h) fun i h' =>
      hi (i + 1) (by rw [List.length_cons]; omega)]
    have h0 := hi 0 (by rw [List.length_cons]; omega)
    rw [show Reading.gl.val x = Reading.gl.val y from h0]

/-- As many masked end values as end values. -/
theorem maskedEnds_length (ends m : List E) (y : E) (h : ends.length = m.length) :
    (maskedEnds ends m y).length = ends.length := by
  simp [maskedEnds, h]

/-- There is a challenge for each of the cube's variables, and Y's. -/
theorem vars_length (sh : Call) (job : W → Front X → Option Job) (w : W) (fr : Front X) (j : Job)
    (e : Ends) (ds : List Fmt.Drawn) (hd : drawsOk ((k4SumJob sh job).callAt w fr) ds = true)
    (hfit : SumShape sh j) (he : sh.ends = some e) :
    (varsOf ((k4SumJob sh job).callAt w fr) ds).length = j.cube.n + 1 := by
  rw [varsOf_length _ ds hd, all_some (k4SumJob sh job) _ _ e he, List.length_append,
    withPoints_length, List.length_singleton, hfit.2.1]
  rfl

/-! ## 2 The last message -/

/-- **The last message reads as the job's end values, masked with Y's challenge.** e: the call's
ends. -/
theorem k4_sent (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (j : Job) (e : Ends)
    (hd : drawsOk ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob sh job)) c t seen ds = some rounds)
    (hj : job t.input (frontOf t seen) = some j) (hfit : SumShape sh j) (he : sh.ends = some e)
    (hn : (j.ends ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take
      j.cube.n)).length = e.n) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = e.n ∧
      s.map Reading.gl.val = (maskedEnds
        (j.ends ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take j.cube.n))
        (endRun c)
        ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).getD j.cube.n
          zeroE)).map Reading.gl.val := by
  obtain ⟨r, s, h1, h2, h3, h4⟩ :=
    sumLast V W X name endName (k4SumJob sh job) c t seen ds rounds e he hd ha
  have hl : (j.ends ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take
      j.cube.n)).length = (endRun c).length := by
    rw [hn, endRun_length c e he]
  refine ⟨r, s, h1, h2, h3, map_eq_of_getD _ _ ?_ fun i hi => ?_⟩
  · rw [h3, maskedEnds_length _ _ _ hl, hn]
  · have h5 := h4 i (by rw [← h3]; exact hi)
    have e1 : (k4SumJob sh job).ends t.input (frontOf t seen)
        ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take
          (k4SumJob sh job).shape.vs.length) =
        j.ends ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take
          j.cube.n) := by
      have e0 : ∀ l, (k4SumJob sh job).ends t.input (frontOf t seen) l = j.ends l := by
        intro l
        show ((job t.input (frontOf t seen)).map (·.ends l)).getD [] = _
        rw [hj]
        rfl
      rw [e0, hfit.2.1]
      rfl
    -- the last of n + 1 is number n
    have getLastD_eq : ∀ (l : List E) (n : ℕ), l.length = n + 1 →
        l.getLastD zeroE = l.getD n zeroE := fun l n h => by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, h, List.getD_eq_getElem?_getD]
      rfl
    rw [e1, getLastD_eq _ _ (vars_length sh job _ _ j e ds hd hfit he)] at h5
    rw [h5, maskedEnds_read _ _ hl]

/-- The job's summand on the sent values reads as the value at which the chain ends. -/
theorem k4_sent_summand (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (j : Job) (e : Ends)
    (hd : drawsOk ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob sh job)) c t seen ds = some rounds)
    (hj : job t.input (frontOf t seen) = some j) (hfit : SumShape sh j) (he : sh.ends = some e)
    (hn : (j.ends ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take
      j.cube.n)).length = e.n)
    (hA : ReadsAlike (j.atEnds
      ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take j.cube.n))) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = e.n ∧
      Reading.gl.val (j.atEnds
        ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take j.cube.n) s) =
      Reading.gl.val (j.atEnds
        ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take j.cube.n)
        (maskedEnds
          (j.ends ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).take j.cube.n))
          (endRun c)
          ((varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds).getD j.cube.n
            zeroE))) := by
  obtain ⟨r, s, h1, h2, h3, h4⟩ :=
    k4_sent (V := V) name endName sh job c t seen ds rounds j e hd ha hj hfit he hn
  exact ⟨r, s, h1, h2, h3, hA _ _ h4⟩

/-! ## 3 The form that is left -/

/-- **The form that is left, made with the job's summand on the SENT values, is worth the first
challenge times what is kept**, in any world that has the part's coins under the sumcheck's own
slots and in which the claimed form is worth the cube's total. -/
theorem k4_rowForm_sent (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (kept : Aff)
    (Wd : World GE) (j : Job) (e : Ends)
    (hd : drawsOk ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob sh job)) c t seen ds = some rounds)
    (hh : hear C ((k4SumJob sh job).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((k4SumJob sh job).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hj : job t.input (frontOf t seen) = some j) (hfit : SumShape sh j) (he : sh.ends = some e)
    (hdY : j.dY + 1 < 2 ^ 32) (hn : (j.ends (h.r.take j.cube.n)).length = e.n)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (h.r.take j.cube.n) (maskedEnds (j.ends (h.r.take j.cube.n)) (endRun c) y))
    (hA : ReadsAlike (j.atEnds (h.r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (h.r.take j.cube.n) (j.ends (h.r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (h.r.take j.cube.n))) :
    ∃ (r : Fmt.RoundView) (s : List E), rounds.getLast? = some r ∧ scalars r.vals = some s ∧
      s.length = e.n ∧
      (rowForm h (j.atEnds (h.r.take j.cube.n) s) kept).value Reading.gl Wd =
        Reading.gl.val h.eps * kept.value Reading.gl Wd := by
  have hr : h.r = varsOf ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds :=
    (sumClaim V W X name endName (k4SumJob sh job) c t seen ds rounds C F G h hd ha hh).2.1
  obtain ⟨r, s, h1, h2, h3, h4⟩ := k4_sent_summand (V := V) name endName sh job c t seen ds rounds
    j e hd ha hj hfit he (by rw [← hr]; exact hn) (by rw [← hr]; exact hA)
  rw [← hr] at h4
  refine ⟨r, s, h1, h2, h3, ?_⟩
  rw [k4_rowForm_worth (V := V) name endName sh job c t seen ds rounds C F G h _ kept Wd j e hd ha
    hh hs hσ hj hfit he hdY hn hP hA hE, h4]
  ring

/-! ## 4 The row products' summand -/

/-- The verifier's summand of the norms' rows reads, of what was heard, the powers omV alone. -/
theorem rowsSummand_congr (y : OnBytes.Model.Layer.Lay) (H H' : OnBytes.Model.Layer.Heard)
    (h : H.omV = H'.omV) (sh : Array E) : rowsSummand y H sh = rowsSummand y H' sh := by
  unfold rowsSummand
  rw [h]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.map_eq_of_getD
#print axioms ProofFile.Honest.K4.maskedEnds_length
#print axioms ProofFile.Honest.K4.vars_length
#print axioms ProofFile.Honest.K4.k4_sent
#print axioms ProofFile.Honest.K4.k4_sent_summand
#print axioms ProofFile.Honest.K4.k4_rowForm_sent
#print axioms ProofFile.Honest.K4.rowsSummand_congr
