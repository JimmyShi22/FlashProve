-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SumCall.lean: CONDITIONAL.

What is here. The law of the masked sumcheck's honest part (Honest/SumLaw/), called at a caller's
job that is made of a `Job` (`k4SumJob`), with no premise left on the number of the challenges or of
the mask entries; and at the merge's sumcheck of the feed-forward layers' rounds. Statements and
proofs.

Y is the further variable of a masked sumcheck, behind the cube's own: the last round's.

  `heard_r_length`   `hear` hands back a challenge for each variable, Y among them
  `k4_sumsTo_heard`   `SumsTo` at what `hear` hands back and at the part's own mask entries
  `k4_rowForm_worth`, `k4_claim`   the law's two forms, called
  `mergeJob_poly`, `mergeJob_alike`, `mergeJob_end`, `mergeSum`, `merge_rowForm_worth`   at the
     merge's sumcheck

Limits. THE VERIFIER's TEXT HERE IS THE PART's (`hear`, Johnson/Desc/Part/MaskedSum4.lean;
`rowForm`, Johnson/Desc/Part/MaskedSumMore.lean) AND NOT THE FLAT TEXT THAT THE LAYERS' OWN ROUNDS
RUN: the tie between the two texts is not called here. That `hear` accepts, that the part's moves
answer and that the challenges have the call's shape are premises, as in the law that is called. THE
WORLD IS A PREMISE: that it holds the part's coins under the sumcheck's own slots, and that the
claimed form is worth the reading of the cube's total in it. For a job at large the premises of
`k4_sumsTo_own` stay, with this turn in the two on lengths: the one on the challenges is gone; the
one on the mask entries has become THAT THE JOB HAS AS MANY END VALUES AS THE CALL STATES, at the
run's challenges: a premise still. At the merge it holds by the way the job is made. Beside the
law's own files this file stands on Honest/SumLaw/FitsAt.lean, and so on the frame's
Honest/SumFits.lean. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMerge
import Johnson.Desc.ProofFile.Honest.SumLaw.FitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Reading Aff Fork World WsClaim)
open OnBytes.Slice (GE)
open OnBytes.Desc.First.P1 (hid psiProd)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends Heard hear rowForm ownSlots)
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-! ## 1 A length

That the end values' mask entries are as many as the call states is `endRun_length` of
Honest/SumLaw/FitsAt.lean. -/

/-- `hear` hands back a challenge for each variable of the call, Y among them: the law's own word on
these challenges (`sumClaim`) with their number (`varsOf_length`, Honest/SumLaw/FitsAt.lean). -/
theorem heard_r_length {name endName : String} {J : SumJob W X} {c : SumCoins name endName J}
    {t : State W X} {seen : Seen} {ds : List Fmt.Drawn} {rounds : List Fmt.RoundView} {C : Aff}
    {F G : Fork} {h : Heard} (hd : drawsOk (J.callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen ds = some rounds)
    (hh : hear C (J.callAt t.input (frontOf t seen)) F rounds = some (h, G)) :
    h.r.length = (J.callAt t.input (frontOf t seen)).all.length := by
  rw [(sumClaim V W X name endName J c t seen ds rounds C F G h hd ha hh).2.1,
    varsOf_length _ ds hd]

/-! ## 2 A job at large -/

/-- **`SumsTo` at what `hear` hands back and at the part's own mask entries.** e: the call's ends.
-/
theorem k4_sumsTo_heard (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (j : Job)
    (e : Ends)
    (hd : drawsOk ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob sh job)) c t seen ds = some rounds)
    (hh : hear C ((k4SumJob sh job).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hj : job t.input (frontOf t seen) = some j) (hfit : SumShape sh j) (he : sh.ends = some e)
    (hdY : j.dY + 1 < 2 ^ 32) (hn : (j.ends (h.r.take j.cube.n)).length = e.n)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (h.r.take j.cube.n) (maskedEnds (j.ends (h.r.take j.cube.n)) (endRun c) y))
    (hA : ReadsAlike (j.atEnds (h.r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (h.r.take j.cube.n) (j.ends (h.r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (h.r.take j.cube.n))) :
    SumsTo Reading.gl ((k4SumJob sh job).callAt t.input (frontOf t seen)).all
      (jobPoly (k4SumJob sh job) t.input (frontOf t seen) (endRun c)) [] h.r
      (Reading.gl.val j.cube.total)
      (Reading.gl.val (j.atEnds (h.r.take j.cube.n)
        (maskedEnds (j.ends (h.r.take j.cube.n)) (endRun c) (h.r.getD j.cube.n zeroE)))) := by
  have hr : h.r.length = j.cube.n + 1 := by
    rw [heard_r_length hd ha hh, all_some (k4SumJob sh job) _ _ e he, List.length_append,
      withPoints_length, List.length_singleton, hfit.2.1]
    rfl
  exact k4_sumsTo_own sh job t.input (frontOf t seen) j hj hfit hdY (endRun c) h.r hr
    (by rw [hn, endRun_length c e he]) hP hA hE

/-- **What `rowForm` is worth**, in any world that has the part's coins under the sumcheck's own
slots and in which the claimed form is worth the cube's total. -/
theorem k4_rowForm_worth (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (S0 : E)
    (kept : Aff) (Wd : World GE) (j : Job) (e : Ends)
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
    (rowForm h S0 kept).value Reading.gl Wd =
      Reading.gl.val h.eps * (Reading.gl.val S0 + kept.value Reading.gl Wd -
        Reading.gl.val (j.atEnds (h.r.take j.cube.n)
          (maskedEnds (j.ends (h.r.take j.cube.n)) (endRun c) (h.r.getD j.cube.n zeroE)))) := by
  have hS := k4_sumsTo_heard (V := V) name endName sh job c t seen ds rounds C F G h j e hd ha hh hj
    hfit he hdY hn hP hA hE
  rw [← hσ] at hS
  exact rowForm_worth (V := V) name endName (k4SumJob sh job) c t seen ds rounds C F G h S0 kept Wd
    _ hd ha hh hs hS

/-- **What the last running claim reads as.** -/
theorem k4_claim (name endName : String) (sh : Call) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob sh job)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (j : Job)
    (e : Ends)
    (hd : drawsOk ((k4SumJob sh job).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob sh job)) c t seen ds = some rounds)
    (hh : hear C ((k4SumJob sh job).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hj : job t.input (frontOf t seen) = some j) (hfit : SumShape sh j) (he : sh.ends = some e)
    (hdY : j.dY + 1 < 2 ^ 32) (hn : (j.ends (h.r.take j.cube.n)).length = e.n)
    (hP : PolyOn j.dY fun y =>
      j.atEnds (h.r.take j.cube.n) (maskedEnds (j.ends (h.r.take j.cube.n)) (endRun c) y))
    (hA : ReadsAlike (j.atEnds (h.r.take j.cube.n)))
    (hE : Reading.gl.val (j.atEnds (h.r.take j.cube.n) (j.ends (h.r.take j.cube.n))) =
      Reading.gl.val (j.cube.summandAt (h.r.take j.cube.n))) :
    Reading.gl.val h.claim =
      hid (((k4SumJob sh job).callAt t.input (frontOf t seen)).all.map (Var.wt Reading.gl))
          (hidingCoin c) (h.r.map Reading.gl.val) +
        Reading.gl.val h.eps * Reading.gl.val (j.atEnds (h.r.take j.cube.n)
          (maskedEnds (j.ends (h.r.take j.cube.n)) (endRun c) (h.r.getD j.cube.n zeroE))) +
        Reading.gl.val h.eps * (Reading.gl.val h.target - Reading.gl.val j.cube.total) *
          psiProd (((k4SumJob sh job).callAt t.input (frontOf t seen)).all.map
            (Var.wt Reading.gl)) (h.r.map Reading.gl.val) :=
  (sumClaim V W X name endName (k4SumJob sh job) c t seen ds rounds C F G h hd ha hh).2.2 _ _
    (k4_sumsTo_heard (V := V) name endName sh job c t seen ds rounds C F G h j e hd ha hh hj hfit he
      hdY hn hP hA hE)

/-! ## 3 The merge -/

/-- The merge's summand on the masked end value has degree at most 1. -/
theorem mergeJob_poly (lay : OnBytes.Model.WsLay) (w : Nat → Nat → F) (cls : List WsClaim)
    (rho : Array E) (rs m : List E) :
    PolyOn (mergeJobOf lay w cls rho).dY fun y =>
      (mergeJobOf lay w cls rho).atEnds rs (maskedEnds ((mergeJobOf lay w cls rho).ends rs) m y) :=
  PolyOn.head _ m

/-- It reads alike on lists that read alike. -/
theorem mergeJob_alike (lay : OnBytes.Model.WsLay) (w : Nat → Nat → F) (cls : List WsClaim)
    (rho : Array E) (rs : List E) : ReadsAlike ((mergeJobOf lay w cls rho).atEnds rs) :=
  ReadsAlike.head

/-- The merge's masked end value, read. -/
theorem mergeJob_end (lay : OnBytes.Model.WsLay) (w : Nat → Nat → F) (cls : List WsClaim)
    (rho : Array E) (rs m : List E) (hm : m.length = 1) (y : E) :
    Reading.gl.val ((mergeJobOf lay w cls rho).atEnds rs
      (maskedEnds ((mergeJobOf lay w cls rho).ends rs) m y)) =
      Reading.gl.val ((mergeJobOf lay w cls rho).cube.summandAt rs) +
        Reading.gl.val y * Reading.gl.val (m.getD 0 zeroE) := by
  obtain ⟨m0, rfl⟩ : ∃ m0, m = [m0] := List.length_eq_one_iff.mp hm
  show Reading.gl.val (OnBytes.addE ((mergeJobOf lay w cls rho).cube.summandAt rs)
    (OnBytes.mulE y m0)) = _
  rw [Reading.gl.add, Reading.gl.mul]
  rfl

/-- The merge's job in the row of the layers' honest parts (`k4Sorts`, Honest/K4/Part.lean). -/
abbrev mergeSum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4PlainShape Q.P.wsLay.lk 1 1) fun w fr => jobMerge Q w (ptsOf Q w fr.heard)

/-- **What `rowForm` is worth at the merge's sumcheck.** The premises on the job that are left: the
list of claims is made. -/
theorem merge_rowForm_worth (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (t : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard) (S0 : E)
    (kept : Aff) (Wd : World GE) (cls : List WsClaim)
    (hd : drawsOk ((mergeSum Q).callAt t.input (frontOf t seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c t seen ds = some rounds)
    (hh : hear C ((mergeSum Q).callAt t.input (frontOf t seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt t.input (frontOf t seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hc : mergeClaimsAt Q t.input (ptsOf Q t.input t.heard) = some cls)
    (hσ : C.value Reading.gl Wd = Reading.gl.val
      (mergeJobOf Q.P.wsLay t.input.w cls (ptsOf Q t.input t.heard).rhoW).cube.total) :
    (rowForm h S0 kept).value Reading.gl Wd =
      Reading.gl.val h.eps * (Reading.gl.val S0 + kept.value Reading.gl Wd -
        (Reading.gl.val ((mergeJobOf Q.P.wsLay t.input.w cls
            (ptsOf Q t.input t.heard).rhoW).cube.summandAt (h.r.take Q.P.wsLay.lk)) +
          Reading.gl.val (h.r.getD Q.P.wsLay.lk zeroE) *
            Reading.gl.val ((endRun c).getD 0 zeroE))) := by
  have key := k4_rowForm_worth (V := V) name endName (k4PlainShape Q.P.wsLay.lk 1 1)
    (fun w fr => jobMerge Q w (ptsOf Q w fr.heard)) c t seen ds rounds C F G h S0 kept Wd
    (mergeJobOf Q.P.wsLay t.input.w cls (ptsOf Q t.input t.heard).rhoW) ⟨1, 1⟩ hd ha hh hs hσ
    (by show (mergeClaimsAt Q t.input (ptsOf Q t.input t.heard)).map _ = _; rw [hc]; rfl)
    (jobFits_parts (mergeJob_jobFits _ _ _ _)) rfl (by show 1 + 1 < 2 ^ 32; norm_num) rfl
    (mergeJob_poly _ _ _ _ _ _) (mergeJob_alike _ _ _ _ _) rfl
  rw [key, mergeJob_end _ _ _ _ _ _ (endRun_length c ⟨1, 1⟩ rfl)]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.heard_r_length
#print axioms ProofFile.Honest.K4.k4_sumsTo_heard
#print axioms ProofFile.Honest.K4.k4_rowForm_worth
#print axioms ProofFile.Honest.K4.k4_claim
#print axioms ProofFile.Honest.K4.mergeJob_poly
#print axioms ProofFile.Honest.K4.mergeJob_alike
#print axioms ProofFile.Honest.K4.mergeJob_end
#print axioms ProofFile.Honest.K4.merge_rowForm_worth
