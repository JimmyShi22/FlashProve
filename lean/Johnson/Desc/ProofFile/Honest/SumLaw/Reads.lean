-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Reads.lean: THE VERIFIER's READER ON THE ROUNDS OF THE MASKED
SUMCHECK's PART: where the call passes `shapeOk` and the challenges have the counts of the call's
entries (`drawsOk_spec`), `readAll` (Johnson/Desc/Part/MaskedSum4.lean) accepts `sumOut`
(Honest/SumLaw/Out.lean), and what it reads is written out. Definitions that the statements need,
and statements with their proofs.
Main names:
  `canon x`: an element as it is heard once it was said: the words below the prime that are read as
    it. `canon_gl`: the reading `Reading.gl` does not see the difference.
  `scalars_rvSaid`, `roundOf_rvSaid`, `elems_one`: one round.
  `varRounds_varOut`: the variables' rounds: what is read is `sentRounds` (Honest/SumLaw/Walk.lean).
  `entries_draw`, `drawsOk_spec`: what `drawsOk` says of the challenges.
  `readOf`: what is read. `readAll_sumOut`: **under the two premises the reader accepts, and reads
    that.**

Limits. Without `shapeOk` the reader need not accept (a variable with one coefficient). Nothing on a
ledger. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Slice (toE ofE)
open VerifiableInference.Desc.Part.MaskedSum

variable {V W X : Type}

/-- An element as it is heard once it was said. -/
def canon (x : E) : E := E.ofTriple (ofE (toE x.triple))

/-- The reading `Reading.gl` does not see the difference. -/
theorem canon_gl (x : E) : Reading.gl.val (canon x) = Reading.gl.val x := by
  show toE (E.ofTriple (ofE (toE x.triple))).triple = toE x.triple
  rw [E.triple_ofTriple, OnBytes.Slice.toE_ofE]

theorem scalars_rvSaid (d : Fmt.Drawn) : ∀ l : List E,
    scalars (rvSaid l d).vals = some (l.map canon)
  | [] => rfl
  | x :: l => by
    show (scalars (rvSaid l d).vals).map (E.ofTriple (ofE (toE x.triple)) :: ·) = _
    rw [scalars_rvSaid d l]
    rfl

theorem roundOf_rvSaid (l : List E) (d : Fmt.Drawn) (n k : Nat) (hn : l.length = n)
    (hk : d.elems.length = k) :
    roundOf n k (rvSaid l d) = some (l.map canon, d.elems.map E.ofTriple) := by
  unfold roundOf
  rw [scalars_rvSaid]
  show (if (l.map canon).length == n && d.elems.length == k then _ else none) = _
  rw [List.length_map, hn, hk]
  simp
  rfl

theorem elems_one (d : Fmt.Drawn) (h : d.elems.length = 1) :
    d.elems.map E.ofTriple = [elemOf d] := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 h
  unfold elemOf
  rw [hx]
  rfl

/-- **The variables' rounds are read as `sentRounds`.** -/
theorem varRounds_varOut (eps : E) (poly : List E → List E) :
    ∀ (L : List (Var × List E)) (a : E) (past : List E) (ds : List Fmt.Drawn)
      (rest : List Fmt.RoundView), (∀ x ∈ L, 2 ≤ x.1.d) → L.length = ds.length →
      (∀ d ∈ ds, d.elems.length = 1) →
      varRounds (L.map (·.1)) (varOut eps poly L a past ds ++ rest) =
        some (sentRounds canon eps poly L a past (ds.map elemOf), rest)
  | [], a, past, [], rest, _, _, _ => by
    rw [varOut_nil, sentRounds.eq_def]
    rfl
  | (v, w) :: L, a, past, d :: ds, rest, h2, hl, h1 => by
    rw [varOut_cons, List.map_cons, List.map_cons, sentRounds_cons]
    have hv : 2 ≤ v.d := h2 (v, w) List.mem_cons_self
    have hr := roundOf_rvSaid
      (sentOfL v (addL (hAt ((v, w) :: L) [] a) (scaleL eps (poly past)))) d (v.d - 1) 1
      (by
        have := cutOf_length v (padTo v.d (addL (hAt ((v, w) :: L) [] a)
          (scaleL eps (poly past)))) (padTo_length _ _) hv
        rw [sentOfL_eq]
        omega)
      (h1 d List.mem_cons_self)
    rw [elems_one d (h1 d List.mem_cons_self)] at hr
    have ih := varRounds_varOut eps poly L
      (addE (mulE a (psiAt v (elemOf d))) (valueAt w (elemOf d))) (past ++ [elemOf d]) ds rest
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
      (by simp only [List.length_cons] at hl; omega)
      (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
    show (match roundOf (v.d - 1) 1 (rvSaid _ d), varRounds (L.map (·.1)) (_ ++ rest) with
      | some (s, [g]), some (l, rest) => some ((s, g) :: l, rest)
      | _, _ => none) = _
    rw [hr, ih]
  | [], _, _, _ :: _, _, _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, _, [], _, _, hl, _ => by simp only [List.length_cons, List.length_nil] at hl; omega

/-! ## What `drawsOk` says -/

theorem entries_draw (k : Call) :
    (entries k).map (·.drawE) =
      1 :: (List.replicate k.all.length 1 ++
        (match k.ends with
         | none => []
         | some _ => [0])) := by
  unfold entries Call.all
  cases k.ends with
  | none =>
    simp only [List.append_nil, List.map_append, List.map_cons, List.map_nil, List.map_map]
    show 1 :: k.vs.map (fun _ => 1) = _
    rw [List.map_const']
  | some e =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, List.length_append,
      List.length_cons, List.length_nil]
    show 1 :: (k.vs.map (fun _ => 1) ++ [1, 0]) = _
    rw [List.map_const', List.replicate_succ', List.append_assoc]
    rfl

/-- The challenges: the first; the variables', Y's among them; at a call with end values one more.
-/
theorem drawsOk_spec {k : Call} {ds : List Fmt.Drawn} (h : drawsOk k ds = true) :
    ∃ (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn), ds = d0 :: (dv ++ dl) ∧ d0.elems.length = 1 ∧
      dv.length = k.all.length ∧ (∀ d ∈ dv, d.elems.length = 1) ∧
      dl.map (·.elems.length) =
        (match k.ends with
         | none => []
         | some _ => [0]) := by
  unfold drawsOk at h
  have h' := eq_of_beq h
  rw [entries_draw] at h'
  obtain ⟨d0, ds', rfl, h0, h1⟩ := List.map_eq_cons_iff.1 h'
  obtain ⟨dv, dl, rfl, hv, hl⟩ := List.map_eq_append_iff.1 h1
  refine ⟨d0, dv, dl, rfl, h0, ?_, fun d hd => ?_, hl⟩
  · have := congrArg List.length hv
    rw [List.length_map, List.length_replicate] at this
    exact this
  · have hm : d.elems.length ∈ dv.map (·.elems.length) := List.mem_map_of_mem hd
    rw [hv] at hm
    exact List.eq_of_mem_replicate hm

/-! ## The reader -/

/-- What is read of the part's rounds. d0: the first challenge. dv: the variables'. -/
def readOf {name endName : String} (J : SumJob W X) (c : SumCoins name endName J) (t : State W X)
    (seen : Seen) (d0 : Fmt.Drawn) (dv : List Fmt.Drawn) :
        VerifiableInference.Desc.Part.MaskedSum.Read :=
  ⟨canon (tailSum (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c))),
    elemOf d0,
    sentRounds canon (elemOf d0) (jobPoly J t.input (frontOf t seen) (endRun c))
      (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) zeroE []
      (dv.map elemOf),
    match J.shape.ends with
    | none => []
    | some e =>
      (saidEnds J e (J.callAt t.input (frontOf t seen)).all (frontOf t seen) (firstRun c) (endRun c)
        (drawnE (d0 :: dv)) t.input).map canon⟩

theorem firstRound_said (k : Call) (A : List E) (mu : E) (d0 : Fmt.Drawn) (hA : A.length = k.lead)
    (h0 : d0.elems.length = 1) :
    firstRound k (rvSaid (A ++ [mu]) d0) = some (A.map canon, [canon mu], [elemOf d0]) := by
  unfold firstRound
  rw [roundOf_rvSaid (A ++ [mu]) d0 (k.lead + 1) 1 (by rw [List.length_append, hA]; rfl) h0,
    elems_one d0 h0]
  show some (((A ++ [mu]).map canon).take k.lead, ((A ++ [mu]).map canon).drop k.lead, _) = _
  rw [List.map_append, ← hA, ← List.length_map (f := canon) (as := A), List.take_left,
    List.drop_left]
  rfl

/-- Every variable of a call that passes the test on the plan has at least two coefficients. (The
library has the same statement as `two_le_allK`, Johnson/Desc/Part/MaskedSumJoint.lean, which this
folder does not import.) -/
theorem all_two {k : Call} (h : shapeOk k = true) : ∀ v ∈ k.all, 2 ≤ v.d := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | some e => exact two_le_all h
  | none =>
    simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact fun v hv => (h.1 v hv).1

theorem saidFirst_eq (J : SumJob W X) (all : List Var) (fr : Front X) (u m ds : List E) (w : W) :
    saidFirst J all fr u m ds w =
      addL (padTo J.shape.lead (J.lead w fr)) (u.take J.shape.lead) ++
        [tailSum (sharesOf J.shape.lead all u)] := rfl

theorem lead_length (J : SumJob W X) (fr : Front X) (u : List E) (w : W) :
    (addL (padTo J.shape.lead (J.lead w fr)) (u.take J.shape.lead)).length = J.shape.lead := by
  rw [addL_length, padTo_length, List.length_take]
  omega

theorem saidEnds_length (J : SumJob W X) (e : Ends) (all : List Var) (fr : Front X)
    (u m ds : List E) (w : W) : (saidEnds J e all fr u m ds w).length = e.n := by
  show (addL (padTo e.n _) (scaleL _ (padTo e.n _))).length = e.n
  rw [addL_length, padTo_length]
  show max e.n ((padTo e.n _).map _).length = e.n
  rw [List.length_map, padTo_length, Nat.max_self]

/-- **Where the call passes `shapeOk` and the challenges have the counts of the call's entries, the
reader accepts the part's rounds, and reads `readOf`.** -/
theorem readAll_sumOut {name endName : String} (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn)
    (hs : shapeOk (J.callAt t.input (frontOf t seen)) = true) (h0 : d0.elems.length = 1)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length)
    (h1 : ∀ d ∈ dv, d.elems.length = 1)
    (hl : dl.map (·.elems.length) =
      (match (J.callAt t.input (frontOf t seen)).ends with
       | none => []
       | some _ => [0])) :
    readAll (J.callAt t.input (frontOf t seen)) (sumOut J c t seen (d0 :: (dv ++ dl))) =
      some (readOf J c t seen d0 dv) := by
  have htake : (dv ++ dl).take (J.callAt t.input (frontOf t seen)).all.length = dv := by
    rw [← hv, List.take_left]
  have hdrop : (dv ++ dl).drop (J.callAt t.input (frontOf t seen)).all.length = dl := by
    rw [← hv, List.drop_left]
  have hfirst := firstRound_said (J.callAt t.input (frontOf t seen))
    (addL (padTo J.shape.lead (J.lead t.input (frontOf t seen))) ((firstRun c).take J.shape.lead))
    (tailSum (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c))) d0
    (lead_length J _ _ _) h0
  have hvars := fun rest => varRounds_varOut (elemOf d0)
    (jobPoly J t.input (frontOf t seen) (endRun c))
    (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) zeroE [] dv rest
    (fun x hx => (wOf_sizes _ _ (all_two hs) x hx).1) (by rw [sharesOf_length, hv]) h1
  rw [sharesOf_fst] at hvars
  simp only [sumOut, readOf]
  rw [htake, hdrop, saidFirst_eq]
  have hends : (J.callAt t.input (frontOf t seen)).ends = J.shape.ends := rfl
  rw [hends] at hl
  cases he : J.shape.ends with
  | none =>
    rw [he] at hl
    have hdl : dl = [] := List.map_eq_nil_iff.1 hl
    rw [hdl]
    unfold readAll
    simp only [hfirst, hvars, hends, he]
  | some e =>
    rw [he] at hl
    obtain ⟨d, dl', rfl, hd, hdl'⟩ := List.map_eq_cons_iff.1 hl
    have hnil : dl' = [] := List.map_eq_nil_iff.1 hdl'
    subst hnil
    have hlast := roundOf_rvSaid (saidEnds J e (J.callAt t.input (frontOf t seen)).all
      (frontOf t seen) (firstRun c) (endRun c) (drawnE (d0 :: dv)) t.input) d e.n 0
      (saidEnds_length _ _ _ _ _ _ _ _) hd
    unfold readAll
    simp only [hfirst, hvars, hends, he, hlast, Option.map_some]

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.canon_gl
#print axioms ProofFile.Honest.SumLaw.scalars_rvSaid
#print axioms ProofFile.Honest.SumLaw.roundOf_rvSaid
#print axioms ProofFile.Honest.SumLaw.elems_one
#print axioms ProofFile.Honest.SumLaw.varRounds_varOut
#print axioms ProofFile.Honest.SumLaw.entries_draw
#print axioms ProofFile.Honest.SumLaw.drawsOk_spec
#print axioms ProofFile.Honest.SumLaw.firstRound_said
#print axioms ProofFile.Honest.SumLaw.all_two
#print axioms ProofFile.Honest.SumLaw.saidFirst_eq
#print axioms ProofFile.Honest.SumLaw.lead_length
#print axioms ProofFile.Honest.SumLaw.saidEnds_length
#print axioms ProofFile.Honest.SumLaw.readAll_sumOut
#print axioms ProofFile.Honest.SumLaw.canon
#print axioms ProofFile.Honest.SumLaw.readOf
