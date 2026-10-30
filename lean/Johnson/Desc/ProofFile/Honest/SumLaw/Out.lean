-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Out.lean: THE ROUNDS OF THE MASKED SUMCHECK's PART, WRITTEN
OUT: played alone (`alone`, Terms.lean of this folder) at as many challenges as it has moves,
`sumPart` (Honest/Sum.lean) says `sumOut`: the first message; the variables' rounds, by the walk of
Honest/SumLaw/Said.lean (`varOut`), Y's among them; at a call with end values, their message.
Definitions that the statements need, and statements with their proofs. Nothing here is part of a
prover.
Main names:
  `withPoints_length`, `all_none`, `all_some`: the call's variables as they stand in a run.
  `gAtOf`, `gAtOf_says`: what the move of the variable number i says, Y's too, in one form.
  `sumOut J c t seen ds`: **the rounds.** `varOut_length`: the walk yields one round for each
    challenge, while variables are left.
  `sumGs_length`, `outOf_sumGs`, `alone_sumPart`: **played alone, the part says them.**
  `state_sumPart`: the state behind the part: it has heard the challenges; nothing else turns.

Limits. The challenges are as many as the part's moves: a premise. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open VerifiableInference.Desc.Part.MaskedSum

variable {V W X : Type}

/-! ## The call's variables -/

theorem withPoints_length : ∀ (vs : List Var) (zs : List E), (withPoints vs zs).length = vs.length
  | [], _ => rfl
  | .plain _ :: vs, zs => congrArg (· + 1) (withPoints_length vs zs)
  | .point _ _ :: vs, _ :: zs => congrArg (· + 1) (withPoints_length vs zs)
  | .point _ _ :: vs, [] => congrArg (· + 1) (withPoints_length vs [])

theorem all_none (J : SumJob W X) (w : W) (fr : Front X) (h : J.shape.ends = none) :
    (J.callAt w fr).all = withPoints J.shape.vs (J.points w fr) := by
  unfold Call.all SumJob.callAt
  simp only [h]

theorem all_some (J : SumJob W X) (w : W) (fr : Front X) (e : Ends) (h : J.shape.ends = some e) :
    (J.callAt w fr).all =
      withPoints J.shape.vs (J.points w fr) ++ [.point zeroE (e.dY + 1)] := by
  unfold Call.all SumJob.callAt
  simp only [h]

theorem sharesOf_length (lead : Nat) (all : List Var) (u : List E) :
    (sharesOf lead all u).length = all.length := by
  unfold sharesOf
  rw [List.length_zip, wOf_length, Nat.min_self]

theorem sharesOf_fst (lead : Nat) (all : List Var) (u : List E) :
    (sharesOf lead all u).map (·.1) = all := by
  unfold sharesOf
  exact List.map_fst_zip (Nat.le_of_eq (wOf_length all _).symm)

/-! ## What the variables' moves say, in one form -/

/-- What the move of the variable number i says; Y has the number of the shape's variables. Beyond
the call's variables its value is no move's of that number. -/
def gAtOf (name endName : String) (J : SumJob W X) (c : SumCoins name endName J) (i : Nat) :
    Seen → State W X → List E :=
  if i < J.shape.vs.length then askG name endName J (saidVar J i) (i + 1) c
  else
    match J.shape.ends with
    | some e => askG name endName J (saidY J e) (J.shape.vs.length + 1) c
    | none => fun _ _ => []

theorem gAtOf_says (name endName : String) (J : SumJob W X) (c : SumCoins name endName J) (w : W)
    (H : List Fmt.Drawn) (x0 : X) (S : Seen) (i : Nat) (own : List Fmt.Drawn)
    (shown : List Fmt.RoundView) (hi : i < (J.callAt w ⟨H, x0, S⟩).all.length)
    (ho : own.length = i + 1) (hs : shown.length = i + 1) :
    gAtOf name endName J c i (S.plus shown) ⟨w, H ++ own, x0⟩ =
      sentOfL ((J.callAt w ⟨H, x0, S⟩).all.getD i (.plain 0))
        (addL (hAt (sharesOf J.shape.lead (J.callAt w ⟨H, x0, S⟩).all (firstRun c))
            ((drawnE own).drop 1) zeroE)
          (scaleL ((drawnE own).headD zeroE)
            (jobPoly J w ⟨H, x0, S⟩ (endRun c) ((drawnE own).drop 1)))) := by
  have hlen : ((drawnE own).drop 1).length = i := by
    rw [List.length_drop, drawnE_eq, List.length_map, ho]
    rfl
  unfold gAtOf jobPoly
  rw [hlen]
  by_cases hv : i < J.shape.vs.length
  · rw [if_pos hv, if_pos hv, askG_at name endName J _ (i + 1) c w H own x0 S shown ho hs]
    rfl
  · rw [if_neg hv, if_neg hv]
    cases he : J.shape.ends with
    | none =>
      rw [all_none J w _ he, withPoints_length] at hi
      exact absurd hi hv
    | some e =>
      rw [all_some J w _ e he, List.length_append, withPoints_length] at hi
      have hi' : i = J.shape.vs.length := by
        simp only [List.length_cons, List.length_nil] at hi
        omega
      show askG name endName J (saidY J e) (J.shape.vs.length + 1) c (S.plus shown)
        ⟨w, H ++ own, x0⟩ = _
      rw [askG_at name endName J _ (J.shape.vs.length + 1) c w H own x0 S shown (by rw [ho, hi'])
        (by rw [hs, hi'])]
      have eg : (J.callAt w ⟨H, x0, S⟩).all.getD i (.plain 0) = .point zeroE (e.dY + 1) := by
        rw [all_some J w _ e he, hi', List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [withPoints_length]), withPoints_length,
          Nat.sub_self]
        rfl
      rw [eg]
      rfl

/-! ## The rounds -/

/-- **The part's rounds, written out**, at as many challenges as the part has moves; at another
number it yields a list that the part does not say (`alone` yields nothing there). -/
def sumOut {name endName : String} (J : SumJob W X) (c : SumCoins name endName J) (t : State W X)
    (seen : Seen) : List Fmt.Drawn → List Fmt.RoundView
  | [] => []
  | d0 :: ds =>
    rvSaid (saidFirst J (J.callAt t.input (frontOf t seen)).all (frontOf t seen) (firstRun c)
        (endRun c) [] t.input) d0 ::
      (varOut (elemOf d0) (jobPoly J t.input (frontOf t seen) (endRun c))
          (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) zeroE []
          (ds.take (J.callAt t.input (frontOf t seen)).all.length) ++
        (match J.shape.ends, ds.drop (J.callAt t.input (frontOf t seen)).all.length with
         | some e, dl :: _ =>
           [rvSaid (saidEnds J e (J.callAt t.input (frontOf t seen)).all (frontOf t seen)
             (firstRun c) (endRun c)
             (drawnE (d0 :: ds.take (J.callAt t.input (frontOf t seen)).all.length)) t.input) dl]
         | _, _ => []))

theorem sumGs_length (name endName : String) (J : SumJob W X) (w : W) (fr : Front X) :
    (sumGs name endName J).length =
      1 + (J.callAt w fr).all.length + (if J.shape.ends.isSome then 1 else 0) := by
  unfold sumGs
  cases he : J.shape.ends with
  | none =>
    rw [all_none J w fr he, withPoints_length]
    simp
    omega
  | some e =>
    rw [all_some J w fr e he]
    simp [withPoints_length]
    omega

/-- The variables' moves, as one list by number, at a call without end values. -/
theorem vars_none (name endName : String) (J : SumJob W X) (c : SumCoins name endName J) :
    ((List.range J.shape.vs.length).map fun i => askG name endName J (saidVar J i) (i + 1) c) =
      (List.range' 0 J.shape.vs.length).map (gAtOf name endName J c) := by
  rw [← List.range_eq_range']
  refine List.map_congr_left fun i hi => ?_
  unfold gAtOf
  rw [if_pos (List.mem_range.1 hi)]

/-- The variables' moves, Y's among them, as one list by number. -/
theorem vars_some (name endName : String) (J : SumJob W X) (c : SumCoins name endName J) (e : Ends)
    (he : J.shape.ends = some e) :
    ((List.range J.shape.vs.length).map fun i => askG name endName J (saidVar J i) (i + 1) c) ++
        [askG name endName J (saidY J e) (J.shape.vs.length + 1) c] =
      (List.range' 0 (J.shape.vs.length + 1)).map (gAtOf name endName J c) := by
  rw [vars_none, ← List.range_eq_range', ← List.range_eq_range', List.range_succ,
    List.map_append]
  congr 1
  show _ = [gAtOf name endName J c J.shape.vs.length]
  unfold gAtOf
  rw [if_neg (Nat.lt_irrefl _)]
  simp only [he]

/-- The walk yields one round for each challenge, while variables are left. -/
theorem varOut_length (eps : E) (poly : List E → List E) : ∀ (L : List (Var × List E)) (a : E)
    (past : List E) (ds : List Fmt.Drawn), ds.length ≤ L.length →
    (varOut eps poly L a past ds).length = ds.length
  | L, a, past, [], _ => by
    rw [varOut_nil]
    rfl
  | (v, w) :: L, a, past, d :: ds, h => by
    rw [varOut_cons, List.length_cons, List.length_cons,
      varOut_length eps poly L _ _ ds (by simp only [List.length_cons] at h; omega)]
  | [], _, _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- The variables' rounds, from the state behind the first challenge. r0: the first round. -/
theorem outOf_gAt (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (r0 : Fmt.RoundView) (d0 : Fmt.Drawn) (ds : List Fmt.Drawn)
    (hl : ds.length = (J.callAt t.input (frontOf t seen)).all.length) :
    outOf
        ((List.range' 0 (J.callAt t.input (frontOf t seen)).all.length).map
          (gAtOf name endName J c))
        (t.hears d0) (seen.plus [r0]) ds =
      varOut (elemOf d0) (jobPoly J t.input (frontOf t seen) (endRun c))
        (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) zeroE []
        ds := by
  refine outOf_vars (gAtOf name endName J c) t.input t.heard t.own seen
    (J.callAt t.input (frontOf t seen)).all
    (sharesOf J.shape.lead (J.callAt t.input (frontOf t seen)).all (firstRun c)) (elemOf d0)
    (jobPoly J t.input (frontOf t seen) (endRun c)) (J.callAt t.input (frontOf t seen)).all.length
    (fun i own shown hi ho hs =>
      gAtOf_says name endName J c t.input t.heard t.own seen i own shown hi ho hs)
    (J.callAt t.input (frontOf t seen)).all.length 0 _ zeroE [] [d0] ds [r0] rfl rfl rfl
    (by omega) hl (by rw [sharesOf_length]) (fun x => rfl) (fun j _ => ?_)
  rw [sharesOf_fst, Nat.zero_add]

/-- **What such moves say is `sumOut`.** -/
theorem outOf_sumGs (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn)
    (hl : ds.length = (sumGs name endName J).length) :
    outOf ((sumGs name endName J).map (· c)) t seen ds = sumOut J c t seen ds := by
  rw [sumGs_length name endName J t.input (frontOf t seen)] at hl
  cases ds with
  | nil =>
    simp only [List.length_nil] at hl
    omega
  | cons d0 ds =>
    have h0 : askG name endName J (saidFirst J) 0 c seen t =
        saidFirst J (J.callAt t.input (frontOf t seen)).all (frontOf t seen) (firstRun c) (endRun c)
            []
          t.input := by
      have := askG_at name endName J (saidFirst J) 0 c t.input t.heard [] t.own seen [] rfl rfl
      rw [Seen.plus_nil, List.append_nil] at this
      exact this
    unfold sumGs
    rw [List.map_append, List.map_append, List.map_map, List.append_assoc]
    show rvSaid (askG name endName J (saidFirst J) 0 c seen t) d0 ::
      outOf _ (t.hears d0) (seen.plus [rvSaid (askG name endName J (saidFirst J) 0 c seen t) d0]) ds
      = _
    rw [h0]
    show _ = rvSaid _ d0 :: _
    congr 1
    cases he : J.shape.ends with
    | none =>
      simp only [he, Option.isSome_none, List.length_cons] at hl
      have hl' : ds.length = (J.callAt t.input (frontOf t seen)).all.length := by
        simp at hl
        omega
      have ev := vars_none name endName J c
      have ea : (J.callAt t.input (frontOf t seen)).all.length = J.shape.vs.length := by
        rw [all_none J _ _ he, withPoints_length]
      show outOf (((List.range J.shape.vs.length).map fun i =>
          askG name endName J (saidVar J i) (i + 1) c) ++ []) (t.hears d0) (seen.plus [_]) ds = _
      rw [List.append_nil, ev, ← ea, outOf_gAt name endName J c t seen _ d0 ds hl',
        List.take_of_length_le (Nat.le_of_eq hl')]
      simp
    | some e =>
      simp only [he, Option.isSome_some, List.length_cons] at hl
      have hl' : ds.length = (J.callAt t.input (frontOf t seen)).all.length + 1 := by
        simp at hl
        omega
      have ev := vars_some name endName J c e he
      have ea : (J.callAt t.input (frontOf t seen)).all.length = J.shape.vs.length + 1 := by
        rw [all_some J _ _ e he, List.length_append, withPoints_length]
        rfl
      obtain ⟨dl, hdl⟩ : ∃ dl, ds.drop (J.callAt t.input (frontOf t seen)).all.length = [dl] := by
        have : (ds.drop (J.callAt t.input (frontOf t seen)).all.length).length = 1 := by
          rw [List.length_drop, hl']
          omega
        exact List.length_eq_one_iff.1 this
      have hsplit : ds = ds.take (J.callAt t.input (frontOf t seen)).all.length ++ [dl] := by
        rw [← hdl, List.take_append_drop]
      have htl : (ds.take (J.callAt t.input (frontOf t seen)).all.length).length =
          (J.callAt t.input (frontOf t seen)).all.length := by
        rw [List.length_take, hl']
        omega
      show outOf (((List.range J.shape.vs.length).map fun i =>
          askG name endName J (saidVar J i) (i + 1) c) ++
            [askG name endName J (saidY J e) (J.shape.vs.length + 1) c,
              askG name endName J (saidEnds J e) (J.shape.vs.length + 2) c]) (t.hears d0)
        (seen.plus [_]) ds = _
      have eapp : ((List.range J.shape.vs.length).map fun i =>
          askG name endName J (saidVar J i) (i + 1) c) ++
            [askG name endName J (saidY J e) (J.shape.vs.length + 1) c,
              askG name endName J (saidEnds J e) (J.shape.vs.length + 2) c] =
          (((List.range J.shape.vs.length).map fun i =>
            askG name endName J (saidVar J i) (i + 1) c) ++
              [askG name endName J (saidY J e) (J.shape.vs.length + 1) c]) ++
            [askG name endName J (saidEnds J e) (J.shape.vs.length + 2) c] := by
        rw [List.append_assoc]
        rfl
      rw [eapp, ev, ← ea, hdl]
      conv_lhs => rw [hsplit]
      rw [outOf_append _ _ _ _ _ _ (by rw [List.length_map, List.length_range', htl]),
        outOf_gAt name endName J c t seen _ d0 _ htl]
      congr 1
      show [rvSaid (askG name endName J (saidEnds J e) (J.shape.vs.length + 2) c
        ((seen.plus [_]).plus _)
        ⟨t.input, (t.heard ++ [d0]) ++ ds.take (J.callAt t.input (frontOf t seen)).all.length,
          t.own⟩) dl] = _
      rw [Seen.plus_plus, List.append_assoc,
        askG_at name endName J _ (J.shape.vs.length + 2) c t.input t.heard
        ([d0] ++ ds.take (J.callAt t.input (frontOf t seen)).all.length) t.own seen _
        (by rw [List.length_append, htl, ea]; simp; omega)
        (by
          rw [List.length_append, varOut_length _ _ _ _ _ _ (by rw [sharesOf_length, htl]), htl,
            ea]
          simp
          omega)]
      rfl

/-- **Played alone, the part says these rounds.** -/
theorem alone_sumPart (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn)
    (hl : ds.length = (sumGs name endName J).length) :
    alone (sumPart (V := V) name endName J) c t seen ds = some (sumOut J c t seen ds) := by
  show aloneFrom (C := SumCoins name endName J) c (sumPart (V := V) name endName J).moves t seen ds
    = _
  rw [sumPart_moves, aloneFrom_mvOf c _ t seen ds hl.symm, outOf_sumGs name endName J c t seen ds
      hl]

/-- The state behind the part. -/
theorem state_sumPart (name endName : String) (J : SumJob W X) (t : State W X)
    (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length) :
    stateFrom (sumPart (V := V) name endName J).moves t ds = ⟨t.input, t.heard ++ ds, t.own⟩ := by
  show stateFrom (C := SumCoins name endName J) (sumPart (V := V) name endName J).moves t ds = _
  rw [sumPart_moves]
  exact stateFrom_mvOf _ t ds hl.symm

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.withPoints_length
#print axioms ProofFile.Honest.SumLaw.all_none
#print axioms ProofFile.Honest.SumLaw.all_some
#print axioms ProofFile.Honest.SumLaw.sharesOf_length
#print axioms ProofFile.Honest.SumLaw.sharesOf_fst
#print axioms ProofFile.Honest.SumLaw.gAtOf_says
#print axioms ProofFile.Honest.SumLaw.sumGs_length
#print axioms ProofFile.Honest.SumLaw.vars_none
#print axioms ProofFile.Honest.SumLaw.vars_some
#print axioms ProofFile.Honest.SumLaw.varOut_length
#print axioms ProofFile.Honest.SumLaw.outOf_gAt
#print axioms ProofFile.Honest.SumLaw.outOf_sumGs
#print axioms ProofFile.Honest.SumLaw.alone_sumPart
#print axioms ProofFile.Honest.SumLaw.state_sumPart
#print axioms ProofFile.Honest.SumLaw.gAtOf
#print axioms ProofFile.Honest.SumLaw.sumOut
