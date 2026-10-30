-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/LawEnds.lean: THE LAW OF THE MASKED SUMCHECK's HONEST PART, FOR
EVERY CALL OF THE VERIFIER's FIRST TEXT: the proofs of three of the seven statements of
Honest/SumLaw/Statement.lean: `SumFirst`, `SumLast`, `SumEnds`: the first message, the last message,
and what lies under the end values' slots (over the library's `ledger_ends`,
Johnson/Desc/Part/MaskedSumLedger.lean). Statements with their proofs.
Main names:
  `aloneFrom_length`: moves that were played alone had as many challenges as moves.
  `take_getD`, `drawn_vars`, `all_pos`: tools.
  `lead_reads`, `ends_reads`: a scalar of the first message; of the last.
  `sumFirst`, `sumLast`, `sumEnds`: **the three.**

Limits. Those of Honest/SumLaw/Statement.lean. Nothing on soundness or on any property of a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part.MaskedSum

variable {V W X : Type}

/-- Moves that were played alone had as many challenges as moves. -/
theorem aloneFrom_length {C : Type} (c : C) : ∀ (mvs : List (Move C W X)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (out : List Fmt.RoundView),
    aloneFrom c mvs t seen ds = some out → ds.length = mvs.length
  | [], _, _, [], _, _ => rfl
  | mv :: mvs, t, seen, d :: ds, out, h => by
    cases hs : mv.say c seen t with
    | error e =>
      simp only [aloneFrom, hs] at h
      cases h
    | ok x =>
      simp only [aloneFrom, hs, Option.map_eq_some_iff] at h
      obtain ⟨out', h', _⟩ := h
      rw [List.length_cons, List.length_cons, aloneFrom_length c mvs _ _ ds out' h']
  | [], _, _, _ :: _, _, h => by simp [aloneFrom] at h
  | _ :: _, _, _, [], _, h => by simp [aloneFrom] at h

/-- A member of a list's first n. -/
theorem take_getD (u : List E) (n i : Nat) (h : i < n) :
    (u.take n).getD i zeroE = u.getD i zeroE := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos h]

/-- A scalar of the first message, read. -/
theorem lead_reads (J : SumJob W X) (all : List Var) (fr : Front X) (u m ds : List E) (w : W)
    (i : Nat) (hi : i < J.shape.lead) :
    Reading.gl.val (((saidFirst J all fr u m ds w).map canon).getD i zeroE) =
      Reading.gl.val ((J.lead w fr).getD i zeroE) + Reading.gl.val (u.getD i zeroE) := by
  rw [map_getD Reading.gl canon canon_gl, saidFirst_eq, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [lead_length]; exact hi), ← List.getD_eq_getElem?_getD,
    addL_getD, padTo_getD, if_pos hi, take_getD u _ i hi]

/-- A scalar of the last message, read. -/
theorem ends_reads (J : SumJob W X) (e : Ends) (all : List Var) (fr : Front X) (u m ds : List E)
    (w : W) (j : Nat) (hj : j < e.n) :
    Reading.gl.val (((saidEnds J e all fr u m ds w).map canon).getD j zeroE) =
      Reading.gl.val ((J.ends w fr ((ds.drop 1).take J.shape.vs.length)).getD j zeroE) +
        Reading.gl.val (ds.getLastD zeroE) * Reading.gl.val (m.getD j zeroE) := by
  rw [map_getD Reading.gl canon canon_gl]
  show Reading.gl.val ((addL (padTo e.n _) (scaleL _ (padTo e.n m))).getD j zeroE) = _
  rw [addL_getD, scaleL_getD, padTo_getD, padTo_getD, if_pos hj, if_pos hj]

/-- The first message's scalars: the proof of `SumFirst`. -/
theorem sumFirst : SumFirst := by
  intro V W X name endName J c t seen ds rounds ha
  have hl : ds.length = (sumGs name endName J).length := by
    have := aloneFrom_length (C := SumCoins name endName J) c
      (sumPart (V := V) name endName J).moves t seen ds rounds ha
    rw [this, sumPart_moves, List.length_map]
  rw [alone_sumPart name endName J c t seen ds hl] at ha
  have hr : rounds = sumOut J c t seen ds := (Option.some.inj ha).symm
  cases ds with
  | nil =>
    rw [sumGs_length name endName J t.input (frontOf t seen)] at hl
    simp only [List.length_nil] at hl
    omega
  | cons d0 ds =>
    refine ⟨rvSaid (saidFirst J (J.callAt t.input (frontOf t seen)).all (frontOf t seen)
      (firstRun c) (endRun c) [] t.input) d0, (sumOut J c t seen (d0 :: ds)).tail, _,
      by rw [hr]; rfl, scalars_rvSaid d0 _, ?_, fun i hi => ?_⟩
    · rw [List.length_map, saidFirst_eq, List.length_append, lead_length]
      rfl
    · exact lead_reads J _ _ _ _ _ _ i hi

/-- The challenges of the last message's formula are the run's. -/
theorem drawn_vars (k : Call) (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn)
    (hv : dv.length = k.all.length) (hpos : 0 < dv.length) (n : Nat) :
    ((drawnE (d0 :: dv)).drop 1).take n = (varsOf k (d0 :: (dv ++ dl))).take n ∧
      (drawnE (d0 :: dv)).getLastD zeroE = (varsOf k (d0 :: (dv ++ dl))).getLastD zeroE := by
  rw [varsOf_cons k d0 dv dl hv]
  refine ⟨rfl, ?_⟩
  show (elemOf d0 :: dv.map elemOf).getLastD zeroE = _
  cases dv with
  | nil => simp only [List.length_nil] at hpos; omega
  | cons d dv => rfl

/-- A call with end values has a variable: Y. -/
theorem all_pos (J : SumJob W X) (w : W) (fr : Front X) (e : Ends) (he : J.shape.ends = some e) :
    0 < (J.callAt w fr).all.length := by
  rw [all_some J w fr e he, List.length_append]
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_left _ _)

/-- The last message's scalars: the proof of `SumLast`. -/
theorem sumLast : SumLast := by
  intro V W X name endName J c t seen ds rounds e he hd ha
  have hr := rounds_eq hd ha
  obtain ⟨d0, dv, dl, rfl, _, hv, _, hl⟩ := drawsOk_spec hd
  have hends : (J.callAt t.input (frontOf t seen)).ends = J.shape.ends := rfl
  rw [hends, he] at hl
  obtain ⟨d, dl', rfl, _, hdl'⟩ := List.map_eq_cons_iff.1 hl
  have hnil : dl' = [] := List.map_eq_nil_iff.1 hdl'
  subst hnil
  have htake : (dv ++ [d]).take (J.callAt t.input (frontOf t seen)).all.length = dv := by
    rw [← hv, List.take_left]
  have hdrop : (dv ++ [d]).drop (J.callAt t.input (frontOf t seen)).all.length = [d] := by
    rw [← hv, List.drop_left]
  have hpos : 0 < dv.length := by rw [hv]; exact all_pos J _ _ e he
  obtain ⟨e1, e2⟩ := drawn_vars (J.callAt t.input (frontOf t seen)) d0 dv [d] hv hpos
    J.shape.vs.length
  refine ⟨rvSaid (saidEnds J e (J.callAt t.input (frontOf t seen)).all (frontOf t seen) (firstRun c)
    (endRun c) (drawnE (d0 :: dv)) t.input) d, _, ?_, scalars_rvSaid d _, ?_, fun j hj => ?_⟩
  · rw [hr]
    simp only [sumOut]
    rw [htake, hdrop]
    simp only [he]
    rw [← List.cons_append, List.getLast?_append]
    rfl
  · rw [List.length_map, saidEnds_length]
  · rw [ends_reads J e _ _ _ _ _ _ j hj, e1, e2]

/-- What lies under the end values' slots: the proof of `SumEnds`. -/
theorem sumEnds : SumEnds := by
  intro V W X name endName J c t seen ds C F G H rounds h e mask entry he hF hd ha hh hl j hj hm
  have hk : J.callAt t.input (frontOf t seen) =
      ⟨J.shape.lead, withPoints J.shape.vs (J.points t.input (frontOf t seen)), some e⟩ := by
    show (⟨J.shape.lead, _, J.shape.ends⟩ : Call) = _
    rw [he]
  obtain ⟨d0, dv, dl, T, hds, hv, hs, hR, hh'⟩ := heard_spec hd ha hh
  have hpos : 0 < dv.length := by rw [hv]; exact all_pos J _ _ e he
  have hsEnd : h.sEnd = F.next + ownSlots (J.callAt t.input (frontOf t seen)).all := by rw [hh']
  have hrr : h.r = dv.map elemOf := by rw [hh']
  have hh2 := hh
  have hR2 := hR
  rw [hk] at hh2 hR2
  have key := ledger_ends Reading.gl mask entry hF hh2 hR2 hl j hj
  rw [← hk, ← hsEnd, hm] at key
  rw [key, hrr]
  have hvals : (readOf J c t seen d0 dv).values =
      (saidEnds J e (J.callAt t.input (frontOf t seen)).all (frontOf t seen) (firstRun c) (endRun c)
        (drawnE (d0 :: dv)) t.input).map canon := by
    simp only [readOf, he]
  obtain ⟨e1, e2⟩ := drawn_vars (J.callAt t.input (frontOf t seen)) d0 dv dl hv hpos
    J.shape.vs.length
  rw [hvals, ends_reads J e _ _ _ _ _ _ j hj, e1, e2, hds, varsOf_cons _ d0 dv dl hv]
  ring

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.aloneFrom_length
#print axioms ProofFile.Honest.SumLaw.take_getD
#print axioms ProofFile.Honest.SumLaw.lead_reads
#print axioms ProofFile.Honest.SumLaw.ends_reads
#print axioms ProofFile.Honest.SumLaw.drawn_vars
#print axioms ProofFile.Honest.SumLaw.all_pos
#print axioms ProofFile.Honest.SumLaw.sumFirst
#print axioms ProofFile.Honest.SumLaw.sumLast
#print axioms ProofFile.Honest.SumLaw.sumEnds
