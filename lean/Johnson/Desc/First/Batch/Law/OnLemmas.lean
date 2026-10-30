-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/OnLemmas.lean
(kind K9, for the table of joints): THEOREMS: THE TWO PROMISES AT K9's BORDERS
(k9OnA, k9OnB: Law/Borders.lean: two tests with code on the record S) AGAINST K9's OWN TEXTS.
  drawnClean_tests  what a yes of the draw's eight tests says of the part in front, and three flags
                    of what it lays.
  onA_of_draw       **a yes of the draw's decision gives k9OnA at the record IN FRONT**: the draw's
                    own tests are the promise's seven clauses.
  onB_behind_draw   behind that yes: the draw has run, chi is drawn, AND THE MARK "the one equation
                    has been made" (doorShutF) IS AS IT WAS IN FRONT: k9OnB behind = not that mark
                    in front. THE DRAW DOES NOT TOUCH THE MARK AND NO TEST OF THE DRAW ASKS IT: SO
                    k9OnB BEHIND THE DRAW CANNOT BE HAD FROM THE DRAW's YES ALONE. (No verdict hangs
                    on it: an adding refuses at a set mark. No proof of K9's law spends k9OnB.)
  drawnClean_marks, marks_behind_draw   **behind a yes of the draw there is a mark**: one for each
                    number of the plan, and the plan's number is not 0. addList_marks: K9's own
                    adding keeps the number of marks. A RUN OR A QUIET STEP BETWEEN MUST KEEP THE
                    MARKS TOO: NOTHING HERE ASKS IT: the ledger's "core" (Law/Stages.lean) holds the
                    sums, chi, the count and the plan's number, NOT the marks: the law on soundness
                    starts from a yes and does not need them. (Who reads them: the door's test
                    "K9.weights-all-taken", and the tail's count of the weights.)
  addOne_flags, addList_flags   K9's own adding (Batch/Add.lean) keeps both flags; AND A YES OF AN
                    ADDING OF A LIST THAT IS NOT EMPTY GIVES THEM: chi is drawn, the mark is not
                    set, in front and behind.
  onB_adds          so k9OnB holds behind the writing of an adding of a list that is not empty,
                    where the draw has run; and an adding keeps k9OnB.
  equation_shut, onB_behind_door   behind a yes of the one equation's block k9OnB is false: the
                    equation sets the mark.
HOW "on" IS MET AT REAL RECORDS: by these lemmas and by rides, not by a theorem on a real file:
where a ride's honest run says yes at K9's draw, k9OnA held in front of it.

-/
import Johnson.Desc.First.Batch.Law.Borders
import Johnson.Desc.First.Batch.Law.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where drawAlone drawnClean drawn ledgerEmpty equation door
  weightNext addForm addRuns addOne addList)
open VerifiableInference.Desc.First (S)

/-- What a yes of the draw's tests says. -/
theorem drawnClean_tests (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    owed.isNone = true ∧ L.handed = false ∧ F.thetaDrawnF = false ∧ F.planClaimsF ≠ 0 ∧
      ledgerEmpty F = true ∧ F.nClaim = 0 ∧ F.LS.size = F.ns ∧
      o.L.handed = true ∧ o.F.thetaDrawnF = true ∧ o.F.doorShutF = F.doorShutF := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, he, h⟩ := ok_bind h
  obtain ⟨_, hn, h⟩ := ok_bind h
  obtain ⟨_, hz, h⟩ := ok_bind h
  have e : o' = o := Except.ok.inj h
  subst e
  unfold drawn at ho
  obtain ⟨_, t1, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, t3, ho⟩ := ok_bind ho
  obtain ⟨_, t4, ho⟩ := ok_bind ho
  obtain ⟨_, t5, ho⟩ := ok_bind ho
  have eo := Except.ok.inj ho
  have u3 := need_ok t3
  have u4 := need_ok t4
  have u5 := need_ok t5
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at u3 u4 u5
  refine ⟨need_ok t1, u3.1.2, u4, u5, need_ok he, by simpa using need_ok hn,
    by simpa using need_ok hz, ?_, ?_, ?_⟩
  all_goals rw [← eo]
  all_goals rfl

/-- The marks that the draw lays: one for each number of the plan; the plan's number is not 0. -/
theorem drawnClean_marks (rows : Nat) (chi : E) (owed : Option Nat) (used : Nat) (L : LinkCtx)
    (F : Fork) (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    o.F.kapMapF.size = o.F.planClaimsF ∧ o.F.planClaimsF ≠ 0 := by
  have h4 := (drawnClean_tests _ _ _ _ _ _ _ h).2.2.2.1
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  have e : o' = o := Except.ok.inj h
  subst e
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact ⟨Array.size_replicate, h4⟩

/-- **Behind a yes of the draw there is a mark**: one for each number of the plan, not 0. -/
theorem marks_behind_draw {Cl : Type} (p : Where) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : S)
    (h : (drawAlone (Cl := Cl) atS p).decide s rs gs = .ok s') :
    ∃ b, atS.get? s' = some b ∧ b.F.kapMapF.size = b.F.planClaimsF ∧ b.F.planClaimsF ≠ 0 ∧
      b.F.kapMapF.isEmpty = false := by
  obtain ⟨a, chi, o, ha, ho, rfl⟩ := drawAlone_decide atS p s rs gs s' h
  obtain ⟨m1, m2⟩ := drawnClean_marks _ _ _ _ _ _ _ ho
  obtain ⟨b, hb, e1, _, _⟩ :=
    atS_reads s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have f1 : b.F = o.F := e1
  refine ⟨b, hb, by rw [f1]; exact m1, by rw [f1]; exact m2, ?_⟩
  have h0 : b.F.kapMapF.size ≠ 0 := by
    rw [f1, m1]
    exact m2
  simpa using h0

/-- K9's own adding of a list keeps the number of marks. -/
theorem addList_marks : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    G.kapMapF.size = F.kapMapF.size
  | [], F, G, h => by rw [← Except.ok.inj h]
  | cl :: l, F, G, h => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := ans_bind h
    rw [addList_marks l F1 G h2, addOne_marks F F1 cl h1]

/-- **A yes of the draw gives the promise in front.** -/
theorem onA_of_draw {Cl : Type} (p : Where) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : S)
    (h : (drawAlone (Cl := Cl) atS p).decide s rs gs = .ok s') : k9OnA s = true := by
  obtain ⟨a, chi, o, ha, ho, _⟩ := drawAlone_decide atS p s rs gs s' h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, _⟩ := drawnClean_tests _ _ _ _ _ _ _ ho
  simp [k9OnA, ha, c1, c2, c3, c4, c5, c6, c7]

/-- Behind the draw's yes: k9OnB is "the mark was not set in front". -/
theorem onB_behind_draw {Cl : Type} (p : Where) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : S) (a : K9.Part) (ha : atS.get? s = some a)
    (h : (drawAlone (Cl := Cl) atS p).decide s rs gs = .ok s') :
    k9OnB s' = !a.F.doorShutF := by
  obtain ⟨a0, chi, o, ha0, ho, rfl⟩ := drawAlone_decide atS p s rs gs s' h
  have e : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst e
  obtain ⟨_, _, _, _, _, _, _, c8, c9, c10⟩ := drawnClean_tests _ _ _ _ _ _ _ ho
  obtain ⟨b, hb, e1, e2, _⟩ :=
    atS_reads s { a0 with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have f1 : b.F = o.F := e1
  have f2 : b.L = o.L := e2
  simp [k9OnB, hb, f1, f2, c8, c9, c10]

/-- K9's own adding of one claim: the two flags. -/
theorem addOne_flags (F G : Fork) (cl : Claim) (h : addOne F cl = .ok G) :
    F.doorShutF = false ∧ F.thetaDrawnF = true ∧ G.doorShutF = false ∧ G.thetaDrawnF = true := by
  unfold addOne at h
  simp only [] at h
  obtain ⟨x, hx, h⟩ := ans_bind h
  obtain ⟨G1, h1, h2⟩ := ans_bind h
  obtain ⟨d1, d2, _, _, _, ex⟩ := weightNext_ok F x hx
  unfold addForm at h1
  simp only [] at h1
  obtain ⟨t, _, h1⟩ := ans_bind h1
  obtain ⟨l, _, h1⟩ := ans_bind h1
  unfold addRuns at h2
  simp only [] at h2
  obtain ⟨t', _, h2⟩ := ans_bind h2
  refine ⟨d1, d2, ?_, ?_⟩
  · rw [← Except.ok.inj h2, ← Except.ok.inj h1, ex]
    exact d1
  · rw [← Except.ok.inj h2, ← Except.ok.inj h1, ex]
    exact d2

/-- A list of claims: the flags stay; at a list that is not empty they are as they must be. -/
theorem addList_flags : ∀ (cls : List Claim) (F G : Fork), addList F cls = .ok G →
    G.doorShutF = F.doorShutF ∧ G.thetaDrawnF = F.thetaDrawnF ∧
      (cls ≠ [] → F.doorShutF = false ∧ F.thetaDrawnF = true)
  | [], F, G, h => by
    have e : F = G := Except.ok.inj h
    subst e
    exact ⟨rfl, rfl, fun hn => absurd rfl hn⟩
  | cl :: l, F, G, h => by
    unfold addList at h
    rw [List.foldlM_cons] at h
    obtain ⟨F1, h1, h2⟩ := ans_bind h
    obtain ⟨a1, a2, a3, a4⟩ := addOne_flags F F1 cl h1
    obtain ⟨b1, b2, _⟩ := addList_flags l F1 G h2
    exact ⟨by rw [b1, a3, a1], by rw [b2, a4, a2], fun _ => ⟨a1, a2⟩⟩

/-- Behind the writing of an adding. -/
theorem onB_adds (e : S) (b : K9.Part) (cls : List Claim) (G : Fork) (hb : atS.get? e = some b)
    (hG : addList b.F cls = .ok G) :
    k9OnB (atS.set e { b with F := G }) = k9OnB e ∧
      (cls ≠ [] → b.L.handed = true → k9OnB (atS.set e { b with F := G }) = true) := by
  obtain ⟨c1, c2, c3⟩ := addList_flags cls b.F G hG
  obtain ⟨b', hb', e1, e2, _⟩ := atS_reads e { b with F := G } (by simp [hb])
  have f1 : b'.F = G := e1
  have f2 : b'.L = b.L := e2
  refine ⟨by simp [k9OnB, hb, hb', f1, f2, c1, c2], fun hn hh => ?_⟩
  obtain ⟨d1, d2⟩ := c3 hn
  simp [k9OnB, hb', f1, f2, c1, c2, d1, d2, hh]

/-- The equation sets the mark. -/
theorem equation_shut (L : LinkCtx) (F G : Fork) (q : K9.Equation)
    (h : equation L F = .ok (q, G)) : G.doorShutF = true := by
  unfold equation at h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← (Prod.mk.inj (Except.ok.inj h)).2]

/-- **Behind the one equation's yes k9OnB is false.** -/
theorem onB_behind_door {Cl : Type} (pw : Where) (ft : Nat) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S) (k : Nat)
    (h : (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok (s', k)) :
    k9OnB s' = false := by
  obtain ⟨a, out, ha, hd, rfl⟩ := oneEquation_inv atS pw ft s rs cols s' k h
  obtain ⟨n, q, G, row, d1, _, hq, _, _, _, hF, _⟩ := door_parts _ _ _ _ _ out hd
  obtain ⟨b, hb, e1, _, _⟩ :=
    atS_reads s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  have f1 : b.F = out.F := e1
  have hs : b.F.doorShutF = true := by
    rw [f1, hF]
    exact equation_shut _ _ _ _ hq
  simp [k9OnB, hb, hs]

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.marks_behind_draw
#print axioms VerifiableInference.Desc.K9L.addList_marks
#print axioms VerifiableInference.Desc.K9L.onA_of_draw
#print axioms VerifiableInference.Desc.K9L.onB_behind_draw
#print axioms VerifiableInference.Desc.K9L.addList_flags
#print axioms VerifiableInference.Desc.K9L.onB_adds
#print axioms VerifiableInference.Desc.K9L.onB_behind_door
