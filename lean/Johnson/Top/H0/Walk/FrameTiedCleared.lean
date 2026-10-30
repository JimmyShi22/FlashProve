-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameTiedCleared.lean: ClearedTiedAtt and ClearedTiedRow (FrameTied.lean),
proved, by the general step at ClearedRec (FrameTiedStep.lean: tied_of_rides).

  standOf_between, shape_across   the book-keeping across "cleared"
  rel_of_sits                     Sits at clearWith gives ClearedRec (clearedGives)
  step_clearedAtt, step_clearedRow   the bundle StepAt at "link m: cleared"
  clearedTiedAtt, clearedTiedRow

Limits: FrameTied.lean's: Sits, LaysNothing, NoneBetween, LettersRide and PileGivesWo are premises.
No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTiedStep
import Johnson.Top.H0.Walk.FrameTiedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers Pub Stand standAt standOf mayWait
  shift rowOf segRow shapeAt quietRow openSets pubSets start)
open VerifiableInference.Desc.First.Pend (pendingRowO)

theorem standOf_between {t : S} (h : t.atBetween = true) :
    standOf t = Stand.between ∧ t.link? = none := by
  unfold S.atBetween at h
  unfold standOf S.link?
  cases hh : t.here <;> simp_all

theorem shape_across {links : List ModelPart} {pk p' : Place} {s t : S} (hmw : mayWait links pk = false)
    (hst : standAt links p' = Stand.between) (hB : t.atBetween = true)
    (hr : t.rowsOwed = s.rowsOwed) (h : shapeAt links (some pk) s = true) :
    shapeAt links (some p') t = true := by
  obtain ⟨h1, h2⟩ := standOf_between hB
  simp only [shapeAt, Bool.and_eq_true, hmw, Bool.or_false] at h
  have hn : t.noneWaits = true := by
    have := h.1.2
    unfold S.noneWaits at this ⊢
    rwa [hr]
  simp [shapeAt, h1, hst, hn, h2]

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
  {links : List ModelPart} {ps : List Place} {get : A → P × S} {k m : Nat} {p' : Place}
  {q : Piece C Fr A Cl W} {X : LinkPub} {lay : WsLay} {lin : Params.LinShape}
  {f : S → Except String S} {In : P × S → VerifiableInference.Desc.Strs → Prop}

/-- «link m: cleared», an attention segment. General in the step f, of which is asked: a yes of f
gives ClearedRec. (General too in what the sub-proof is said to have left: the row of the table is
empty there.) -/
theorem step_clearedAtt {left : S → Option WsForkOut} (hsub : links[m]? = some ModelPart.attention)
    (hk : ps[k]? = some ⟨1, some m, 13, KindName.frame⟩)
    (hmw : mayWait links ⟨1, some m, 13, KindName.frame⟩ = false) (hk' : ps[k + 1]? = some p')
    (hst : standAt links p' = Stand.between) (hn : NoneBetween N ps k)
    (hS : Sits get q f) (hf : ∀ s t, f s = .ok t → ClearedRec X left lay lin s t)
    (hE : LaysNothing q)
    (hL : LettersRide N Mg (Yes f) q.base In
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1))) :
    StepAt N Mg links ps get k ⟨1, some m, 13, KindName.frame⟩ q (Yes f) In := by
  have hi : (rowOf links ⟨1, some m, 13, KindName.frame⟩).ins = [] := by
    simp [rowOf, hsub, segRow, shift]
  have ho : (rowOf links ⟨1, some m, 13, KindName.frame⟩).outs = [] := by
    simp [rowOf, hsub, segRow, shift]
  exact
    { hk := hk
      hq := by simp [quietRow, hi, ho]
      hrel := hS
      hE := hE
      hfail := fun s t h => (hf s t h).2.2.2.2.2.2.1
      hshape := fun s t h hs => by
        rw [hk] at hs
        rw [hk']
        exact shape_across hmw hst (hf s t h).1 (hf s t h).2.2.2.2.2.1 hs
      hG := fun s t h => (hf s t h).2.2.2.2.2.2.2.2.2.1
      hB := fun s t h => by rw [(hf s t h).2.2.2.1]
      hbook := fun s t h hb =>
        book_across hn (hf s t h).2.2.2.1 (hf s t h).2.2.2.2.2.2.2.2.2.2.1 hb
      hL := hL
      hins := fun p s t y y' w hr hy hu hF hall i hi' => by
        have hio : outsQ links ps k i := by
          unfold insQ rowQ at hi'
          unfold outsQ rowQ
          simp only [hk, Option.map_some, Option.getD_some, hi, ho] at hi' ⊢
          exact hi'
        exact hL.items p s t y y' w i hr hy hu hF (Or.inr hio) (hall i hio) }

/-- «link m: cleared», a layers' or the head's segment. -/
theorem step_clearedRow {sub : ModelPart} {left : S → Option WsForkOut} (hsub : links[m]? = some sub)
    (hne : sub ≠ ModelPart.attention)
    (hk : ps[k]? = some ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩)
    (hmw : mayWait links ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩ = false)
    (hk' : ps[k + 1]? = some p') (hst : standAt links p' = Stand.between)
    (hn : NoneBetween N ps k)
    (hS : Sits get q f) (hf : ∀ s t, f s = .ok t → ClearedRec X left lay lin s t)
    (hE : LaysNothing q)
    (hL : LettersRide N Mg (Yes f) q.base In
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1)))
    (hW : PileGivesWo Mg m (Yes f) q.base In) :
    StepAt N Mg links ps get k ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩ q (Yes f) In := by
  have hi : (rowOf links ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩).ins = [Item.wo m] := by
    cases sub <;> simp_all [rowOf, segRow, shift]
  have ho : (rowOf links ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩).outs = [] := by
    cases sub <;> simp_all [rowOf, segRow, shift]
  have hc : (rowOf links ⟨1, some m, 13 + 2 * shift sub, KindName.frame⟩).ctx =
      [Item.pile, Item.pinW, Item.pinI] := by
    cases sub <;> simp_all [rowOf, segRow, shift]
  exact
    { hk := hk
      hq := by simp [quietRow, hi, ho, Item.isRow, Item.isPin]
      hrel := hS
      hE := hE
      hfail := fun s t h => (hf s t h).2.2.2.2.2.2.1
      hshape := fun s t h hs => by
        rw [hk] at hs
        rw [hk']
        exact shape_across hmw hst (hf s t h).1 (hf s t h).2.2.2.2.2.1 hs
      hG := fun s t h => (hf s t h).2.2.2.2.2.2.2.2.2.1
      hB := fun s t h => by rw [(hf s t h).2.2.2.1]
      hbook := fun s t h hb =>
        book_across hn (hf s t h).2.2.2.1 (hf s t h).2.2.2.2.2.2.2.2.2.2.1 hb
      hL := hL
      hins := fun p s t y y' w hr hy hu hF hall i hi' => by
        have hout : ∀ j, j ∈ [Item.pile, Item.pinW, Item.pinI] ++ [Item.unmarked] →
            outsQ links ps k j := by
          intro j hj
          unfold outsQ rowQ
          simp only [hk, Option.map_some, Option.getD_some, ho, hc, List.nil_append]
          exact hj
        unfold insQ rowQ at hi'
        simp only [hk, Option.map_some, Option.getD_some, hi, hc, List.append_assoc] at hi'
        rcases List.mem_append.1 hi' with h | h
        · have e : i = Item.wo m := by simpa using h
          subst e
          exact hW p s t y y' w hr hy hF (hall Item.pile (hout _ (by simp)))
        · exact hL.items p s t y y' w i hr hy hu hF (Or.inr (hout i h)) (hall i (hout i h)) }

end

theorem clearedTiedAtt : ClearedTiedAtt := by
  intro A Cl P W C Fr N Mg links ps get k m p' q X counts left lay lin hsub hk hmw hk' hst hn hS hE
    hL
  exact tied_of_rides (step_clearedAtt hsub hk hmw hk' hst hn hS
    (clearedGives X counts left lay lin) hE hL)

theorem clearedTiedRow : ClearedTiedRow := by
  intro A Cl P W C Fr N Mg links ps get k m sub p' q X counts left lay lin hsub hne hk hmw hk' hst
    hn hS hE hL hW
  exact tied_of_rides (step_clearedRow hsub hne hk hmw hk' hst hn hS
    (clearedGives X counts left lay lin) hE hL hW)

#print axioms clearedTiedAtt
#print axioms clearedTiedRow

end Johnson.Desc.First.Walk.Tied
