-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameTiedLaid.lean: LaidTied and FrontTied (FrameTied.lean), proved, by the
general step at the relation "the record is handed on" (FrameTiedStep.lean).

  step_same              the bundle StepAt for a piece that hands the record on, at an empty row
  step_laid, step_front  so at "link m: laid" and at a front that asks nothing
  laidTied, frontTied

Limits: FrameTied.lean's: Sits, LaysNothing, NoneBetween and LettersRide are premises. No
soundness statement.

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

/-- A piece that hands the record on, at a row that is empty. -/
theorem step_same {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × S} {k : Nat} {pk : Place}
    {q : Piece C Fr A Cl W} {f : S → Except String S}
    {In : P × S → VerifiableInference.Desc.Strs → Prop} (hk : ps[k]? = some pk)
    (hi : (rowOf links pk).ins = []) (ho : (rowOf links pk).outs = [])
    (hn : NoneBetween N ps k)
    (hsh : ∀ s, shapeAt links ps[k]? s = true → shapeAt links ps[k + 1]? s = true)
    (hS : Sits get q f) (hf : ∀ s t, f s = .ok t → t = s) (hE : LaysNothing q)
    (hL : LettersRide N Mg (Yes f) q.base In
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1))) :
    StepAt N Mg links ps get k pk q (Yes f) In where
  hk := hk
  hq := by simp [quietRow, hi, ho]
  hrel := fun a τ b hb => by
    obtain ⟨h1, h2, h3⟩ := hS a τ b hb
    exact ⟨h1, h2, h3⟩
  hE := hE
  hfail := fun _ _ e => by rw [hf _ _ e]
  hshape := fun s t e h => by rw [hf _ _ e]; exact hsh s h
  hG := fun _ _ e => by rw [hf _ _ e]
  hB := fun _ _ e => by rw [hf _ _ e]
  hbook := fun s t e h => book_across hn (by rw [hf _ _ e]) (by rw [hf _ _ e]) h
  hL := hL
  hins := fun p s t y y' w e hy hu hF hall i hi' => by
    have hio : outsQ links ps k i := by
      unfold insQ rowQ at hi'
      unfold outsQ rowQ
      simp only [hk, Option.map_some, Option.getD_some, hi, ho] at hi' ⊢
      exact hi'
    exact hL.items p s t y y' w i e hy hu hF (Or.inr hio) (hall i hio)

/-- «link m: laid». -/
theorem step_laid {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × S} {k m : Nat} {p' : Place}
    {q : Piece C Fr A Cl W} {In : P × S → VerifiableInference.Desc.Strs → Prop}
    (hk : ps[k]? = some ⟨1, some m, 0, KindName.frame⟩)
    (hk' : ps[k + 1]? = some p') (hl : p'.link = some m) (hp : p'.piece = 1)
    (hn : NoneBetween N ps k) (hS : Sits get q (layFront m)) (hE : LaysNothing q)
    (hL : LettersRide N Mg (Yes (layFront m)) q.base In
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1))) :
    StepAt N Mg links ps get k ⟨1, some m, 0, KindName.frame⟩ q (Yes (layFront m)) In := by
  obtain ⟨c, l, pc, kd⟩ := p'
  simp only at hl hp
  subst hl hp
  refine step_same hk ?_ ?_ hn ?_ hS (fun s t h => (Law.layFront_ok h).1) hE hL
  · cases hs : links[m]? <;> simp [rowOf, hs, segRow]
  · cases hs : links[m]? <;> simp [rowOf, hs, segRow]
  · intro s h
    rw [hk] at h
    rw [hk']
    simpa [shapeAt, standAt, mayWait] using h

theorem laidTied : LaidTied := by
  intro A Cl P W C Fr N Mg links ps get k m p' q hk hk' hl hp hn hS hE hL
  exact tied_of_rides (step_laid hk hk' hl hp hn hS hE hL)

/-- The chain's front, where it asks nothing. -/
theorem step_front {A Cl P W : Type} {C : CK} {Fr : Frame} {N : Numbers} {Mg : Meaning P W}
    {links : List ModelPart} {ps : List Place} {get : A → P × S} {q : Piece C Fr A Cl W}
    {In : P × S → VerifiableInference.Desc.Strs → Prop}
    (hk : ps[0]? = some ⟨1, none, 0, KindName.frame⟩)
    (hk' : ps[1]? = some ⟨1, some 0, 0, KindName.frame⟩) (hn : NoneBetween N ps 0)
    (hS : Sits get q .ok) (hE : LaysNothing q)
    (hL : LettersRide N Mg (Yes .ok) q.base In
      ((openSets links ps (start links))[1]?.getD []) ((pubSets Mg.more links ps)[1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) 1)) :
    StepAt N Mg links ps get 0 ⟨1, none, 0, KindName.frame⟩ q (Yes .ok) In := by
  refine step_same hk ?_ ?_ hn ?_ hS (fun s t h => (Except.ok.inj h).symm) hE hL
  · simp [rowOf]
  · simp [rowOf]
  · intro s h
    rw [hk] at h
    rw [hk']
    simp only [shapeAt, standAt, mayWait, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨⟨by simpa using h1, by simpa using h2⟩, ?_⟩
    cases hL' : s.link? with
    | none => rfl
    | some L => rw [hL'] at h3; simp at h3

theorem frontTied : FrontTied := by
  intro A Cl P W C Fr N Mg links ps get q hk hk' hn hS hE hL
  exact tied_of_rides (step_front hk hk' hn hS hE hL)

#print axioms laidTied
#print axioms frontTied

end Johnson.Desc.First.Walk.Tied
