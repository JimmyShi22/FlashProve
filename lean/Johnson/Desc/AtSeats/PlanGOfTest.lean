-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/PlanGOfTest.lean: THE PREMISE hPlG (`PlanG`,
Johnson/Desc/K13/Law/OthersGAt.lean: six facts on the planner's values at the first segment) OF
THE TIE AT THE FIRST SEGMENT's OPENING, AT THE COMPOSED FILLING's OWN LETTERS: THREE OF THE SIX BY
THE MAKE, THREE OUT OF ONE CLOSED TEST ON THE PUBLIC PARAMETERS. A definition, and statements with
their proofs. `planZeroB built W dg`: the test: reads the planner's list of segments and the public
  parameters alone: segment 0's number of slots is its plan's; the plan's state of the approximate
  range proof has heard nothing; the lookup argument's place at segment 0 has a shape, is the
  calls', begins where the fresh ledger ends, has room within the slots, and stands at segment 0.
  `zeroAt_ok`: what `zeroAt`'s value is made of. `planG_of_test`: at the letters nsOf := "the
  list's entry's slots" and d := `K3Data.of W ⟨cs, sh, ly, the list's arrays⟩`: BY THE MAKE:
  arrays, shape, layout. OUT OF THE TEST: slots, unheard, place. `planG_at9`: so at `Dm.pubD`'s
  own letters, under hb: Dm's list is the list that `zeroAt` reads. `planZeroB_rejects`: the test
  can fail: at an empty list.
What is not claimed. That the test accepts at any public parameters. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OthersGAt
import Johnson.Desc.Sound.MgAll
import Johnson.Top.H0.Walk.FrameLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model
open Johnson.Desc.First.Walk (LayPar startFork)
open Johnson.Desc.First.Walk.Seat (zeroAt pubOf)
open VerifiableInference.Desc.First.Look (K3Data placeAt)
open VerifiableInference.Desc.Sound (MgData)

/-- **The closed test.** -/
def planZeroB (built : Array Stages.LinkH) (W : Verify.Public) (dg : Bool) : Bool :=
  match built[0]? with
  | none => false
  | some X0 =>
    match W.G[X0.g]? with
    | none => false
    | some hp =>
      X0.ns == hp.ns && hp.tl.heard.isNone &&
        match placeAt W 0 dg with
        | none => false
        | some p =>
          match p.shape with
          | none => false
          | some f =>
            !p.digits && (startFork (pubOf X0) hp.ns).next == p.first &&
              decide (p.first + Forest.elems f ≤ hp.ns) && p.link == 0

/-- What `zeroAt`'s value is made of. -/
theorem zeroAt_ok {built : Array Stages.LinkH} {W : Verify.Public} {X : LayPar}
    (h : zeroAt built W = some X) :
    ∃ X0 hp, built[0]? = some X0 ∧ W.G[X0.g]? = some hp ∧ X.X = pubOf X0 ∧ X.ns = hp.ns ∧
      X.tl₀ = hp.tl := by
  unfold zeroAt at h
  cases h0 : built[0]? with
  | none => simp [h0] at h
  | some X0 =>
    simp [h0] at h
    obtain ⟨_, h⟩ := h
    cases hg : W.G[X0.g]? with
    | none => simp [hg] at h
    | some hp =>
      simp [hg] at h
      subst h
      exact ⟨X0, hp, rfl, hg, rfl, rfl, rfl⟩

/-- **The six, at the composed filling's make of the two letters.** -/
theorem planG_of_test {built : Array Stages.LinkH} {W : Verify.Public} {X : LayPar}
    (hX : zeroAt built W = some X) (cs : Codes) (sh : ReqShape) (ly : ReqLayout) (dg : Bool)
    (h : planZeroB built W dg = true) :
    PlanG X (fun m => (built[m]?).map (·.ns)) (K3Data.of W ⟨cs, sh, ly, built.map (·.arrayOf)⟩) dg
      sh ly := by
  obtain ⟨X0, hp, h0, hg, eX, en, et⟩ := zeroAt_ok hX
  unfold planZeroB at h
  rw [h0] at h
  dsimp only at h
  rw [hg] at h
  dsimp only at h
  cases hpl : placeAt W 0 dg with
  | none => simp [hpl] at h
  | some p =>
    cases hf : p.shape with
    | none => simp [hpl, hf] at h
    | some f =>
      simp only [hpl, hf, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq,
        Option.isNone_iff_eq_none] at h
      obtain ⟨⟨a1, a2⟩, ⟨⟨b1, b2⟩, b3⟩, b4⟩ := h
      refine ⟨?_, ?_, ?_, ⟨p, f, hpl, hf, b1, ?_, ?_, b4⟩, rfl, rfl⟩
      · show (built[0]?).map (·.ns) = some X.ns
        rw [h0, en, Option.map_some, a1]
      · rw [et]
        exact a2
      · show (built.map (·.arrayOf)).getD 0 #[] = X.X.arrayOf
        rw [eX, Array.getD_eq_getD_getElem?, Array.getElem?_map, h0]
        rfl
      · rw [eX, en]
        exact b2
      · rw [en]
        exact b3

/-- **At `Dm.pubD`'s own letters.** -/
theorem planG_at9 {Xi Pp Tok : Type} {rows cols nD : ℕ} {XV : Verify.Public}
    (𝔇 : MgData Xi Pp Tok rows cols nD XV) {built : Array Stages.LinkH} {X : LayPar}
    (hb : 𝔇.built = built) (hX : zeroAt built XV = some X) (dg : Bool)
    (h : planZeroB built XV dg = true) : PlanG X 𝔇.pubD.nsOf 𝔇.pubD.d3 dg 𝔇.shape 𝔇.layout := by
  subst hb
  exact planG_of_test hX 𝔇.cs 𝔇.shape 𝔇.layout dg h

/-- The test can fail. -/
theorem planZeroB_rejects (W : Verify.Public) (dg : Bool) : planZeroB #[] W dg = false := rfl

end VerifiableInference.Desc.K13.Law
