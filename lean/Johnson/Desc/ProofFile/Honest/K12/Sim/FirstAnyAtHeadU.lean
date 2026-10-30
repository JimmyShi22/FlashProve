-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstAnyAtHeadU.lean: `any_at_place`
(Sim/FirstAnyAtPlace.lean) under the library's head (`P5J.AtMg`), at the place at which the proof
file's description seats the test on G_u, `(fourOf Np).U`, off the description's own shared list: at
every job at that place.

  `facts_UFull`, `facts_head_U`   the seven public tests at the written place `piUFull`: the block's
                 test on the plan from the library's `closed_UFull`, the other six shown in
                 Sim/FirstPubAtHead.lean, Sim/FirstSeatAtHead.lean, Sim/MeetsAtHead.lean or
                 Sim/DrawsAtHead.lean; so they hold at the seated place
  `atU_is_any`   the job of `jobAtU`, at every record, state function, readers and vector, is a job
                 at its place which says that the table has come earlier
  `first_any_head_U`   the statement

By what. `nums_head_U`, `thin_head_U` (Sim/FirstPubAtHead.lean), `planOk_head_U` (NearAtHead.lean),
`find_gu` (Sim/FirstSeatAtHead.lean), called.

Limits.
- "At every job at the place" says nothing on whether any job there is the prover's. Who owns the
  fresh table that came earlier is not named: the job's field is any address. The one job that is
  typed at this place, `jobAtU` (JobShared.lean), is an instance, at every record and so at every
  number in the record's second field (`atU_is_any`).
- All limits of Sim/FirstAnyAtPlace.lean stand. Among them: "every job" takes in jobs of which the
  sentence says nothing of any run, and no book is asked. The challenges are one list written by
  hand. The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.Member (piUFull)
open ProofFile.Honest.K14 (SendPub)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

theorem facts_UFull : PlaceFacts piUFull dsFull :=
  ⟨VerifiableInference.Desc.K12.Coin.At.closed_UFull.plan, formPubB_U, enough_U, tabB_U,
    count_UFull, quiet_UFull, draws_UFull⟩

/-- The typed job is a job at its place which says that the table has come earlier. -/
theorem atU_is_any {W X : Type} (A : SendPub) (p : P12) (door : W → Front X → T12)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtU A p door weights rand u?).toRun.toTest.p = p ∧
      (jobAtU A p door weights rand u?).toRun.toTest.fresh.isNone = false := ⟨rfl, rfl⟩

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

theorem facts_head_U (h : P5J.AtMg o Z D r Zp Np cF) : PlaceFacts (fourOf Np).U dsFull :=
  facts_carry (congrArg (·.stages) (nums_head_U h)) (thin_head_U h) (planOk_head_U h) facts_UFull

local instance (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) :=
  ⟨(default, default)⟩

local instance (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **Under the head, at every job at the place of the test on G_u.** -/
theorem first_any_head_U {V W X Pb : Type} (h : P5J.AtMg o Z D r Zp Np cF) (J : TestJob W X)
    (Js : SimJob Pb) (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).U) (ho : Js.own = false) :
    FirstPub J Js ∧
    (∀ fs : List (Fall (P5J.F0T o Zp Np cF).S₂),
      ∃ σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V W X Pb,
        testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ) ∧
    ∀ (fs : List (Fall (P5J.F0T o Zp Np cF).S₂))
      (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V W X Pb),
      testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ →
      σ.fits = true ∧
      σ.members = [firstMember J Js, restMember J Js] ∧
      (∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
        (testOn φ J Js) (testBud Js) (firstMember J Js)) ∧
      firstMember J Js ∈ σ.members ∧
      ∀ (φ : Face V W Pb) (chain firstTree : ℕ)
        (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
        (asks : List (List (List ℕ))),
        testOn φ J Js (firstMember J Js) ca m (bareFront chain m) ∧
        m.seen = (bareFront chain m).seen ∧
        drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) dsFull = true ∧
        testBud Js (firstMember (V := V) J Js).number dsFull asks ∧
        (bareFront chain m).holds chain firstTree ((firstMember (V := V) J Js).rounds.map (·.1))
          dsFull = true ∧
        (firstMember J Js).part.stopAt (φ.sees m.st.input) m.loc dsFull ≠ some .hid ∧
        (∀ c, ∃ l, σ.shows φ (firstMember J Js) c m dsFull asks = some l ∧
          scalars l = 2 * J.s₀.k + 1 ∧ columns l = 0) ∧
        (Prob.unif (Cs (firstMember (V := V) J Js).part.takes ×
            CsAll (firstMember (V := V) J Js).part.spends)).map
            (fun c => σ.shows φ (firstMember J Js) (c.1, c.2, ca) m dsFull asks) =
          (Prob.unif (Cs (firstMember (V := V) J Js).sim.takes)).map fun c =>
            (firstMember J Js).tells φ c m.st.input (bareFront chain m) dsFull asks := by
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_gu h
  rw [← hJ] at hf hpl hr hor hs
  exact any_at_place J Js (hJ ▸ facts_head_U h) _ b hf hpl hr hor hfr hs ho

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.facts_UFull
#print axioms ProofFile.Honest.K12.Light.atU_is_any
#print axioms ProofFile.Honest.K12.Light.facts_head_U
#print axioms ProofFile.Honest.K12.Light.first_any_head_U
