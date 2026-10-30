-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/MeetsEveryFront.lean: at the first member of a proximity test,
in both arms: the record `MeetsAt` (Sim/MeetsOwnAtHead.lean: the six hypotheses of the sentence
`ExactMember`, Johnson/Desc/ProofFile/Honest/Small/Field.lean, in its order; "something"; the
equation) holds at every front, all challenges and all positions at which the three of the six hold
that say something at this member. It imports Mathlib.

  `MeetsEvery`   a definition of this file, made so that a top statement stays short: at every
                 front, list of challenges and list of positions: where the front shows what the
                 stand has seen, the challenges are such as the member's declared rounds can draw,
                 and the side's bound `testBud` (Sim/Row.lean) holds at the member's number:
                 `MeetsAt` at the side's own `testOn` and `testBud`
  `MeetsSome`    a definition of this file: there are a front, challenges and positions at which
                 these three hold
  `meets_every_earlier`, `meets_some_earlier`   where the first fold's fresh table has come earlier:
                 at every job at a place that passes `PlaceFacts` (Sim/FirstAnyAtPlace.lean). There
                 `testBud` asks nothing at this member (`testBud_first`, Sim/MeetsAtHead.lean)
  `meets_every_O`, `meets_some_O`   where the fold sends its own table: under the library's head
                 (`P5J.AtMg`, Johnson/P5J/AtMg.lean), at every job at the seated place of the test
                 on G_omega

Why every front. Of the six, On asks nothing at this member, at any front (`testOn_first`); the
member's rounds open and read nothing, so every front holds what is read (`holds_of_quiet`); the
part has no second stop (`stop_first`). One clause alone binds the front: that it shows what the
stand has seen. The witnesses in `MeetsSome`: the front `bareFront chain m` (Sim/MeetsAtHead.lean),
made of the stand; the place's written list of challenges; no position, or 51 written ones.

By what. `meetsAt_of_exact`, `exact_at_O`, `quiet_head_O`, `draws_head_O`, `testBud_own`, `bud_51`,
`s₀_head_O` (Sim/MeetsOwnAtHead.lean); `some_at_O` (Sim/BudOwnAtHead.lean); `exact_first`
(Sim/ExactFirst.lean); `first_count` (Sim/FirstCount.lean); `firstPub_any`
(Sim/FirstAnyAtPlace.lean).

Limits.
- "At every front that shows what the stand has seen": that the frame's own front at a run
  (`Run.beforeAt`, Johnson/Desc/ProofFile/Honest/Side.lean) is such a front at the stand that the
  run's play reaches is not shown here.
- The stand is any: no stand is shown to be one that a play reaches.
- The side is any: nothing is asked of it here.
- "At every job at the place" says nothing on whether any job there is the prover's, nor does it
  settle the state on entry.
- The first member alone. At the second member On and "the front holds what is read" do read the
  front: nothing of this file carries over.
- All other limits of Sim/FirstAnyAtPlace.lean, Sim/MeetsOwnAtHead.lean and Sim/BudOwnAtHead.lean
  stand. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtPlace
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {S Cl V W X Pb : Type}

/-! ## 1 The two definitions -/

/-- **At every front, challenges and positions at which the three hypotheses hold that say something
at the first member: all six, "something" and the equation.** -/
def MeetsEvery (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : ℕ) (J : TestJob W X)
    (Js : SimJob Pb) (ca : CsAll (firstMember (V := V) J Js).part.carries)
    (m : ProofFile.Honest.Mid W X) : Prop :=
  ∀ (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ))),
    m.seen = front.seen →
    drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true →
    testBud Js (firstMember (V := V) J Js).number ds asks →
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m front ds asks

/-- **There are a front, challenges and positions at which these three hold.** V: the type at which
the member is taken. -/
def MeetsSome (V : Type) (J : TestJob W X) (Js : SimJob Pb) (m : ProofFile.Honest.Mid W X) : Prop :=
  ∃ (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List ℕ))),
    m.seen = front.seen ∧
    drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true ∧
    testBud Js (firstMember (V := V) J Js).number ds asks

/-! ## 2 Where the table has come earlier -/

theorem meets_every_earlier {ds₀ : List Fmt.Drawn} (J : TestJob W X) (Js : SimJob Pb)
    (F : PlaceFacts J.p ds₀) (hfr : J.fresh.isNone = false) (hs : Js.p = J.p)
    (ho : Js.own = false) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X) :
    MeetsEvery φ σ chain firstTree J Js ca m := fun front ds asks h2 h3 h4 =>
  meetsAt_of_exact
    (exact_first φ σ J Js chain firstTree _ _ hfr (firstPub_any J Js F hfr hs ho)) ca m front ds
    asks (testOn_first φ J Js ca m front) h2 h3 h4
    (holds_of_quiet front chain firstTree _ ds F.quiet)
    (stop_first (V := V) J Js (φ.sees m.st.input) m.loc ds) fun c => by
      obtain ⟨l, hl, _⟩ := first_count φ σ J Js hfr (firstPub_any J Js F hfr hs ho) m ds h3 asks c
      rw [hl]
      rfl

theorem meets_some_earlier {ds₀ : List Fmt.Drawn} (V : Type) (J : TestJob W X) (Js : SimJob Pb)
    (F : PlaceFacts J.p ds₀) (ho : Js.own = false) (m : ProofFile.Honest.Mid W X) :
    MeetsSome V J Js m :=
  ⟨bareFront 0 m, ds₀, [], seen_bareFront 0 m, F.draws, testBud_first Js ho ds₀ []⟩

/-! ## 3 Where the fold sends its own table -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

theorem meets_every_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (Js : SimJob Pb) (J : TestJob W X) (hp : J.p = pO) (hfr : J.fresh.isNone = true)
    (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : ℕ) (ca : CsAll (firstMember (V := V) J Js).part.carries)
    (m : ProofFile.Honest.Mid W X) : MeetsEvery φ σ chain firstTree J Js ca m :=
  fun front ds asks h2 h3 h4 =>
    meetsAt_of_exact (exact_at_O h hO Js J hp hfr hJ ho φ σ chain firstTree) ca m front ds asks
      (testOn_first φ J Js ca m front) h2 h3 h4
      (holds_of_quiet front chain firstTree _ ds (quiet_head_O (V := V) h hO Js J hp))
      (stop_first (V := V) J Js (φ.sees m.st.input) m.loc ds)
      (some_at_O h hO Js J hp hfr hJ ho φ σ m ds h3 asks)

theorem meets_some_O (V : Type) (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (Js : SimJob Pb) (J : TestJob W X) (hp : J.p = pO) (hJ : Js.p = pO)
    (m : ProofFile.Honest.Mid W X) : MeetsSome V J Js m :=
  ⟨bareFront 0 m, dsOwn, asksTo 51, seen_bareFront 0 m, draws_head_O (V := V) h hO Js J hp,
    testBud_own Js dsOwn (asksTo 51) (by rw [s₀_head_O h hO Js hJ]; exact bud_51)⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.MeetsEvery
#print axioms ProofFile.Honest.K12.Light.MeetsSome
#print axioms ProofFile.Honest.K12.Light.meets_every_earlier
#print axioms ProofFile.Honest.K12.Light.meets_some_earlier
#print axioms ProofFile.Honest.K12.Light.meets_every_O
#print axioms ProofFile.Honest.K12.Light.meets_some_O
