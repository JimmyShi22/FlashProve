-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15P.lean: TWO PUBLIC CLAUSES THAT THE COMPOSITION OF THE PROXIMITY TEST's LAW ASKS OF A MEMBER (MemberFacts, Johnson/Desc/Sound/SeamMembers.lean), FOR THE ONE MEMBER OF THE KEY FILE's FIRST PROXIMITY TEST's GROUP: the seat fits; the test's first radius against the member's own. Statements with proofs; two evaluations in the kernel, one a control. IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. SeatFits (Johnson/Desc/Sound/MsgSig.lean) at a list of one member; the written stages and the planner's radii (Johnson/RunOne/Law/K12Facts15S.lean).
USER. Whoever lays MemberFacts at the key file's first proximity test.

  seatFits_all, seatFits_one: GENERAL: where the plain test on a seat finds no fault at any member of a list, the list's seats fit; and at a list of one member. One call a member of seat_of_noFault (Johnson/Desc/Sound/PlanMemProofs.lean).
  hfit_full, hfit_full_no: by the kernel, at the written value: the first stage's radius is below (e + 1) * 2 ^ (the stage's log-length less the member's), e the radius of the lookups' own message; with e in the place of e + 1 it is not. (The test is true of an empty list of stages: the control's no shows that a first stage is there.)
  hfit_scope: the clause at the place's own first stage, from scope's equations.
Limits. That the member's shape is the written one, that the codes are the written ones, where the member sits: others'. One size. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15S
import Johnson.Desc.Sound.PlanMemProofs
import Johnson.Top.H.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key
open Johnson.G.OfPlan (Made)
open Johnson.Pack (aOf)
open Lk6.AtPlan (keyFull)
open Johnson.Top.H (eRng1 csKey shMul)
open H2K.Pub (sgOf)

/-- **Where the plain test on a seat finds no fault at any member of a list, the list's seats fit.** -/
theorem seatFits_all {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (tag : String)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)
    (h : ∀ i, seatFaultAt G cs tag (l.get i).1 (seat i).1 (seat i).2 = none) : SeatFits G cs l seat :=
  fun i => seat_of_noFault G cs tag _ _ _ (h i)

/-- At a list of one member. -/
theorem seatFits_one {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (tag : String) (sh : OnBytes.OracleShape)
    (e : ℕ) (p : ℕ × ℕ) (h : seatFaultAt G cs tag sh p.1 p.2 = none) :
    SeatFits G cs [(sh, e)] (fun _ => p) := by
  intro i
  obtain ⟨i, hi⟩ := i
  have h0 : i = 0 := by
    have : i < 1 := hi
    omega
  subst h0
  exact seat_of_noFault G cs tag sh p.1 p.2 h

theorem hfit_full : (stagesFull.head?.all fun a =>
    decide (radRng (sgOf a).st < (eRng1 + 1) * 2 ^ ((sgOf a).C.a - aOf csKey shMul))) = true := by
  decide +kernel

/-- A control: with the radius itself in the place of the radius and one. -/
theorem hfit_full_no : (stagesFull.head?.all fun a =>
    decide (radRng (sgOf a).st < eRng1 * 2 ^ ((sgOf a).C.a - aOf csKey shMul))) = false := by
  decide +kernel

/-- The test's first radius against the member's own. -/
theorem hfit_scope {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
    {m : Made} {N : H2U.PlaceNums} (hN : rangesNumbers m = .ok N)
    (h : (rangesTest laid back N : Block σ Cl).planOk = true) (hk : m.p.chains.made.sized.key = keyFull)
    (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : (rangesParams N).nums.stages = a :: rest) :
    radRng (sgOf a).st < (eRng1 + 1) * 2 ^ ((sgOf a).C.a - aOf csKey shMul) := by
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays h).1
  have e : stagesFull = a :: rest := by
    rw [← hs, hn, (numbers_parts hN).2.2.2.2.2, hk]
    rfl
  have h1 := hfit_full
  rw [e] at h1
  exact of_decide_eq_true h1

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.seatFits_all
#print axioms Johnson.RunOne.Law.K12Facts15.seatFits_one
#print axioms Johnson.RunOne.Law.K12Facts15.hfit_full
#print axioms Johnson.RunOne.Law.K12Facts15.hfit_full_no
#print axioms Johnson.RunOne.Law.K12Facts15.hfit_scope
