-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K12FitTop.lean: the comparison "the radius fits" (Johnson/Goal/Numbers/K12Fit.lean) in the very form in
which K14's files' top for the shared chain's ledger takes it at the two proximity tests (its
binders hfit9 and hfit10), from the test's yes and one tie between the test's first written stage
and the planner's first stage.
  FirstTie σ st π r: for the first written stage a₀ of the place π: the planner's list st has a
      first stage with a₀'s numbers, and the top's letter r reads, at a₀, radBy σ
      st
  hfit9_of, hfit10_of: the two binders, sign for sign, at any three radii at which fitB says yes
  hfit_at_seat: both at the seat's own letters Q.codes, Q.S, rad2 0, rad5 0, rad5 1, from SeatRadii,
      the two equations on Q, and the two ties

What is not claimed. FirstTie: its neighbour is closedL_in_scope_U | _O (radBy …
(sgOf a) = rUFull a at every written stage, in the goals' scope). Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Goal.Numbers.K14Radii

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Johnson.G
open Johnson.Pack (aOf)
open Johnson.Top.H (stageOf)
open H2K.Pub (radBy sgOf)
open H2K.Member (setAt szUFull szOFull)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (P12)

/-- The tie between the place's first written stage and the planner's first stage. -/
def FirstTie (σ : Setting) (st : List StageSize) (π : P12) (r : Fmt.M1.Stage → ℕ) : Prop :=
  ∀ a₀ rest, π.nums.stages = a₀ :: rest → ∃ y rest', st = y :: rest' ∧
    sgOf a₀ = stageOf y.g y.t ∧ r (sgOf a₀).st = radBy σ st (sgOf a₀)

theorem fit_at_first {σ : Setting} {st : List StageSize} {cs : Codes}
    {l : List (OracleShape × ℕ)} {π : P12} {r : Fmt.M1.Stage → ℕ} (h : fitB σ st cs l = true)
    (ht : FirstTie σ st π r) (a₀ : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (ha : π.nums.stages = a₀ :: rest) (sh : OracleShape) (e0 : ℕ) (hm : (sh, e0) ∈ l) :
    r (sgOf a₀).st < (e0 + 1) * 2 ^ ((sgOf a₀).C.a - aOf cs sh) := by
  obtain ⟨y, rest', rfl, e1, e2⟩ := ht a₀ rest ha
  rw [e2]
  exact fit_of h a₀ e1 sh e0 hm

/-- **The top's binder at the test on G_u.** -/
theorem hfit9_of {σ : Setting} {st : List StageSize} {cs : Codes} {S : LinShape} {rU rO rSp : ℕ}
    {π : P12} {r : Fmt.M1.Stage → ℕ} (h : fitB σ st cs (pairsOf S rU rO rSp) = true)
    (ht : FirstTie σ st π r) :
    ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (H2K.Pub.sgOf a₀).st < (rU + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf cs S.fold.u) ∧
      r (H2K.Pub.sgOf a₀).st < (rSp + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf cs S.sharedSplit) :=
  fun a₀ rest ha => ⟨fit_at_first h ht a₀ rest ha _ _ (by simp [pairsOf]),
    fit_at_first h ht a₀ rest ha _ _ (by simp [pairsOf])⟩

/-- **The top's binder at the test on G_omega.** -/
theorem hfit10_of {σ : Setting} {st : List StageSize} {cs : Codes} {S : LinShape} {rU rO rSp : ℕ}
    {π : P12} {r : Fmt.M1.Stage → ℕ} (h : fitB σ st cs (pairsOf S rU rO rSp) = true)
    (ht : FirstTie σ st π r) :
    ∀ a₀ rest, π.nums.stages = a₀ :: rest →
      r (H2K.Pub.sgOf a₀).st < (rO + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf cs S.omega) ∧
      r (H2K.Pub.sgOf a₀).st < (rSp + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf cs S.sharedSplit) :=
  fun a₀ rest ha => ⟨fit_at_first h ht a₀ rest ha _ _ (by simp [pairsOf]),
    fit_at_first h ht a₀ rest ha _ _ (by simp [pairsOf])⟩

/-- **Both at the seat's own letters**, in a proof file. -/
theorem hfit_at_seat {x : LinSized} (hx : realSized = some (x, codesFull2)) {work : ℕ} {Q : P14}
    {Wr : Rounds} {sentU : Array OracleNotice} {rad2 rad5 : ℕ → ℕ}
    (h : SeatRadii 2 work Q Wr sentU rad2 rad5 8342416 3131972 6117) (hS : Q.S = x.shape)
    (hc : Q.codes = codesFull2) {πA πB : P12} {rA rB : Fmt.M1.Stage → ℕ}
    (tA : FirstTie setAt szUFull πA rA) (tB : FirstTie setAt szOFull πB rB) :
    (∀ a₀ rest, πA.nums.stages = a₀ :: rest →
      rA (H2K.Pub.sgOf a₀).st <
        (rad2 0 + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.fold.u) ∧
      rA (H2K.Pub.sgOf a₀).st <
        (rad5 1 + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.sharedSplit)) ∧
    (∀ a₀ rest, πB.nums.stages = a₀ :: rest →
      rB (H2K.Pub.sgOf a₀).st <
        (rad5 0 + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.omega) ∧
      rB (H2K.Pub.sgOf a₀).st <
        (rad5 1 + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.sharedSplit)) := by
  obtain ⟨f1, f2⟩ := fit_at_letters_real hx h hS
  rw [hc]
  exact ⟨hfit9_of f1 tA, hfit10_of f2 tB⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.fit_at_first
#print axioms Desc.K14.Law.hfit9_of
#print axioms Desc.K14.Law.hfit10_of
#print axioms Desc.K14.Law.hfit_at_seat
