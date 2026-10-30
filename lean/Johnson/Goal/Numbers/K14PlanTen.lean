-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K14PlanTen.lean: the ten premises of the seam at the shared chain's two proximity tests that
read no record of a run (another file's list: Johnson/Second/Seam/PlanFacts.lean: Facts P sentU
layU layO, which it evaluates at the planner's chains), BY LEAN's KERNEL at the typed shape and
codes of a proof file and of a key file.
  Ten cs S sentU layU layO: the ten, in that list's order: withU S = some sentU; sentU.size = 2;
      (withOmega S).size = 2; the two layouts; the split is needed; the masks go ahead; K1.Tie at
      S.fold.u, S.omega, S.sharedSplit
  tenB, tenB_sound: one test with code, and what its yes gives
  ten_real, ten_key: the yes: decide +kernel

What is not claimed. That a seated description's shape and codes are the typed ones. Nothing on a
run's record. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14CondAt
import Johnson.Desc.K1.Law.Port2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc.K1 (realSized Tie)
open Lk6.AtPlan (keyFull)

/-- The ten. -/
structure Ten (cs : Codes) (S : LinShape) (sentU : Array OracleNotice) (layU layO : TreeLay) :
    Prop where
  hU : withU S = some sentU
  hsU : sentU.size = 2
  hsO : (withOmega S).size = 2
  hlU : layTrees cs sentU = some layU
  hlO : layTrees cs (withOmega S) = some layO
  hS : S.sharedSplitNeeded = true
  hm : S.masksAhead = true
  hTU : Tie cs S.fold.u
  hTO : Tie cs S.omega
  hTS : Tie cs S.sharedSplit

/-- K1.Tie's four clauses as a test. -/
def tieTestB (cs : Codes) (s : OracleShape) : Bool :=
  decide (s.answers = 1) && cs.lengthsOk && Blk.shapeOk cs s &&
    (VerifiableInference.Desc.K1.Msg.of cs s).padFits

theorem tie_of_test {cs : Codes} {s : OracleShape} (h : tieTestB cs s = true) : Tie cs s := by
  unfold tieTestB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- **The test.** -/
def tenB (cs : Codes) (S : LinShape) : Bool :=
  (withU S).any fun sentU => (layTrees cs sentU).any fun _ =>
    (layTrees cs (withOmega S)).any fun _ =>
      decide (sentU.size = 2) && decide ((withOmega S).size = 2) && S.sharedSplitNeeded &&
        S.masksAhead && tieTestB cs S.fold.u && tieTestB cs S.omega && tieTestB cs S.sharedSplit

theorem tenB_sound {cs : Codes} {S : LinShape} (h : tenB cs S = true) :
    ∃ sentU layU layO, Ten cs S sentU layU layO := by
  unfold tenB at h
  cases h1 : withU S with
  | none =>
    rw [h1] at h
    cases h
  | some sentU =>
    rw [h1, Option.any_some] at h
    cases h2 : layTrees cs sentU with
    | none =>
      rw [h2] at h
      cases h
    | some layU =>
      rw [h2, Option.any_some] at h
      cases h3 : layTrees cs (withOmega S) with
      | none =>
        rw [h3] at h
        cases h
      | some layO =>
        rw [h3, Option.any_some] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
        exact ⟨sentU, layU, layO, h1, a1, a2, h2, h3, a3, a4, tie_of_test a5, tie_of_test a6,
          tie_of_test a7⟩

theorem ten_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∃ sentU layU layO, Ten codesFull2 x.shape sentU layU layO := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => tenB p.2 p.1.shape) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, tenB_sound h⟩

theorem ten_key : ∃ sentU layU layO, Ten keyFull.codes keyFull.once.shape sentU layU layO :=
  tenB_sound (by decide +kernel)

end Desc.K14.Law

#print axioms Desc.K14.Law.tie_of_test
#print axioms Desc.K14.Law.tenB_sound
#print axioms Desc.K14.Law.ten_real
#print axioms Desc.K14.Law.ten_key
