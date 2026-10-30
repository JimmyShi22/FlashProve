-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmsWiderKey.lean: a bound on a check (any function) that is stated with a public
reading (an oracle algorithm that is run in the experiment and returns a public value d) carries to
a wider key, if the check at the wider key accepts no more often.

What this file states. Johnson/Top/ArmsD.lean bounds a check v at keys k, with what it promises read
at the value d of a public reading that is run in the experiment. Johnson/Top/OnFilesArmsC.lean has
keys (c, k). `ArmBoundD.widerKey`: if a check v' at keys (c, k) accepts, at every hash function, no
more often than v at k, then v's bound is a bound of v', with the same reading, the same promise
(read at d and k; c is not read) and the same ε. A committer that names c after its queries is
covered: c goes into the state that the committer hands to the prover. `toldPart Pub part vf (c, k)
x π`: run the public reading; say no unless the part of its value that a key holds is c; then the
member at the whole value. `toldPart_le`: it accepts no more often than `readArm Pub vf`
(Johnson/Top/ArmsTold.lean). `toldPart_det`: at c := the part of the reading's value the two give
one answer. `ArmBoundD.toldPart`: so a bound of `readArm Pub vf` is a bound of `toldPart Pub part
vf`. Over any family of oracles S.

Under which hypotheses. The premise is a hypothesis. So is v's bound. The reading draws no coin (in
`ArmBoundD.widerKey`, `toldPart_le` and `ArmBoundD.toldPart`).

What it does not show. One direction. The promise is still read at the reading's whole value d,
which the key does not hold: an extractor that needs d must run the reading (`ZKCP.Gen.extD`). The
reading does not read c.


-/
import Johnson.Top.ArmsTold

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ZKCP.Gen

open Rom (OSpec Fam)
open Prob (pr expect)

variable {S : OSpec} {X K Pf D C : Type}

/-- Where the promise holds, the bad event of the last step has probability 0. -/
theorem pr_armD_of_holds {Holds : D → K → Rom.Trace S → X → Pf → Rom.Trace S → Prop}
    (p : PMF Bool) (k : K) (trC : Rom.Trace S) (x : X) (π : Pf) (trP : Rom.Trace S) (d : D)
    (h : Holds d k trC x π trP) :
    pr (p.bind fun b => PMF.pure (⟨b, k, trC, x, π, trP, d⟩ : ArmOutD S X K Pf D))
      (armBadD Holds) = 0 := by
  classical
  rw [Prob.pr_bind]
  refine le_antisymm
    (le_trans (Prob.expect_mono _ fun b => ?_) (le_of_eq (Prob.expect_const _ 0))) (zero_le _)
  rw [Prob.pr_pure, if_neg]
  rintro ⟨-, hb⟩
  exact hb h

/-- A check's bound carries to a wider key, where the check at the wider key accepts no more
often. -/
theorem ArmBoundD.widerKey {rd : K → Rom.OComp S D} (hrd : ∀ k, (rd k).NoCoin)
    {v : K → X → Pf → Rom.OComp S Bool} {v' : C × K → X → Pf → Rom.OComp S Bool}
    (hle : ∀ (f : Fam S) ck x π, pr ((v' ck x π).runEager f) {b | b = true} ≤
      pr ((v ck.2 x π).runEager f) {b | b = true})
    {Holds : D → K → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD rd v Holds ε) :
    ArmBoundD (fun ck : C × K => rd ck.2) v'
      (fun d ck trC x π trP => Holds d ck.2 trC x π trP) ε := by
  classical
  intro tC tP St Ct Pt hC hP
  have b := h tC tP (C × St) (mapO (fun o : (C × K) × St => (o.1.2, (o.1.1, o.2))) Ct)
    (fun s => Pt s.2) (queryBound_mapO _ Ct tC hC) fun s => hP s.2
  refine le_trans ?_ b
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  have hp : ∀ (γ : Type) (z : γ),
      Rom.OComp.runEager f (Rom.OComp.pure z : Rom.OComp S γ) = PMF.pure z := fun _ _ => rfl
  simp only [Rom.PrCoins]
  rw [runEager_armExpD (rd := fun ck : C × K => rd ck.2) (fun ck => hrd ck.2),
    runEager_armExpD hrd, withTrace_mapO]
  unfold mapO
  simp only [runEager_bindO, hp, PMF.pure_bind, PMF.bind_bind]
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o => ?_
  rw [Prob.pr_bind, Prob.pr_bind]
  refine Prob.expect_mono _ fun o' => ?_
  by_cases hh : Holds ((rd o.1.1.2).det f) o.1.1.2 o.2 o'.1.1 o'.1.2 o'.2
  · rw [pr_armD_of_holds
      (Holds := fun d (ck : C × K) trC x π trP => Holds d ck.2 trC x π trP) _ _ _ _ _ _ _ hh]
    exact zero_le _
  · rw [pr_armD_of_not
      (Holds := fun d (ck : C × K) trC x π trP => Holds d ck.2 trC x π trP) _ _ _ _ _ _ _ hh,
      pr_armD_of_not (Holds := Holds) _ _ _ _ _ _ _ hh]
    exact hle f _ _ _

variable [DecidableEq C]

/-- Run the public reading; say no unless the part of its value that stands in a key is the key's c;
then the member at the whole value. -/
def toldPart (Pub : Rom.OComp S D) (part : D → C) (vf : D → K → X → Pf → Rom.OComp S Bool)
    (ck : C × K) (x : X) (π : Pf) : Rom.OComp S Bool :=
  Pub.bind fun d => if part d = ck.1 then vf d ck.2 x π else .pure false

/-- It accepts no more often than the check that reads the value itself. -/
theorem toldPart_le {Pub : Rom.OComp S D} (hn : Pub.NoCoin) (part : D → C)
    (vf : D → K → X → Pf → Rom.OComp S Bool) (f : Fam S) (ck : C × K) (x : X) (π : Pf) :
    pr ((toldPart Pub part vf ck x π).runEager f) {b | b = true} ≤
      pr ((readArm Pub vf ck.2 x π).runEager f) {b | b = true} := by
  have hr : Pub.runEager f = PMF.pure (Pub.det f) := hn.runEager f
  unfold toldPart readArm
  simp only [runEager_bindO, hr, PMF.pure_bind]
  by_cases hc : part (Pub.det f) = ck.1
  · rw [if_pos hc]
  · rw [if_neg hc]
    have hp : Rom.OComp.runEager f (Rom.OComp.pure false : Rom.OComp S Bool) = PMF.pure false := rfl
    rw [hp, Prob.pr_pure, if_neg]
    · exact zero_le _
    · exact fun h => Bool.noConfusion h

/-- At c := the part of the reading's value, `toldPart` and `readArm` give one answer. -/
theorem toldPart_det (Pub : Rom.OComp S D) (part : D → C)
    (vf : D → K → X → Pf → Rom.OComp S Bool) (g : Fam S) (k : K) (x : X) (π : Pf) :
    (toldPart Pub part vf (part (Pub.det g), k) x π).det g = (readArm Pub vf k x π).det g := by
  unfold toldPart readArm
  rw [Rom.OComp.det_bind, Rom.OComp.det_bind, if_pos rfl]

/-- A bound of the check that reads the public value itself is a bound of the check whose key holds
a part of it. -/
theorem ArmBoundD.toldPart {Pub : Rom.OComp S D} (hn : Pub.NoCoin) (part : D → C)
    {vf : D → K → X → Pf → Rom.OComp S Bool}
    {Holds : D → K → Rom.Trace S → X → Pf → Rom.Trace S → Prop} {ε : ℕ → ℕ → ℝ≥0∞}
    (h : ArmBoundD (fun _ => Pub) (readArm Pub vf) Holds ε) :
    ArmBoundD (fun _ : C × K => Pub) (ZKCP.Gen.toldPart Pub part vf)
      (fun d ck trC x π trP => Holds d ck.2 trC x π trP) ε :=
  ArmBoundD.widerKey (fun _ => hn) (toldPart_le hn part vf) h

end ZKCP.Gen

#print axioms ZKCP.Gen.ArmBoundD.widerKey
#print axioms ZKCP.Gen.toldPart_det
#print axioms ZKCP.Gen.ArmBoundD.toldPart
