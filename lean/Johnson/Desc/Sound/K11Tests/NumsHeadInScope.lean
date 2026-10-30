-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/NumsHeadInScope.lean: THE TEST WITH CODE numsB Z 24 numsFull.rows
(Johnson/Top/H0/MergeLaw/PlanNumsAt.lean: three tests on the planner's numbers in one) SAYS YES AT
ALL PUBLIC FILES IN THE GOALS' SCOPE, UNDER ONE EQUATION ON THE FIRST CHAIN's PARAMETERS. It is the
field nums of the named condition for the merge of the claims on the committed table
(kind K11). Statements and proofs. One closed fact is by Lean's kernel.

  wsLay_in_scope        in scope the layout of the committed table in what publicOf returns is the
                        value of a closed term: wsLayOf wsFull true recordLines.blockLog
  m0lk_full             that term's number of rows is 3,076,096 and its column bits are 18: by the
                        kernel
  nsB_head_of_public    the first test: the planner's link number 24 has the head's number of slots
  nRB_of_public         the second: numsFull.rows is the layout's number of rows
  kColB_of_public       the third, UNDER hk: the first chain's row's shape has 18 column bits
  numsB_head_of_public  the three

hk IS A PREMISE. It is what the head P5J.AtMgA says in its field cols13, and what the first entry
pin gives (first_in_scope, Johnson/Goal/Numbers/KeyInScope.lean). It is not paid here.

Limits. That the premises can be met together is not shown here. Nothing on a verifier's state.
Nothing on soundness.

-/
import Johnson.IMR.PureJoin
import Johnson.Top.H0.MergeLaw.PlanNumsAt
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Numbers.KeyPlansAtPure
import Johnson.Flat.ClaimsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Params (recordLines)
open Lk6.AtPlan Johnson.G
open VerifiableInference.PlanWritten
open VerifiableInference.Desc.First.MergeLaw (numsB nsB nRB kColB)

/-- The rows and the column bits of the committed table's layout at the written sizes. -/
def m0lk : Option (Nat × Nat) :=
  match wsLayOf wsFull true recordLines.blockLog with
  | .ok Y => some (Y.m0, Y.lk)
  | .error _ => none

/-- By the kernel. -/
theorem m0lk_full : m0lk = some (3076096, 18) := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}

/-- **In scope the committed table's layout is the written sizes'.** -/
theorem wsLay_in_scope {X : Verify.Public} (hS : VerifierAndGoals.InScope P = true)
    (hX : publicOf P.pol P.KL (some lay) = .ok X) :
    wsLayOf wsFull true recordLines.blockLog = .ok X.layers.wsLay := by
  obtain ⟨v, hv⟩ := inScope_policy hS
  have hO : publicOfO OnBytes.secondHashFunction P.pol P.KL (some lay) = .ok X := by
    rw [publicOfO_older]
    exact hX
  rw [hv] at hO
  exact (VerifiableInference.Number.ByRuns.args_of_steps (publicSteps_of_O hO)).2

/-- So its two numbers. -/
theorem m0lk_in_scope {X : Verify.Public} (hS : VerifierAndGoals.InScope P = true)
    (hX : publicOf P.pol P.KL (some lay) = .ok X) :
    X.layers.wsLay.m0 = 3076096 ∧ X.layers.wsLay.lk = 18 := by
  have h := m0lk_full
  unfold m0lk at h
  rw [wsLay_in_scope hS hX] at h
  have e := Option.some.inj h
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- **The first test.** -/
theorem nsB_head_of_public (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X) : nsB Z 24 = true := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts P.pol lay P.KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  unfold ProofFile.Plain.linksPlain at h₀
  rw [hq, hN] at h₀ hB
  obtain ⟨-, -, -, -, e0⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨ar, e⟩ := (Meaning.built_at hB).2 24 _ e0
  unfold nsB
  rw [e]
  exact decide_eq_true rfl

/-- **The second test.** -/
theorem nRB_of_public (hS : VerifierAndGoals.InScope P = true)
    (hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X) :
    nRB Z OnBytes.Flat.numsFull.rows = true := by
  unfold nRB
  rw [(m0lk_in_scope hS hX).1]
  exact decide_eq_true rfl

/-- **The third test, under hk.** -/
theorem kColB_of_public (hS : VerifierAndGoals.InScope P = true)
    (hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X)
    (hk : (VerifiableInference.Desc.K13.whereOf Z).lin.kCol = 18) :
    kColB (VerifiableInference.Desc.K13.whereOf Z).lin Z.p.X.layers.wsLay = true := by
  unfold kColB
  rw [(m0lk_in_scope hS hX).2, hk]
  exact decide_eq_true rfl

/-- **THE THREE.** -/
theorem numsB_head_of_public (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hX : publicOf P.pol P.KL (some lay) = .ok Z.p.X)
    (hk : (VerifiableInference.Desc.K13.whereOf Z).lin.kCol = 18) :
    numsB Z 24 OnBytes.Flat.numsFull.rows = true := by
  unfold numsB
  rw [nsB_head_of_public hS hR hZ hX, nRB_of_public hS hX, kColB_of_public hS hX hk]
  rfl

end

end LT28.K11Tests

#print axioms LT28.K11Tests.m0lk_full
#print axioms LT28.K11Tests.wsLay_in_scope
#print axioms LT28.K11Tests.m0lk_in_scope
#print axioms LT28.K11Tests.nsB_head_of_public
#print axioms LT28.K11Tests.nRB_of_public
#print axioms LT28.K11Tests.kColB_of_public
#print axioms LT28.K11Tests.numsB_head_of_public
