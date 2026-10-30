-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTest.lean: AN ARGUMENT SYSTEM WHOSE COMMITTER AND PROVER GO TO ONE HASH FUNCTION BY
THE THIRD EXIT (overOneF, Rom/OverOneF.lean), WHERE A FAILED TRY OF A SEARCH ASKS ONE BLOCK.
overOneArgF turns the prover alone; overOneArgFF turns both. The verifier stays at overOne.

How. Index privacy and completeness read the honest side only through the law of its output at each
fixed hash function: the real experiment is eager in the hash function, and a view holds the
adversary's own queries. So two schemes with one verifier whose committer and prover have the same
law at every hash function (SameHonestLaw) have the same completeness error and the same index
privacy, with the same simulator (completeness_congr, privacy_congr). Which blocks the honest side
asked is in no view. Under FactorsBy the third exit has the first exit's law at every hash function
(runEager_overOneF_eq), so privacy_overOne and completeness_overOne carry.

Nothing here is a goal. FactorsBy is a premise, as in every statement on values of the third exit.
Of the honest side's query log nothing is said.
-/
import Rom.OverOneF
import Rom.ExitPriv

set_option autoImplicit false

namespace Rom
open ZKCP
open scoped ENNReal

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- Two schemes over the same oracles with one verifier, whose committer and prover have the same
law at every fixing of the oracles. -/
structure SameHonestLaw {S : OSpec} (A A' : Gen.Arg S I X W IVK ISK Pf) : Prop where
  C : ∀ g i, (A'.C i).runEager g = (A.C i).runEager g
  P : ∀ g k b, (A'.P k b).runEager g = (A.P k b).runEager g
  V : A'.V = A.V

section Congr
variable {S : OSpec} {A A' : Gen.Arg S I X W IVK ISK Pf}

theorem realLoop_congr (h : SameHonestLaw A A') (Z : Gen.ViewEnv S IVK X W Pf) (g : Fam S)
    (isk : ISK) : ∀ (Vt : Gen.AdvVerifier S X Pf) (n : ℕ) (v : Gen.View S IVK X Pf),
      (Gen.realLoop A' Z isk Vt n v).runEager g = (Gen.realLoop A Z isk Vt n v).runEager g
  | .halt, _, _ => rfl
  | .query o q k, n, v => by
    simp only [Gen.realLoop, OComp.runEager]
    exact realLoop_congr h Z g isk (k _) n _
  | .sample m k, n, v => by
    simp only [Gen.realLoop, OComp.runEager]
    exact congrArg _ (funext fun r => realLoop_congr h Z g isk (k r) n _)
  | .request _, 0, _ => rfl
  | .request k, n + 1, v => by
    simp only [Gen.realLoop]
    cases Z v with
    | none => rfl
    | some b =>
      simp only [OComp.runEager_bind]
      rw [h.P g isk b.pairs]
      exact congrArg _ (funext fun πs => realLoop_congr h Z g isk (k _) n _)

theorem realExp_congr (h : SameHonestLaw A A') (Vt : IVK → Gen.AdvVerifier S X Pf)
    (Z : Gen.ViewEnv S IVK X W Pf) (i : I) (N : ℕ) (g : Fam S) :
    (Gen.realExp A' Vt Z i N).runEager g = (Gen.realExp A Vt Z i N).runEager g := by
  have e1 : Gen.realExp A' Vt Z i N = (A'.C i).bind fun key =>
      Gen.realLoop A' Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩ := rfl
  have e2 : Gen.realExp A Vt Z i N = (A.C i).bind fun key =>
      Gen.realLoop A Z key.2 (Vt key.1) N ⟨key.1, [], [], []⟩ := rfl
  rw [e1, e2, OComp.runEager_bind, OComp.runEager_bind, h.C g i]
  exact congrArg _ (funext fun key => realLoop_congr h Z g key.2 _ N _)

/-- **Index privacy reads the honest side through its law alone.** -/
theorem privacy_congr {R : Gen.RelPair I X W PP} {B : ℕ} {Sim : Gen.Simulator S PP IVK X Pf}
    {ζ : ℕ → ℕ → ℝ≥0∞} (h : SameHonestLaw A A') (hp : Gen.HasIndexPrivacyWith R A B Sim ζ) :
    Gen.HasIndexPrivacyWith R A' B Sim ζ := by
  intro i Z hZ tV Vt N hb
  obtain ⟨h1, h2⟩ := hp i Z hZ tV Vt N hb
  have e : (fun T => Pr (Gen.realExp A' Vt Z i N) (fun _ => T)) =
      fun T => Pr (Gen.realExp A Vt Z i N) (fun _ => T) :=
    funext fun T => Pr_congr_runEager (realExp_congr h Vt Z i N) _
  refine ⟨?_, h2⟩
  rw [e]
  exact h1

theorem verifyAll_congr (h : SameHonestLaw A A') (ivk : IVK) :
    ∀ l : List (X × Pf), Gen.verifyAll A' ivk l = Gen.verifyAll A ivk l
  | [] => rfl
  | (x, π) :: rest => by
    show ((A'.V ivk x π).bind fun c => (Gen.verifyAll A' ivk rest).bind fun cs =>
      OComp.pure (c && cs)) = ((A.V ivk x π).bind fun c => (Gen.verifyAll A ivk rest).bind fun cs =>
      OComp.pure (c && cs))
    rw [h.V, verifyAll_congr h ivk rest]

theorem completenessExp_congr (h : SameHonestLaw A A') (i : I) (b : List (X × W)) (g : Fam S) :
    (Gen.completenessExp A' i b).runEager g = (Gen.completenessExp A i b).runEager g := by
  have e1 : Gen.completenessExp A' i b = (A'.C i).bind fun key =>
      (A'.P key.2 b).bind fun πs =>
        Gen.verifyAll A' key.1 ((b.map Prod.fst).zip πs.val) := rfl
  have e2 : Gen.completenessExp A i b = (A.C i).bind fun key =>
      (A.P key.2 b).bind fun πs =>
        Gen.verifyAll A key.1 ((b.map Prod.fst).zip πs.val) := rfl
  rw [e1, e2, OComp.runEager_bind, OComp.runEager_bind, h.C g i]
  refine congrArg _ (funext fun key => ?_)
  rw [OComp.runEager_bind, OComp.runEager_bind, h.P g key.2 b]
  refine congrArg _ (funext fun πs => ?_)
  rw [verifyAll_congr h]

/-- **Completeness reads the honest side through its law alone.** -/
theorem completeness_congr {R : Gen.RelPair I X W PP} {B : ℕ} {a : ℝ≥0∞}
    (h : SameHonestLaw A A') (hc : Gen.HasCompletenessError R A B a) :
    Gen.HasCompletenessError R A' B a := fun i b hb =>
  (Pr_congr_runEager (completenessExp_congr h i b) _).trans_le (hc i b hb)

end Congr

section Exit
variable {S : OSpec} (m : OracleCoding S lam) (more : More S lam)

/-- **The scheme over one hash function with committer and prover by the third exit.** -/
def overOneArgFF (A : Gen.Arg S I X W IVK ISK Pf) : Gen.Arg (rom lam) I X W IVK ISK Pf where
  C := fun i => (A.C i).overOneF m more
  P := fun k b => (A.P k b).overOneF m more
  V := fun v x π => (A.V v x π).overOne m

variable {A : Gen.Arg S I X W IVK ISK Pf}

theorem sameHonestLaw_overOneFF (hC : ∀ i, (A.C i).FactorsBy (AgreeF m more))
    (hP : ∀ k b, (A.P k b).FactorsBy (AgreeF m more)) :
    SameHonestLaw (schemeOverOneHashFunction m A) (overOneArgFF m more A) :=
  ⟨fun g i => runEager_overOneF_eq m more g _ (hC i),
    fun g k b => runEager_overOneF_eq m more g _ (hP k b), rfl⟩

/-- **Completeness at the third exit**, at the same error. -/
theorem completeness_overOneFF (R : Gen.RelPair I X W PP) (B : ℕ) (a : ℝ≥0∞)
    (hC : ∀ i, (A.C i).FactorsBy (AgreeF m more))
    (hP : ∀ k b, (A.P k b).FactorsBy (AgreeF m more))
    (h : Gen.HasCompletenessError R A B a) :
    Gen.HasCompletenessError R (overOneArgFF m more A) B a :=
  completeness_congr (sameHonestLaw_overOneFF m more hC hP) (completeness_overOne m R A B a h)

/-- **Index privacy at the third exit**, with the simulator and the bound of the first exit. -/
theorem privacy_overOneFF (R : Gen.RelPair I X W PP) (B : ℕ) (Sim : Gen.Simulator S PP IVK X Pf)
    (ζ : ℕ → ℕ → ℝ≥0∞) (hC : ∀ i, (A.C i).FactorsBy (AgreeF m more))
    (hP : ∀ k b, (A.P k b).FactorsBy (AgreeF m more))
    (h : Gen.HasIndexPrivacyWith R A B Sim ζ) :
    Gen.HasIndexPrivacyWith R (overOneArgFF m more A) B (simOne m Sim) ζ :=
  privacy_congr (sameHonestLaw_overOneFF m more hC hP) (privacy_overOne m R A B Sim ζ h)

end Exit

end Rom

#print axioms Rom.privacy_congr
#print axioms Rom.completeness_congr
#print axioms Rom.sameHonestLaw_overOneFF
#print axioms Rom.completeness_overOneFF
#print axioms Rom.privacy_overOneFF
