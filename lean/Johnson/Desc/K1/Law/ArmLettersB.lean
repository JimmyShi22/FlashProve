-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmLettersB.lean: TWO OF THE SENTENCES ON LETTERS THAT THE PAYERS hAtt2_ofB AND hLay_ofB
(Johnson/Desc/K1/Law/ArmAttIn.lean, ArmLayIn.lean) LEAVE, AS TESTS WITH CODE ON PUBLIC DATA, each with its law.
  `hKlB X trees d`   at each of the attention links: the public parameters have a plan Ap, the plan's list of the
                   ledger's arrays has an entry at the number of the array of the reads, and its number of
                   columns is plannedK Ap + d. d = 0: THE TEST. d = 1: ITS BENT TWIN (it must reject wherever the
                   test accepts: there are twelve attention links)
  `hKl_of_B`         hKlB X trees 0 = true gives hKl
  `hnmB names arrayOf`   at each of the 25 links: names l is the written list of link l's arrays
  `hnm_of_B`         hnmB … = true gives hnm
  `attCount` [kernel]   the test looks at twelve links
  two kernel evaluations of hnmB at made-up lists: alike: true; one name bent: false
NO TEST FOR hUL: it is an equation of functions; at the closed constant it comes down to
`Look.tlAt X l = some hp.tl`, and the parameters' type has no decidable equality.
What is not claimed. The tests' values at any public file. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmLayIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First.Att.P (plannedK)

/-- **The test for hKl** (d = 0), and its bent twin (d = 1). -/
def hKlB (X : Verify.Public) (trees : ℕ → List First.FillSent.TreeLook) (d : ℕ) : Bool :=
  (List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == .attention) ||
      match X.A[l / 2]? with
      | none => false
      | some Ap =>
        match (trees l)[Ap.iU3]? with
        | none => false
        | some t => t.2.1 == plannedK Ap + d

theorem hKl_of_B {X : Verify.Public} {trees : ℕ → List First.FillSent.TreeLook}
    (h : hKlB X trees 0 = true) :
    ∀ l Ap t, (linksFull[l]?).getD .layers = .attention → X.A[l / 2]? = some Ap →
      (trees l)[Ap.iU3]? = some t → t.2.1 = plannedK Ap := by
  intro l Ap t hs hA ht
  have hl : l < 25 := by
    by_contra hc
    have e : linksFull[l]? = none := List.getElem?_eq_none (by
      have : linksFull.length = 25 := by decide
      omega)
    rw [e] at hs
    cases hs
  have h0 := List.all_eq_true.1 h l (List.mem_range.2 hl)
  rw [hs, hA] at h0
  dsimp only at h0
  rw [ht] at h0
  simpa using h0

/-- How many links hKlB looks at. -/
theorem attCount :
    ((List.range 25).filter fun l => (linksFull[l]?).getD .layers == .attention).length = 12 := by
  decide +kernel

/-- **The test for hnm.** -/
def hnmB (names : ℕ → Array (ℕ × String)) (arrayOf : Array (Array (ℕ × String))) : Bool :=
  (List.range 25).all fun l => names l == arrayOf.getD l #[]

theorem hnm_of_B {names : ℕ → Array (ℕ × String)} {arrayOf : Array (Array (ℕ × String))}
    (h : hnmB names arrayOf = true) : ∀ l, l < 25 → names l = arrayOf.getD l #[] :=
  fun l hl => eq_of_beq (List.all_eq_true.1 h l (List.mem_range.2 hl))

theorem hnm_alike : hnmB (fun l => if l = 3 then #[(3, "a")] else #[])
    #[#[], #[], #[], #[(3, "a")]] = true := by decide +kernel

/-- **BENT**: one name differs. -/
theorem hnm_fails : hnmB (fun l => if l = 3 then #[(3, "a")] else #[])
    #[#[], #[], #[], #[(3, "b")]] = false := by decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hKl_of_B
#print axioms VerifiableInference.Desc.K1.attCount
#print axioms VerifiableInference.Desc.K1.hnm_of_B
#print axioms VerifiableInference.Desc.K1.hnm_alike
#print axioms VerifiableInference.Desc.K1.hnm_fails
