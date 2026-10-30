-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Statements.lean
(kind K9's soundness lemma): THE STATEMENTS, each a definition of type Prop, and
THE CHECK AGAINST SILLY MEMBERS. Each statement takes the functions of which it speaks as arguments,
so that it can be asked of other functions than K9's.

  T1 add        the algebra of the ledger: what adding one claim does to the ledger's value.
  T2 eqn        the one equation's value on the data is the ledger's value.
  T3 add eqn    the count: if the polynomial in chi that the claims add up to on the data is not the
                zero polynomial, at most d values of chi make the one equation hold. THE DATA D
                STAND OUTSIDE chi.
  K9Law add eqn := T1 add ∧ T2 eqn ∧ T3 add eqn: THE LEMMA IS THIS ONE PROPOSITION.
T1 and T2 have a second clause: the function returns somewhere. It shuts out a function that refuses
everything, and nothing else: a function that returns at one toy ledger alone meets it.

BETWEEN THE ADDING AND THE EQUATION a segment has further steps (the runs behind the batching: they
write the row weights coef of virtual rows). So (T3) has a third function, after, of which it asks
that it leaves the ledger's sums alone (keepsSums); and THE WORLD IS TAKEN AT THE LEDGER AT WHICH
THE EQUATION IS MADE, behind these steps.

THE SILLY MEMBERS, and what Lean says of them (theorems below):
  an adding that returns the ledger unturned       not_T1_idle · not_law_idle
  an adding that refuses everything                not_T1_refuse · not_law_refuse
  an equation that is always 0 = 0                 not_T2_nought · not_law_nought
  an equation that refuses everything              not_T2_refuse · not_law_refuse'
  an equation that is always 1 = 0                 not_T2_never · not_law_never
  both idle: unturned ledger, 0 = 0                not_T3_idle
(T3) ALONE is met by every pair under which no challenge passes (the equation 1 = 0; a refuser): a
verifier that says no to all is sound. That is why the lemma is the conjunction.
The theorem that K9's own functions meet K9Law is in Law/Count.lean.

-/
import Prob.Cnt
import Johnson.Desc.First.Batch.Law.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Equation Ans ledgerEmpty)

/-- **(T1) The algebra of the ledger.** Adding a claim adds chi ^ exponent * the claim's value to
the ledger's value, in every world under every reading; of the ledger only the weights L, the
coefficients LS, the constant, the count of claims and the marks change. -/
def T1 (add : Fork → Claim → Option Fork) : Prop :=
  (∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K) (F G : Fork) (cl : Claim),
    F.LS.size = F.ns → add F cl = some G →
    G.total ρ W = F.total ρ W +
        ρ.val F.theta ^ expo F.planClaimsF F.nClaim cl * claimValue ρ W cl ∧
      G = { F with trees := G.trees, LS := G.LS, c0 := G.c0, nClaim := F.nClaim + 1,
                   kapMapF := G.kapMapF } ∧
      G.LS.size = G.ns ∧ treesFrame G.trees = treesFrame F.trees) ∧
  ∃ F cl, (add F cl).isSome = true

/-- **(T2) The equation is the ledger's value.** On all data, the left side of the one equation is
the ledger's value in the world of these data. -/
def T2 (eqn : LinkCtx → Fork → Ans (Equation × Fork)) : Prop :=
  (∀ (K : Type) [CommRing K] (ρ : Reading K) (D : Bound K) (L : LinkCtx) (F G : Fork)
      (q : Equation),
    eqn L F = .ok (q, G) →
    eqValue ρ (dimsOf L.check) D q = F.total ρ (worldAt ρ L F D)) ∧
  ∀ c : ChainCheck, ∃ L F x, L.check = c ∧ eqn L F = .ok x

/-- The premises of (T3), by name. If the element drawn is chi: F chi: the ledger at which the
claims are added; cls chi: the claims; after chi: the steps between the adding and the equation;
L chi: the segment's record at which the equation is made. -/
structure Premises (add : Fork → Claim → Option Fork) {K : Type} [Field K] (ρ : Reading K)
    (D : Bound K) (L : E → LinkCtx) (F : E → Fork) (cls : E → List Claim)
    (after : E → Fork → Option Fork) (t : List (ℕ × K)) (d : ℕ) : Prop where
  /-- the ledger holds the element drawn -/
  holdsChi : ∀ chi, (F chi).theta = chi
  /-- nothing has been added before the first claim -/
  startsEmpty : ∀ chi, ledgerEmpty (F chi) = true
  /-- the steps between the adding and the equation leave the ledger's sums alone -/
  keepsSums : ∀ chi G H, after chi G = some H → sums H = sums G
  /-- the exponents differ from each other and are at most d -/
  termsOk : TermsOk t d
  /-- FIXED BEFORE THE DRAW: on the data D, in the world of the ledger at which the equation is
  made, the weighted sum of the claims is a polynomial in chi whose terms t do not depend on chi -/
  fixedBefore : ∀ chi G H, (cls chi).foldlM add (F chi) = some G → after chi G = some H →
    claimsSum ρ (worldAt ρ (L chi) H D) (ρ.val chi) (F chi).planClaimsF (F chi).nClaim (cls chi) =
      termsSum t (ρ.val chi)

/-- chi is a challenge at which all claims are added, the steps behind the adding return, the
equation is made, and it holds on D. -/
def Passes (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork))
    {K : Type} [Field K] (ρ : Reading K) (D : Bound K) (L : E → LinkCtx) (F : E → Fork)
    (cls : E → List Claim) (after : E → Fork → Option Fork) (chi : E) : Prop :=
  ∃ G H q G', (cls chi).foldlM add (F chi) = some G ∧ after chi G = some H ∧
    eqn (L chi) H = .ok (q, G') ∧ eqValue ρ (dimsOf (L chi).check) D q = 0

/-- **(T3) The count.** If one of the terms is not 0, the elements of the field that are the reading
of a challenge that passes are at most d. (Where d is the number of the field's elements or more,
this says nothing.) -/
def T3 (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork)) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (ρ : Reading K) (D : Bound K) (L : E → LinkCtx)
      (F : E → Fork) (cls : E → List Claim) (after : E → Fork → Option Fork) (t : List (ℕ × K))
      (d : ℕ),
    Premises add ρ D L F cls after t d → (∃ y ∈ t, y.2 ≠ 0) →
    Prob.cnt (fun x : K => ∃ chi, ρ.val chi = x ∧ Passes add eqn ρ D L F cls after chi) ≤ d

/-- **THE LEMMA, as one proposition.** -/
def K9Law (add : Fork → Claim → Option Fork) (eqn : LinkCtx → Fork → Ans (Equation × Fork)) :
    Prop :=
  T1 add ∧ T2 eqn ∧ T3 add eqn

/-! ## The silly members -/

/-- The claim "1 = 0". -/
def oneIsNought : Claim := { form := Aff.ofConst oneE }

theorem claimValue_one {K : Type} [CommRing K] (ρ : Reading K) (W : World K) :
    claimValue ρ W oneIsNought = 1 := by
  simp [claimValue, oneIsNought, Aff.value_ofConst, ρ.one]

/-- An adding that returns the ledger unturned does not meet (T1). -/
theorem not_T1_idle : ¬ T1 (fun F _ => some F) := by
  intro h
  have h1 := (h.1 Cb.Gl.E Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ {} {} oneIsNought rfl rfl).1
  rw [claimValue_one] at h1
  simp [expo, oneIsNought] at h1

/-- An adding that refuses everything does not meet (T1). -/
theorem not_T1_refuse : ¬ T1 (fun _ _ => none) := by
  intro h
  obtain ⟨F, cl, hx⟩ := h.2
  simp at hx

/-- The equation c = 0. -/
def constantEq (c : E) : Equation := { terms := #[], onMasks := #[], constant := c }

theorem eqValue_constant {K : Type} [CommRing K] (ρ : Reading K)
    (dims : Nat → String → Nat × Nat) (D : Bound K) (c : E) :
    eqValue ρ dims D (constantEq c) = ρ.val c := by
  simp [eqValue, constantEq, maskValue, sumFrom]

/-- An equation that is always 0 = 0 does not meet (T2), if there is a ChainCheck at all. -/
theorem not_T2_nought (c : ChainCheck) : ¬ T2 (fun _ F => .ok (constantEq zeroE, F)) := by
  intro h
  have h1 := h.1 Cb.Gl.E Reading.gl ⟨fun _ _ _ _ => 0, fun _ => 0⟩ { check := c } { c0 := oneE }
    { c0 := oneE } (constantEq zeroE) rfl
  rw [eqValue_constant] at h1
  simp [Fork.total, treesValue, slotsValue, sumFrom, Reading.gl.one, Reading.gl.zero] at h1

/-- An equation that is always 1 = 0 does not meet (T2), if there is a ChainCheck at all. -/
theorem not_T2_never (c : ChainCheck) : ¬ T2 (fun _ F => .ok (constantEq oneE, F)) := by
  intro h
  have h1 := h.1 Cb.Gl.E Reading.gl ⟨fun _ _ _ _ => 0, fun _ => 0⟩ { check := c } {} {}
    (constantEq oneE) rfl
  rw [eqValue_constant] at h1
  simp [Fork.total, treesValue, slotsValue, sumFrom, Reading.gl.one, Reading.gl.zero] at h1

/-- An equation that refuses everything does not meet (T2), if there is a ChainCheck at all. -/
theorem not_T2_refuse (c : ChainCheck) : ¬ T2 (fun _ _ => .error "no") := by
  intro h
  obtain ⟨L, F, x, _, hx⟩ := h.2 c
  simp at hx

/-- The idle pair does not meet (T3): with the one claim "1 = 0" every challenge passes. -/
theorem not_T3_idle (c : ChainCheck) :
    ¬ T3 (fun F _ => some F) (fun _ F => .ok (constantEq zeroE, F)) := by
  intro h
  have h1 := h Cb.Gl.E Reading.gl ⟨fun _ _ _ _ => 0, fun _ => 0⟩ (fun _ => { check := c })
    (fun chi => { theta := chi }) (fun _ => [oneIsNought]) (fun _ G => some G) [(0, 1)] 0
    { holdsChi := fun _ => rfl
      startsEmpty := fun _ => by simp [ledgerEmpty, isZeroE, zeroE, E.mk3]
      keepsSums := fun _ G H hH => by rw [← Option.some.inj hH]
      termsOk := by simp [TermsOk]
      fixedBefore := fun chi G H _ _ => by
        simp only [claimsSum, sumFrom, claimValue_one]
        simp [termsSum, expo, oneIsNought] }
    ⟨(0, 1), by simp, by simp⟩
  rcases Nat.card_eq_zero.mp (Nat.le_zero.mp h1) with h3 | h3
  · exact h3.false ⟨0, zeroE, Reading.gl.zero, _, _, constantEq zeroE, _, rfl, rfl, rfl, by
      rw [eqValue_constant, Reading.gl.zero]⟩
  · exact h3.not_finite inferInstance

/-! ### The same members against the lemma as one proposition -/

theorem not_law_idle (eqn : LinkCtx → Fork → Ans (Equation × Fork)) :
    ¬ K9Law (fun F _ => some F) eqn := fun h => not_T1_idle h.1

theorem not_law_refuse (eqn : LinkCtx → Fork → Ans (Equation × Fork)) :
    ¬ K9Law (fun _ _ => none) eqn := fun h => not_T1_refuse h.1

theorem not_law_nought (c : ChainCheck) (add : Fork → Claim → Option Fork) :
    ¬ K9Law add (fun _ F => .ok (constantEq zeroE, F)) := fun h => not_T2_nought c h.2.1

theorem not_law_never (c : ChainCheck) (add : Fork → Claim → Option Fork) :
    ¬ K9Law add (fun _ F => .ok (constantEq oneE, F)) := fun h => not_T2_never c h.2.1

theorem not_law_refuse' (c : ChainCheck) (add : Fork → Claim → Option Fork) :
    ¬ K9Law add (fun _ _ => .error "no") := fun h => not_T2_refuse c h.2.1

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.not_T1_idle
#print axioms VerifiableInference.Desc.K9L.not_T1_refuse
#print axioms VerifiableInference.Desc.K9L.not_T2_nought
#print axioms VerifiableInference.Desc.K9L.not_T2_never
#print axioms VerifiableInference.Desc.K9L.not_T2_refuse
#print axioms VerifiableInference.Desc.K9L.not_T3_idle
#print axioms VerifiableInference.Desc.K9L.not_law_idle
#print axioms VerifiableInference.Desc.K9L.not_law_refuse
#print axioms VerifiableInference.Desc.K9L.not_law_nought
#print axioms VerifiableInference.Desc.K9L.not_law_never
#print axioms VerifiableInference.Desc.K9L.not_law_refuse'
