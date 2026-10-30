-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscMask.lean: what the masks of a zero-knowledge sumcheck for a polynomial summand hide: the
exact law of all that its prover sends.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdPscMaskProofs.lean. Algebra and laws of random variables only: no protocol term occurs here.

The setting, in the types of Cb/Ld/LdHide.lean: l is the list of all variables of the sumcheck (a
dummy last variable, if there is one, is one of them). The claim is "the sum of a summand over all
variables is τ".
"The summand" has two parts: the polynomial summand in the maps, and the value of a linear form in
incoming masks (entries of earlier blocks) times the product ψ_1 .. ψ_k of the public polynomials,
whose sum is that value; τ is the target of the two together. The prover holds two kinds of mask
entries of its own:
    W : HIdx l → E, the coefficients of one hiding polynomial U;
    c : Cx → E, the inner masks: they change the summand, but not its sum, and they blind the values
      that are shown at the end.
It sends, all in the clear: μ = the sum of U; after the verifier's coefficient ε, round by round at
the challenges γ, the round polynomials q of U + ε (summand); at the end the values v a, for a in
the set A of the maps whose values are shown.
Here the summand enters only through its round polynomials "u c" (they may depend on the inner
masks) and the maps only through the values "v c". What is asked of them:
    (cons) for every c the round polynomials u c are consistent with the claimed sum τ
           (`Spec.rounds_cons`: the round polynomials of a summand are consistent with its sum; so
           this says "the inner masks do not change the sum, and the claim holds");
    (val) uniform c gives uniform values. `Spec.psc_val_own`: so it is for v c a = F a + β c a with
          β ≠ 0 (one inner mask for each value, the case of a dummy variable with challenge β); for
          values that are a fixed vector plus a surjective additive image of c:
          `Prob.map_unif_add_addMonoidHom`.
The simulator (`pscSim`) is given l (public), the set A of the maps whose values are shown, τ, ε, γ
and nothing else: no state beyond what l holds, no witness, no symbol of an oracle, no answer to a
sample. It draws coefficients W' and values v' uniformly and outputs the sum of U', the round
polynomials of U' + ε τ ψ_1 .. ψ_k, and v': it runs the honest prover on the summand "τ times the
product of the public polynomials".

Consistent with a claimed sum σ (`HCons`, Cb/Ld/LdHide.lean): the first round polynomial sums to σ,
each later one to the value of the one before at its challenge. `HVar.OK`: the variable's sum of its
public polynomial ψ is 1.

Main names. All but the first and the third have the hypothesis that every variable of l has
`HVar.OK`.
  `Spec.rounds_cons`: round polynomials of a summand (`HRounds`) are consistent (`HCons`) with its
    sum.
  `Spec.psc_tr_law`: the transcript: for every fixed round polynomials u₀ consistent with τ, the
    pair (μ, q) has the law of the simulator's pair. So its law is one and the same whatever the
    witness and the inner masks are (u₀ is any consistent choice): c has no influence on that law,
    although the last round polynomials do contain c.
  `Spec.psc_val_own`: the values.
  `Spec.psc_mask_law`: all together, under (cons) and (val): over uniform (W, c) the triple
    (μ, q, v) has exactly the law of the simulator.
  `Spec.psc_sim_unif`: what that law is: the simulator's map is injective, and its image is the set
    of triples that pass the checks for the claim μ + ε τ (`PPass`); so the law is uniform on these:
    pair uniform on the passing pairs, values uniform, the two independent.
  `Spec.psc_sim_card`: their number: one factor |E| for each coefficient of U and each value.
No value is shown: A and Cx empty; the statements hold as they stand, and the triple is the pair.

Limits: this file does not say where the entries W, c lie in the rows of an oracle, and that nothing
else reads them: Cb/Ld/LdPscZk.lean says at which entries of the messages they lie (not in which
rows) and which parts of this block read them (`PscPar.Own`, `PscPar.OwnOK`; see its Limits). This
file says nothing on what earlier messages (the oracle that holds the masks, the answer to its
sample) show of W and c. It says nothing on soundness. E is a finite field (ring, module and
challenges in one).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdHide
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob

section Defs
variable {E : Type} [Field E]

/-- the block's own mask entries: the coefficients of the hiding polynomial, the inner masks -/
abbrev PMask (l : List (HVar E)) (Cx : Type) : Type := (HIdx l → E) × (Cx → E)

/-- all that the prover sends: the sum of the hiding polynomial, the round polynomials, the values
at the end -/
abbrev PMsg (l : List (HVar E)) (A : Type) : Type := E × (RIdx l → E) × (A → E)

variable {Cx A : Type}

/-- What the honest prover sends, as a function of its own masks. u c: the round polynomials of the
summand; v c: the values. -/
def pscMsg (l : List (HVar E)) (γ : HPt l) (ε : E) (u : (Cx → E) → RIdx l → E)
    (v : (Cx → E) → A → E) (M : PMask l Cx) : PMsg l A :=
  (hMu l M.1, hTr l 0 M.1 γ + ε • u M.2, v M.2)

/-- what the simulator outputs, as a function of its coins -/
def pscSimMsg (l : List (HVar E)) (γ : HPt l) (ε τ : E) (s : (HIdx l → E) × (A → E)) : PMsg l A :=
  (hMu l s.1, hTr l (ε * τ) s.1 γ, s.2)

/-- The simulator. -/
def pscSim [Fintype E] (l : List (HVar E)) (A : Type) [Fintype A]
    [DecidableEq A] (γ : HPt l) (ε τ : E) : PMF (PMsg l A) :=
  (unif ((HIdx l → E) × (A → E))).map (pscSimMsg l γ ε τ)

/-- The triple passes the checks: the round polynomials are consistent with the claimed sum μ + ε τ.
-/
def PPass (l : List (HVar E)) (γ : HPt l) (ε τ : E) (p : PMsg l A) : Prop :=
  HCons l (p.1 + ε * τ) p.2.1 γ

end Defs

namespace Spec

/-- States: the round polynomials of a summand (`HRounds`) are consistent (`HCons`) with its sum. -/
def rounds_cons : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (l : List (HVar R))
      (f : HPt l → M) (q : RIdx l → M) (γ : HPt l),
    HRounds l f q γ → HCons l (hSumAll l f) q γ

section
variable (E : Type) [Field E] [Fintype E]

/-- The transcript: one law, whatever the round polynomials of the summand are. (not all hypotheses
are named here: see the statement below) -/
def psc_tr_law : Prop :=
  ∀ l : List (HVar E), (∀ v ∈ l, v.OK) →
    ∀ (γ : HPt l) (ε τ : E) (u₀ : RIdx l → E), HCons l τ u₀ γ →
      (unif (HIdx l → E)).map (fun W => (hMu l W, hTr l 0 W γ + ε • u₀)) =
        (unif (HIdx l → E)).map fun W => (hMu l W, hTr l (ε * τ) W γ)

/-- The values: one inner mask for each, with a non-zero factor. -/
def psc_val_own : Prop :=
  ∀ (A : Type) [Fintype A] [DecidableEq A] (F : A → E) (β : E),
    β ≠ 0 → (unif (A → E)).map (fun c a => F a + β * c a) = unif (A → E)

/-- States, under the hypotheses below: all that the prover sends has the law of the simulator. -/
def psc_mask_law : Prop :=
  ∀ l : List (HVar E), (∀ v ∈ l, v.OK) →
    ∀ (Cx A : Type) [Fintype Cx] [DecidableEq Cx] [Fintype A] [DecidableEq A] (γ : HPt l) (ε τ : E)
        (u : (Cx → E) → RIdx l → E) (v : (Cx → E) → A → E),
      (∀ c, HCons l τ (u c) γ) → (unif (Cx → E)).map v = unif (A → E) →
      (unif (PMask l Cx)).map (pscMsg l γ ε u v) = pscSim l A γ ε τ

/-- States, under the hypotheses below: the simulator's map is injective, and its image is the set
of triples that pass the checks. So the simulator's law is uniform on the triples that pass the
checks. -/
def psc_sim_unif : Prop :=
  ∀ l : List (HVar E), (∀ v ∈ l, v.OK) →
    ∀ (A : Type) (γ : HPt l) (ε τ : E),
      Function.Injective (pscSimMsg (A := A) l γ ε τ) ∧
      ∀ p : PMsg l A, PPass l γ ε τ p ↔ ∃ s, pscSimMsg l γ ε τ s = p

/-- The number of triples that pass the checks. -/
def psc_sim_card : Prop :=
  ∀ l : List (HVar E), (∀ v ∈ l, v.OK) →
    ∀ (A : Type) [Fintype A] [DecidableEq A] (γ : HPt l) (ε τ : E),
      cnt (fun p : PMsg l A => PPass l γ ε τ p) =
        Fintype.card E ^ (Fintype.card (HIdx l) + Fintype.card A)

end
end Spec
end Cb
