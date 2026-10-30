-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallChanceAll.lean: THE SMALLNESS TEST: THE COUNT OF Johnson/P1K8R/FallAtStepAll.lean
AS A CHANCE OVER A LIST OF CHALLENGES, UNDER A NAMED LAW, FOR EVERY FUNCTION front WITH THREE
PROPERTIES. Lemmas; none of the library's goals. No prover stands in them; nothing on completeness,
soundness or hiding. An assembly: no new argument.

The law (Johnson/Desc/K8/Honest/ChanceOfCounts.lean): ι a finite type of rounds, A i round i's
challenges, the list f : ∀ i, A i uniform. j: the batching's round. el: the field element that round
j's challenge gives; at most w challenges give one element (w = 1 where A j is the round's typed
challenges; the sampler's number where it is its written verifier messages that pass the test of
work).
  **`fall_chance_all`**   in the goals' scope, at every segment l < 25, K := 14 l + 9, or 347 at the
      head's: for every front : (∀ i, A i) → Option (the statement's public part × the state) such
      that (free) it does not read round j's challenge, (reach) every value of it is a state reached
      at number K of the flat list, (bound) d bounds the exponents at whatever such a state holds:
      the chance that front returns a state at which the seated batching block's step says yes at
      some round that has drawn el (f j) in reduced words and `selfUnits` says no at the state that
      the step returns is at most nU[2] * d * w / (the number of round j's challenges)
  **`fall_chance_typed`**   the same at the typed layer (Johnson/Desc/K8/Honest/ChiTyped.lean):
      round j's challenges are typed challenges of the batching's round (through an injective view);
      the step is asked at a round whose challenge is the typed challenge's own untyped view; the
      bound is nU[2] * d / (the number of round j's challenges)
Limits. front IS A LETTER: that any run of a prover is such a function is not shown. The law is
named, not derived: nothing says that the challenges of a run are drawn so (the test of work; that a
random oracle's answers along a run are such a list). One of the tests behind the adding. No sum
over segments. d is tied to no number of the plan; no number is evaluated. That any state is reached
is not said: where front returns nothing the event is empty.

-/
import Johnson.P1K8R.FallAtStepAll
import Johnson.Desc.K8.Honest.ChanceOfCounts
import Johnson.Desc.K8.Honest.ChiTyped

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Tie.Pv.Tail.Port (topOf)
open scoped ENNReal

/-- **The count at the step, at all 25 segments, as a chance over the list.** -/
theorem fall_chance_all {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (el : A j → Cb.Gl.E) (w : ℕ)
        (_ : ∀ x, Prob.cnt (fun a => el a = x) ≤ w)
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : ∀ f a, front (Function.update f j a) = front f)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn.elems = [Slice.ofE (el (f j))] ∧ b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d * w : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hcount⟩ := fall_at_step_all hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j el w hw front hfree hreach d hd
  exact chance_of_counts j el w hw front hfree
    (fun zs x => ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
      r.drawn.elems = [Slice.ofE x] ∧ b.step 0 zs.2 [r] cols = .ok (t, m) ∧
        zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true)
    ((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d)
    (fun f zs hf => hcount zs.1 zs.2 d (hreach f zs hf) (hd f zs hf))

/-- **The same at the typed layer**: round j's challenges are typed challenges of the batching's
round; the step is asked at a round whose challenge is the typed challenge's own untyped view. -/
theorem fall_chance_typed {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i, Fintype (A i)]
        [∀ i, Nonempty (A i)] (j : ι) (k : Fmt.Kind) (_ : k ≠ .seeds) (_ : k ≠ .sealed)
        (view : A j → Run.Ch .two (K9.entry p) k) (_ : Function.Injective view)
        (front : (∀ i, A i) → Option (ProofFile.InstPub × S))
        (_ : ∀ f a, front (Function.update f j a) = front f)
        (_ : ∀ f zs, front f = some zs →
          Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) zs) (d : ℕ)
        (_ : ∀ f zs, front f = some zs → ∀ tl F funs, zs.2.tl? = some tl →
          zs.2.fork? = some F → zs.2.funs? = some funs → F.planClaimsF + topOf tl funs ≤ d + 1),
        Prob.pr (Prob.unif (∀ i, A i)) {f | ∃ zs, front f = some zs ∧
          ∃ (r : Fmt.RoundView) (cols : List Desc.OpenedColumn) (t : S) (m : Nat),
            r.drawn = Run.drawnOf .two (K9.entry p) k (view (f j)) ∧
              b.step 0 zs.2 [r] cols = .ok (t, m) ∧
              zeroUnitAt (ProofFile.k8NU Bs.G₀ X) t = true} ≤
          (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * d : ℕ) : ℝ≥0∞) / Fintype.card (A j) := by
  obtain ⟨b, p, X, hb, hp, hX, hall⟩ := fall_chance_all hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, ?_⟩
  intro ι _ _ A _ _ j k h5 h6 view hview front hfree hreach d hd
  have h1 := oneElem_bat p k h5 h6
  have hw : ∀ x, Prob.cnt (fun a => elOf (K9.entry p) k (view a) = x) ≤ 1 := fun x =>
    Prob.cnt_le_one fun a a' ha ha' => hview (elems_inj _ h1 _ _ (ha.trans ha'.symm))
  have h := hall j (fun a => elOf (K9.entry p) k (view a)) 1 hw front hfree hreach d hd
  rw [Nat.mul_one] at h
  refine (Prob.pr_mono _ fun f hf => ?_).trans h
  obtain ⟨zs, hz, r, cols, t, m, hr, hst, hzu⟩ := hf
  refine ⟨zs, hz, r, cols, t, m, ?_, hst, hzu⟩
  rw [hr, shows_chi _ k h1]
  rfl

end P1K8

#print axioms P1K8.fall_chance_all
#print axioms P1K8.fall_chance_typed
