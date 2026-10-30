-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SeamFactors.lean: the factor of a seed that the protocol's verifier
samples for the link proof's own OOD samples is never 0.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

Under Johnson/LinkSim/ no other file calls factorAt, fr_factors or fr_lSeed: they are not on the
proof chain. That chain gets the non-zero factor through the honest prover's own invariant instead
(Johnson/LinkSim/AtText/SeamClaim.lean).

What this file proves. Spec.factorAt, proved as factorAt, holds for every rounds' description ds and
round n that pass the test facOk. At every verifier message, round n has sampled an element x at the
place facIx ds n, x read in the field is not 0, and unitOf leaves it unchanged. At the full-size
parameters (dsFull), fr_factors applies this to the five rounds that sample a seed of the link
proof's own OOD samples: 1 (the first sample, on the two folded rows), and 15, 23, 30 and 37 (the
switches'). fr_lSeed then says that the first seed's factor, as the prover's algorithm has it, is
the sampled element read in the field, and is not 0.

Why. The prover's algorithm reads a seed's factor through unitOf (OnBytes/Slice/CorePeel.lean),
which puts 1 in place of a sampled element 0 (lSeed, Johnson/Prover/Link/LinkAll.lean; ansAt,
Johnson/Prover/Link/BodyAll.lean). The verifier's state reads the sampled element itself. If a
factor 0 were sampled, the two would differ, and the claim left at the base case could be false at
the honest prover's last message. At the challenges that the protocol's verifier messages give, this
does not happen, at any verifier message.

The other names (namespace OnBytes.LinkSim.Seam).
  facIx ds n      the place of the last element that round n declares.
  facOk ds n      a Boolean test on the rounds' description: round n declares at least one
                  element, no more never-0 elements than elements, and its last element is declared
                  never 0.
  both_run        at every verifier message, each round's challenges satisfy the format's six
                  conditions (FitsDrawn, Johnson/Desc/K12/Law/FitWritten.lean), and their words are
                  below the prime.
  fr_facOk        at the full-size parameters, facOk accepts rounds 1, 15, 23, 30 and 37.
  fr_facNo        a control that checks that the test can fail: it rejects round 16, which samples
                  positions alone.
  fr_facIx1       at round 1 the place is the one that lSeed reads.
  cubeAt, fr_cube   the number by which the prover's answer at a switch reads the factor's place
                  (the last argument of ansAt in sAns, Johnson/Prover/Link/BodyAll.lean), with the
                  codes as a variable. At the plan's own codes it is facIx at rounds 15, 23, 30
                  and 37.
  unit_parts      a control on the other side: at the element 0, which no round of the protocol
                  samples at such a place, unitOf differs from the sampled element.

Limits.
- Only at one choice of challenge types: challenges as hash blocks, over the field GF (ckP .two).
- fr_cube is about the plan's own codes. At the four switches, the prover's algorithm computes its
  number from the codes in the verifier's state after the fold; that the verifier's state holds
  these codes along a run is not proved here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SeamSizes
import Johnson.Prover.Link.BodyAtFull
import Johnson.Prover.Link.BodyUnit
import Johnson.Prover.Send.Factors

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (frP p12Of)
open H2K.Pub (sgOf)
open OnBytes.Flat (dsFull)
open Johnson.Prover.Link
open _root_.Iop (Rho)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD uL drawnSL)

/-- The place of the last element that round n declares. -/
def facIx (ds : List RD) (n : ℕ) : ℕ := ((ds[n]?).map (·.entry.drawE)).getD 0 - 1

/-- A Boolean test: round n's last declared element is declared never 0. -/
def facOk (ds : List RD) (n : ℕ) : Bool :=
  match ds[n]? with
  | some d =>
    decide (d.entry.drawNZ ≤ d.entry.drawE) && decide (0 < d.entry.drawE) &&
      ((Fmt.dsElems d.entry d.kind)[d.entry.drawE - 1]? == some Fmt.Draw.elemNZ)
  | none => false

/-- At every verifier message, each round's challenges satisfy the format's six conditions, and
their words are below the prime. -/
theorem both_run : ∀ (ds : List RD) (ρ : Rho (uL (ckP .two) ds)),
    List.Forall₂ (fun (w : RD) (D : Fmt.Drawn) =>
      H2K.Fit.FitsDrawn w.entry w.kind D ∧ ∀ x ∈ D.elems, ltE x = true) ds
      (drawnSL (ckP .two) ds ρ)
  | [], _ => .nil
  | d :: ds, (_, ρ) =>
    .cons ⟨H2K.Fit.fitsDrawn_ckP _ _ _, ltE_dr d.entry d.kind _⟩ (both_run ds ρ)

/-- Statement only; proved as factorAt below. **A seed's factor is never 0**: where facOk accepts
round n, at every verifier message the element at facIx is not 0 in the field, and unitOf leaves it
unchanged. -/
def Spec.factorAt : Prop :=
  ∀ (ds : List RD) (n : ℕ), facOk ds n = true → ∀ ρ : Rho (uL (ckP .two) ds),
    ∃ x, (drawsOf (drawnSL (ckP .two) ds ρ) n).elems[facIx ds n]? = some x ∧
      readE (E.ofTriple x) ≠ 0 ∧ (unitOf (readE (E.ofTriple x))).val = readE (E.ofTriple x)

/-- Proof of Spec.factorAt. -/
theorem factorAt : Spec.factorAt := by
  intro ds n hok ρ
  unfold facOk at hok
  cases hd : ds[n]? with
  | none =>
    rw [hd] at hok
    cases hok
  | some d =>
    rw [hd] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨h1, h2⟩, h3⟩ := hok
    obtain ⟨D', hD', hfit, hlt⟩ := forall₂_get (both_run ds ρ) n d hd
    have eD : drawsOf (drawnSL (ckP .two) ds ρ) n = D' := by
      show (drawnSL (ckP .two) ds ρ).getD n _ = D'
      rw [List.getD_eq_getElem?_getD, hD']
      rfl
    have eI : facIx ds n = d.entry.drawE - 1 := by
      unfold facIx
      rw [hd]
      rfl
    obtain ⟨x, hx, hnz⟩ := forall₂_get hfit.nz _ _ h3
    have hx0 : x ≠ (0, 0, 0) := hnz rfl
    have hz : Own.allZero (E.ofTriple x) = false := Johnson.Prover.Send.isZeroE_ofTriple x hx0
    have hl : ltE x = true := hlt x (List.mem_of_getElem? hx)
    exact ⟨x, by rw [eD, eI]; exact hx, readE_ne_zero_of x hl hz, unit_of_factor x hl hz⟩

/-! ## At the full-size parameters -/

set_option maxRecDepth 100000 in
/-- At the full-size parameters, facOk accepts rounds 1, 15, 23, 30 and 37. -/
theorem fr_facOk : [1, 15, 23, 30, 37].all (facOk dsFull) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A control that checks that the test can fail: it rejects round 16, which samples positions
alone. -/
theorem fr_facNo : facOk dsFull 16 = false := by decide +kernel

set_option maxRecDepth 100000 in
/-- At round 1, facIx is the place that lSeed reads. -/
theorem fr_facIx1 : facIx dsFull 1 = frS.P.aR + frS.P.aP := by decide +kernel

/-- **At the five rounds that sample a seed, at every verifier message, the factor is not 0.** -/
theorem fr_factors (ρ : Rho (uL (ckP .two) dsFull)) : ∀ n ∈ [1, 15, 23, 30, 37],
    ∃ x, (drawsOf (drawnSL (ckP .two) dsFull ρ) n).elems[facIx dsFull n]? = some x ∧
      readE (E.ofTriple x) ≠ 0 ∧ (unitOf (readE (E.ofTriple x))).val = readE (E.ofTriple x) :=
  fun n hn => factorAt dsFull n (List.all_eq_true.1 fr_facOk n hn) ρ

/-- **The first seed's factor, as the prover's algorithm has it, is the sampled element**, and it is
not 0. -/
theorem fr_lSeed (ρ : Rho (uL (ckP .two) dsFull)) :
    ((lSeed frS (drawsOf (drawnSL (ckP .two) dsFull ρ))).2 : GEˣ).val =
        readE (((drawsOf (drawnSL (ckP .two) dsFull ρ) 1).elems.map E.ofTriple).getD
          (frS.P.aR + frS.P.aP) zeroE) ∧
      readE (((drawsOf (drawnSL (ckP .two) dsFull ρ) 1).elems.map E.ofTriple).getD
        (frS.P.aR + frS.P.aP) zeroE) ≠ 0 := by
  obtain ⟨x, hx, h0, h1⟩ := fr_factors ρ 1 (by simp)
  rw [fr_facIx1] at hx
  have e : ((drawsOf (drawnSL (ckP .two) dsFull ρ) 1).elems.map E.ofTriple).getD
      (frS.P.aR + frS.P.aP) zeroE = E.ofTriple x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]
    rfl
  refine ⟨?_, by rw [e]; exact h0⟩
  show (unitOf (readE (((drawsOf (drawnSL (ckP .two) dsFull ρ) 1).elems.map E.ofTriple).getD
    (frS.P.aR + frS.P.aP) zeroE))).val = _
  rw [e]
  exact h1

/-- The number by which the prover's answer at switch j reads the factor's place, with the codes as
a variable. -/
def cubeAt (Kd : Codes) (p : P12) (j : ℕ) (next : Fmt.M1.Stage) : ℕ :=
  (Send.cube Kd
    (switchTargetStage ((stageAt p (j + 1) next).getD default).code
      ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1).shape).bits

set_option maxRecDepth 100000 in
/-- At the plan's own codes that number is the place of the last declared element. -/
theorem fr_cube :
    (List.range 4).map (fun j => cubeAt frP.codes (p12Of frP) j (frRest.getD j default)) =
      [15, 23, 30, 37].map (facIx dsFull) := by decide +kernel

/-- A control: at the element 0 unitOf differs from the sampled element. -/
theorem unit_parts :
    (unitOf (readE (E.ofTriple (0, 0, 0)))).val ≠ readE (E.ofTriple (0, 0, 0)) := by
  have h : readE (E.ofTriple (0, 0, 0)) = 0 := readE_of_isZeroE _ rfl
  rw [h]
  unfold unitOf
  rw [dif_neg (fun hn => hn rfl)]
  exact one_ne_zero

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.both_run
#print axioms OnBytes.LinkSim.Seam.factorAt
#print axioms OnBytes.LinkSim.Seam.fr_facOk
#print axioms OnBytes.LinkSim.Seam.fr_facNo
#print axioms OnBytes.LinkSim.Seam.fr_facIx1
#print axioms OnBytes.LinkSim.Seam.fr_factors
#print axioms OnBytes.LinkSim.Seam.fr_lSeed
#print axioms OnBytes.LinkSim.Seam.fr_cube
#print axioms OnBytes.LinkSim.Seam.unit_parts
