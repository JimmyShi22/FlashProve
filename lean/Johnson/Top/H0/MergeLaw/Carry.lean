-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Carry.lean: the prover's loss is carried from the proved block's typed
rounds
to the merge's written rounds. Definitions, and theorems with their proofs.

Main names:
  `conv`, `uholds_conv`, `ev_conv`: the library states the sumcheck's tie on the form with kept maps
    (`MergeL.toSum`), the proved block on the record's own form (`L.T`); the two types of outputs
    part
    in two functions out of the empty type. `conv` goes from one to the other, field by field.
  `typed_out`: the typed block's output at the typed transcript of what was heard.
  `merge_carry`: the library's `CarryS.doomed` (OnBytes/Flat) at `mergeMaps`, one statement at a
  time.

Limits. `merge_carry` has one premise with content, `hQ`; Johnson/Top/H0/MergeLaw/Plain.lean pays
it.
The error is the maps' image of the block's own; it is held against no price here. Nothing on
hiding.

-/
import Johnson.Top.H0.MergeLaw.Out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading wsForkStart)
open VerifiableInference.Desc (roundsFit noDigest fieldPrimeWord)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headClaimMergeKind)
open OnBytes.Tie.Pv.Lay.Eng (sumTr sumOut)
open _root_.Run (ckP)

/-- An output of the sumcheck in the form with kept maps (none is kept), as one in the record's own
form: field by field. -/
def conv (L : MergeL GE) (o : L.toSum.T.par.Out) : L.T.par.Out := ⟨o.st, o.eps, o.pt, o.fin, o.vals⟩

theorem uholds_conv (L : MergeL GE) (o : L.toSum.T.par.Out) (m : L.J → GE) :
    L.T.par.UHolds (conv L o) m ↔ L.toSum.T.par.UHolds o m := by
  have e1 : ∀ f : L.T.par.B → GE, ∑ b, f b = 0 := fun f => Finset.sum_eq_zero fun b _ => (show Empty
      from b).elim
  have e2 : ∀ f : L.toSum.T.par.B → GE, ∑ b, f b = 0 := fun f => Finset.sum_eq_zero fun b _ => (show
      Empty from b).elim
  unfold PscPar.UHolds
  rw [e1, e2]
  exact Iff.rfl

theorem ev_conv (L : MergeL GE) (o : L.toSum.T.par.Out) (m : L.J → GE) :
    L.EV (conv L o) m ↔ L.toSum.T.par.EHolds o m () := (L.kval_iff o m).symm

/-- The typed block's output at the typed transcript of what was heard is the library's `sumOut`,
where the block's target at the drawn
element is the reading of T. -/
theorem typed_out (G : WeightsL GE) (Ex : ExtSpec) (x₀ : G.St) (y : Ex.Str) (x mu eps cY beta v T :
    E) (qs : List (List E × E))
    (hβ : Reading.gl.val beta ≠ 0) (htg : G.L.tg (x₀, Reading.gl.val x) = Reading.gl.val T) :
    (G.blk (G.L.V1 Ex)).out x₀ y
        (show Tr (drawRound GE :: shapeS G.L.T.par) from
          (((), ()), Reading.gl.val x, ((), Reading.gl.val mu), Reading.gl.val eps,
            sumTr Reading.gl G.L.toSum qs [cY] beta hβ fun _ => Reading.gl.val v)) =
      some (conv G.L (sumOut Reading.gl G.L.toSum (fun st => pick (G.L.toSum.T.par.vars st)) (x₀,
          Reading.gl.val x) T mu eps qs
        [cY] beta hβ fun _ => Reading.gl.val v)) := by
  have h : (G.blk (G.L.V1 Ex)).out x₀ y
      (show Tr (drawRound GE :: shapeS G.L.T.par) from
        (((), ()), Reading.gl.val x, ((), Reading.gl.val mu), Reading.gl.val eps,
          sumTr Reading.gl G.L.toSum qs [cY] beta hβ fun _ => Reading.gl.val v)) =
      some (shortV G.L.T.par G.L.F1 (G.L.tg (x₀, Reading.gl.val x), (x₀, Reading.gl.val x))
        (((), Reading.gl.val mu), Reading.gl.val eps, sumTr Reading.gl G.L.toSum qs [cY] beta hβ fun
            _ => Reading.gl.val v)) :=
    TWhole.short_out G.L.T.par G.L.F1 Ex G.L.pick_ok (G.L.tg (x₀, Reading.gl.val x), (x₀,
        Reading.gl.val x)) y _
  rw [h, htg]
  rfl

/-- **The prover's loss is carried from the typed rounds to the written ones**, at one statement.
`bad'`: what the prover has lost towards at
the typed rounds. The one premise with content, `hQ`: at every written transcript at which the
decision says yes, `bad'` at the image gives Q. -/
theorem merge_carry (P : HeadMergeP) (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT}
    {dY dV : RDT}
    (hk : ds.length = G.k) (H : MergeDs dZ d0 ds dY dV) (ε : Err (G.blk (G.L.V1 Ex)).shape) (s : S)
    (bad' : Tr (G.blk (G.L.V1 Ex)).shape → Prop) (Q : S → Prop) (hd : Doomed (G.blk (G.L.V1
        Ex)).shape ε bad')
    (hQ : ∀ (τ : Tr (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV])))) (s' : S),
      roundsFit (headClaimMergeKind P).rounds ((rvT (ckP .two) _ τ).map noDigest) = true →
      (∀ r ∈ (rvT (ckP .two) _ τ).map noDigest, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧
          x.2.2 < fieldPrimeWord) →
      headMergeDecide P s ((rvT (ckP .two) _ τ).map noDigest) = .ok s' →
      bad' ((mergeMaps G Ex dZ d0 ds dY dV hk).view τ) → Q s') :
    Doomed (uLT (ckP .two) (dZ :: d0 :: (ds ++ [dY, dV]))) ((mergeMaps G Ex dZ d0 ds dY dV hk).err
        ε) (fun τ =>
      (mergeMaps G Ex dZ d0 ds dY dV hk).pass τ = true →
      roundsFit (headClaimMergeKind P).rounds ((rvT (ckP .two) _ τ).map noDigest) = true →
      (∀ r ∈ (rvT (ckP .two) _ τ).map noDigest, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧
          x.2.2 < fieldPrimeWord) →
      ∀ s', headMergeDecide P s ((rvT (ckP .two) _ τ).map noDigest) = .ok s' → Q s') :=
  CarryS.doomed (mergeMaps G Ex dZ d0 ds dY dV hk).carry ε _ (Maps.fits _ (mergeMaps_ok G Ex hk H)
      ε) _ bad'
    (fun τ hτ hp => by
      rw [Maps.tr_of_pass _ τ hp] at hτ
      cases hτ)
    (fun τ τ' hτ hb hp hf hw s' h => by
      rw [Maps.tr_of_pass _ τ hp] at hτ
      cases hτ
      exact hQ τ s' hf hw h hb)
    hd

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.typed_out
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_carry
