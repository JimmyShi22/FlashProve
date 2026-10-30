-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSend2.lean: towards the law of a sending in the form of the rule of
composition: at a place with one seed, the seed that the kind's decision cuts off what the verifier
is shown of the written round of the seeds reads, in the field, as the seed that the library's map
of written rounds reads (gSeed).

Main names: reads_shown.

What is not claimed. One seed alone. The written round is asked to draw as many elements as the
place's point has coordinates, and one more, which is drawn other than 0. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend1
import Johnson.Desc.K1.Law.SeedIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (noDigest)

/-- **The seed that the decision reads is the seed that the library's map reads.** -/
theorem reads_shown (P : Par) (h1 : P.seeds = 1) (d : RDT)
    (hE : nE (Fmt.dsOf d.entry d.kind) = P.coordinates + 1)
    (hz : IsNZ (Fmt.dsOf d.entry d.kind) P.coordinates) (m : (wT d).Msg) (c : (wT d).Chal) :
    ReadsAs P (noDigest (shownAt d m c))
      (fun _ => gSeed P.coordinates _ (valsOf (toRD d) c)) := by
  intro i
  have hi : i.val = 0 := by
    have := i.isLt
    omega
  have he : (noDigest (shownAt d m c)).drawn.elems = (rvOf (toRD d) (msgRD d m) c).els := rfl
  have hmap := rvOf_els (toRD d) (msgRD d m) c
  have hl : (rvOf (toRD d) (msgRD d m) c).els.length = P.coordinates + 1 := by
    have := congrArg List.length hmap
    rw [List.length_map, elemsV_length] at this
    exact this.trans hE
  have hl' : ((rvOf (toRD d) (msgRD d m) c).els.map E.ofTriple).length = P.coordinates + 1 := by
    rw [List.length_map, hl]
  have hv : P.coordinates < ((rvOf (toRD d) (msgRD d m) c).els.map E.ofTriple).length := by
    rw [hl']
    exact Nat.lt_succ_self _
  refine ⟨(((rvOf (toRD d) (msgRD d m) c).els.map E.ofTriple).take P.coordinates,
    ((rvOf (toRD d) (msgRD d m) c).els.map E.ofTriple)[P.coordinates]), ?_, ?_, ?_⟩
  · rw [hi]
    unfold seedsOf
    rw [h1, he]
    simp only [cutSeeds, List.getElem?_cons_zero, List.drop_eq_getElem_cons hv, List.headD_cons]
  · intro t
    have ht : t.val < (rvOf (toRD d) (msgRD d m) c).els.length := by
      rw [hl]
      exact Nat.lt_succ_of_lt t.isLt
    show readL _ t.val = gVec P.coordinates _ (valsOf (toRD d) c) t
    rw [gVec_rvOf (toRD d) (msgRD d m) c P.coordinates]
    unfold readL ptL
    rw [List.getD_eq_getElem _ _ (by rw [List.length_take, hl']; omega), List.getElem_take,
      List.getElem_map, readE_ofTriple, List.getD_eq_getElem _ _ ht]
  · show readE _ = ((unitOf ((elemsV _ (valsOf (toRD d) c)).getD P.coordinates 0) : GEˣ) : GE)
    rw [unitOf_val (elemsV_nz _ P.coordinates hz _), List.getElem_map, readE_ofTriple, ← hmap,
      List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact Nat.lt_succ_self _),
      List.getElem_map]

end VerifiableInference.Desc.K1
