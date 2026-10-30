-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsPow.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. THE TWO LAST FIELDS OF POWERS THAT THE HONEST PARTS OF THE FEED-FORWARD LAYERS' ROUNDS
READ ARE THE VERIFIER's: om, the powers of the element that joins the two claims in front of the
batched sumcheck; rhoW, the powers of the element that batches the merge's claims. Beside
PtsAt.lean, under the same premises.

  `tapeEps_head`, `drawnOf_putBack`, `powersAt_one`   tools
  `at_stackPow`   **the element that joins the two claims**
  `merge_drawn`, `at_mergePow`   **the element that batches the merge's claims**

Limits. Those of PtsAt.lean. THE NUMBER OF rhoW's POWERS IS THE PLAN's NUMBER OF CLAIMS; the flat
text of the merge takes as many as it is handed slots: that these two numbers are one is said in
ClaimsAre.lean (`mergeSlots_size`), from the hearing's return: `LedG` alone does not give it. No
field of what the verifier has heard holds either list: the verifier's are written as the powers of
the first element that the batching round of the tape has sampled: of om, as the library's law on
the batched sumcheck's return has it (`hearStack_tape`, OnBytes/Desc/First/K4/StackTape.lean); of
rhoW, as the merge's flat text is handed it (`hear_ended`, Johnson/Top/H0/MergeLaw/Said.lean): the
tape u5 on which the merge runs. Equations between machine words.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt
import Johnson.Top.H0.MergeLaw.Said
import Johnson.Top.H0.MergeLaw.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Fork Level Tsc powers Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.P1 (drawnOf tapeEps putBack claimsIn_spec)
open OnBytes.Desc.First.K4 (k0 hearStack_tape mergeFront drop_drop')
open OnBytes.Road.K4 (LedG ksOf)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)

/-- The first element that a tape's first round sampled. -/
theorem tapeEps_head : ∀ t : Tape, tapeEps t = (drawnOf t).headD zeroE
  | [] => rfl
  | _ :: _ => rfl

/-- Laying elements back in front of what the first round has to send leaves what it sampled. -/
theorem drawnOf_putBack (l : List E) : ∀ t : Tape, drawnOf (putBack l t) = drawnOf t
  | [] => rfl
  | ⟨_, _, _, _, _⟩ :: _ => rfl

/-- The powers of the one element that a challenge holds. -/
theorem powersAt_one (ds : List Fmt.Drawn) (j n : ℕ) (x : E) (h : elemsAt ds j = #[x]) :
    powersAt ds j n = powers x n := by
  unfold powersAt
  rw [h]
  rfl

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} (w : K4In) (h : List Fmt.Drawn)

/-- **om**, at every prefix from the batched sumcheck's first round on. -/
theorem at_stackPow
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 3 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).om = powers (tapeEps (t.drop (k4StartAt Q 3 - 1))) 2 := by
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  have e3 : k4StartAt Q 2 + (Q.P.y.h.lt + 3) = k4StartAt Q 3 - 1 := by omega
  have c4 := L.c4
  rw [at_b3, e3] at c4
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, Ga, ms, y, p, ht, _⟩ :=
    hearStack_tape c4
  have b : elemsAt ds (k4StartAt Q 3 - 1) = #[x] := hD.at ht (by omega)
  rw [pts_om_val, own_take Q h ds hh, powersAt_take ds _ _ n (by omega), powersAt_one ds _ _ x b,
    ht]
  rfl

/-- The merge's batching round has sampled one element. -/
theorem merge_drawn
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    drawnOf (t.drop (k4StartAt Q 6 - 1)) = [tapeEps u5] := by
  have s6 : k4StartAt Q 6 = k4StartAt Q 5 + (Q.P.rd.muH2 + 5) := rfl
  have e6 : k4StartAt Q 5 + (Q.P.rd.muH2 + 4) = k4StartAt Q 6 - 1 := by omega
  obtain ⟨cl, c7⟩ := L.c7
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, _, _, et, _⟩ := hear_ended (hear_of_flat c7)
  have d5 : drawnOf u5 = [tapeEps u5] := by
    rw [et]
    rfl
  have hfr := L.front
  rw [at_b6, e6] at hfr
  unfold mergeFront at hfr
  split at hfr
  · obtain ⟨_, v1, _, ht, _⟩ := claimsIn_spec hfr
    rw [ht, drawnOf_putBack, d5]
  · rw [← hfr.2.2, d5]

/-- **rhoW**, at every prefix from the merge's first round on. -/
theorem at_mergePow
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 6 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rhoW = powers (tapeEps u5) Q.hp.NCL := by
  have s6 : k4StartAt Q 6 = k4StartAt Q 5 + (Q.P.rd.muH2 + 5) := rfl
  have b : elemsAt ds (k4StartAt Q 6 - 1) = #[tapeEps u5] := by
    rw [← hD.elems (by omega), merge_drawn L]
  rw [pts_rhoW_val, own_take Q h ds hh, powersAt_take ds _ _ n (by omega),
    powersAt_one ds _ _ _ b]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.tapeEps_head
#print axioms ProofFile.Honest.K4.drawnOf_putBack
#print axioms ProofFile.Honest.K4.powersAt_one
#print axioms ProofFile.Honest.K4.at_stackPow
#print axioms ProofFile.Honest.K4.merge_drawn
#print axioms ProofFile.Honest.K4.at_mergePow
