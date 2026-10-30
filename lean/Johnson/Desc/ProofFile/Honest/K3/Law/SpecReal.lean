-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecReal.lean: the honest side of the kind "lookup" (K3). The
hypotheses of `lawfulSpec` (Honest/K3/Law/SpecProof.lean) at a proof file's lookup of shape h: which
of the clauses of `SpecAt` follow from tests on public numbers, and what is left. Theorems.

Terms. Honest/K3/GLOSSARY.md ("fit", "lawful", "relation after the challenge", "settled",
"specification").

What is shown, by the file's sections.
  1. `numsAre_real`: conditional on the verifier's tests on the face: the specification's numbers
     `Fo.numsF h lm jLK theta` are those of `faceOf h`.
  2. `padding_real`: conditional on `FoNums.ok h`: as many keys are padding.
  3. `midCongr`: the statement `MidCongr` of Honest/K3/JobsSpecOwed.lean: the relation after the
     challenge reads keys and bits inside the sizes alone.
  4. `specAt_real`: conditional on `Fit R`, `FoNums.ok h`, an input that has settled, and the
     relation after the challenge at the structure's keys and bits: `SpecAt` at a course whose face
     is `faceOf h` and whose summands are `specJobsF h lm jLK`.
  5. `lawful_real`: conditional on the same and on `Numbered R`: `Lawful` there.

Hypotheses that remain. Those named at each theorem. The relation after the challenge remains a
hypothesis: it is what the statements on a trace conclude. By name, in `specAt_real` and
`lawful_real`: `hf`, `hJ`: the course's face and summands; `hF`: `Fit R`; `hok`: `FoNums.ok h`;
`hs`: `Ask.Settled` at the place's number of rounds in front; `hM`: the relation; `hW`: (in
`lawful_real`) `Numbered R`, which at one part of keys follows from `Fit R` (`numbered_of_fit`,
Honest/K3/Law/NumberedOfFit.lean; so Honest/K3/Law/SpecAtSite.lean has it). In `numsAre_real`:
`hok`: the verifier's tests on the face. In `mid_of_same`: `h`, `hf`, `hM`: the two data are the
same inside the sizes; n + 2 = 2 ^ w; the relation at the first.

How the proof goes. It rests on Honest/K3/JobsSpecTies.lean (factor, table), Honest/K3/JobsSpec.lean
(orders) and `Cb.Fo.pads_sum` (OnBytes/Tie/Pv/Lookup/Forest/FoPadSum.lean).

Users. This file is imported by Honest/K3/Law/SpecAtSite.lean, Honest/K3/Law/SpecRealMember.lean
[not in this library] and Honest/K3/Law/Thread/LeftAtCalls.lean.

Limits. No shape is shown here that passes `FoNums.ok`, and no course at such a shape.
An instance of the hypotheses of `lawful_real`: Honest/K3/Law/SpecRealMember.lean
[not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecMember
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecTies
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecOwed
import OnBytes.Tie.Pv.Lookup.Forest.FoPadSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE)
open OnBytes.Model (orderDefault)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.K3 (faceOf)

/-! ## 1 The numbers -/

/-- **Conditional on the verifier's tests on the face: at a proof file's lookup the specification's
public numbers are the face's.** No instance of these hypotheses is exhibited in this file. -/
theorem numsAre_real (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat) (theta : KE)
    (hok : (faceOf h).ok = true) : NumsAre (faceOf h) (_root_.Fo.numsF h lm jLK theta) := by
  have hperm := fun l (hl : l < h.v) => perm_of_ok (f := faceOf h) (v := h.v) hok rfl hl
  have hv : 1 ≤ h.v := by
    simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hok
    exact hok.1.1.1.2 h.v (by show h.v ∈ [h.v]; simp)
  have hv' : (_root_.Fo.numsF h lm jLK theta).v' + 1 = h.v := by
    show h.v - 1 + 1 = h.v
    omega
  refine ⟨?_, rfl, rfl, rfl, (by show FoNums.n + 2 ≤ 2 ^ FoNums.w; decide), fun _ => rfl, ?_,
    fun _ => rfl, ?_, ?_⟩
  · rw [hv']
    rfl
  · intro l hl
    exact hperm l (by rw [← hv']; exact hl)
  · exact (numsF_oE_oB h lm jLK theta).1
  · exact (numsF_oE_oB h lm jLK theta).2

/-! ## 2 The padding -/

/-- **Conditional on `FoNums.ok h`: the padding counted by call is the face's, counted by tree.**
No instance of these hypotheses is exhibited in this file. -/
theorem padding_real (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat) (theta : KE)
    (hok : FoNums.ok h = true) :
    ((_root_.Fo.numsF h lm jLK theta).pads.map (·.2)).sum = ((faceOf h).padding.map (·.1)).sum := by
  have e := Cb.Fo.pads_sum hok
  have hs : h.pub.size = h.NT := (Cb.Fo.ok_parts hok).1.2.2.2.2.2.1
  show Cb.Lkp.padNum (FoNums.pads h) = _
  rw [e]
  unfold OnBytes.Model.Forest.Shape.padding
  rw [Cb.Fo.array_sum, hs]
  show _ = (((h.emptyKeys, _) :: (List.range h.NT).map _).map (·.1)).sum
  rw [List.map_cons, List.sum_cons, List.map_map]
  rfl

/-! ## 3 The relation after the challenge reads inside the sizes alone -/

/-- One way. -/
theorem mid_of_same {P : Type} (D D' : Data P KE) (h : SameInside D D')
    (hf : D.N.n + 2 = 2 ^ D.N.w) (hM : D.Mid) : D'.Mid := by
  obtain ⟨N, key, bits, al⟩ := D
  obtain ⟨N', key', bits', al'⟩ := D'
  obtain ⟨hN, hal, hkey, hbits⟩ := h
  simp only at hN hal hkey hbits hf
  subst hN
  subst hal
  obtain ⟨h1, h2, h3⟩ := hM
  refine ⟨fun u hu j hj => ?_, ?_, ?_⟩
  · show bits' u j * (bits' u j - 1) = 0
    rw [← hbits u j hu hj]
    exact h1 u hu j hj
  · refine Eq.trans (Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun j hj => ?_) h2
    show (2 : KE) ^ j * bits' u j = 2 ^ j * bits u j
    rw [hbits u j (Finset.mem_range.1 hu) (by rw [← hf]; exact Finset.mem_range.1 hj)]
  · refine Eq.trans (Finset.prod_congr rfl fun b hb => ?_) (h3.trans ?_)
    · show al - key' b = al - key b
      rw [hkey b (Finset.mem_range.1 hb)]
    · show Cb.Lkp.padFac N.tab N.pads al *
          ∏ j ∈ Finset.range (N.n + 2), Cb.Lkp.tabProd N.d N.tab bits al j ^ 2 ^ j =
        Cb.Lkp.padFac N.tab N.pads al *
          ∏ j ∈ Finset.range (N.n + 2), Cb.Lkp.tabProd N.d N.tab bits' al j ^ 2 ^ j
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      congr 1
      show ∏ u ∈ Finset.range (2 ^ N.d), (1 + bits u j * (al - 1 - N.tab u)) =
        ∏ u ∈ Finset.range (2 ^ N.d), (1 + bits' u j * (al - 1 - N.tab u))
      refine Finset.prod_congr rfl fun u hu => ?_
      rw [hbits u j (Finset.mem_range.1 hu) (by rw [← hf]; exact Finset.mem_range.1 hj)]

/-- Being the same inside goes both ways. -/
theorem sameInside_symm {P : Type} {D D' : Data P KE} (h : SameInside D D') : SameInside D' D := by
  obtain ⟨hN, hal, hkey, hbits⟩ := h
  have hv : D'.v = D.v := by
    unfold Data.v
    rw [hN]
  exact ⟨hN.symm, hal.symm, fun x hx => (hkey x (by rw [← hv]; exact hx)).symm,
    fun u j hu hj => (hbits u j (by rw [hN]; exact hu) (by rw [hN]; exact hj)).symm⟩

/-- **The relation after the challenge reads keys and bits inside the sizes alone**, where all
planes count. -/
theorem midCongr : MidCongr := by
  intro P D D' h hf
  exact ⟨mid_of_same D D' h hf, mid_of_same D' D (sameInside_symm h) (by rw [← h.N]; exact hf)⟩

/-! ## 4 SpecAt at a proof file's lookup -/

/-- **Conditional on `Fit R`, `FoNums.ok h`, an input that no longer moves from the challenges in
front of the lookup on, and the relation after the challenge at the structure's keys and bits:
`SpecAt`** at a course whose face is `faceOf h` and whose summands are the specification's at
`Fo.numsF h lm jLK`. An instance: Honest/K3/Law/SpecRealMember.lean [not in this library] (by
evaluation). -/
theorem specAt_real (R : Course Ask) (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat)
    (hf : R.f = faceOf h) (hJ : R.J = (specJobsF h lm jLK).asked) (hF : Fit R)
    (hok : FoNums.ok h = true) (hs : Ask.Settled R.a.base R.t.input)
    (hM : (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) (R.t.input R.t.heard) R.pts).Mid) :
    SpecAt R (fun theta => _root_.Fo.numsF h lm jLK theta) (R.t.input R.t.heard) := by
  have hd : R.f.d = h.d := by rw [hf]; rfl
  have hmu : R.f.mu = 5 := by rw [hf]; rfl
  have hz : R.zb0.size = 5 + h.d := by
    rw [← hmu, ← hd]
    show ((varChals _ _ _ _ (R.f.mu + R.f.d)).toArray).size = _
    simp [varChals]
  refine ⟨hJ, fun s _ => one_of_settled R hF hs s, ?_, ?_, ?_, ?_, hM⟩
  · rw [hf]
    exact numsAre_real h lm jLK _ (by rw [← hf]; exact hF.ok)
  · show up (R.f.factor R.pts.theta R.pts.alpha) = _
    rw [show R.f.factor = (faceOf h).factor by rw [hf]]
    exact factor_tie h hok lm jLK _ R.pts
  · rw [show R.f.leaf = (faceOf h).leaf by rw [hf], hd, hmu]
    exact leaf_tie h hok lm jLK R.pts.theta R.pts.alpha R.zb0 hz
  · rw [show R.f.padding = (faceOf h).padding by rw [hf]]
    exact padding_real h lm jLK _ hok

/-- **Conditional on the same, and on `Numbered R`: at a proof file's lookup the specification's
summands are lawful.** An instance: Honest/K3/Law/SpecRealMember.lean [not in this library] (by
evaluation). -/
theorem lawful_real (R : Course Ask) (h : OnBytes.Model.Forest.Shape) (lm jLK : Nat)
    (hf : R.f = faceOf h) (hJ : R.J = (specJobsF h lm jLK).asked) (hF : Fit R) (hW : Numbered R)
    (hok : FoNums.ok h = true) (hs : Ask.Settled R.a.base R.t.input)
    (hM : (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) (R.t.input R.t.heard) R.pts).Mid) :
    Lawful R
      (planesOf (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) (R.t.input R.t.heard) R.pts))
      (keysOf (dataAt (fun theta => _root_.Fo.numsF h lm jLK theta) (R.t.input R.t.heard) R.pts)) :=
  lawfulSpec _ _ _ R hF hW (specAt_real R h lm jLK hf hJ hF hok hs hM)

#print axioms ProofFile.Honest.K3.Law.Spec.specAt_real
#print axioms ProofFile.Honest.K3.Law.Spec.lawful_real
#print axioms ProofFile.Honest.K3.Law.Spec.numsAre_real
#print axioms ProofFile.Honest.K3.Law.Spec.padding_real
#print axioms ProofFile.Honest.K3.Law.Spec.mid_of_same
#print axioms ProofFile.Honest.K3.Law.Spec.sameInside_symm
#print axioms ProofFile.Honest.K3.Law.Spec.midCongr

end ProofFile.Honest.K3.Law.Spec
