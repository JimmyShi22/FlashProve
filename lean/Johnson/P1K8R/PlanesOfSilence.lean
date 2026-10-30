-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PlanesOfSilence.lean: THE SMALLNESS TEST: WHERE THE LOOKUP's SECOND TEST ON ITS OWN
SAMPLES (`goodK3Out`, Johnson/Desc/ProofFile/Honest/K3/GoodDraws.lean) SAYS YES, AND WHAT THE DATA
HOLD AS HEARD AGREES WITH THESE SAMPLES IN THE ELEVEN OPEN FIELDS (`OpenSame`, `lookHeardAt`,
Johnson/Desc/ProofFile/Honest/K3/HeardWhole.lean): `planesLive`
(Johnson/Desc/K8/Honest/PlanesFew.lean) SAYS YES. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

ds, own: the lookup's own samples, by round, from its first round on. f: the lookup's face; h: its
shape.
  `val_ne_one`   a word below the prime that is not the word 1 does not have the value 1
  **`leaves_fine`**, **`bits_fine`**   a yes of `goodK3Out f ds`: no challenge of the leaves'
      sumcheck's variables, and none of the bits', has the value 0 or 1
  **`leavesA_fine`**   a yes of `goodK3Out (faceOf h) ds`: the leaves' factor of `lookHeardAt h 0
      ds` does not have the value 0
  **`planes_of_silence`**   tl.heard = some g; g agrees with `lookHeardAt tl.f9 0 own` in the eleven
      fields; a yes of `goodK3Out (faceOf tl.f9) own`; the form that the leaves' sumcheck was handed
      names no entry; the leaves' eps does not have the value 0: then `planesLive tl` says yes
By: `planesGood_of` (Johnson/Desc/K8/Honest/GoodOf.lean) · `planesLive_of` (PlanesLiveOf.lean) ·
`val_ne_of_word` (ReadsLiveOf.lean) · OnBytes.Slice.readE_inj, readE_one.
Limits. The agreement, the form's emptiness and eps are premises: that the state in front of a
segment's batching meets them is not shown here. Nothing on `digitsLive`. Nothing on any measure.
-/
import Johnson.Desc.K8.Honest.GoodOf
import Johnson.Desc.K8.Honest.ReadsLiveOf
import Johnson.Desc.ProofFile.Honest.K3.GoodDraws
import Johnson.Desc.ProofFile.Honest.K3.HeardWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K3 (LFace Spot goodK3Out spotsOut leavesR bitsR varChals elemAt elemsAt
  roundAt firstRound lookHeardAt OpenSame ptsOf)

/-- A word below the prime that is not the word 1 does not have the value 1. -/
theorem val_ne_one (w : E) (hok : OnBytes.okE w = true) (h1 : w ≠ oneE) :
    Reading.gl.val w ≠ 1 := fun e =>
  h1 (OnBytes.Slice.readE_inj w oneE hok rfl (e.trans OnBytes.Slice.readE_one.symm))

theorem getD_zero_headD (l : List E) (d : E) : l.getD 0 d = l.headD d := by
  cases l <;> rfl

/-- A spot that forbids 0 and 1, where it is fine. -/
theorem fine_vals (f : LFace) (ds : List Fmt.Drawn) (s : ProofFile.Honest.K3.Stage) (r : Nat)
    (h : Spot.fine f ds ⟨s, r, 0, true⟩ = true) :
    Reading.gl.val (elemAt ds (firstRound f s + r)) ≠ 0 ∧
      Reading.gl.val (elemAt ds (firstRound f s + r)) ≠ 1 := by
  have e : Spot.value f ds ⟨s, r, 0, true⟩ = elemAt ds (firstRound f s + r) :=
    getD_zero_headD _ _
  unfold Spot.fine at h
  rw [e] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.not_true, Bool.false_or, bne_iff_ne] at h
  exact ⟨val_ne_of_word _ h.1.1 h.1.2, val_ne_one _ h.1.1 h.2⟩

theorem out_spots (f : LFace) (ds : List Fmt.Drawn) (h : goodK3Out f ds = true) :
    ∀ p ∈ spotsOut f, Spot.fine f ds p = true := by
  unfold goodK3Out at h
  rw [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1

/-- The challenges of a sumcheck's variables, where their spots are fine. -/
theorem chals_fine (f : LFace) (ds : List Fmt.Drawn) (s : ProofFile.Honest.K3.Stage) (n : Nat)
    (h : ∀ l, l < n → Spot.fine f ds ⟨s, 1 + l, 0, true⟩ = true) :
    ∀ w ∈ varChals f 0 ds s n, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1 := by
  intro w hw
  unfold varChals at hw
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hw
  have e : roundAt f 0 s + 1 + l = firstRound f s + (1 + l) := by
    unfold roundAt
    omega
  rw [e]
  exact fine_vals f ds s (1 + l) (h l (List.mem_range.1 hl))

/-- **The leaves' challenges.** -/
theorem leaves_fine (f : LFace) (ds : List Fmt.Drawn) (h : goodK3Out f ds = true) :
    ∀ w ∈ (leavesR f 0 ds).toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1 := by
  intro w hw
  unfold leavesR at hw
  rw [List.toList_toArray] at hw
  refine chals_fine f ds .leaves (f.mu + f.d) (fun l hl => out_spots f ds h _ ?_) w hw
  unfold spotsOut
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inr ⟨l, hl, rfl⟩)

/-- **The bits' challenges.** -/
theorem bits_fine (f : LFace) (ds : List Fmt.Drawn) (h : goodK3Out f ds = true) :
    ∀ w ∈ (bitsR f 0 ds).toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1 := by
  intro w hw
  unfold bitsR at hw
  rw [List.toList_toArray] at hw
  refine chals_fine f ds .bits (f.mu + f.d) (fun l hl => out_spots f ds h _ ?_) w hw
  unfold spotsOut
  simp only [List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr ⟨l, hl, rfl⟩

/-- **The leaves' factor.** -/
theorem leavesA_fine (h : Forest.Shape) (ds : List Fmt.Drawn)
    (hg : goodK3Out (K3.faceOf h) ds = true) :
    Reading.gl.val (lookHeardAt h 0 ds).leavesA ≠ 0 := by
  unfold goodK3Out at hg
  rw [Bool.and_eq_true] at hg
  have h2 := hg.2
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
  exact val_ne_of_word _ h2.1 h2.2

theorem chals_size (f : LFace) (ds : List Fmt.Drawn) (s : ProofFile.Honest.K3.Stage) (n : Nat) :
    (varChals f 0 ds s n).toArray.size = n := by
  unfold varChals
  simp

theorem leavesR_size (f : LFace) (ds : List Fmt.Drawn) : (leavesR f 0 ds).size = f.mu + f.d := by
  unfold leavesR
  exact chals_size f ds .leaves (f.mu + f.d)

theorem bitsR_size (f : LFace) (ds : List Fmt.Drawn) : (bitsR f 0 ds).size = f.mu + f.d := by
  unfold bitsR
  exact chals_size f ds .bits (f.mu + f.d)

theorem face_size (h : Forest.Shape) : (K3.faceOf h).mu + (K3.faceOf h).d = 5 + (h.kT + h.cK) :=
  rfl

theorem look_zb0 (h : Forest.Shape) (ds : List Fmt.Drawn) :
    (lookHeardAt h 0 ds).zb0 = leavesR (K3.faceOf h) 0 ds := rfl

theorem look_zb1 (h : Forest.Shape) (ds : List Fmt.Drawn) :
    (lookHeardAt h 0 ds).zb1 = bitsR (K3.faceOf h) 0 ds := rfl

/-- **From the second test's yes to `planesLive`.** -/
theorem planes_of_silence (tl : HTailF2) (g : Forest.Heard) (own : List Fmt.Drawn)
    (hg : tl.heard = some g) (ho : OpenSame g (lookHeardAt tl.f9 0 own))
    (hs : goodK3Out (K3.faceOf tl.f9) own = true)
    (hstart : g.leaves.start.ents.isEmpty = true) (heps : Reading.gl.val g.leaves.eps ≠ 0) :
    planesLive tl = true := by
  have z0 : g.zb0 = leavesR (K3.faceOf tl.f9) 0 own := ho.zb0.trans (look_zb0 tl.f9 own)
  have z1 : g.zb1 = bitsR (K3.faceOf tl.f9) 0 own := ho.zb1.trans (look_zb1 tl.f9 own)
  have e0 : g.zb0.size = 5 + (tl.f9.kT + tl.f9.cK) := by rw [z0, leavesR_size, face_size]
  have e1 : g.zb1.size = 5 + (tl.f9.kT + tl.f9.cK) := by rw [z1, bitsR_size, face_size]
  have n0 : 5 + tl.f9.kT + tl.f9.cK ≤ g.zb0.size := by omega
  have n1 : 5 + tl.f9.kT + tl.f9.cK ≤ g.zb1.size := by omega
  refine planesLive_of tl g hg (planesGood_of tl g hstart heps ?_ ?_ ?_ n0 n1)
  · rw [ho.leavesA]
    exact leavesA_fine tl.f9 own hs
  · intro w hw
    have hw' := mem_extract _ _ _ w hw
    rw [z0] at hw'
    exact leaves_fine _ own hs w hw'
  · intro w hw
    have hw' := mem_extract _ _ _ w hw
    rw [z1] at hw'
    exact bits_fine _ own hs w hw'

end P1K8

#print axioms P1K8.val_ne_one
#print axioms P1K8.getD_zero_headD
#print axioms P1K8.fine_vals
#print axioms P1K8.out_spots
#print axioms P1K8.chals_fine
#print axioms P1K8.leaves_fine
#print axioms P1K8.bits_fine
#print axioms P1K8.leavesA_fine
#print axioms P1K8.chals_size
#print axioms P1K8.leavesR_size
#print axioms P1K8.bitsR_size
#print axioms P1K8.face_size
#print axioms P1K8.look_zb0
#print axioms P1K8.look_zb1
#print axioms P1K8.planes_of_silence
