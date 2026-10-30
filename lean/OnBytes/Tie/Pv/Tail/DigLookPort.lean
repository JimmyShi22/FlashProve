-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/DigLookPort.lean: where the seam in front of the lookup on the digits of a
smallness test (InSubAtPort.lean) meets the lookup of a sub-proof at the verifier's own record of
public numbers (`Cb.Fo.forB` at h := tl.f9, OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean): the joints in
front, and the joint keys.

The lookup's entries are read off all messages of the link (`msg₀`): its end claims read the digits
and the bits of the counts, which stand in the late message, and entries of the link's mask row,
which is sent at the link's start. The seam's letters read the late message alone (`entU`). The two
readings are asked to agree at the digits' places.

Main names:
  `lateO`: the seam's letters `lateU` (InSubAtPort.lean) at the type of entries with one more,
    Option J₀: the entries are read with 0 at the entry that is no cell (`zext`), and a place
    (array, row, column) is named some (en ..).
  `forA_key`: the joint keys of `forA` at `digL` (OnBytes/Tie/Pv/Lookup/Digits/PortKnow.lean) are
    the shifted joint keys of `portQJ tl (some ∘ en)`, at any reading of the entries.
  `forIn_iff_inD₁`: the relaxed relation of the joint in front of `forB` at `digL` (`forIn`), with
    `eqs₁` riding and the entries read by msg₀, holds if and only if that of `inD₁` does, under
    `shapeTest2` and the agreement of msg₀ with the late reading at the digits' places (hlo, hhi).
Limits: `shapeTest2` and `colsTest` are Bools on public numbers: that they are true at a given
sub-proof is a run, no proof term. mk (how J₀ names the mask row's entry under a slot) and jLK (the
sub-proof's next free slot when the lookup begins) are letters, and so are entU, en and msg₀. No
knowledge soundness is stated here. Nothing on an honest prover.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortKnow
import OnBytes.Tie.Pv.Tail.InSubAtPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.DgP Cb.Pv.Tail Iop IOR Cb.LdLkp Cb.Lkp Cb.Fo CbQ TWhole

section
variable {E : Type} {tl : HTailF2} {U W₀ J : Type} (Λ : Letters E (sizeOf tl).size)
  (h : colsTest tl = true) (entU : U → J → E) (en : Ent3 → J) (bk : U → W₀ → Λ.W)

instance : Fintype (lateU Λ h entU en bk).I := inferInstanceAs (Fintype (Pl tl))
instance [Fintype J] : Fintype (lateU Λ h entU en bk).J := inferInstanceAs (Fintype J)
instance [DecidableEq J] : DecidableEq (lateU Λ h entU en bk).J :=
  inferInstanceAs (DecidableEq J)

end

section
variable {E : Type} [Field E] {tl : HTailF2} {U W₀ J₀ : Type}

/-- The seam's letters at the type of entries with one more. -/
abbrev lateO (Λ : Letters E (sizeOf tl).size) (h : colsTest tl = true) (entU : U → J₀ → E)
    (en : Ent3 → J₀) (bk : U → W₀ → Λ.W) : LateU Λ U W₀ :=
  lateU Λ h (fun u => zext (entU u)) (fun n => some (en n)) bk

/-- The joint keys of `forA` at `digL` are the shifted joint keys of the record of the digits. -/
theorem forA_key [Fintype E] [Fintype J₀] [DecidableEq J₀] (hT : TailOK tl) (hP : PortOK tl)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) {St₀ : Type} (x : St₀ × E) (μ : Option J₀ → E) :
    (forA E tl.f9 (digL E tl en mk jLK St₀)).key x μ =
      shKeyQ (portQJ tl fun n => some (en n)).fK ((portQJ tl fun n => some (en n)).key μ)
        (portQJ tl fun n => some (en n)).tagE x.2 := by
  have h0 : Port.t0Of tl.f9 0 = 0 := dgP_t00 hT hP
  have hnc : 0 < tl.f9.NC := by rw [hT.nc]; decide
  have hrow : FoNums.tauN tl.f9 0 0 = 0 := hP.rows 0 hnc 0 (by positivity)
  have hk : Port.key tl.f9 (forT E tl.f9 x.1) (forK E (digL E tl en mk jLK St₀) x.1 μ) =
      (portQJ tl fun n => some (en n)).key μ := by
    funext X
    rw [dgP_key_portJ (fun n => some (en n)) hT h0 μ X]
    unfold Port.key
    split_ifs with hX
    · rfl
    · show ((FoNums.tauN tl.f9 0 (Port.t0Of tl.f9 0) : ℕ) : E) = ((Port.t0Of tl.f9 0 : ℕ) : E)
      rw [h0, hrow]
  show shKeyQ (Port.fK tl.f9)
    (Port.key tl.f9 (forT E tl.f9 x.1) (forK E (digL E tl en mk jLK St₀) x.1 μ))
    (fun c => ((c : ℕ) : E)) x.2 = _
  rw [hk]
  rfl

/-- The joint in front of `forB` at `digL`, with `eqs₁` riding, is the joint at which the seam ends.
-/
theorem forIn_iff_inD₁ (Λ : Letters E (sizeOf tl).size) (h : colsTest tl = true)
    (entU : U → J₀ → E) (en : Ent3 → J₀) (bk : U → W₀ → Λ.W) (mk : ℕ → J₀) (jLK : ℕ) {pp : ℕ}
    (hs : shapeTest2 tl pp = true) {MM Kc : Type} (left : MM → Λ.M) (right : MM → U)
    (k : MM × W₀ → Kc) (msg₀ : MM → J₀ → E)
    (hlo : ∀ m i, msg₀ m (en ((portQ tl).lo i)) = entU (right m) (en ((portQ tl).lo i)))
    (hhi : ∀ m i, msg₀ m (en ((portQ tl).hi i)) = entU (right m) (en ((portQ tl).hi i)))
    (a : (Λ.X × Dr (sizeOf tl).size) × Λ.E.Str) (w : MM × W₀) :
    (Cb.Fo.forIn E tl.f9 (digL E tl en mk jLK (Λ.X × Dr (sizeOf tl).size))
        ((lateO Λ h entU en bk).eqs₁ left right k) msg₀).relR a w ↔
      ((lateO Λ h entU en bk).inD₁ left right k).relR a w := by
  have hQ := lateU_ok Λ h (fun u => zext (entU u)) (fun n => some (en n)) bk hs
  have hlo' : ∀ m i, zext (msg₀ m) ((portQJ tl fun n => some (en n)).lo i) =
      zext (entU (right m)) ((portQJ tl fun n => some (en n)).lo i) := hlo
  have hhi' : ∀ m i, zext (msg₀ m) ((portQJ tl fun n => some (en n)).hi i) =
      zext (entU (right m)) ((portQJ tl fun n => some (en n)).hi i) := hhi
  rw [forIn_dig hs en mk jLK]
  constructor
  · rintro ⟨h1, g⟩
    refine ⟨h1, (dgQ_in (portQJ tl fun n => some (en n)) hQ
      (zext (entU (right w.1)))).2 ⟨fun i => ?_, fun i => ?_⟩⟩
    · rw [← hlo' w.1 i]
      exact g.1 i
    · rw [← hhi' w.1 i]
      exact g.2 i
  · rintro ⟨h1, h2⟩
    have g := (dgQ_in (portQJ tl fun n => some (en n)) hQ (zext (entU (right w.1)))).1 h2
    refine ⟨h1, fun i => ?_, fun i => ?_⟩
    · have e := g.1 i
      rw [← hlo' w.1 i] at e
      exact e
    · have e := g.2 i
      rw [← hhi' w.1 i] at e
      exact e

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.forA_key
#print axioms OnBytes.Tie.Pv.Tail.forIn_iff_inD₁
