-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Fwd210.lean: ROW 2.10 OF THE KEY FILE's TABLES (the shared chain's block 10: the proximity test on G_omega): THE PROMISE's HALF, WHOLE: the promise at border 10 in front, the held block's yes and the strings' staying give the promise at border 11 behind. One statement; its proof is a call of the rule fwd₂_seat (Johnson/RunOne/Law/K12Fwd29.lean).
OBJECT. On₂ at borders 10 and 11. USER. Whoever fills the field r2_10 of The21 by the two halves.
LETTERS AND PREMISES as at row 2.9, at this place's parameters; hst at (shapeAt X).testOmega. (shape): Johnson/RunOne/Law/K12Shape210.lean.
Limits. A block that says no to all meets the statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Fwd29
import Johnson.RunOne.Law.K12Shape210

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.K12Fwd210
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (Blk' Gs)
open LKFU.Shape23
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12Fwd29 (fwd₂_seat sampled_of_msgIs)
open Johnson.RunOne.Law.K12Shape210 (shape₂_10_11)

theorem pins_11_10 : ∀ j ∈ pinned (open₂ 11), j ∈ pinned (open₂ 10) := by decide
theorem pins_11_5 : ∀ j ∈ pinned (open₂ 11), j ∈ [0, 2, 3, 4, 5] := by decide

theorem sampled_10 (S : LinShape) (a : Nat) (d : St₂) (h : ok (shape₂ S a 10 d) = true) : ∀ o ∈ [0, 2, 3], ∃ x, d.st.oracles[o]? = some x ∧ x.sampled = true := by
  simp [ok, shape₂] at h
  obtain ⟨_, _, _, _, _, _, _, _, ⟨c9, _⟩, _, ⟨c11, c11'⟩, _⟩ := h
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact sampled_of_msgIs _ _ _ _ c9
  · exact sampled_of_msgIs _ _ _ _ c11
  · exact sampled_of_msgIs _ _ _ _ c11'

variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat)
  (coll : Strs → Rec → Prop) (off₂ : Nat → Nat)

/-- **The promise's half of row 2.10.** -/
theorem fwd_210 (p : P12) (he : p.early = true) (ha : p.answers = 1) (hst : p.nums.stages.length = (shapeAt X).testOmega.length) (hft : p.nums.firstTree = 0)
    (ha1 : (oneAt X).given.plan.samples = 1) (hlen : (oneAt X).codes.lengthsOk = true) (hSm : B.SmOnly)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (b : Block St₂ Key.Claim) (hb : b.decide = (K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide) :
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 10 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 10) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 11 c :=
  fwd₂_seat X N P D B at_ R enc rad coll off₂ 10 11 (by omega) pins_11_10 pins_11_5 (·.gOmega) (fun _ => none) p he ha hlen hSm hcoll
    (fun d d' rs gs h h10 => shape₂_10_11 _ _ p he ha d d' rs gs h hst hft ha1 h10) (fun d h => sampled_10 _ _ d h) b hb

end Johnson.RunOne.Law.K12Fwd210

#print axioms Johnson.RunOne.Law.K12Fwd210.fwd_210
