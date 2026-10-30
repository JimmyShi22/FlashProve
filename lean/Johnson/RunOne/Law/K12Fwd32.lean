-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Fwd32.lean: ROW 3.2 OF THE KEY FILE's TABLES (the last chain's block 2: the proximity test on the own group): THE PROMISE's HALF, WHOLE: the promise at border 2 in front, the held block's yes and the strings' staying give the promise at border 3 behind. One statement; its proof is a joining of calls.
OBJECT. On₃ (Johnson/RunOne/KeyRowsAtFk.lean) at borders 2 and 3. USER. Whoever fills the field r3_2 of The21 by the two halves.
LETTERS. The tables' own. PREMISES: on the place's parameters p: early · answers = 1 · hst: its number of stages is the shape's (testOwn) · on the plan: ha1: one answer to a sample · hcoll (what CellOnly coll gives) · hb: the block decides as the seated test · AND, AT EACH STATE IN FRONT: the codes' lengths are in order AT THE STATE's CODES: the promise at border 2 of this chain does not say what the codes are: to be had from the history (by a law: the carried codes are the plan's) or kept as a premise.
NO PREMISE ON THE PLACE's FIRST TREE's NUMBER; NONE ON THE READING's SAMPLES: no pin is open behind this test (pins3, by evaluation).
Limits. A block that says no to all meets the statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Shape32
import Johnson.RunOne.Law.K12Free32
import Johnson.RunOne.Law.K12Order
import Johnson.RunOne.Law.KeyQuietSub
import Johnson.RunOne.KeyRowsAtFk
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.K12Fwd32
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (Blk' Gs)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12Shape32 (own_yes shapeB₃_2_3)
open Johnson.RunOne.Law.K12Free32 (free₃_seat)
open Johnson.RunOne.Law.K12Order (k12_inOrder)

/-- No pin is open behind the own test. -/
theorem pins3 : pinned (open₃ 3) = [] := by decide

variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (coll : Strs → Rec → Prop) (off₂ off₃ : Nat → Nat)

/-- **The promise's half of row 3.2.** -/
theorem fwd_32 (p : P12) (he : p.early = true) (ha : p.answers = 1) (hst : p.nums.stages.length = (shapeAt X).testOwn.length)
    (ha1 : (oneAt X).given.plan.samples = 1) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (b : Block St₃ Key.Claim) (hb : b.decide = (K12.Seat.onOwn (proximityTestKind guardedProximityTestParts p : Blk')).decide) :
    ∀ a c rs gs, On₃ X N P D B at_ R coll off₂ off₃ 2 a → a.1.2.st.codes.lengthsOk = true → (held b : Block (P₃ × St₃) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₃ 2) (strsOf (fr₃ X N P D) a.2) (strsOf (fr₃ X N P D) c.2) → On₃ X N P D B at_ R coll off₂ off₃ 3 c := by
  intro a c rs gs hon hl hd Hy
  obtain ⟨e1, hy⟩ := held_decide b a.1 rs gs c.1 hd
  rw [hb] at hy
  obtain ⟨tE, hk, e2⟩ := own_yes p a.1.2 c.1.2 rs gs hy
  have ec : c.1 = (a.1.1, { a.1.2 with st := tE.st, book := tE.book, roots := tE.roots }) := Prod.ext e1 e2
  have K1 := H2K.Out.k12_out p he ha _ tE rs gs hk
  have hpin : ∀ j ∈ pinned (open₃ 3), j ∈ pinned (open₃ 2) := fun j hj => by
    rw [pins3] at hj
    cases hj
  refine KeyQuietSub.onAt_fwd_sub (Fk X N P) B.h₃ at_ _ _ _ _ _ (open₃ 2) (open₃ 3) hpin a.1 c.1 _ _ (fun _ => trivial) ?_ Hy ?_
    (shapeB₃_2_3 _ _ _ _ _ _ p he ha a.1.2 c.1.2 rs gs hy hst ha1) hon
  · intro _ _ j hj
    rw [pins3] at hj
    cases hj
  · intro _ hf
    rw [ec]
    exact free₃_seat (Fk X N P) B.h₃ at_ _ _ R coll off₂ off₃ hpin a.1 tE _ _ K1.book (k12_inOrder p _ tE rs gs hk hl) rfl hcoll Hy hf

end Johnson.RunOne.Law.K12Fwd32

#print axioms Johnson.RunOne.Law.K12Fwd32.pins3
#print axioms Johnson.RunOne.Law.K12Fwd32.fwd_32
