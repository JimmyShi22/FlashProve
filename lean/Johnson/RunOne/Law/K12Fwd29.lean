-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Fwd29.lean: ROW 2.9 OF THE KEY FILE's TABLES (the shared chain's block 9: the proximity test on G_u): THE PROMISE's HALF, WHOLE: the promise at border 9 in front, the held block's yes and the strings' staying give the promise at border 10 behind. Statements with proofs; each proof is a joining of calls.
OBJECT. On₂ (Johnson/RunOne/KeyRowsAtFk.lean): the tables' promise at the shared chain's borders, at the key file's own description. USER. Whoever fills the field r2_9 of The21 by the two halves (the claim's half: back_29, KeyRide23.lean).
LETTERS. The tables' own. PREMISES: on the place's parameters p: early · answers = 1 · hst: its number of stages is the shape's · hft: its first tree's number is 0 (the maker's literal) · on the plan: ha1: one answer to a sample · hlen: the codes' lengths are in order · on the tables' files' letters: B.SmOnly · hcoll (what their CellOnly coll gives) · hb: the block decides as the seated test (retyping and baring turn no decision).
  fwd₂_seat: the rule for both tests of the shared chain: by onAt_fwd_sub (Johnson/RunOne/Law/KeyQuietSub.lean): (marked): empty at this chain's meaning · (smp): smp₂_of_smpStay over Johnson/RunOne/Law/K12Keeps.lean at SmpStay · (shape): a premise of the rule · (free): Johnson/RunOne/Law/K12Free23.lean, the order by K12Order.lean (the codes: out of Free₂'s own fields codes and last).
  fwd_29: at row 2.9: (shape) by Johnson/RunOne/Law/K12Shape29.lean.
Limits. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Shape29
import Johnson.RunOne.Law.K12Free23
import Johnson.RunOne.Law.K12Order
import Johnson.RunOne.Law.K12Keeps
import Johnson.RunOne.Law.KeyQuietSub
import Johnson.RunOne.KeyRowsAtFk
import Johnson.RunOne.KeySmStay
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.K12Fwd29
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay beginRun_smpStay)
open H2K.JointK (Blk' Gs)
open LKFU.Shape23
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.K12Shape29 (seat_yes shape₂_9_10)
open Johnson.RunOne.Law.K12Free23 (free₂_seat)
open Johnson.RunOne.Law.K12Order (k12_inOrder)
open Johnson.RunOne.Law.K12Keeps (k12_keeps)

theorem sampled_of_msgIs (st : Statement) (o a : Nat) (f : Bool) (h : msgIs st o (some a) f = true) : ∃ x, st.oracles[o]? = some x ∧ x.sampled = true := by
  unfold msgIs at h
  cases hx : st.oracles[o]? with
  | none =>
    rw [hx] at h
    cases h
  | some x =>
    rw [hx] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨x, rfl, h.1.1⟩

theorem orc₂_mem (k o : Nat) (h : orc₂ k = some o) : o ∈ [0, 2, 3] := by
  unfold orc₂ at h
  split at h
  · cases h
    simp
  · split at h
    · cases h
      simp
    · split at h
      · cases h
        simp
      · cases h

variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat)
  (coll : Strs → Rec → Prop) (off₂ : Nat → Nat)

/-- **The promise's half across a proximity test of the shared chain.** -/
theorem fwd₂_seat (k k' : Nat) (h6 : 6 ≤ k) (hpin : ∀ j ∈ pinned (open₂ k'), j ∈ pinned (open₂ k)) (hpin5 : ∀ j ∈ pinned (open₂ k'), j ∈ [0, 2, 3, 4, 5])
    (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hlen : (oneAt X).codes.lengthsOk = true) (hSm : B.SmOnly) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (step : ∀ d d' rs gs, (Block.inside (K12.Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') K12.Seat.leave).decide d rs gs = .ok d' →
      ok (shape₂ (shapeAt X) (oneAt X).given.plan.samples k d) = true → ok (shape₂ (shapeAt X) (oneAt X).given.plan.samples k' d') = true)
    (hsam : ∀ d, ok (shape₂ (shapeAt X) (oneAt X).given.plan.samples k d) = true → ∀ o ∈ [0, 2, 3], ∃ x, d.st.oracles[o]? = some x ∧ x.sampled = true)
    (b : Block St₂ Key.Claim) (hb : b.decide = (Block.inside (K12.Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') K12.Seat.leave).decide) :
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ k a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ k) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ k' c := by
  intro a c rs gs hon hd Hy
  obtain ⟨e1, hy⟩ := held_decide b a.1 rs gs c.1 hd
  rw [hb] at hy
  obtain ⟨tE, hk, e2⟩ := seat_yes g mask p a.1.2 c.1.2 rs gs hy
  have ec : c.1 = (a.1.1, { a.1.2 with st := tE.st, book := tE.book, roots := tE.roots }) := Prod.ext e1 e2
  have K1 := H2K.Out.k12_out p he ha _ tE rs gs hk
  have hS : SmpStay a.1.2.st c.1.2.st := by
    rw [e2]
    exact k12_keeps groundKeeps_smpStay (fun d d' g run hb => beginRun_smpStay d d' g run hb) p _ tE rs gs hk
  refine KeyQuietSub.onAt_fwd_sub (Fk X N P) B.h₂ at_ _ _ _ _ _ (open₂ k) (open₂ k') hpin a.1 c.1 _ _ (fun _ => trivial) ?_ Hy ?_ (step _ _ rs gs hy) hon
  · intro hs hf j hj
    refine (smp₂_of_smpStay B hSm a.1 c.1 _ _ e1 hS fun o ho => ?_).symm
    have earr : B.arr (at_ j).1 (at_ j).2 = j := hf.arr j (hpin5 j hj)
    rw [earr] at ho
    exact hsam _ hs o (orc₂_mem j o ho)
  · intro _ hf
    rw [ec]
    refine free₂_seat (Fk X N P) B.h₂ at_ _ _ R coll _ off₂ k k' h6 hpin a.1 tE _ _ K1.codes K1.shapes K1.book ?_ rfl hcoll Hy hf
    refine k12_inOrder p _ tE rs gs hk ?_
    show a.1.2.st.codes.lengthsOk = true
    rw [hf.codes, codes_of_last (oneAt X) _ a.1.1.2 hf.last]
    exact hlen

theorem pins_10_9 : ∀ j ∈ pinned (open₂ 10), j ∈ pinned (open₂ 9) := by decide
theorem pins_10_5 : ∀ j ∈ pinned (open₂ 10), j ∈ [0, 2, 3, 4, 5] := by decide

theorem sampled_9 (S : LinShape) (a : Nat) (d : St₂) (h : ok (shape₂ S a 9 d) = true) : ∀ o ∈ [0, 2, 3], ∃ x, d.st.oracles[o]? = some x ∧ x.sampled = true := by
  simp [ok, shape₂] at h
  obtain ⟨_, _, _, _, _, _, _, _, ⟨c9, _⟩, _, ⟨c11, c11'⟩, _⟩ := h
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact sampled_of_msgIs _ _ _ _ c9
  · exact sampled_of_msgIs _ _ _ _ c11
  · exact sampled_of_msgIs _ _ _ _ c11'

/-- **The promise's half of row 2.9.** -/
theorem fwd_29 (p : P12) (he : p.early = true) (ha : p.answers = 1) (hst : p.nums.stages.length = (shapeAt X).testU.length) (hft : p.nums.firstTree = 0)
    (ha1 : (oneAt X).given.plan.samples = 1) (hlen : (oneAt X).codes.lengthsOk = true) (hSm : B.SmOnly)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (b : Block St₂ Key.Claim) (hb : b.decide = (K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide) :
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 9 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 9) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 10 c :=
  fwd₂_seat X N P D B at_ R enc rad coll off₂ 9 10 (by omega) pins_10_9 pins_10_5 (·.gU) (·.firstMask) p he ha hlen hSm hcoll
    (fun d d' rs gs h h9 => shape₂_9_10 _ _ p he ha d d' rs gs h hst hft ha1 h9) (fun d h => sampled_9 _ _ d h) b hb

end Johnson.RunOne.Law.K12Fwd29

#print axioms Johnson.RunOne.Law.K12Fwd29.fwd₂_seat
#print axioms Johnson.RunOne.Law.K12Fwd29.fwd_29
