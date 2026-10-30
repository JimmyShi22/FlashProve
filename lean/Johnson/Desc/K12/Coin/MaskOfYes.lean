-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/MaskOfYes.lean: **"THE MASK HAS COME" IS SAID BY THE TEST's OWN YES** (first
arm): the three places at which the promise "K12.maskCome" is spent, without it. Statements and
proofs.
The kind's files' `mask_of_step` (Johnson/Desc/K12/Law/MaskIffOwn.lean): the test on the
plan, a yes of the block's STEP, and "the first fold sends no mask of its own" give that the record
in front names a mask. Each spender of the promise stands under a yes of that very block:
  `atFinish_mask`: at the first chain's finish: a yes of the seat's step: whatever record the door
    in lays names a mask.
  `atFinish_seats_step`: `atFinish_seats` (BookAppends.lean) at the step, its premise on the mask
    gone.
  `atFinish_shapes_step`: `atFinish_shapes` (ShapesAppend.lean) likewise.
  `yes_mask`: at the piece of the kind's own block: wherever it puts out, the record in front names
    a mask. `leads_without_mask`: so a plain law of that piece whose promise asks "and the mask has
    come" holds without that clause (`leads_drop_yes`, GameYes.lean).
  `seat_yes_mask`: the same at a seat's piece (the kind's block behind two doors): whatever record
    the door in lays names a mask.
Limits. First arm alone (ownMask = false). Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.ShapesAppend
import Johnson.Desc.K12.Coin.GameYes
import Johnson.Desc.K12.Law.MaskIffOwn
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.RiderLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open VerifiableInference.Desc.K12.Door (shapesIn)

theorem isSome_of_ne_none {α : Type} {x : Option α} (h : x ≠ none) : x.isSome = true := by
  cases x with
  | none => exact absurd rfl h
  | some _ => rfl

/-- A block's step says yes on as many rounds as it declares. -/
theorem step_decide {S Cl : Type} (b : Block S Cl) (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ gs, b.decide s (rs.map noDigest) gs = .ok s' := by
  simp only [Block.step] at h
  obtain ⟨_, _, h⟩ := H2K.FoldLaw.bind_ok h
  obtain ⟨_, _, h⟩ := H2K.FoldLaw.bind_ok h
  obtain ⟨x, hx, h⟩ := H2K.FoldLaw.bind_ok h
  cases h
  exact ⟨_, hx⟩

/-- Under the test on the plan the block's step says yes on no empty list of rounds. -/
theorem step_cons (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 tE : T12) (F n : ℕ)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 rs cols = .ok (tE, n)) : ∃ r0 rs', rs = r0 :: rs' := by
  cases rs with
  | cons r0 rs' => exact ⟨r0, rs', rfl⟩
  | nil =>
    exfalso
    have hl := roundsFit_count _ _ ((step_iff _ _ _ _ _ _ _).1 h).1.1
    obtain ⟨_, _, _, R, _, _, hR⟩ :=
      H2K.Made.rounds_top p.nums _ (k12_rounds guardedProximityTestParts p hp)
    rw [hR] at hl
    simp at hl

/-- **A yes of the block's step says that the mask has come.** -/
theorem mask_of_yes (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) (t0 tE : T12) (F n : ℕ) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').step F t0 rs cols = .ok (tE, n)) : t0.mask.isSome = true := by
  obtain ⟨r0, rs', rfl⟩ := step_cons p hp t0 tE F n rs cols h
  exact isSome_of_ne_none (mask_of_step p t0 tE F n r0 rs' cols hp h ho)

/-- At the first chain's finish: whatever record the door in lays names a mask. -/
theorem atFinish_mask (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) (ft : ℕ) (s s' : First.S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (k : ℕ) (h : (atFinish p).step ft s rs cols = .ok (s', k)) :
    ∀ t, enterFinish s = .ok t → t.mask.isSome = true := by
  intro t ht
  obtain ⟨t₁, t', he, hb, _⟩ := (Seat.step_inside ft enterFinish _ leaveFinish s s' rs cols k).1 h
  rw [ht] at he
  obtain rfl := Except.ok.inj he
  exact mask_of_yes p hp ho _ t' ft k rs cols hb

/-- **`atFinish_seats` at the step, its premise on the mask gone.** -/
theorem atFinish_seats_step (L : Laid) (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) (he : p.early = true) (ha : p.answers = 1) (ft : ℕ)
    (s s' : First.S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ)
    (h : (atFinish p).step ft s rs cols = .ok (s', k)) (hS : SeatsPrefix L s.book)
    (hgo : ∀ first rest A, p.nums.stages = first :: rest →
      laidFrom s.st.codes s.book.trees.size (sendsFrom p 0 rest) = some A →
      (L.places.drop s.book.place.size).take A.places.length = A.places ∧
      (L.shapes.drop s.book.trees.size).take A.shapes.length = A.shapes) :
    SeatsPrefix L s'.book := by
  obtain ⟨gs, hd⟩ := step_decide (atFinish p) ft s s' rs cols k h
  exact atFinish_seats L p he ha s s' _ gs hd (atFinish_mask p hp ho ft s s' rs cols k h) hS hgo

/-- **`atFinish_shapes` at the step, likewise.** -/
theorem atFinish_shapes_step (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (ho : p.nums.ownMask = false) (he : p.early = true) (ha : p.answers = 1) (ft : ℕ)
    (s s' : First.S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ)
    (h : (atFinish p).step ft s rs cols = .ok (s', k)) :
    ∃ first rest, p.nums.stages = first :: rest ∧
      shapesIn s'.st = shapesIn s.st ++ noticesOf (sendsFrom p 0 rest) := by
  obtain ⟨gs, hd⟩ := step_decide (atFinish p) ft s s' rs cols k h
  exact atFinish_shapes p he ha s s' _ gs hd (atFinish_mask p hp ho ft s s' rs cols k h)

/-- At the piece of the kind's own block: wherever it puts out, the record in front names a mask. -/
theorem yes_mask {W : Type} (F : Frame) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (ho : π.nums.ownMask = false)
    (p : Piece (ckP .two) F T12 Unit W) (hb : p.b = proximityTestKind guardedProximityTestParts π) (h0 : p.back = [])
    (x : T12 × F.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds)) (b : T12 × F.E.Str)
    (h : p.ior.red.out x τ = some b) : x.1.mask.isSome = true := by
  obtain ⟨_, k, hst, _⟩ := yes_step p h0 x τ b h
  rw [hb] at hst
  exact mask_of_yes π hp ho x.1 b.1 _ k _ _ hst

/-- **A plain law of that piece whose promise asks "and the mask has come" holds without it.** -/
theorem leads_without_mask {W : Type} (F : Frame) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (ho : π.nums.ownMask = false)
    (p : Piece (ckP .two) F T12 Unit W) (hb : p.b = proximityTestKind guardedProximityTestParts π) (h0 : p.back = [])
    (on : T12 × F.E.Str → Prop) (Q : T12 × F.E.Str → T12 × F.E.Str → Prop)
    (h : p.ior.red.Leads (fun a => on a ∧ a.1.mask.isSome = true) Q p.err) :
    p.ior.red.Leads on Q p.err :=
  leads_drop_yes h fun a τ b _ hb' => yes_mask F π hp ho p hb h0 a τ b hb'

/-- **At a seat's piece** (the kind's block behind two doors): wherever it puts out, whatever record
the door in lays names a mask. -/
theorem seat_yes_mask {S W : Type} (F : Frame) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Blk').planOk = true) (ho : π.nums.ownMask = false)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (p : Piece (ckP .two) F S Unit W) (hb : p.b = (proximityTestKind guardedProximityTestParts π : Blk').inside enter leave)
    (h0 : p.back = []) (x : S × F.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds)) (b : S × F.E.Str)
    (h : p.ior.red.out x τ = some b) : ∀ t, enter x.1 = .ok t → t.mask.isSome = true := by
  intro t ht
  obtain ⟨_, k, hst, _⟩ := yes_step p h0 x τ b h
  rw [hb] at hst
  obtain ⟨t₁, t', he, hk, _⟩ := (Seat.step_inside _ enter _ leave _ _ _ _ k).1 hst
  rw [ht] at he
  obtain rfl := Except.ok.inj he
  exact mask_of_yes π hp ho _ t' _ k _ _ hk

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.seat_yes_mask
#print axioms VerifiableInference.Desc.K12.Coin.mask_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_mask
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_seats_step
#print axioms VerifiableInference.Desc.K12.Coin.atFinish_shapes_step
#print axioms VerifiableInference.Desc.K12.Coin.leads_without_mask
