-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrameOfFront.lean: the code switch: THE FRAME THAT THE ROWS' MAKER
MAKES AT A YES IS A FUNCTION OF THE FRONT ALONE: nothing that is sent or drawn in the switch's two
rounds enters it.

The program's switchFrame (OnBytes/Iop/Cs.lean:412-440) is handed the statement S3 behind the
sending and the joins. Of that statement it reads the codes and the messages' shapes, nothing else.
  SameShapes    two statements with the same codes and, number by number, the same shape (or no
                message)
  SameShapes.getD, rowBits, placeBits, tableBits, padOf  what such two statements share: a message's
                shape read with a default, and the four numbers that the frame's maker reads off
                shapes
  frame_congr   at two such statements switchFrame has the same value, at all other arguments
  idsOf, skelOf  the numbers that a switch's sending returns at a front; the front's statement with
                the notices received and nothing else (the library's stSent): both functions of the
                front
  frameAt       switchFrame at skelOf, idsOf and the front's carried rows and target
  shapes_at_yes  at a yes (K2Hears/Whole.lean's AtYes) S3 and skelOf of the front are SameShapes
  frame_of_front  at a yes the maker's frame is frameAt of the front
So «the frame is the public frame W₀» is a clause on the record IN FRONT, not on the transcript.
LIMITS. That frameAt of a front is the PLAN's is not said: the front's shapes, numbers, target and
the carried rows' layout are the record's. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.Whole
import Johnson.Top.H.SwitchPads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (switchNotices sendByL8)

/-- The same codes and, number by number, the same shape. -/
structure SameShapes (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  shape : ∀ o : Nat, (S'.oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape)

namespace SameShapes
variable {S S' : Statement} (h : SameShapes S S')
include h

theorem getD (o : Nat) : (S'.oracles.getD o default).shape = (S.oracles.getD o default).shape := by
  have e := h.shape o
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases h1 : S'.oracles[o]? <;> cases h2 : S.oracles[o]? <;> simp [h1, h2] at e ⊢
  exact e

theorem rowBits (o : Nat) (part : Part) : S'.rowBits o part = S.rowBits o part := by
  have e := h.shape o
  unfold Statement.rowBits
  cases h1 : S'.oracles[o]? <;> cases h2 : S.oracles[o]? <;> simp [h1, h2] at e ⊢
  rw [e]

theorem placeBits (o : Nat) (part : Part) : S'.placeBits o part = S.placeBits o part := by
  have e := h.shape o
  unfold Statement.placeBits
  cases h1 : S'.oracles[o]? <;> cases h2 : S.oracles[o]? <;> simp [h1, h2] at e ⊢
  rw [e, h.codes]

theorem tableBits (o : Nat) (part : Part) : S'.tableBits o part = S.tableBits o part := by
  unfold Statement.tableBits
  rw [h.rowBits, h.placeBits]

theorem padOf (o : Nat) : OnBytes.padOf S' o = OnBytes.padOf S o := by
  unfold OnBytes.padOf
  rw [h.codes, h.getD]

end SameShapes

/-- **The frame reads the codes and the shapes alone.** -/
theorem frame_congr {S S' : Statement} (h : SameShapes S S') (old : SingleRows) (T : SwitchTarget)
    (g : Nat) (anew : Array Nat) : switchFrame S' old T g anew = switchFrame S old T g anew := by
  have hp : switchParts S' old = switchParts S old :=
    Johnson.Top.H.parts_congr S S' old h.codes fun o _ => h.getD o
  unfold switchFrame
  simp only [h.codes, hp, h.tableBits, h.rowBits, h.padOf, h.getD]

/-- The numbers that a switch's sending returns at a front. -/
def idsOf (x : _root_.Tw.K2.Front) : Array Nat :=
  (Array.range (switchNotices x.T x.others).size).map (· + x.st.oracles.size)

/-- The front's statement with the notices received. -/
def skelOf (x : _root_.Tw.K2.Front) : Statement :=
  OnBytes.Slice.stSent x.st (switchNotices x.T x.others)

/-- **The frame at a front.** -/
def frameAt (x : _root_.Tw.K2.Front) : Option SwitchFrame :=
  switchFrame (skelOf x) x.f.rows x.T ((idsOf x).getD 0 noId)
    ((idsOf x).extract 1 (1 + x.T.kept.size))

theorem shapes_at_yes {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) : SameShapes (skelOf x) S3 := by
  refine ⟨A.same.codes.trans A.sent.codes, fun o => ?_⟩
  rw [A.same.shape o]
  by_cases ho : o < x.st.oracles.size
  · rw [A.sent.old o ho]
    unfold skelOf
    rw [OnBytes.Slice.stSent_old _ _ o ho]
  · obtain ⟨i, rfl⟩ : ∃ i, o = x.st.oracles.size + i := ⟨o - x.st.oracles.size, by omega⟩
    rw [A.sent.shape i]
    unfold skelOf
    rw [OnBytes.Slice.stSent_new, Option.map_map]
    rfl

/-- **At a yes the maker's frame is the frame at the front.** -/
theorem frame_of_front {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) :
    switchFrame S3 x.f.rows x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size)) =
      frameAt x := by
  rw [frame_congr (shapes_at_yes A), A.sent.ids]
  rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.frame_congr
#print axioms VerifiableInference.Desc.First.K2.frame_of_front
