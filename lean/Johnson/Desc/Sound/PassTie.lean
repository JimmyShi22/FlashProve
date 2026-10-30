-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PassTie.lean: A BLOCK WHOSE `decide` HANDS THE RECORD ON (a seal) IS TIED TO THE
TYPED BLOCK THAT HANDS ITS STATEMENT ON.

The setting. `PieceTie` (Johnson/Desc/Sound/TypedRow.lean) ties a block on its stretch to a proved
typed block. `KObj.BK.pass` (Johnson/Desc/Sound/TypedLists.lean) is the typed block without a round
that hands its statement on.

What is said. `skipAll`, `skipAll_tr`, `skipAll_fits`: the reading of rounds that skips every round.
`passTie`: the tie, at every joint and for every reading that reads no tree from the block's place
on (`ReadsBelow`, Johnson/Desc/Sound/RunIsDecide.lean), whatever the block's rounds and errors are.

Limits. A fact on the frame, general in the block.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.Sound.TypedLists
import Johnson.Desc.Sound.QuietGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- The reading of rounds that skips every round. -/
def skipAll : (s : Shape) → CarryS s []
  | [] => .nil
  | _ :: s => .skip fun _ _ => skipAll s

theorem skipAll_tr : ∀ (s : Shape) (τ : Iop.Tr s), (skipAll s).tr τ = some ()
  | [], _ => rfl
  | _ :: s, (_, _, τ) => skipAll_tr s τ

theorem skipAll_fits : ∀ (s : Shape) (ε : Err s), (skipAll s).Fits () ε
  | [], _ => trivial
  | _ :: s, (_, ε) => fun _ _ => skipAll_fits s ε

/-- **A block whose `decide` hands the record on is tied to the typed block that hands its statement
on**, at every joint, for every reading that reads no tree from the block's place on, whatever its
rounds and its errors are. The extractor hands the witness back. -/
theorem passTie (p : Piece C F S Cl W) (A : JK)
    (rd : S × F.E.Str → A.X × A.E.Str) (wr : W → A.W) (hnd : (F.all.map (·.no)).Nodup)
    (hrd : ReadsBelow p.base rd) (hext : ∀ a τ w, p.ext a τ w = w)
    (hb : ∀ s rs gs s', p.b.decide s rs gs = .ok s' → s' = s) :
    PieceTie p (BK.pass A) rd rd wr wr :=
  ⟨fun _ => skipAll _, fun _ => skipAll_fits _ _, fun a τ a' _ ho => by
    obtain ⟨-, -, h3, h4⟩ := (Piece.out_iff _ a a' τ).1 ho
    have e1 : a'.1 = a.1 := hb _ _ _ _ h3
    have e2 : rd a' = rd a := by
      obtain ⟨s', y'⟩ := a'
      obtain ⟨s, y⟩ := a
      have e1' : s' = s := e1
      have h4' : y' = _ := h4
      rw [e1', h4']
      exact hrd.imp hnd _ (Nat.le_refl _) s y τ
    refine ⟨(), skipAll_tr _ τ, ?_, fun w => congrArg wr (hext a τ w)⟩
    rw [e2]
    rfl⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.skipAll_tr
#print axioms VerifiableInference.Desc.Sound.skipAll_fits
#print axioms VerifiableInference.Desc.Sound.passTie
