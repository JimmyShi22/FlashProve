-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ClaimCarried.lean: THE WEIGHTS' CLAIM ACROSS THE FIRST JOINT: ONE HOME FOR "WHAT THE STORED TABLE DECODES TO". Three small theorems. A joint build of files of Johnson/Desc/Sound/ and Johnson/Desc/K14/Law/. A PIECE OF THE CARRIAGE; NO LAW OF A BLOCK.
Two forms that this file avoids. (1) The first table's pileOne is not laid as the sentence "the reader gives a record of (Eval), and …" at every border: pileOne is open one block before (Eval) is laid: there that sentence can be false of every witness. The filling
that is meant lays pileOne through the record's own rows (one with that sentence where (Eval) is laid, under the promise): JointFilling.lean, PointAtJoint.lean. (2) The top statements' decoder and the typed data do not have records of one type (DecFields.lean's head): (DEC) and (KEY)
typed at one type are unpayable at the letters that are meant: both are said through a map tr of records.

  decTop_is_decAtRec: decTop (Johnson/Desc/Sound/DecTop.lean: the first table's decoder made of the top statements' D) IS decAtRec of D through the string made of the cells: rfl.
  one_decoder: WHERE D, THROUGH THAT STRING, IS THE GUARDED DECODER AT tr OF THE RECORD (DEC), decTop is decAtRec (decGuard coll dcd held) (tr ∘ recOf ∘ fst).
  carried: under (DEC) and (KEY): "the first chain's promise that the table decodes gives the shared chain's" and "the shared chain's pin on the cells gives the first chain's pinW": the first joint's two premises (TP), (PW), at the guarded decoder decK.
WHAT STAYS, BY NAME: **(DEC): ∀ c r, D (tabBack a c) r = decGuard collAt dcdAt held c (tr r)**: by DecFields.lean it is two ties of fields: SHOWN BY NOBODY · **(KEY): recAt (start₂ ‹public›) = tr (recOf ‹public›)**: the two readers of the key's seeds and record give one record: NOT the equation that other files have at their
description (that one is between two readers of ONE type): its kin.

Limits. Unfoldings. D, recOf, tr, start₂ and the typed data's letters stay letters. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtK14Closed
import Johnson.Desc.Sound.DecFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open _root_.Run.PQ (SgX)
open _root_.Iop (oneExternalString)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (decodesOf pinWOf MsgT decTop tabBack decAtRec decGuard CellsOf)

variable {Cells Tok : Type}

/-- The first table's decoder made of the top statements' is a decoder at a reader of the record. -/
theorem decTop_is_decAtRec {P S Rec M : Type} (a : Nat) (D : (oneExternalString (2 ^ a) SgX).Str → Rec → Option M)
    (recOf : P → Rec) :
    decTop (S := S) a D recOf = decAtRec (fun c r => D (tabBack a c) r) (fun x : P × S => recOf x.1) := rfl

/-- **One home**: where the top statements' decoder, through the cells, is the guarded decoder at tr of the record. -/
theorem one_decoder {P S Rec R M : Type} (a : Nat) (D : (oneExternalString (2 ^ a) SgX).Str → Rec → Option Cells)
    (recOf : P → Rec) (tr : Rec → R) (coll : CellsOf → R → Prop) (dcd : CellsOf → R → Option M)
    (held : M → Option Cells) (hDEC : ∀ c r, D (tabBack a c) r = decGuard coll dcd held c (tr r)) :
    decTop (S := S) a D recOf = decAtRec (decGuard coll dcd held) (fun x : P × S => tr (recOf x.1)) := by
  funext c x
  exact hDEC c (recOf x.1)

/-- **"Decodes" and the cells' pin cross the joint at one decoder**: from (DEC) and (KEY). -/
theorem carried {P S Rec : Type} (a : Nat) (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (D : (oneExternalString (2 ^ a) SgX).Str → Rec → Option Cells) (recOf : P → Rec)
    (tr : Rec → (ixOf2 p.S.fold err₂ eM rank).Rec) (start₂ : P → St)
    (hDEC : ∀ c r, D (tabBack a c) r =
      decGuard (collAt p err₂ eM rank) (dcdAt p err₂ eM rank) held c (tr r))
    (hKEY : ∀ x : P, recAt p err₂ eM rank (start₂ x) = tr (recOf x)) (x : P × S) (y : Strs) :
    (decodesOf (decTop (S := S) a D recOf) x y → decodesOf (decK p err₂ eM rank held) (start₂ x.1) y) ∧
      ∀ w : Wit Cells Tok MsgT, pinWOf (decK p err₂ eM rank held) (start₂ x.1) y w →
        pinWOf (decTop (S := S) a D recOf) x y w := by
  have e : decTop (S := S) a D recOf y.cell x = decK p err₂ eM rank held y.cell (start₂ x.1) := by
    rw [one_decoder a D recOf tr _ _ held hDEC]
    show decGuard _ _ held y.cell (tr (recOf x.1)) =
      decGuard _ _ held y.cell (recAt p err₂ eM rank (start₂ x.1))
    rw [hKEY]
  refine ⟨fun h => ?_, fun w h => ?_⟩
  · unfold decodesOf at h ⊢
    rw [← e]
    exact h
  · unfold pinWOf at h ⊢
    rw [e]
    exact h

end Desc.K14.Law

#print axioms Desc.K14.Law.decTop_is_decAtRec
#print axioms Desc.K14.Law.one_decoder
#print axioms Desc.K14.Law.carried
