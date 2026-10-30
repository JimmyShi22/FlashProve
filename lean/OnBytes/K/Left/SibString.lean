-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SibString.lean: the typed string that is assembled from what the program has read of
an entry's chain, as a typed string for the written link over letters; and the nine equations on the
two strings that `SameRun2` asks.

The left half types what the program's reader has read at the entry's description D: a string
`π : OneProtocolProof 256 (PSXE D dec).up` (`assembleS`, OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean). The entry's arm of
the compiled verifier runs at an object whose link is written over letters: `sibQ C ds a xs dec2`
(OnBytes/K/Arm/SameSib.lean). At the sizes in use the letters are D's by theorems, not by
unfolding, so the two types of strings are equal by a proof alone. Here π is carried over
(`strTo`, OnBytes/K/StringTo.lean): a definition, field by field, in which six fields are π's own.
For proofs only; the program does not import this file.

Main names:
  `sib_shape`, `sib_ext`: the rounds, and the kind of external strings, are the same.
  `sibString`: π as a string for `sibQ C ds a xs dec2`, if C, ds and a are D's.
  `sameRun_sibString`: `sameRun_sib` at `π2 := sibString … π`: its nine premises on the strings are
    paid. Of the twenty fields of `SameRun2` the two on the maps are left as premises. Asked still:
    the six letters are D's; the two decisions agree at the two instances; the two pairs of maps
    agree.
  `sibQFull`, `sibQSmall`: `sibQ` at the written letters of the two sizes; its protocol is
    `linkSibFull` (`linkSibSmall`, OnBytes/Flat/LinkSibAt.lean), by unfolding.
  `sibStringFull`, `sibStringSmall`: at the two sizes, for every digest c: from a string at
    `entryXD recordGround c` (`smallRecordGround`) to one for `sibQFull` (`sibQSmall`).

Limits: types and values alone: nothing on whether any verifier accepts a string. Nothing on
soundness. The type of strings of an object with records whose link is `linkSibFull` is not named
here.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.StringTo
import OnBytes.K.Arm.SameSib
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Carry OnBytes.Flat OnBytes.Tie OnBytes.Slice
open TypedOracleCompiler.Run.PQ (XD SOf wqX)
open OnBytes.K (fixB fixW fixP strTo)
open OnBytes.K.Arm (sibQ sibW sameRun_sib)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (chalP ckP)
open _root_.Run.PQ (View SgX CK XO)

section Letters
variable (C : CK) (ds : List PQ.RD) (a : ℕ) (xs : List XO) {Y2 : Type} (dec2 : Y2 → View → Bool)
  {X : Type} (D : XD) (dec : X → View → Bool)

/-- the rounds are the same -/
theorem sib_shape (hC : C = D.C) (hds : ds = D.ds) :
    (PSXE D dec).up.loc.shape = (sibQ C ds a xs dec2).loc.shape := by
  subst hC hds
  rfl

/-- the kind of external strings is the same -/
theorem sib_ext (ha : a = D.a) : twoExternalStrings (2 ^ D.a) SgX = twoExternalStrings (2 ^ a) SgX := by
  subst ha
  rfl

/-- **The string at the description, as a string for the written link over letters.** -/
def sibString (hC : C = D.C) (hds : ds = D.ds) (ha : a = D.a) (π : OneProtocolProof 256 (PSXE D dec).up) :
    OneProtocolProof 256 (sibQ C ds a xs dec2) :=
  strTo (sib_shape C ds a xs dec2 D dec hC hds) (sib_ext a D ha) π

variable {I X' : Type} {L : BatchProtocolWithLeafBody I X'} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **`sameRun_sib` at the carried string**: the nine premises on the strings are paid. -/
theorem sameRun_sibString (x : X) (x2 : Y2) (hC : C = D.C) (hds : ds = D.ds) (ha : a = D.a)
    (hxs : xs = D.xs) (hK : K = D.K) (hchal : HEq chal (chalP D.base.plan.field D.K))
    (hdec : dec2 x2 = dec x)
    (embS2 : (p : OPos (_root_.Run.Twin.up (SOf C ds))) →
      OSym (_root_.Run.Twin.up (SOf C ds)) p → Body L)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L) (hS : HEq embS2 embS)
    (embP2 : PlainPart (_root_.Run.Twin.up (SOf C ds)) (_root_.Run.Twin.allLo (SOf C ds)) →
      PlainPart (shapeOf L .link) (annOf L .link))
    (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
      PlainPart (shapeOf L .link) (annOf L .link)) (hP : HEq embP2 embP)
    (π : OneProtocolProof 256 (PSXE D dec).up) :
    SameRun2 (L := L) (t := .link) (fixB (sibQ C ds a xs dec2) x2) (fixB (PSXE D dec).up x)
      (fixW (sibW C ds a xs K chal dec2) x2) (fixW (wqXE D dec) x) embS2 embS embP2 embP
      (fixP (sibString C ds a xs dec2 D dec hC hds ha π) x2) (fixP π x) :=
  sameRun_sib C ds a xs K chal dec2 D dec x x2 hC hds ha hxs hK hchal hdec embS2 embS hS embP2 embP
    hP (sibString C ds a xs dec2 D dec hC hds ha π) π rfl rfl
    (OnBytes.K.strTo_plains _ _ π) (OnBytes.K.strTo_opens _ _ π) (OnBytes.K.strTo_ext _ _ π) rfl
    rfl rfl rfl

end Letters

/-! ## At the two sizes -/

/-- the written link at the full size, every round marked local -/
abbrev sibQFull :
    BatchInteractiveOracleProof (RecP NZ frS.P.v 29 1 × RecP NZ frS.P.v 29 1) (twoExternalStrings (2 ^ frS.P.T.a) SgX) :=
  sibQ (ckP .two) dsFull frS.P.T.a frD.xs fun rr => decFullX (recX rr)

/-- the written link at the small example, every round marked local -/
abbrev sibQSmall :
    BatchInteractiveOracleProof (RecP NZ srS.P.v 19 1 × RecP NZ srS.P.v 19 1) (twoExternalStrings (2 ^ srS.P.T.a) SgX) :=
  sibQ (ckP .two) dsSmall srS.P.T.a srD.xs fun rr => decSmallX (recX rr)

/-- its protocol is `linkSibFull` -/
theorem sibQFull_loc : sibQFull.loc = linkSibFull := rfl

/-- its protocol is `linkSibSmall` -/
theorem sibQSmall_loc : sibQSmall.loc = linkSibSmall := rfl

/-- **At the full size**, for every digest c and every decision. -/
def sibStringFull (c : ByteArray) {X : Type} (dec : X → View → Bool)
    (π : OneProtocolProof 256 (PSXE (entryXD recordGround c) dec).up) : OneProtocolProof 256 sibQFull :=
  sibString (ckP .two) dsFull frS.P.T.a frD.xs _ (entryXD recordGround c) dec
    (letters_full c).1.symm (letters_full c).2.1.symm (letters_full c).2.2.1.symm π

/-- **At the small example**, for every digest c and every decision. -/
def sibStringSmall (c : ByteArray) {X : Type} (dec : X → View → Bool)
    (π : OneProtocolProof 256 (PSXE (entryXD smallRecordGround c) dec).up) : OneProtocolProof 256 sibQSmall :=
  sibString (ckP .two) dsSmall srS.P.T.a srD.xs _ (entryXD smallRecordGround c) dec
    (letters_small c).1.symm (letters_small c).2.1.symm (letters_small c).2.2.1.symm π

end OnBytes.K.Left
