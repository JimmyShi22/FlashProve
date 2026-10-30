-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ArmString.lean: the typed string that is assembled from what the program has read of an
entry's chain, at the type of Link strings of the object with records `LrG T`
(Johnson/EntryRec/Defs.lean) whose link is the written link over letters.

The entry's arm of the compiled verifier takes a Link string `πL : OneProtocolProof 256 (batLC L aL)`
(Johnson/TypedOracleCompiler/RecCompile/Carrier.lean). At `L := LrG T`, T's link being `linkProtocolOfRoundData C ds a xs dec2`, and
`aL := Run.Twin.allLo (SOf C ds)`, that protocol is `sibQ C ds a xs dec2`
(OnBytes/K/Arm/SameSib.lean) by unfolding. So the string of OnBytes/K/Left/SibString.lean is a
string of the arm's own type, and part of what `SameRun2` asks is shown at the arm's own protocol,
wire record and string.

Main names:
  `batLC_sib`, `wSib_sib`: the arm's protocol is `sibQ`, its Link's wire record `wSib`
    (Johnson/EntryRec/OklaSib.lean) is `sibW`: by unfolding.
  `armString T D dec hC hds ha π`: the string π at the description D, at the arm's own type.
  `armString_salt` … `armString_ext`: its nine fields are π's: six as equations, the plain parts
    and the two kinds of openings as heterogeneous equations.
  `sameRun_arm`: `SameRun2` between the arm's protocol, wire record and string at x2 and the
    skeleton's at x. Asked: the six letters are D's; the two decisions agree at the two instances;
    the two pairs of maps agree.
  `armStringFull T c dec`, `armStringSmall T c dec`: at the two sizes, for every digest c.
  `armStringFull_eq`, `armStringSmall_eq`: they are `armString` at the description of that size and
    digest, with the three proofs out of `letters_full c` (`letters_small c`): by unfolding.

What the definition reads: `armString` is a function of the string π that is written down: it lays
π's nine fields, six as they are and three carried along proofs of three equations on the
description's letters (C, ds, a). It asks no oracle, makes no choice, and has no case on a
proposition. (Lean marks it noncomputable with its section; nothing in it hangs on that.)

Limits: types and values alone: nothing on whether any verifier accepts a string; nothing on
soundness; no probability. T is a letter: no object is written here.

Terms: lean/GLOSSARY.md.


-/
import Johnson.EntryRec.OklaSib
import OnBytes.K.Left.SibString

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Carry OnBytes.Flat OnBytes.Tie OnBytes.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.RunA (RestR LrG wSib)
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.K (fixB fixW fixP)
open OnBytes.K.Arm (sibQ sibW)
open OnBytes.K.Left (sibString sameRun_sibString sibStringFull sibStringSmall)
open _root_.Run (ckP chalP)
open _root_.Run.PQ (CK XO View SgX)

section Letters
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List PQ.RD} {xs : List XO}
  {dec2 : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec2))

/-- the arm's protocol is the written link over letters, every round marked local -/
theorem batLC_sib :
    batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds)) = sibQ C ds a xs dec2 := rfl

/-- its Link's wire record is the one with the five fields of the sibling's -/
theorem wSib_sib (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    wSib T K chal = sibW C ds a xs K chal dec2 := rfl

variable {X₀ : Type} (D : XD) (dec : X₀ → View → Bool)

/-- **The string at the description, at the arm's own type.** -/
def armString (hC : C = D.C) (hds : ds = D.ds) (ha : a = D.a) (π : OneProtocolProof 256 (PSXE D dec).up) :
    OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds))) :=
  sibString C ds a xs dec2 D dec hC hds ha π

section Nine
variable (hC : C = D.C) (hds : ds = D.ds) (ha : a = D.a) (π : OneProtocolProof 256 (PSXE D dec).up)

theorem armString_salt : (armString T D dec hC hds ha π).salt = π.salt := rfl
theorem armString_roots : (armString T D dec hC hds ha π).roots = π.roots := rfl
theorem armString_rtreq : (armString T D dec hC hds ha π).rtreq = π.rtreq := rfl
theorem armString_slot : (armString T D dec hC hds ha π).slot = π.slot := rfl
theorem armString_path : (armString T D dec hC hds ha π).path = π.path := rfl
theorem armString_rsalt : (armString T D dec hC hds ha π).rsalt = π.rsalt := rfl
theorem armString_plains : HEq (armString T D dec hC hds ha π).plains π.plains :=
  OnBytes.K.strTo_plains _ _ π
theorem armString_opens : HEq (armString T D dec hC hds ha π).opens π.opens :=
  OnBytes.K.strTo_opens _ _ π
theorem armString_ext : HEq (armString T D dec hC hds ha π).ext π.ext :=
  OnBytes.K.strTo_ext _ _ π

end Nine

variable {I' X' : Type} {L : BatchProtocolWithLeafBody I' X'} (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **`SameRun2` at the arm's own protocol, wire record and string.** -/
theorem sameRun_arm (x : X₀) (x2 : (Seed × Ans) × (Seed × Ans)) (hC : C = D.C) (hds : ds = D.ds)
    (ha : a = D.a) (hxs : xs = D.xs) (hK : K = D.K)
    (hchal : HEq chal (chalP D.base.plan.field D.K)) (hdec : dec2 x2 = dec x)
    (embS2 : (p : OPos (_root_.Run.Twin.up (SOf C ds))) →
      OSym (_root_.Run.Twin.up (SOf C ds)) p → Body L)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L) (hS : HEq embS2 embS)
    (embP2 : PlainPart (_root_.Run.Twin.up (SOf C ds)) (_root_.Run.Twin.allLo (SOf C ds)) →
      PlainPart (shapeOf L .link) (annOf L .link))
    (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
      PlainPart (shapeOf L .link) (annOf L .link)) (hP : HEq embP2 embP)
    (π : OneProtocolProof 256 (PSXE D dec).up) :
    SameRun2 (L := L) (t := .link)
      (fixB (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds))) x2) (fixB (PSXE D dec).up x)
      (fixW (wSib T K chal) x2) (fixW (wqXE D dec) x) embS2 embS embP2 embP
      (fixP (armString T D dec hC hds ha π) x2) (fixP π x) :=
  sameRun_sibString C ds a xs dec2 D dec K chal x x2 hC hds ha hxs hK hchal hdec embS2 embS hS
    embP2 embP hP π

end Letters

/-! ## At the two sizes -/

/-- **At the full size**, for every digest c and every decision. -/
def armStringFull {I X RI : Type} [Fintype RI] [Nonempty RI]
    (T : RestR I X RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a
      linkSibFull)
    (c : ByteArray) {X₀ : Type} (dec : X₀ → View → Bool)
    (π : OneProtocolProof 256 (PSXE (entryXD recordGround c) dec).up) :
    OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) :=
  sibStringFull c dec π

/-- **At the small example**, for every digest c and every decision. -/
def armStringSmall {I X RI : Type} [Fintype RI] [Nonempty RI]
    (T : RestR I X RI (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a
      linkSibSmall)
    (c : ByteArray) {X₀ : Type} (dec : X₀ → View → Bool)
    (π : OneProtocolProof 256 (PSXE (entryXD smallRecordGround c) dec).up) :
    OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) :=
  sibStringSmall c dec π

/-- At the full size it is `armString` at `entryXD recordGround c`. -/
theorem armStringFull_eq {I X RI : Type} [Fintype RI] [Nonempty RI]
    (T : RestR I X RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a
      linkSibFull)
    (c : ByteArray) {X₀ : Type} (dec : X₀ → View → Bool)
    (π : OneProtocolProof 256 (PSXE (entryXD recordGround c) dec).up) :
    armStringFull T c dec π = armString T (entryXD recordGround c) dec (letters_full c).1.symm
      (letters_full c).2.1.symm (letters_full c).2.2.1.symm π := rfl

/-- At the small example it is `armString` at `entryXD smallRecordGround c`. -/
theorem armStringSmall_eq {I X RI : Type} [Fintype RI] [Nonempty RI]
    (T : RestR I X RI (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a
      linkSibSmall)
    (c : ByteArray) {X₀ : Type} (dec : X₀ → View → Bool)
    (π : OneProtocolProof 256 (PSXE (entryXD smallRecordGround c) dec).up) :
    armStringSmall T c dec π = armString T (entryXD smallRecordGround c) dec
      (letters_small c).1.symm (letters_small c).2.1.symm (letters_small c).2.2.1.symm π := rfl

end TypedOracleCompiler.Compile.Batch.Cms
