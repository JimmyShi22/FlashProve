-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmStrLaws.lean: the written way from typed strings at the entry's description to Link
strings of the object with records (`armString`, Johnson/Flat/ArmString.lean) keeps all nine fields:
`StrLaws` (Johnson/Top/ArmLinkAt.lean).

`link_field` (Johnson/Top/ArmLinkAt.lean) takes the way `str` as a letter with the record
`StrLaws str` of nine laws. Here that record is shown of `armString`, and of `armStringFull` and
`armStringSmall` at the digest of a description's three public files and the run's decision there.
For proofs only; the program does not import this file.

Main names:
  `strLaws_to`: of `strTo hs hE` (OnBytes/K/StringTo.lean), for any two protocols.
  `strLaws_arm`: of `armString T D dec hC hds ha`.
  `strLaws_fullAt`, `strLaws_smallAt`: of `armStringFull T c dec`, `armStringSmall T c dec`, at
    every digest c and every decision.
  `strLaws_full T Z`, `strLaws_small T Z`: at `c := Z.digest` and `dec := decAt G Z.digest`, G the
    ground of that size.

Limits: types and values alone. Nothing on whether any verifier accepts a string; nothing on
soundness.

Terms: lean/GLOSSARY.md.


-/
import Johnson.Top.ArmLinkAt
import Johnson.Flat.ArmString

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (ckP)
open _root_.Run.PQ (View SgX CK XO)

/-- A string carried along two equations keeps all nine fields. -/
theorem strLaws_to {Y Y' : Type} {E E' : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Q' : BatchInteractiveOracleProof Y' E'}
    (hs : Q.loc.shape = Q'.loc.shape) (hE : E = E') :
    StrLaws (OnBytes.K.strTo (lam := 256) (Q := Q) (Q' := Q') hs hE) :=
  ⟨fun _ => rfl, fun _ => rfl, OnBytes.K.strTo_plains hs hE, OnBytes.K.strTo_opens hs hE,
    OnBytes.K.strTo_ext hs hE, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- **`StrLaws` of `armString`.** -/
theorem strLaws_arm {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed]
    [Nonempty Seed] {a : ℕ} {C : CK} {ds : List PQ.RD} {xs : List XO}
    {dec2 : (Seed × Ans) × (Seed × Ans) → View → Bool}
    (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec2)) {X₀ : Type} (D : XD)
    (dec : X₀ → View → Bool) (hC : C = D.C) (hds : ds = D.ds) (ha : a = D.a) :
    StrLaws (armString T D dec hC hds ha) :=
  ⟨armString_salt T D dec hC hds ha, armString_roots T D dec hC hds ha,
    armString_plains T D dec hC hds ha, armString_opens T D dec hC hds ha,
    armString_ext T D dec hC hds ha, armString_rtreq T D dec hC hds ha,
    armString_slot T D dec hC hds ha, armString_path T D dec hC hds ha,
    armString_rsalt T D dec hC hds ha⟩

section Full
variable {I X RI : Type} [Fintype RI] [Nonempty RI]
  (T : RestR I X RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a
    linkSibFull)

/-- At the full size, at every digest and every decision. -/
theorem strLaws_fullAt (c : ByteArray) {X₀ : Type} (dec : X₀ → View → Bool) :
    StrLaws (armStringFull T c dec) :=
  strLaws_arm T (entryXD recordGround c) dec (letters_full c).1.symm (letters_full c).2.1.symm
    (letters_full c).2.2.1.symm

/-- **At the full size, at the digest of Z's three public files and the run's decision there.** -/
theorem strLaws_full (Z : Pub) :
    StrLaws (armStringFull T Z.digest (decAt recordGround Z.digest)) :=
  strLaws_fullAt T Z.digest _

end Full

section Small
variable {I X RI : Type} [Fintype RI] [Nonempty RI]
  (T : RestR I X RI (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a
    linkSibSmall)

/-- At the small example, at every digest and every decision. -/
theorem strLaws_smallAt (c : ByteArray) {X₀ : Type} (dec : X₀ → View → Bool) :
    StrLaws (armStringSmall T c dec) :=
  strLaws_arm T (entryXD smallRecordGround c) dec (letters_small c).1.symm
    (letters_small c).2.1.symm (letters_small c).2.2.1.symm

/-- **At the small example, at the digest of Z's three public files and the run's decision there.**
-/
theorem strLaws_small (Z : Pub) :
    StrLaws (armStringSmall T Z.digest (decAt smallRecordGround Z.digest)) :=
  strLaws_smallAt T Z.digest _

end Small

end OnBytes.K.Arm
