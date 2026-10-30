-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Vals/EncId.lean: the key's code as a value with code, at both sizes: `encId`
(Johnson/TypedOracleCompiler/Top/IdSeedAt.lean) written out free of the object. It reads of a key its root and its
record, and the configuration's digest c beside.
`encS_eq`, `encF_eq`: it is `encId` at the ground, at every rest T. No `noncomputable` stands in
this file.

-/
import Johnson.TypedOracleCompiler.Top.IdSeedAt
import OnBytes.Flat.EntryTerm

set_option autoImplicit false
set_option maxRecDepth 40000

namespace PV.EncId
open _root_.Iop (Dig InteractiveOracleProof twoExternalStrings)
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.Tie
open OnBytes.RunA (RestR LrG)
open _root_.Run.PQ (SgX)
open OnBytes.K OnBytes.K.IdTable OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch.Cms (KeyRoot)

/-! ## The small example -/

/-- the tables' shape: six typed numbers -/
def shapeS : Params.IndexShape := Params.smallRecordLink.table

/-- **keyCode, written out free of the object**: the code of a key (c, (root, record)): `encId`'s body.
  -/
def encS (c cm : Dig 256) (rcd : RecSmall) : Option ZKCP.Str :=
  OnBytes.Tie.idCodeS
    ⟨(shapeS, _root_.Run.digToBytes c, ⟨_root_.Run.digToBytes cm, spellAns srS.P.v 1 rcd.2⟩),
      spellSeed 19 1 rcd.1, []⟩

/-- It is `encId` at the ground, at every rest T. -/
theorem encS_eq {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
    {Q : InteractiveOracleProof (RecSmall × RecSmall) (twoExternalStrings (2 ^ a) SgX)}
    (T : RestR I' X' RI (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) a Q)
    (k : Dig 256 × KeyRoot 256 (LrG T)) :
    encId smallRecordGround T k = encS k.1 k.2.cm k.2.rcd := rfl


/-! ## The full size -/

/-- the tables' shape: six typed numbers -/
def shapeF : Params.IndexShape := Params.recordLink.table

/-- **keyCode, written out free of the object**: the code of a key (c, (root, record)): `encId`'s body.
  -/
def encF (c cm : Dig 256) (rcd : RecFull) : Option ZKCP.Str :=
  OnBytes.Tie.idCodeS
    ⟨(shapeF, _root_.Run.digToBytes c, ⟨_root_.Run.digToBytes cm, spellAns frS.P.v 1 rcd.2⟩),
      spellSeed 29 1 rcd.1, []⟩

/-- It is `encId` at the ground, at every rest T. -/
theorem encF_eq {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
    {Q : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ a) SgX)}
    (T : RestR I' X' RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) a Q)
    (k : Dig 256 × KeyRoot 256 (LrG T)) :
    encId recordGround T k = encF k.1 k.2.cm k.2.rcd := rfl

end PV.EncId
