-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/SpellsIdCode.lean: the hash function's answer at the code of a key at the full size
(`PV.EncId.encF`, Johnson/Top/Fire/Code/Vals/EncId.lean) is the format's commitment ID
(`Fmt.publishedIDW`, Fmt/Rules4.lean) over that hash function, read on byte strings, at the key's
parts as a file spells them. Statements with their proofs. The hash function is a variable.

Under which hypothesis. That the key has a code. Every key of these types has one
(`PV.EncId.encF_total`, Johnson/Flat/Told/Dec/TAt.lean): a law that rests on it is called where this
is used.
Limits. An equation between two Lean texts, both made of the same functions of Fmt/. The spellings
of the OOD seed and the OOD answers are the same terms on both sides: nothing is said of them here.
Nothing on a commitment's properties or on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Top.Fire.Code.Vals.EncId
import Johnson.TypedOracleCompiler.Top.TieIdBytes
import OnBytes.Tie.IdKeySeedFmt
import Run.OCompM

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Cpp
open OnBytes.Flat OnBytes.Slice OnBytes.K.IdTable
open _root_.Iop (Dig)

/-- What enters the commitment ID at a key of the full size: the shape, the told part, the root and
the OOD answers; the OOD seed; no further digest. -/
def idKeyOf (c cm : Dig 256) (rcd : RecFull) : OnBytes.Tie.IdKeyS :=
  ⟨(PV.EncId.shapeF, _root_.Run.digToBytes c, ⟨_root_.Run.digToBytes cm, spellAns 11 1 rcd.2⟩),
    spellSeed 29 1 rcd.1, []⟩

/-- The code of a key at the full size (`encF`) is `idCodeS` at `idKeyOf`: by unfolding. -/
theorem encF_is (c cm : Dig 256) (rcd : RecFull) :
    PV.EncId.encF c cm rcd = OnBytes.Tie.idCodeS (idKeyOf c cm rcd) := rfl

/-- At the full size's shape the table's name bears the six numbers 32, 402653184, 44040191, 11, 1,
40: by unfolding. -/
theorem name_is (cB rootB : ByteArray) (answers : List OnBytes.E) :
    OnBytes.Key.nameOf PV.EncId.shapeF cB ⟨rootB, answers⟩ =
      Fmt.tableName rootB cB 32 402653184 44040191 11 1 40 := rfl

/-- The bytes that are hashed for the ID at `idKeyOf` are `Fmt.publishedBytes` at the key's parts.
-/
theorem idBytes_is (c cm : Dig 256) (rcd : RecFull) :
    OnBytes.Tie.idBytesS (idKeyOf c cm rcd) =
      Fmt.publishedBytes (_root_.Run.digToBytes c)
        (Fmt.tableName (_root_.Run.digToBytes cm) (_root_.Run.digToBytes c) 32 402653184 44040191
          11 1 40)
        ((spellSeed 29 1 rcd.1).map OnBytes.E.triple)
        ((spellAns 11 1 rcd.2).map OnBytes.E.triple) [] := by
  rw [OnBytes.Tie.idBytesS_fmt]
  unfold idKeyOf
  dsimp only
  rw [name_is]

/-- **The answer at a key's code is the format's commitment ID**, for a key that has a code. -/
theorem digest_encF (hash : ZKCP.Oracle 256) (c cm : Dig 256) (rcd : RecFull)
    (h : PV.EncId.encF c cm rcd ≠ none) :
    ((PV.EncId.encF c cm rcd).map hash).getD (fun _ => false) =
      _root_.Run.bytesToDig (Fmt.publishedIDW (m := Id) (Fmt.HM (m := Id) (_root_.Run.oB hash))
        (_root_.Run.digToBytes c)
        (Fmt.tableName (_root_.Run.digToBytes cm) (_root_.Run.digToBytes c) 32 402653184 44040191
          11 1 40)
        ((spellSeed 29 1 rcd.1).map OnBytes.E.triple)
        ((spellAns 11 1 rcd.2).map OnBytes.E.triple) []) := by
  rw [encF_is] at h ⊢
  have hk : OnBytes.Tie.idOkS (idKeyOf c cm rcd) = true := by
    by_contra hn
    apply h
    unfold OnBytes.Tie.idCodeS
    rw [if_neg hn]
  unfold OnBytes.Tie.idCodeS
  rw [if_pos hk, Option.map_some, Option.getD_some]
  unfold Fmt.publishedIDW
  rw [← idBytes_is c cm rcd, Fmt.HM_id]
  unfold Fmt.HO
  rw [if_neg (by decide)]
  unfold _root_.Run.oB OnBytes.Tie.idStrS
  rw [OnBytes.K.Arm.bytesToDig_digToBytes]

end Bind.Cpp

#print axioms Bind.Cpp.encF_is
#print axioms Bind.Cpp.name_is
#print axioms Bind.Cpp.idBytes_is
#print axioms Bind.Cpp.digest_encF
