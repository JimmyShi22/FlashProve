-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/OneSlotTyped.lean: the two letters ds and xs of the compiled slot, AT THE SLOT's
OWN TYPES, made of a one-chain description's declared
rounds (Johnson/Desc/Link/OneSlot.lean): so that dec · ds · xs are one declared line where a value
takes all three as letters.
  specOf l       a description of the format whose rounds are l; the other fields are fillers, to
  the letter those of the library's wFull | wSmall
                 (OnBytes/Flat/LinkSibAt.lean): the rounds' data depend on the rounds and on the
                 number of the first tree alone (Run.rds_congr)
  dsOf F file    the rounds' data: Run.PQ.rds at specOf of the written rounds, carried by PQ.ofLib:
  the library's dsFull | dsSmall's own make; it may
                 refuse (Johnson.G.OfPlan.writtenOf)
  xsTyped F      the stored openings as Run.PQ.XO
Definitions with code; no theorem here. dsOf AND xsTyped AT THE TYPED PARAMETERS ARE EVALUATED BY
THE KERNEL in Johnson/Desc/K15/TypedV.lean. What has been held by value (outside this
library) are the forms beneath them: roundsOf = frFmt | srFmt, and xsOf = frD.xs | srD.xs
field by field. From the first of these to
«dsOf = dsFull | dsSmall» is a theorem: Johnson/Desc/Link/OneSlotAt.lean.
-/
import Johnson.Desc.Link.OneSlot
import OnBytes.TypedOracleCompiler.Run.PlanQJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {Xi : Type}

def specOf (l : List Fmt.Round) : Fmt.Spec :=
  { label := 0, plan := ⟨.two, 0, 0, 0, 0, 0, []⟩, params := ByteArray.empty, statement :=
      ByteArray.empty, rand := .inFile
    firstTree := 0, cfg := ByteArray.empty, rounds := l }

def OneChainFileDescription.dsOf (F : OneChainFileDescription Xi) (file : String) : Except String (List TypedOracleCompiler.Run.PQ.RD) :=
  (F.roundsOf file).map fun l => (_root_.Run.PQ.rds (specOf l)).map TypedOracleCompiler.Run.PQ.ofLib

def OneChainFileDescription.xsTyped (F : OneChainFileDescription Xi) : List _root_.Run.PQ.XO :=
  F.roundsDeclaredByBlocks.zipIdx.flatMap fun r => r.1.stored.map fun s => ⟨r.2, s.item == 1, s.lo, s.count⟩

end VerifiableInference.Desc
