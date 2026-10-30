-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/PartChainOn.lean: a part of the join whose checker answers its own queries at a finite
set of strings by a table (`pinOn`, OnBytes/Slice/AtSet.lean).

Main definition: `Part.on`.
-/
import OnBytes.Slice.JoinThree
import OnBytes.Slice.AtSet
import OnBytes.Slice.OneWorldChain
import OnBytes.Slice.JudgeLink
import OnBytes.Slice.OneWorldTop
import OnBytes.Slice.RootsInAt
import Fmt.M1SpecKnownProofs
import Run.PlanPullM1
import OnBytes.Params.Spell
import OnBytes.Params.ToyDescriptions
import OnBytes.Tie.SpecXBase
import OnBytes.Slice.TopAny
import OnBytes.Slice.BaseAt
import OnBytes.Slice.BatAt
import OnBytes.Slice.CornersAt
import OnBytes.Slice.CsMet
import OnBytes.Slice.LinkSound
import OnBytes.Slice.CodeFacts
import OnBytes.Slice.MembFacts
import OnBytes.Slice.RoundsOf
import OnBytes.Slice.RoundsLink
import OnBytes.Entry.File
import Fmt.M3Items
import OnBytes.Params.EntryRoundsToy
import OnBytes.Slice.BatSem
import OnBytes.Slice.ManyClosesStd
import OnBytes.Slice.ManyHolds
import OnBytes.Params.EntryCheckIff
import OnBytes.Slice.ManyBlkWritten
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Iop.Link
import OnBytes.Iop.Prox
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.BlkSendCs
import OnBytes.Slice.BlkHead
import OnBytes.Slice.BlkHeadTie
import OnBytes.Slice.BlkTieFold
import OnBytes.Slice.ManyBlk
import OnBytes.Slice.ManyView
import OnBytes.Slice.ChainErrAny
import OnBytes.Slice.CsErr
import OnBytes.Slice.NoWorkRatesNum
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Slice.NoWorkRatesTail
import OnBytes.Slice.NoWorkRatesLink
import OnBytes.Slice.SemLib
import OnBytes.Slice.FoldAt
import OnBytes.Slice.ManyNumLink
import OnBytes.Tie.EntryPre
import OnBytes.Slice.FitsReadAt
import Fmt.M3ParOfLaws
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M1SpecKnown
import Fmt.M3ParOfLawsProofs
import OnBytes.Slice.BlkSem
import OnBytes.Slice.BlkSwitches
import OnBytes.Slice.SameStoredAt
import OnBytes.Slice.SameAt
import OnBytes.Slice.Decoder
import OnBytes.Slice.SameRawOf
import OnBytes.Slice.WalkOff
import OnBytes.Tie.EntryAtCfg

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal

section
variable {lam : ℕ} {γ Sg : Type}

/-- A part with its checker's queries at the strings of S answered by the table T. All other fields
are the part's own. -/
noncomputable def Part.on (s : Part lam γ Sg) (S : Finset (List Bool)) (T : List Bool → Dig lam) :
    Part lam γ Sg :=
  { s with chk := fun x => pinOn S T (s.chk x) }

end

end OnBytes.Slice
