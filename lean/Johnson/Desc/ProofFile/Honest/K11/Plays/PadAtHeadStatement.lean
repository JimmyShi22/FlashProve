-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/PadAtHeadStatement.lean: TWO OF THE PREMISES OF
`MaskTieOfRoad` (MaskRoadStatement.lean of this folder), THE ONE ON THE PAD AND THE BOUND ON THE
LETTER free, UNDER THE LIBRARY's HEAD ALONE, AT free := 3569: STATEMENTS ALONE: two definitions of
propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's goals: they are
lemmas' statements.

  `PadAtHead`    the head: at every member xM that `xAt` finds at the seat (73, 2) of the head's
                 list of members: none of the first 3569 places of mask row 0 is a pad's place
  `FreeAtHead`   the head · the maker's base Bs: 3531 + (2 lk + 2) ≤ 3569, at the kind's own lk

Limits. THE OTHER TEN PREMISES OF `MaskTieOfRoad` STAY. 3569 is the least number that serves: the
slot 3531 and the run's 38 entries; how many places of that row are free in all is not said. BY THE
TEXT OF THE LEMMA THAT IS CALLED (`noPad_one`, Honest/Law/Rule/ReaderPays.lean) THE PAD IN THAT ROW
IS ITS LAST PLACE ALONE: so the first statement says that the mask code's message has at least 3570
entries, and no more. The head is a premise, at the earlier hash, at the full size. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.MaskRoadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain padB)
open VerifiableInference.Desc.Sound (Mem xAt)
open P5J (AtMgA TS)

/-- The statement on the pad. Not proved here; a lemma's statement, none of the library's goals. -/
def PadAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x),
    ∀ xM : Mem, xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
      ∀ ν, ν < 3569 → padB h.𝔇.cs (xM.1.l.get xM.2).1 true 0 ν = false

/-- The statement on the bound. Not proved here; a lemma's statement, none of the library's goals.
-/
def FreeAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (_ : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    3531 + (2 * (_root_.K11.parOf Zp Bs.G₀).lay.lk + 2) ≤ 3569

end ProofFile.Honest.K11
