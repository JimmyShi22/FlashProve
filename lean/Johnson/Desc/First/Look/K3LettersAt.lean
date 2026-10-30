-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LettersAt.lean: the kind "lookup" (K3): CLOSED TERMS FOR THE LETTERS OF
ITS LAW AT THE TABLE OF JOINTS THAT ARE THE KIND's TO NAME: each a definition off the public
data X alone, or off nothing.

Main names:
  `k3QAny`: the letter Q of `HeadMean` (what is known of the ledger in front of the head's calls):
    nothing is asked.
  `k3AdrAt X`: the letter adr (where a cell of the head's sub-proof lies): the lookups' authors' own
    map `adrOf` at the public data's head's shape, layout and border: THE VALUE AT WHICH THEIR
    CLOSED CALLER `headRiderAt` CALLS IT (Johnson/Desc/First/Look/K3CallerHead.lean).
  `k3SizesAt X`, `k3PolicyAt X`: the head's kind's two classes, as `headRiderAt` lays them.
  `k3PrimeAt`: the letter pp of `K3Plan`: the field's prime, as the Bool `digBAt` lays it.
  `k3FloorAt X`: the letter floor of `K3Plan`: the head's keys' floor off the head's shape.
  `k3StoredAt rad arr seat`: `K3Letters` with the stored table's five laid as the conduit of
    Johnson/Desc/First/Look/K3StoredThree.lean; rad, arr and seat stay letters.

Limits: definitions. That they are the RIGHT terms is said by nothing here: `k3AdrAt`, `k3SizesAt`,
`k3PolicyAt` and `k3FloorAt` are what the lookups' authors' own closed caller and its docstring
name; `k3PrimeAt` what their Bool lays. Nothing on soundness; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3FillWorth
import Johnson.Desc.First.Look.K3CallerHead
import Johnson.Desc.First.Look.K3StoredThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr adrOf)

/-- Nothing is asked of the ledger in front of the head's calls. SO THE FACT THAT THE FIELD "behind"
IS HANDED ON WHAT THE BLOCK LEAVES (`K3LeftAt … Q`) IS IDLE AT THIS Q: the rule that pays "behind"
(`calls_behind`) does not spend it: it takes the sharper fact off the block's own yes. -/
def k3QAny : Fork → Prop := fun _ => True

/-- Where a cell of the head's sub-proof lies, off the public data. -/
def k3AdrAt (X : Verify.Public) : HeadAdr := adrOf X.hS X.HLy (Verify.borderOf X.y)

/-- The head's kind's sizes, off the public data. -/
@[reducible] def k3SizesAt (X : Verify.Public) : Desc.Kinds.Head.Sizes :=
  Desc.Kinds.Head.Law.sizesOf X.hS

/-- The head's kind's policy, off the public data. -/
@[reducible] def k3PolicyAt (X : Verify.Public) : Desc.Kinds.Head.Policy :=
  Desc.Kinds.Head.Law.policyOf X.hS

/-- The field's prime. -/
def k3PrimeAt : ℕ := Cb.Gl.p

/-- The head's keys' floor, off the public data. -/
def k3FloorAt (X : Verify.Public) : ℕ := Model.Head.keyFloor X.hS

/-- The kind's letters, with the stored table's five laid as the conduit. -/
def k3StoredAt {rows cols : ℕ} {Tok : Type} (rad : OracleShape → ℕ) (arr : ℕ → ℕ → ℕ)
    (seat : ℕ → Bool → ℕ → ℕ × ℕ) : K3Letters (Stored.CellsW rows cols) Tok where
  rad := rad
  arr := arr
  seat := seat
  oW := Stored.oWc rows cols
  wOf := Stored.wOfC
  nr := rows
  nc := cols
  msgW := Stored.msgWc

end VerifiableInference.OnPublicFiles
