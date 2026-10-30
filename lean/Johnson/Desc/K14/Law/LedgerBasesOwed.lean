-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerBasesOwed.lean: THREE STATEMENTS THAT ARE OWED FOR K14's LAW, AS
PROPOSITIONS BY def: NO PROOF HERE. The laws of the shared chain's later blocks ask that the trees
of o_u, o_omega and o_sp are sent in front of them: comparisons of a tenant's tree's number with a
piece's base. A piece's base is the row's first base and the trees that the earlier pieces' written
rounds send (Tiled, Johnson/Desc/Sound/ChainRule.lean). OWED, AT EVERY PLAN, WITH NOTHING EVALUATED:
written rounds that go along declared rounds send as many trees as these declare roots; of the
kind's eight blocks the two sendings alone declare roots: as many as their layouts have trees; so
the bases of the row's pieces number 3 and 6.

  TreesAlongOwed   nTrees of written rounds along declared rounds: the declared roots, summed
  RootsOwed        the declared roots of the kind's eight blocks, block by block
  BasesOwed        in a tiled row whose first piece has no round and whose next six go along the
                   kind's first six blocks: the bases of the pieces number 3 and 6
What is not claimed. That they hold.
(They are proved in Johnson/Desc/K14/Law/LedgerBases.lean: treesAlong, roots, bases.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Sound.Stretch
import Johnson.Desc.Sound.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- The roots that a list of declared rounds declares. -/
def rootsOf (rs : List Fmt.DeclaredRound) : ℕ := (rs.map (·.entry.roots)).sum

/-- OWED: written rounds along declared rounds, as many as these, send the declared roots' trees. -/
def TreesAlongOwed : Prop :=
  ∀ (num : Fmt.TreeSource → ℕ) (rs : List Fmt.DeclaredRound) (ds : List RDT), Along (RoundIs num) rs ds →
    ds.length = rs.length → nTrees ds = rootsOf rs

/-- OWED: of the kind's eight blocks the two sendings alone declare roots: their layouts' trees. -/
def RootsOwed : Prop :=
  ∀ (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (sentU : Array OracleNotice)
    (layU layO : TreeLay), blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] →
    withU Q.S = some sentU → layTrees Q.codes sentU = some layU →
    layTrees Q.codes (withOmega Q.S) = some layO →
    [b1, b2, b3, b4, b5, b6, b7, b8].map (fun b => rootsOf b.rounds) =
      [0, layU.shapes.size, 0, 0, layO.shapes.size, 0, 0, 0]

/-- OWED: the bases of the row's pieces number 3 and 6. -/
def BasesOwed : Prop :=
  ∀ (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (sentU : Array OracleNotice)
    (layU layO : TreeLay), blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] →
    withU Q.S = some sentU → layTrees Q.codes sentU = some layU →
    layTrees Q.codes (withOmega Q.S) = some layO →
    ∀ (C : CK) (Fr : Frame) (S Cl W : Type) (num : Fmt.TreeSource → ℕ)
      (f pt x2 x3 x4 x5 x6 : Piece C Fr S Cl W) (rest : List (Piece C Fr S Cl W)),
      Tiled f (pt :: x2 :: x3 :: x4 :: x5 :: x6 :: rest) → f.ds = [] →
      (∀ y ∈ [(pt, b1), (x2, b2), (x3, b3), (x4, b4), (x5, b5)],
        Along (RoundIs num) y.2.rounds y.1.ds ∧ y.1.ds.length = y.2.rounds.length) →
      pt.base = f.base ∧ x2.base = f.base ∧ x3.base = f.base + layU.shapes.size ∧
        x5.base = f.base + layU.shapes.size ∧
        x6.base = f.base + layU.shapes.size + layO.shapes.size

end Desc.K14.Law
