-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerSentBeforeOwed.lean: ONE STATEMENT THAT IS OWED FOR K14's LAW, AS A
PROPOSITION BY def: NO PROOF HERE. The laws of the shared chain's two proximity tests (blocks 9 and
10) ask that the trees of o_u, o_omega and o_sp are sent in front of them (SentBefore,
Johnson/Desc/Sound/LedgerRides.lean). sb_sh (Johnson/Desc/Sound/SeamTreesSh.lean)
has it from the bases of the row's pieces number 3 and 6; BasesOwed
(Johnson/Desc/K14/Law/LedgerBasesOwed.lean) has these two bases at every plan. OWED: the join, in
the form in which the two tests' laws ask it.

  SentBeforeOwed   in a tiled row whose first piece has no round and stands at lo, and whose next
                   five go along the kind's first five blocks: SentBefore of all three messages at
                   every piece from number 6 on
What is not claimed. That it holds.
(It is proved in Johnson/Desc/K14/Law/LedgerSentBefore.lean: sentBefore.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerBasesOwed
import Johnson.Desc.Sound.SeamTreesSh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence (tenantSh)
open _root_.Run.PQ (CK)

/-- OWED: the three messages' trees are sent in front of every piece from number 6 on. -/
def SentBeforeOwed : Prop :=
  ∀ (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (sentU : Array OracleNotice)
    (layU layO : TreeLay), blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] →
    withU Q.S = some sentU → layTrees Q.codes sentU = some layU →
    layTrees Q.codes (withOmega Q.S) = some layO → 0 < sentU.size → 1 < (withOmega Q.S).size →
    ∀ (C : CK) (Fr : Frame) (P₁ S₂ Cl Cells Tok : Type) (num : Fmt.TreeSource → ℕ) (N : NumbersS)
      (f pt x2 x3 x4 x5 x6 : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
      (rest : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))),
      N.tenant = tenantSh f.base layU layO → N.lo = f.base →
      Tiled f (pt :: x2 :: x3 :: x4 :: x5 :: x6 :: rest) → f.ds = [] →
      (∀ y ∈ [(pt, b1), (x2, b2), (x3, b3), (x4, b4), (x5, b5)],
        Along (RoundIs num) y.2.rounds y.1.ds ∧ y.1.ds.length = y.2.rounds.length) →
      ∀ (k : ℕ) (x : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)), 6 ≤ k →
        (f :: pt :: x2 :: x3 :: x4 :: x5 :: x6 :: rest)[k]? = some x → ∀ m : Msg2,
        SentBefore N f (pt :: x2 :: x3 :: x4 :: x5 :: x6 :: rest) k x m

end Desc.K14.Law
