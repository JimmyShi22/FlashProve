-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ShJointWithin.lean (it imports
Johnson/Desc/AtSeats/HpileAt9.lean): ALL SIX FIELDS OF Sh.Joint A O
(Johnson/Desc/K14/Law/SharedConstJoint.lean) AT THE FIRST TABLE's COMPOSED MEANING mgAll 𝔇 Mg.
One theorem: a joining.

  Sh.joint_mgAll_within  Sh.joint_mgAll (Johnson/Desc/K14/Law/SharedConstJointAt.lean) with hpile
                         by hpile_at9. LEFT: the eight equations on letters
                         (hMg · hcs · hG · harr · hsmp · hms · hPw · hw) · hn
                         (𝔇.P13.lin.matrixRows = nR) · hmat (𝔇.mat13 c = matBy kCol (O.matC c))
                         · hW: at what O.R holds of, not failed, the test pileWithinC accepts
                         ("every ledger fits; no pending row names a mask entry at or beyond its
                         table's size").
What is not claimed. hW at the R meant (ReachBelow.lean has it of reached states of the first chain,
from the description's return and its test on the public parameters: not joined here: O.R is a
letter). That the ten equations hold at the two tables' closed terms. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstJointAt
import Johnson.Desc.AtSeats.HpileAt9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData CellsQ mgAll)
open VerifiableInference.Desc.K13.Law (matBy)

/-- **Sh.Joint at the composed meaning, its field pile paid too.** -/
theorem Sh.joint_mgAll_within {Xi P₀ P₁ Tok : Type} {rows cols nR : ℕ}
    {X : OnBytes.Model.Verify.Public} (A : ShPlan Xi)
    (O : ShOpen P₀ P₁ (CellsQ rows cols) Tok A.Q) (𝔇 : MgData Xi P₀ Tok rows cols nR X)
    (Mg : Meaning P₀ (Wit (CellsQ rows cols) Tok MsgT))
    (hMg : mgAll 𝔇 Mg = O.Mg₁) (hcs : 𝔇.cs = A.Q.codes) (hG : 𝔇.G = A.G) (harr : 𝔇.arr = O.arr)
    (hsmp : HEq 𝔇.smp O.smp₁) (hms : 𝔇.ms = O.ms₁) (hPw : 𝔇.P13 = O.Pw) (hw : 𝔇.N.w = O.N₁.w)
    (hn : 𝔇.P13.lin.matrixRows = nR)
    (hmat : ∀ c, 𝔇.mat13 c = matBy 𝔇.P13.lin.kCol (O.matC c))
    (hW : ∀ p, O.R p → (O.get p).2.failed = none →
      VerifiableInference.Desc.K13.pileWithinC (O.get p).2 = true) :
    Sh.Joint A O :=
  Sh.joint_mgAll A O 𝔇 Mg hMg hcs hG harr hsmp hms hPw hw fun p y w _ hR hm hs => by
    refine HashBuild.hpile_at9 𝔇 Mg O.matC hn hmat O.get O.R hW p y w hR hm ?_
    rw [hPw, harr]
    exact hs

end Desc.K14.Law
