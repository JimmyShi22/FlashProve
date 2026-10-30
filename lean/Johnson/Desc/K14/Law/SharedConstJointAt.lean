-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SharedConstJointAt.lean: WHAT THE SHARED TABLE's CONSTANT ASKS OF THE FIRST
TABLE's OWN MEANING AT THE JOINT (Sh.Joint, Johnson/Desc/K14/Law/SharedConstJoint.lean), AT THE
FIRST TABLE's COMPOSED MEANING mgAll 𝔇 Mg (Johnson/Desc/Sound/MgAll.lean).
Three theorems.

OBJECT   the six fields of Sh.Joint A O.
USER     the premise hJ : Sh.Joint A O of the shared table's constant's tops. Nobody calls it.

  jointFour_cast   JointFour (Johnson/Flat/Last/JointFour.lean) goes over equal letters; the
                   reader of OOD samples is typed over the codes, so its equation is one between
                   types that are equal by the codes' equation (HEq).
  Sh.joint_of_four Sh.Joint from JointFour at the constant's letters, with pile and po: the
                   constant's stOf₁ | tabP₁ are JointFour's two readers by unfolding.
  Sh.joint_mgAll   **Sh.Joint A O where O.Mg₁ = mgAll 𝔇 Mg** and seven letters of the constant
                   are 𝔇's: pin · wrow · evalLaid · wSits by jointFour_mgAll
                   (Johnson/Flat/Last/RowZeroAtMgAll.lean) · po BY THE MAKE: mgAll's pileOne reads
                   no oracle's string. LEFT: the eight equations on letters (hMg · hcs · hG · harr
                   · hsmp · hms · hPw · hw) and hpile: Sh.Joint.pile's own text at mgAll 𝔇 Mg.
What is not claimed. hpile (paid, under a test on the state at what O.R holds of, in
Johnson/Desc/AtSeats/ShJointWithin.lean). That the eight equations hold at the closed terms for 𝔇 and for A, O.
Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstJoint
import Johnson.Flat.Last.RowZeroAtMgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.Sound (MsgT Mem Sending ocEnd MgData CellsQ mgAll stFirst tabFirst)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.OnPublicFiles.Last (jointFour_mgAll)

/-- JointFour goes over equal letters. -/
theorem jointFour_cast {P₀ Xi Cells Tok : Type} {c c' : OnBytes.Codes} (hc : c = c')
    {G G' : FileDescription Xi} (hG : G = G') {arr arr' : ℕ → ℕ → ℕ} (ha : arr = arr')
    {s : P₀ × First.S → (x : Sending) → (i : Fin x.l.length) → Option ((sigOf c x.l).om i).Smp}
    {s' : P₀ × First.S → (x : Sending) → (i : Fin x.l.length) → Option ((sigOf c' x.l).om i).Smp}
    (hs : HEq s s') {ms ms' : List Mem} (hm : ms = ms') {Pw Pw' : Where} (hP : Pw = Pw')
    {u u' : ℕ × ℕ} (hu : u = u') {M M' : Meaning P₀ (Wit Cells Tok MsgT)} (hM : M = M')
    (J : JointFour c G arr s ms stFirst (tabFirst arr) Pw u M) :
    JointFour c' G' arr' s' ms' stFirst (tabFirst arr') Pw' u' M' := by
  subst hc hG ha hm hP hu hM
  cases hs
  exact J

namespace Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- Sh.Joint from JointFour at the constant's letters. -/
theorem joint_of_four
    (J : JointFour A.Q.codes A.G O.arr O.smp₁ O.ms₁ stOf₁ (tabP₁ A O) O.Pw O.N₁.w O.Mg₁)
    (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd O.get O.N₁ O.Mg₁ O.links (ps A O) p y → O.R p →
      (O.get p).2.failed = none → pileStep stOf₁ (tabP₁ A O) O.Pw O.matC (O.get p) w →
      O.Mg₁.pileOne (O.get p) y w)
    (hpo : ∀ a (y y' : Strs) (w : Wit Cells Tok MsgT), O.Mg₁.pileOne a y w → O.Mg₁.pileOne a y' w) :
    Joint A O :=
  ⟨J.pin, J.wrow, J.evalLaid, J.wSits, hpile, hpo⟩

end Sh

/-- **Sh.Joint at the composed meaning.** -/
theorem Sh.joint_mgAll {Xi P₀ P₁ Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
    (A : ShPlan Xi) (O : ShOpen P₀ P₁ (CellsQ rows cols) Tok A.Q)
    (𝔇 : MgData Xi P₀ Tok rows cols nR X) (Mg : Meaning P₀ (Wit (CellsQ rows cols) Tok MsgT))
    (hMg : mgAll 𝔇 Mg = O.Mg₁) (hcs : 𝔇.cs = A.Q.codes) (hG : 𝔇.G = A.G) (harr : 𝔇.arr = O.arr)
    (hsmp : HEq 𝔇.smp O.smp₁) (hms : 𝔇.ms = O.ms₁) (hPw : 𝔇.P13 = O.Pw) (hw : 𝔇.N.w = O.N₁.w)
    (hpile : ∀ p y (w : Wit (CellsQ rows cols) Tok MsgT),
      ocEnd O.get O.N₁ (mgAll 𝔇 Mg) O.links (Sh.ps A O) p y → O.R p →
      (O.get p).2.failed = none → pileStep Sh.stOf₁ (Sh.tabP₁ A O) O.Pw O.matC (O.get p) w →
      (mgAll 𝔇 Mg).pileOne (O.get p) y w) :
    Sh.Joint A O :=
  Sh.joint_of_four A O
    (jointFour_cast hcs hG harr hsmp hms hPw hw hMg (jointFour_mgAll 𝔇 Mg))
    (hMg ▸ hpile) (hMg ▸ fun _ _ _ _ h => h)

end Desc.K14.Law
