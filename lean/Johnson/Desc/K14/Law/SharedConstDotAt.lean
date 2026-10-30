-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SharedConstDotAt.lean: THE PREMISE hdot OF ROW 0's TOPS OF THE
LAST TABLE (Johnson/Flat/Last/RowZeroAtShX.lean: rowZeroOwed_atZ_sh and those beneath it), AT THE
SHARED TABLE's CONSTANT's OWN MEANING Sh.mg A O (Johnson/Desc/K14/Law/SharedConst.lean). Two
theorems.

Why. Row 0's tops end at the shared table's meaning in the form meaningSigS cs G arr smp₂ ms₂
decT₂ MS, MS a letter, and ask of it hdot: the sentence DotEq … at the tops' own letters gives
MS.dot. "Whose MS?": MS := Sh.mg A O ITSELF: the constant's meaning is its own meaningSigS …
(sh_mg_form, Johnson/P5J/L0/LastForms.lean: rfl: the signature's layer laid twice
is laid once).


  Sh.dot_is     the field dot of Sh.mg A O IS the sentence DotEq at the constant's letters (gLaid
                O.Pw O.get · Omega's fixed reader · W's vector at Sh.xW A O, laid by linLayW
                A.Q.codes O.Pw.lin): rfl.
  Sh.hdot_at    **hdot at MS := Sh.mg A O**, get := O.get · mem := Sh.mem A · Q := A.Q · sentU :=
                Sh.sentU A · xW := Sh.xW A O. LEFT: three equations between the two tables'
                letters: hcs (𝔇.cs = A.Q.codes) · harr (𝔇.arr = O.arr) · hPw (𝔇.P13 = O.Pw),
                and hlay, the tops' own.
What is not claimed. That a top's conclusion at 𝔇.cs can be read at A.Q.codes without carrying
smp₂ along hcs (at the composed meaning's closed constant hcs is no rfl). Nothing on soundness.

-/
import Johnson.Flat.Last.RowZeroOmega
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.OnPublicFiles.Last (omLast)
open VerifiableInference.Desc.K13.Law (vecAt)

namespace Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

theorem dot_is (q : P₁) (s : St) (y : Strs) (w : Wit Cells Tok MsgT) :
    (mg A O).dot q s y w =
      DotEq A.Q.par.S.matrixRows A.Q.par.S.kCol (gLaid O.Pw O.get q)
        (omLast O.arr (mem A) A.Q (sentU A) w) (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt (linLayW A.Q.codes O.Pw.lin) ((xW A O).1.l.get (xW A O).2).1
          (wTab A.Q.codes O.arr (xW A O) w)) := rfl

end Sh

/-- **hdot at the shared table's constant's own meaning.** -/
theorem Sh.hdot_at {Xi Xi₀ P₀ P₁ Tok : Type} {rows cols nR : ℕ}
    {X : OnBytes.Model.Verify.Public} (A : ShPlan Xi)
    (O : ShOpen P₀ P₁ (CellsQ rows cols) Tok A.Q) (𝔇 : MgData Xi₀ P₀ Tok rows cols nR X)
    (hcs : 𝔇.cs = A.Q.codes) (harr : 𝔇.arr = O.arr) (hPw : 𝔇.P13 = O.Pw) (lay₀ : VectorLay)
    (hlay : lay₀ = linLayW 𝔇.cs 𝔇.P13.lin) :
    ∀ q (s : St) y w,
      DotEq A.Q.par.S.matrixRows A.Q.par.S.kCol (gLaid 𝔇.P13 O.get q)
        (omLast 𝔇.arr (Sh.mem A) A.Q (Sh.sentU A) w)
        (s.loc.psiSh.map OnBytes.Model.Reading.gl.val)
        (vecAt lay₀ ((Sh.xW A O).1.l.get (Sh.xW A O).2).1 (wTab 𝔇.cs 𝔇.arr (Sh.xW A O) w)) →
      (Sh.mg A O).dot q s y w := by
  intro q s y w h
  rw [hlay, hcs, harr, hPw] at h
  exact h

end Desc.K14.Law
