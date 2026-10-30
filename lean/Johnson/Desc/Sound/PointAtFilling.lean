-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtFilling.lean: THE TIE AT "LIN point": ONE NAMED FILLING OF THE SHARED CHAIN's TABLE's LETTERS, AT WHICH THE ELEVEN EQUATIONS OF LETTERS OF point_leadsB_codes (Johnson/Desc/Sound/PointAtK14Codes.lean) ARE rfl. Two definitions, one theorem. A joint build of this folder's files with
K13's and K14's files (Johnson/Desc/K13/Law/, Johnson/Desc/K14/Law/).

  mgPoint: the items' meanings: meaningSigS (pin, pinT at the guarded decoder decK) with pin₁, nearU, recRow, omU, dot, ev, claimM LAID AS TERMS: the very right sides of the equations that PointAtK14Fill | Closed | All ask. What it leaves of Mg₀: row, unmarked1.
  pmPoint: the promise's meanings: promSigS (noColl, shown, held) with tablePromise := decodesOf decK and shape 1 | 2 := shape1 | shape2 (Johnson/Desc/K14/Law/PointCounts.lean), each with "the record does not yet note o_u". What it leaves of Pm₀: shape at every other border, nothingLeft.
  point_leadsB_at_filling: point_leadsB_codes' conclusion where the table's two records ARE these: the eleven equations are paid by rfl: Lean's word that they can hold TOGETHER.
WHY. Eleven equations on two records' fields could clash (two on one field; a field's type that no term meets): here one record of each sort meets them all. IT IS NO MEMBER OF THE WHOLE: the other premises stand.

Limits. As PointAtK14Codes.lean's. The letters inside the two records (rg, omW, gOf, held, matC, laid, stOf, tabP, get, the samples' readers, the members, the codes, arr, err₂, eM, rank, e') stay letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtK14Codes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending meaningSigS promSigS)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy vecAt)

variable {P₁ A₁ Xi Cells Tok : Type}

/-- **The items' meanings, filled for the tie at "LIN point".** -/
noncomputable def mgPoint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat) (get : P₁ → A₁)
    (smp₁ : A₁ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (lay₀ : VectorLay)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (p : Par) (e' : Nat)
    (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (laid : P₁ → Option EvalAt) (matC : Cells → Nat → Nat → GE)
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  { meaningSigS cs G arr smp₂ ms₂ (decK p err₂ eM rank held) Mg₀ with
    pin₁ := fun j t q y w => pinJT cs G arr smp₁ ms₁ j t (get q) y w
    nearU := fun s y w => NearAt OnBytes.Model.Reading.gl p (uAt p notedU s) (rg w) (colsOf y.cell) e'
    recRow := fun s w => RecAll OnBytes.Model.Reading.gl p (uAt p notedU s) (rg w)
    omU := fun s w => ∀ y < p.S.matrixRows, omW w y =
      ∑ t ∈ Finset.range (2 ^ p.S.kLo),
        eqK ((s.loc.psiSh.take p.S.kLo).map OnBytes.Model.Reading.gl.val) t *
          uOf (uAt p notedU s).loc (rg w) (t + 2 ^ p.S.kLo * y)
    dot := fun q s _ w => DotEq p.S.matrixRows p.S.kCol (gOf q) (omW w)
      (s.loc.psiSh.map OnBytes.Model.Reading.gl.val) (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w))
    ev := fun q _ w => ∃ D, laid q = some D ∧
      OnBytes.Means.Says OnBytes.Model.Reading.gl D.st D.r (wordsOn (stOf q) (tabP q w))
    claimM := fun q _ w => ∃ D, laid q = some D ∧
      VerifiableInference.Desc.K13.Law.Holds OnBytes.Model.Reading.gl
        (witOf (matBy (nR := p.S.matrixRows) p.S.kCol (matC w.cells))
          (wordsOn (stOf q) (tabP q w))) D.row }

/-- **The promise's meanings, filled for the tie at "LIN point".** -/
noncomputable def pmPoint (cs : OnBytes.Codes) (G : FileDescription Xi)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (stOf₂ : St → OnBytes.Statement) (bookOf₂ : St → OnBytes.TreeBook) (Pm₀ : PromMeaning St) :
    PromMeaning St :=
  { promSigS cs G smp₂ ms₂ stOf₂ bookOf₂ Pm₀ with
    tablePromise := decodesOf (decK p err₂ eM rank held)
    shape := fun k s => match k with
      | 1 => shape1 p s && !notedU s
      | 2 => shape2 p s && !notedU s
      | k => Pm₀.shape k s }

variable {F : Frame}

/-- **The debt at "LIN point" at the named filling: the eleven equations of letters are rfl.** -/
theorem point_leadsB_at_filling (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → A₁)
    (smp₁ : A₁ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells) (lay₀ : VectorLay)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (lo : Nat)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    -- SIX CONDITIONS ON NUMBERS MORE, as the statement on codes asks them (its first is ha above)
    (hk : 0 < (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l - 1)
    (hr : (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l ≤
      2 ^ (codeOf P.par.S.fold.index.code).a)
    (he : 0 < e') (hle : e' ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a -
      ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a)
      (2 ^ (codeOf P.par.S.fold.index.code).a -
        ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1) e')
    (laid : P₁ → Option EvalAt) (matC : Cells → Nat → Nat → GE)
    -- THE FILLING: TWO EQUATIONS: the items' and the promise's meanings ARE the two named records
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
    (stOf₂ : St → OnBytes.Statement) (bookOf₂ : St → OnBytes.TreeBook)
    (hMg : Mg = mgPoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ lay₀ stOf tabP rg omW P.par e' gOf err₂ eM rank held laid
      matC Mg₀)
    (hPm : Pm = pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
    (hOc : OcReadsBelow lo Oc) (hlo : lo ≤ base) (hw : N.w.1 < base) (hi : N.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N.w.1 N.w.2)
    -- The step back from (Eval): the letters and ties of Johnson/Desc/K13/Law/PointStepBack.lean
    (hOk : ∀ p y D, Oc p y → laid p = some D → D.Ok P.par.S)
    (hg : ∀ p y' D, Oc p y' → laid p = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hW : ∀ p y D, Oc p y → laid p = some D → WSits cs arr xW lay₀ stOf tabP p D)
    (htab : ∀ p (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP p w' = tabP p w)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    (belowPiece (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ N f (belowPiece b1 base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (belowPiece b1 base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (belowPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
          ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  subst hMg hPm
  exact point_leadsB_codes cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ lay₀ stOf tabP rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl
    e' base d hd ext err N _ _ Oc split f r gOf lo err₂ eM rank held ha hix hroom hk hr he hle hM hJ rfl rfl rfl
    rfl rfl rfl rfl rfl rfl hOc hlo hw hi hxW hsW laid matC rfl rfl hOk hg hW htab hH

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_at_filling
