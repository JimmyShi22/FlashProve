-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtK14All.lean: THE TIE AT "LIN point": point_leadsB_closed (Johnson/Desc/Sound/PointAtK14Closed.lean) WITH THE STEP BACK FROM (Eval) AND THE TIE OF THE VECTOR LAID IN (s4a_all, Johnson/Desc/K13/Law/PointStepBack.lean). One theorem: ONE CALL.
(hg) is fenced by the slot's own condition too, as in PointStepBack.lean. (Why s4a_all and not s4a_paid (PointStepBack.lean) at one rg for all statements: there s4a_paid's ev, claimM and the tie of the vector cannot hold together at the filling that is meant: true and empty there. Here the words of the first chain's statement read what was handed:
wordsOn (stOf p) (tabP p w); the shared chain's own words stay the letter rg: TWO NUMBERINGS, TWO READERS). A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K13/ and K14/.

  point_leadsB_all: the debt at the shared chain's block 1, at the piece that a description holds, the two lists of errors named; vec IS A TERM: vecAt lay₀ ‹W's member's shape›: the table's entry at row = the layout's index's low bits, place = its high bits.
**WHAT STAYS WITH WEIGHT: hbad: THE STATEMENT ON CODES** (its payer named, the call owed). s4a AND hvec ARE EXCHANGED, NOT PAID: (hOk, hg, hW STAND UNFENCED HERE, "for all p inside Oc": PAYABLE BECAUSE laid IS A LETTER HERE: it may give nothing at a marked record or at one over other codes; where laid is code: PointAtJoint.lean, AtOcEnd.lean) for **hW: inside the slot's own condition W SITS AS THE PLAN SAYS: seven public facts on the handed record against the plan (WSits): no member is shown; six are tests with
code, none run** · hOk · hg · htab (the tables read a witness's messages and pads alone) · hH ("held": two members are theorems of Johnson/Desc/K13/Law/HeldTab.lean) · two equations of letters (ev, claimM). BESIDE: what PointAtK14Closed.lean names.

Limits. As PointAtK14Closed.lean's. NO MEMBER IS SHOWN: no values of all letters are made at which every premise holds: a theorem under premises at free letters can be idle.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.PointStepBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy vecAt)

variable {P₁ A₁ Xi Cells Tok : Type} {F : Frame}

/-- **The debt at "LIN point", at the description's piece, with the step back from (Eval) and the tie of the vector laid in.** -/
theorem point_leadsB_all (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (gOf : P₁ → Nat → GE) (lo ef : Nat)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    -- THE STATEMENT ON CODES
    (hbad : ∀ t rec, ¬ (ixOf2 P.par.S.fold err₂ eM rank).Coll t rec.1 →
      cnt ((ixOf2 P.par.S.fold err₂ eM rank).Bad t rec e') ≤ ef)
    -- the filling
    (hpin₁ : Mg.pin₁ = fun j t q y w => pinJT cs G arr smp₁ ms₁ j t (get q) y w)
    (hpT : Mg.pinT = pinWOf (decK P.par err₂ eM rank held))
    (hTP : Pm.tablePromise = decodesOf (decK P.par err₂ eM rank held))
    (hS1 : Pm.shape 1 = fun s => shape1 P.par s && !notedU s)
    (hS2 : Pm.shape 2 = fun s => shape2 P.par s && !notedU s)
    (hnU : Mg.nearU = fun s y w =>
      NearAt OnBytes.Model.Reading.gl P.par (uAt P.par notedU s) (rg w) (colsOf y.cell) e')
    (hrR : Mg.recRow = fun s w => RecAll OnBytes.Model.Reading.gl P.par (uAt P.par notedU s) (rg w))
    (hoU : Mg.omU = fun s w => ∀ y < P.par.S.matrixRows, omW w y =
      ∑ t ∈ Finset.range (2 ^ P.par.S.kLo),
        eqK ((s.loc.psiSh.take P.par.S.kLo).map OnBytes.Model.Reading.gl.val) t *
          uOf (uAt P.par notedU s).loc (rg w) (t + 2 ^ P.par.S.kLo * y))
    (hdt : Mg.dot = fun p s _ w => DotEq P.par.S.matrixRows P.par.S.kCol (gOf p) (omW w)
      (s.loc.psiSh.map OnBytes.Model.Reading.gl.val) (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)))
    (hOc : OcReadsBelow lo Oc) (hlo : lo ≤ base) (hw : N.w.1 < base) (hi : N.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N.w.1 N.w.2)
    -- The step back from (Eval): the letters and ties of Johnson/Desc/K13/Law/PointStepBack.lean
    (laid : P₁ → Option EvalAt) (matC : Cells → Nat → Nat → GE)
    (hev : Mg.ev = fun p _ w => ∃ D, laid p = some D ∧
      OnBytes.Means.Says OnBytes.Model.Reading.gl D.st D.r (wordsOn (stOf p) (tabP p w)))
    (hcl : Mg.claimM = fun p _ w => ∃ D, laid p = some D ∧
      VerifiableInference.Desc.K13.Law.Holds OnBytes.Model.Reading.gl
        (witOf (matBy (nR := P.par.S.matrixRows) P.par.S.kCol (matC w.cells))
          (wordsOn (stOf p) (tabP p w))) D.row)
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
      ((vecMaps d P.par.S.kCol).err ((ef * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) :=
  point_leadsB_closed cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ (vecAt lay₀ (xW.1.l.get xW.2).1) rg omW P b1 b2 b3 b4 b5
    b6 b7 b8 hbl e' base d hd ext err N Mg Pm Oc split f r gOf lo ef err₂ eM rank held ha hix hroom hbad hpin₁ hpT
    hTP hS1 hS2 hnU hrR hoU hdt hOc hlo hw hi hxW hsW
    (fun a τ b w hon hb _ hE hvi hpI =>
      s4a_all cs G arr xW smp₂ ms₂ c₀ lay₀ stOf tabP P b1 base d ext err N Mg Pm Oc split f r gOf err₂ eM rank held
      hTP laid matC hev hcl hOk hg hW htab hH a τ b w hon hb hE hvi hpI)

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_all
