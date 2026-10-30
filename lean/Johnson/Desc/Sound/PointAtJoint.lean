-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtJoint.lean: the tie at "LIN point" at the sentences that the first joint hands on: the claim on the matrix := all rows on the first chain's table are true (RowsTrue, Johnson/Desc/K13/Law/Letters.lean, through the record's own rows), (Eval) := its WRow (the same file). Two theorems. (Why "no mark": a premise hEL : ∀ p y, Oc p y → EvalLaid … is false at the Oc that is meant, the first chain's whole promise at its last border: a marked record is inside, and a marked record need not have (Eval) laid: a theorem under it is true and empty there.
So "no mark" is spent: the own item unmarked1 stands in the relation behind the block: the step back from (Eval) takes it (PointTie.lean … PointAtK14Closed.lean: one premise in that binder); hEL, hg and hW read "Oc p y → no mark → …"; a twelfth equation hun says what unmarked1 means). A joint build of this folder's files with K13's and K14's files: Johnson/Desc/K13/Law/, Johnson/Desc/K14/Law/.
WHY. PointAtK14All.lean | PointAtK14Codes.lean stand at "the reader laid gives a record D, and … D.row" (the premises hcl | hev of Johnson/Desc/K13/Law/PointStepBack.lean). As a filling of the FIRST table's pileOne that sentence is wrong: pileOne is open one block before (Eval) is laid, where the reader may give nothing. THE CURE: pileOne := RowsTrue
at every border; where the record has (Eval) laid (EvalLaid) the two sentences are one (laidOf_true | laidOf_says, Johnson/Desc/K13/Law/LaidAt.lean). HERE THAT IS SPENT: inside the slot's own condition Oc, AT A RECORD WITHOUT A MARK, the handed record has EvalLaid (hEL): so:
  s4a_joint: the step back from (Eval) (the premise s4a of point_leadsB_closed) AT RowsTrue | WRow: from s4a_all (Johnson/Desc/K13/Law/PointStepBack.lean) at an auxiliary record of meanings and the two lemmas.
  point_leadsB_joint: point_leadsB_codes' conclusion at these two sentences. laid IS NO LETTER: it is the reader with code, laidOf Pw ‹the first chain's record in what was handed› (Johnson/Desc/K13/Law/LaidAt.lean); (hOk) IS EXCHANGED, NOT PAID: it follows (laidOf_ok, the same file) from TWO PREMISES: hEL (inside Oc, at a record without a mark, the handed record has (Eval) laid) · hlin (the first chain's shape of the test on the table is the shared chain's).
THE CLAIM's SENTENCE IS TYPED AT THE FIRST CHAIN's OWN NUMBERS (Pw.lin.matrixRows | Pw.lin.kCol): the reader at the block that joins the pending rows is typed so: one filling then meets its law and this tie without a cast.
AT WHICH BORDERS THESE TWO ARE OPEN, AND WHETHER THEY CAN BE TRUE THERE (asked before typing): claimM: the shared chain's borders 0 and 1: it reads what was handed alone: the first chain's LAST record, whose table holds the one joined row · ev: from border 2 to the last chain's block 0: the same record: where nothing is
laid WRow is true of all words (not false): under Oc, at a record without a mark, it is "(Eval) says its claim".

Limits. As PointAtK14Codes.lean's. hEL IS A PREMISE: at Oc := the first chain's promise at its last border it wants the public item evalLaid FILLED by a test that gives EvalLaid (evalLaidB, Johnson/Desc/K13/Law/Bools.lean, by reading: not joined here). NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtK14Codes
import Johnson.Desc.K13.Law.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy vecAt RowsTrue WRow EvalLaid laidOf laidOf_ok laidOf_true
  laidOf_says)

variable {P₁ P₀ Xi Cells Tok : Type} {F : Frame}

/-- **The step back from (Eval), at the sentences that the first joint hands on.** -/
theorem s4a_joint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat) (get : P₁ → P₀ × First.S)
    (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells) (lay₀ : VectorLay)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT) (P : P14) (b1 : Block St Unit)
    (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N : NumbersS) (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm : PromMeaning St)
    (Oc : P₁ → Strs → Prop) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Unit (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (hTP : Pm.tablePromise = decodesOf (decK P.par err₂ eM rank held))
    (Pw : Where) (hlin : Pw.lin = P.par.S) (matC : Cells → Nat → Nat → GE)
    (hev : Mg.ev = fun p _ w => WRow Pw (get p).2 (wordsOn (stOf p) (tabP p w)))
    (hcl : Mg.claimM = fun p _ w =>
      RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
        (fun w' : Wit Cells Tok MsgT => witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf p) (tabP p w')))
        (get p).2 w)
    (hun : Mg.unmarked1 = fun p => (get p).2.failed = none)
    (hEL : ∀ p y, Oc p y → (get p).2.failed = none → EvalLaid Pw (get p).2)
    (hg : ∀ p y' D, Oc p y' → (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hW : ∀ p y D, Oc p y → (get p).2.failed = none → laidOf Pw (get p).2 = some D → WSits cs arr xW lay₀ stOf tabP p D)
    (htab : ∀ p (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP p w' = tabP p w)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    ∀ a τ b w, onQ₂ N Pm Oc split f (liftedPiece b1 base d ext err :: r) 1 a →
      (liftedPiece b1 base d ext err).ior.red.out a τ = some b → ownItem N Mg .unmarked1 b w →
      ownItem N Mg .ev b w →
      VIs P.par.S (gOf a.1.1) (TabX2 P.par err₂ eM rank (tabOf a.2) a.1.2.loc.key)
        (vecAt lay₀ (xW.1.l.get xW.2).1 (wTab cs arr xW w)) → ownItem N Mg .pinI b w →
      ownItem N Mg .claimM a (extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
        ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (liftedPiece b1 base d ext err :: r) 1).2 a)) w) := by
  intro a τ b w hon hb hU hE hvi hpI
  have hK : b.1.1 = a.1.1 := lifted_handed b1 base d ext err a τ b hb
  have hm : (get a.1.1).2.failed = none := by
    have h : Mg.unmarked1 b.1.1 := hU
    rw [hK, hun] at h
    exact h
  have hL : EvalLaid Pw (get a.1.1).2 := hEL a.1.1 _ hon.2 hm
  have hOk : ∀ p y D, (Oc p y ∧ (get p).2.failed = none) → laidOf Pw (get p).2 = some D → D.Ok P.par.S := by
    intro p y D ho hD
    obtain ⟨D', hD', hok, -⟩ := laidOf_ok (hEL p y ho.1 ho.2)
    rw [hD'] at hD
    obtain rfl := Option.some.inj hD
    rw [← hlin]
    exact hok
  have hE' : Mg.ev b.1.1 (strsOf F b.2) w := hE
  rw [hK, hev] at hE'
  have h2 := s4a_all cs G arr xW smp₂ ms₂ c₀ lay₀ stOf tabP P b1 base d ext err N
    { Mg with
      ev := fun p _ w => ∃ D, laidOf Pw (get p).2 = some D ∧
        OnBytes.Means.Says OnBytes.Model.Reading.gl D.st D.r (wordsOn (stOf p) (tabP p w))
      claimM := fun p _ w => ∃ D, laidOf Pw (get p).2 = some D ∧
        VerifiableInference.Desc.K13.Law.Holds OnBytes.Model.Reading.gl
          (witOf (matBy (nR := P.par.S.matrixRows) P.par.S.kCol (matC w.cells))
            (wordsOn (stOf p) (tabP p w))) D.row }
    Pm (fun p y => Oc p y ∧ (get p).2.failed = none) split f r gOf err₂ eM rank held hTP
    (fun p => laidOf Pw (get p).2) matC rfl rfl hOk (fun p y' D ho => hg p y' D ho.1 ho.2)
    (fun p y D ho => hW p y D ho.1 ho.2) htab hH
    a τ b w ⟨hon.1, hon.2, hm⟩ hb
    (by
      show ∃ D, laidOf Pw (get b.1.1).2 = some D ∧ _
      rw [hK]
      exact (laidOf_says hL _).2 hE')
    hvi hpI
  show Mg.claimM a.1.1 (strsOf F a.2) _
  rw [hcl]
  have key : ∀ L : LinShape, L = P.par.S → ∀ w₀ : Wit Cells Tok MsgT,
      RowsTrue (nR := P.par.S.matrixRows) (k := P.par.S.kCol)
        (fun w' : Wit Cells Tok MsgT => witOf (matBy P.par.S.kCol (matC w'.cells))
          (wordsOn (stOf a.1.1) (tabP a.1.1 w'))) (get a.1.1).2 w₀ →
      RowsTrue (nR := L.matrixRows) (k := L.kCol)
        (fun w' : Wit Cells Tok MsgT => witOf (matBy L.kCol (matC w'.cells))
          (wordsOn (stOf a.1.1) (tabP a.1.1 w'))) (get a.1.1).2 w₀ := by
    intro L hL w₀ h
    subst hL
    exact h
  exact key Pw.lin hlin _ ((laidOf_true hL _ _).1 h2)

/-- **The debt at "LIN point", at the description's piece, at the sentences that the first joint hands on.** -/
theorem point_leadsB_joint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
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
    (Pw : Where) (hlin : Pw.lin = P.par.S) (matC : Cells → Nat → Nat → GE)
    (hev : Mg.ev = fun p _ w => WRow Pw (get p).2 (wordsOn (stOf p) (tabP p w)))
    (hcl : Mg.claimM = fun p _ w =>
      RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
        (fun w' : Wit Cells Tok MsgT => witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf p) (tabP p w')))
        (get p).2 w)
    (hun : Mg.unmarked1 = fun p => (get p).2.failed = none)
    (hEL : ∀ p y, Oc p y → (get p).2.failed = none → EvalLaid Pw (get p).2)
    (hg : ∀ p y' D, Oc p y' → (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hW : ∀ p y D, Oc p y → (get p).2.failed = none → laidOf Pw (get p).2 = some D → WSits cs arr xW lay₀ stOf tabP p D)
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
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) :=
  point_leadsB_closed cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ (vecAt lay₀ (xW.1.l.get xW.2).1) rg omW P b1 b2 b3 b4 b5
    b6 b7 b8 hbl e' base d hd ext err N Mg Pm Oc split f r gOf lo (efIx P.par err₂ eM rank e') err₂ eM rank held ha
    hix hroom
    (fun t rec hc => foldErr_ix (codeOf P.par.S.fold.index.code) (ixOf2 P.par.S.fold err₂ eM rank) e' ha hk hr
      rfl he hle hM hJ t rec hc)
    hpin₁ hpT hTP hS1 hS2 hnU hrR hoU hdt hOc hlo hw hi hxW hsW
    (s4a_joint cs G arr get xW smp₂ ms₂ c₀ lay₀ stOf tabP P b1 base d ext err N Mg Pm Oc split f r gOf err₂ eM rank
      held hTP Pw hlin matC hev hcl hun hEL hg hW htab hH)

end Desc.K14.Law

#print axioms Desc.K14.Law.s4a_joint
#print axioms Desc.K14.Law.point_leadsB_joint
