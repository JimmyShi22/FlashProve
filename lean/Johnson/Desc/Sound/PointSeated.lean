-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointSeated.lean: the tie at "LIN point" at the piece that is seated over Johnson/Desc/Block.lean: the law moves along Block.retype. Two definitions, seven theorems. (The last theorem hands on PointAtJoint.lean's hEL, hg, hW under "no mark": without it hEL is false at the slot's own condition that is meant (a marked record is inside it), and a theorem under it true and empty there.) A joint build of K13's and K14's files.
Why. In Block.lean the fold's type of claims is not Unit, and the shared chain is laid by Chain.retype (Johnson/Desc/Block.lean): the block that is seated at the shared chain's place 1 is b1.retype (piece_at_the_fold, a name that is declared nowhere in this library). belowPiece (Johnson/Desc/Sound/PointBelow.lean) and every theorem
from point_leadsB_typed to point_leadsB_joint stand at Unit: AT A PIECE THAT IS NOT THE SEATED ONE. HERE THE STEP THAT LACKED:
  Piece.un: a piece at any type of claims, as a piece at Unit: its block retyped; its base, rounds' data, rounds behind, extractor and errors as they are.
  seatedPiece b base d ext err: the piece whose block is (below b.retype).lift …, at any type of claims Cl'.
  seated_ior: its reduction IS belowPiece's (a piece's run reads its block's name, rounds and decide alone; retype keeps these to the letter): rfl · acts_seated | on_seated | step_seated: the tables' acting part, promise and step at a list of pieces and at the list of their twins at Unit are one.
  piece_is_seated: a piece whose block is (below b.retype).lift …, whose rounds are [d] and behind which no round is laid IS seatedPiece b (its base) d ext err for some ext, err: what piece_at_the_fold is joined to.
  leadsB_at_seated: the debt at the seated piece, in the seated list, from the debt at belowPiece in the list of twins · point_leadsB_seated: point_leadsB_joint's conclusion AT THE SEATED PIECE, for every type of claims.
WHAT STAYS OF "it is the description's piece": that the real piece at place 1 is seatedPiece b1 … (its block: piece_at_the_fold; one written round; no round behind) and that its extractor is the table's.

Limits. As PointAtJoint.lean's. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtJoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending below)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy vecAt RowsTrue WRow EvalLaid laidOf)

/-- A piece at any type of claims, as a piece at Unit. -/
def unP {C : CK} {F : Frame} {S Cl W : Type} (x : Piece C F S Cl W) : Piece C F S Unit W :=
  ⟨x.b.retype, x.base, x.ds, x.back, x.ext, x.err⟩

variable {W P₁ Cl' : Type} {F : Frame}

/-- The piece that is seated at the shared chain's place over Block's ninth: the block retyped, with the test below the prime in front, lifted. -/
def seatedPiece (b : Block St Unit) (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W)
    (err : Err (uLT (ckP .two) [d])) : Piece (ckP .two) F (P₁ × St) Cl' W :=
  ⟨(below (b.retype (Cl' := Cl'))).lift Prod.snd fun t s => (t.1, s), base, [d], [], ext, err⟩

section
variable (b : Block St Unit) (base : Nat) (d : RDT)
  (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) (err : Err (uLT (ckP .two) [d]))
  (N : NumbersS) (Mg : MeaningS St P₁ W) (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
  (f : Piece (ckP .two) F (P₁ × St) Cl' W) (r : List (Piece (ckP .two) F (P₁ × St) Cl' W))

/-- **The seated piece's reduction is belowPiece's.** -/
theorem seated_ior :
    (seatedPiece (Cl' := Cl') (W := W) (F := F) (P₁ := P₁) b base d ext err).ior =
      (belowPiece (W := W) (F := F) (P₁ := P₁) b base d ext err).ior := rfl

/-- The acting parts in front of the block, at the seated list and at the list of twins, are one. -/
theorem acts_seated :
    actQ N f (seatedPiece b base d ext err :: r) 1 = actQ N (unP f) (belowPiece b base d ext err :: r.map unP) 1 :=
  rfl

/-- So are the promises in front of it. -/
theorem on_seated :
    onQ₂ N Pm Oc split f (seatedPiece b base d ext err :: r) 1 =
      onQ₂ N Pm Oc split (unP f) (belowPiece b base d ext err :: r.map unP) 1 := rfl

/-- So is the relation that is owed. -/
theorem step_seated (E : (P₁ × St) × F.E.Str → W → W) :
    stepPt N Mg Pm Oc split f (seatedPiece b base d ext err :: r) E =
      stepPt N Mg Pm Oc split (unP f) (belowPiece b base d ext err :: r.map unP) E := by
  cases r <;> rfl

/-- **The debt at the seated piece, in the seated list, from the debt at belowPiece in the list of twins.** -/
theorem leadsB_at_seated (E : (P₁ × St) × F.E.Str → W → W) (εK εO : Err (uLT (ckP .two) [d]))
    (g : (belowPiece (W := W) (F := F) (P₁ := P₁) b base d ext err).ior.red.LeadsB
      (actQ N (unP f) (belowPiece b base d ext err :: r.map unP) 1).2
      (onQ₂ N Pm Oc split (unP f) (belowPiece b base d ext err :: r.map unP) 1)
      (stepPt N Mg Pm Oc split (unP f) (belowPiece b base d ext err :: r.map unP) E) εK εO) :
    (seatedPiece (Cl' := Cl') (W := W) (F := F) (P₁ := P₁) b base d ext err).ior.red.LeadsB
      (actQ N f (seatedPiece b base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (seatedPiece b base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (seatedPiece b base d ext err :: r) E) εK εO := by
  rw [step_seated]
  exact g

end

/-- A piece with that block, one written round and no round behind is seatedPiece. -/
theorem piece_is_seated (b : Block St Unit) (d : RDT) (pt : Piece (ckP .two) F (P₁ × St) Cl' W)
    (hb : pt.b = (below (b.retype (Cl' := Cl'))).lift Prod.snd fun t s => (t.1, s)) (hds : pt.ds = [d])
    (hback : pt.back = []) :
    ∃ (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) (err : Err (uLT (ckP .two) [d])),
      pt = seatedPiece b pt.base d ext err := by
  obtain ⟨b0, base, ds, back, ext, err⟩ := pt
  simp only at hb hds hback
  subst hb hds hback
  exact ⟨ext, err, rfl⟩

variable {P₀ Xi Cells Tok : Type}

/-- **The debt at "LIN point" AT THE SEATED PIECE, for every type of claims.** -/
theorem point_leadsB_seated (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
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
    (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ N f (seatedPiece b1 base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (seatedPiece b1 base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (seatedPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ N split 1
          ((actQ N f (seatedPiece b1 base d ext err :: r) 1).2 a).1 (strsOfAct F ((actQ N f (seatedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) :=
  leadsB_at_seated b1 base d ext err N Mg Pm Oc split f r _ _ _
    (point_leadsB_joint cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ lay₀ stOf tabP rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl e'
      base d hd ext err N Mg Pm Oc split (unP f) (r.map unP) gOf lo err₂ eM rank held ha hix hroom hk hr he hle hM
      hJ hpin₁ hpT hTP hS1 hS2 hnU hrR hoU hdt hOc hlo hw hi hxW hsW Pw hlin matC hev hcl hun hEL hg hW htab hH)

end Desc.K14.Law

#print axioms Desc.K14.Law.seated_ior
#print axioms Desc.K14.Law.acts_seated
#print axioms Desc.K14.Law.on_seated
#print axioms Desc.K14.Law.step_seated
#print axioms Desc.K14.Law.leadsB_at_seated
#print axioms Desc.K14.Law.piece_is_seated
#print axioms Desc.K14.Law.point_leadsB_seated
