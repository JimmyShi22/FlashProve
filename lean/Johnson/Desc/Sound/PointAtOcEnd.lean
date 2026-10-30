-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtOcEnd.lean: THE DEBT AT "LIN point", ONE STATEMENT AT THE TABLES' OWN TERMS: at the seated piece (Johnson/Desc/Sound/PointSeated.lean), for every type of claims, WITH THE FOUR LETTERS OF THE SHARED TABLE LAID AS placesAll LAYS THEM (Johnson/Desc/Sound/TablesGlued.lean): the numbers tiedNumbers N₁ Ns ·
the items' meanings tiedMeaning get (mg1Joint …) (mgJoint …) · the promise's meanings pmPoint … · THE SLOT's OWN CONDITION ocEnd get N₁ (mg1Joint …) links ps: THE FIRST CHAIN's WHOLE PROMISE AT ITS LAST BORDER. One theorem. A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K13/ and K14/.
WHAT HAS GONE FROM THE PREMISES OF point_leadsB_seated: the twelve equations of letters (rfl) · hOc (hOc_at_ocEnd: from a test with code on the first table's numbers) · hEL (hEL_at_ocEnd) · hW (hW_at_ocEnd): Johnson/Desc/Sound/JointFilling.lean, AtOcEnd.lean. SO NO PREMISE SPEAKS "FOR ALL p INSIDE Oc" ANY MORE BUT hg.
WHAT STANDS IN THEIR PLACE: THREE TESTS ON THE FIRST TABLE (h2: evalLaid, h3: "K13.wSits" are among the public items at the last border, at the merged filling of the door; hbelow: the sampled tenants' trees lie below lo) · THREE CONDITIONS ON THE FILLING's LETTERS, EACH BY THE MAKE OF A LETTER (hst · hbook · htab; a reader that meets
hbook and htab: tabByBook) · ONE EQUATION ON THE PLAN (hsh: W's member's shape is the linear claim's shape for W); W's seat is the first table's own N₁.w (hsW); the layout is linLayW cs Pw.lin by make.
WHAT STAYS: hbl · hd · hix (the index's own test) · hroom (the matrix has room in the index's plain rows): both follow from a yes of b1 by plan_at_yes (a name that this library does not hold), which is not spent here · the conditions on numbers of the statement on codes · hlo | hw | hi · hxW | hsW · hlin · hg (inside Oc, without a mark: gOf is the sum of the record's row's weights: BY THE MAKE OF gOf) · hH (HeldTie). e' · eM · err₂ · rank ARE FREE LETTERS HERE: at the last radius inside hJ the key's list of errors exceeds all challenges: THE LAW IS TRUE AND HOLLOW THERE: the radius is laid in PointAtCap.lean | PointLayersAtCap.lean. The piece's own err stands in no clause.
IS EACH PREMISE PAYABLE AT THE MEANT LETTERS? AtOcEnd.lean's head, and: hg: at gOf := gLaid Pw get it holds at every handed record (gLaid_is, AtOcEnd.lean) · hH: at the full size's own held: it is through Lean (heldTie_full, Johnson/Desc/Sound/HeldAlong.lean).

Limits. As PointAtJoint.lean's and AtOcEnd.lean's. IT IS A LAW OF ONE BLOCK UNDER PREMISES; the promise that it spends must be MADE by the first chain's blocks: their laws are other files' to show. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointSeated
import Johnson.Desc.Sound.AtOcEnd

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
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ actQ stepPt strsOfAct SitsAt extS MsgT Mem Sending CellsOf ocEnd
  tiedMeaning tiedNumbers sampledBelow)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **The debt at "LIN point", at the seated piece, at the tables' own terms.** -/
theorem point_leadsB_at_ocEnd (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (base : Nat) (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (split : Bool)
    (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE) (lo : Nat)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (Pw : Where) (hlin : Pw.lin = P.par.S) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
    (stOf₂ : St → OnBytes.Statement) (bookOf₂ : St → OnBytes.TreeBook)
    (ha : P.par.S.fold.index.code.logN ≤ 32) (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : 0 < (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l - 1)
    (hr : (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l ≤
      2 ^ (codeOf P.par.S.fold.index.code).a)
    (he : 0 < e') (hle : e' ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a -
      ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a)
      (2 ^ (codeOf P.par.S.fold.index.code).a -
        ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1) e')
    -- three tests on the first table
    (h2 : Pub.evalLaid ∈ (pubSets (Mg₁.more.merge wSitsMore) links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets (Mg₁.more.merge wSitsMore) links ps)[ps.length]?.getD [])
    (hbelow : sampledBelow lo N₁ ((openSets links ps (start links))[ps.length]?.getD []) = true)
    (hlo : lo ≤ base) (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    -- the filling's letters, each by its make; one equation on the plan
    (hst : ∀ a, stOf₁ a = a.2.st)
    (hbook : ∀ (a : P₀ × First.S) (w : Wit Cells Tok MsgT) n j t sh, a.2.book.place[n]? = some (j, t) →
      (a.2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ a w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps p y' →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f
        (seatedPiece b1 base d ext err :: r) 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁)
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f
        (seatedPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) :=
  point_leadsB_seated (Cl' := Cl') cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ (linLayW cs Pw.lin) (fun q => stOf₁ (get q))
    (fun q => tabP₁ (get q)) rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl e' base d hd ext err (tiedNumbers N₁ Ns)
    (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀)
    (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
    (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f r gOf lo err₂ eM rank held ha
    hix hroom hk hr he hle hM hJ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hOc_at_ocEnd cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ get N₁ links ps lo hbelow) hlo hw hi hxW hsW Pw
    hlin matC rfl rfl rfl
    (hEL_at_ocEnd cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ get N₁ links ps h2) hg
    (hW_at_ocEnd cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ get N₁ links ps xW (linLayW cs Pw.lin)
      (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) h3 (fun p => hst (get p)) rfl
      (fun p w n j t sh => hbook (get p) w n j t sh) hsh hsW)
    (fun p w w' => htab (get p) w w') hH

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_at_ocEnd
