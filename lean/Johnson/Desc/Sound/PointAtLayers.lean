-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtLayers.lean: THE DEBT AT "LIN point" AT ANY MEANING OF THE FIRST TABLE THAT SAYS, AT FIVE FIELDS, WHAT THE FIRST JOINT SAYS: so that the law is a law AT THE ONE TERM into which the kinds' layers of the first table's filling are composed, whichever layer lays which field. One structure, five theorems.
WHY. point_leadsB_at_ocEnd (Johnson/Desc/Sound/PointAtOcEnd.lean) stands at ONE NAMED TERM, mg1Joint. Other files lay the same fields in a layer of their own (the claim's sentence; evalLaid; "K13.wSits"; and more rows of the door): one owner a field. A law at mg1Joint's term is then a law at a term that nobody composes. HERE Mg₁ IS A LETTER.
  JointSays … Mg₁: FIVE EQUATIONS OF FIELDS: pin (the oracles' layer's pinJT) · pileOne (all rows on the record's table are true at the reader) · wrow (WRow, Johnson/Desc/K13/Law/Letters.lean, at these words) · pub at evalLaid · pub at "K13.wSits".
  jointSays_mg1Joint: mg1Joint meets it (so it is no structure without a member).
  hEL_layers · hW_layers: hEL_at_ocEnd (JointFilling.lean) and hW_at_ocEnd (AtOcEnd.lean) at such an Mg₁; the two tests on the table at Mg₁'s OWN filling of the door.
  point_leadsB_layers: point_leadsB_at_ocEnd's conclusion with Mg₁ in mg1Joint's place.
IS EACH NEW PREMISE PAYABLE? J: at a composed term each of the five is rfl if the layer that lays the field lays this term and no layer above lays it anew · hread (LettersReadBelow): at a term whose decodes | shown | noColl are the oracles' layer's: lettersReadBelow_sig, from one test with code · h2 | h3: tests on the table AT THE COMPOSED TERM's OWN DOOR: TO BE RUN THERE: their like ran true at ANOTHER merge (a run at twins of four kinds' rows with wSitsMore, Johnson/Desc/K13/Law/SitsDoor.lean): that merge has not been held against the door of a composed term.

Limits. As PointAtOcEnd.lean's. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtOcEnd

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
  ocEnd_pub tiedMeaning tiedNumbers OcReadsBelow LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok evalLaidB evalLaidB_iff wSitsItem wSitsB wSitsL
  wSeatB wSitsB_gives witOf matBy RowsTrue WRow)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **What the first joint says, at five fields of the first table's meaning.** -/
structure JointSays (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (stOf₁ : P₀ × First.S → Statement)
    (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT) (Pw : Where) (wSeat : Nat × Nat)
    (matC : Cells → Nat → Nat → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) : Prop where
  pin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w
  pileOne : Mg₁.pileOne = fun a _ w =>
    RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
      (fun w' : Wit Cells Tok MsgT => witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf₁ a) (tabP₁ a w')))
      a.2 w
  wrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w))
  evalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2
  wSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB cs Pw a.2 && wSeatB wSeat a.2)

section
variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ : List Mem) (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
  (Pw : Where) (wSeat : Nat × Nat) (matC : Cells → Nat → Nat → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))

/-- The named filling meets it. -/
theorem jointSays_mg1Joint (decT₁ : CellsOf → P₀ × First.S → Option Cells) :
    JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat matC
      (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) :=
  ⟨rfl, rfl, rfl, pub_evalLaid cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁,
    pub_wSits cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁⟩

variable (J : JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat matC Mg₁)
  (get : P₁ → P₀ × First.S) (N₁ : Numbers) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
include J

/-- hEL at such a meaning. -/
theorem hEL_layers (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) :
    ∀ p y, ocEnd get N₁ Mg₁ links ps p y → (get p).2.failed = none → EvalLaid Pw (get p).2 :=
  fun p y h hm => (evalLaidB_iff Pw _).1
    ((J.evalLaid (get p)).symm.trans (ocEnd_pub get N₁ Mg₁ links ps p y h hm .evalLaid h2))

/-- hW at such a meaning. -/
theorem hW_layers (xW : Mem) (lay₀ : VectorLay) (stOf : P₁ → Statement)
    (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hst : ∀ p, stOf p = (get p).2.st) (hlay : lay₀ = linLayW cs Pw.lin)
    (hbook : ∀ p (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP p w n = w.tab cs sh (arr j t) j t)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = wSeat) :
    ∀ p y D, ocEnd get N₁ Mg₁ links ps p y →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → WSits cs arr xW lay₀ stOf tabP p D := by
  intro p y D h hm hD
  have hb := ocEnd_pub get N₁ Mg₁ links ps p y h hm wSitsItem h3
  rw [J.wSits, Bool.and_eq_true] at hb
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨D', hD', -, hst', hS⟩ := wSitsB_gives hb1
  rw [hD] at hD'
  obtain rfl := Option.some.inj hD'
  have hE : evalLaidB Pw (get p).2 = true := by
    unfold wSitsB wSitsL at hb1
    rw [List.all_cons, Bool.and_eq_true] at hb1
    exact hb1.1
  obtain ⟨D₂, hD₂, -, -, -, l, hl, hw, -, -⟩ := laidOf_ok ((evalLaidB_iff Pw _).1 hE)
  rw [hD] at hD₂
  obtain rfl := Option.some.inj hD₂
  have hplace : (get p).2.book.place[D.w]? = some (wSeat.1, wSeat.2) := by
    unfold wSeatB at hb2
    rw [hl] at hb2
    rw [hw]
    exact of_decide_eq_true (by simpa using hb2)
  have hshape : ((get p).2.st.oracles[D.w]?).map (·.shape) = some (xW.1.l.get xW.2).1 := by
    rw [← hst', ← hsh]
    exact hS.shape
  refine ⟨hst'.trans (hst p).symm, hS.codes, ?_, fun w => ?_, hS.lay.trans hlay.symm, hS.lengths, hsh ▸ hS.code⟩
  · rw [← hst'] at hshape
    obtain ⟨x, hx, hxs⟩ := Option.map_eq_some_iff.1 hshape
    exact ⟨x, hx, hxs⟩
  · rw [hseat]
    exact hbook p w D.w wSeat.1 wSeat.2 _ hplace hshape

end

/-- **The debt at "LIN point", at the seated piece, at any meaning of the first table that says what the joint says.** -/
theorem point_leadsB_layers (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
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
    -- the first table's meaning: five fields are what the joint says; two tests on the table; the letters that the promise reads read below lo
    (J : JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁)
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hlo : lo ≤ base) (hw : N₁.w.1 < base) (hi : N₁.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    -- the filling's letters, each by its make; one equation on the plan
    (hst : ∀ a, stOf₁ a = a.2.st)
    (hbook : ∀ (a : P₀ × First.S) (w : Wit Cells Tok MsgT) n j t sh, a.2.book.place[n]? = some (j, t) →
      (a.2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ a w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁ links ps p y' →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ Mg₁ links ps) split f
        (seatedPiece b1 base d ext err :: r) 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ Mg₁ links ps) split f
        (seatedPiece b1 base d ext err :: r) fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r) 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) :=
  point_leadsB_seated (Cl' := Cl') cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ (linLayW cs Pw.lin) (fun q => stOf₁ (get q))
    (fun q => tabP₁ (get q)) rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl e' base d hd ext err (tiedNumbers N₁ Ns)
    (tiedMeaning get Mg₁
      (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
    (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
    (ocEnd get N₁ Mg₁ links ps) split f r gOf lo err₂ eM rank held ha
    hix hroom hk hr he hle hM hJ
    (by show (fun j t p => Mg₁.pin j t (get p)) = _; rw [J.pin]) rfl rfl rfl rfl rfl rfl rfl rfl
    (ocEndReadsBelow P₁ P₀ _ get lo N₁ Mg₁ links ps hread) hlo hw hi hxW hsW Pw
    hlin matC (by show (fun p => Mg₁.wrow (get p)) = _; rw [J.wrow]) (by show (fun p => Mg₁.pileOne (get p)) = _; rw [J.pileOne]) rfl
    (hEL_layers cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ J get N₁ links ps h2) hg
    (hW_layers cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ J get N₁ links ps xW (linLayW cs Pw.lin)
      (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) h3 (fun p => hst (get p)) rfl
      (fun p w n j t sh => hbook (get p) w n j t sh) hsh hsW)
    (fun p w w' => htab (get p) w w') hH

end Desc.K14.Law

#print axioms Desc.K14.Law.jointSays_mg1Joint
#print axioms Desc.K14.Law.hEL_layers
#print axioms Desc.K14.Law.hW_layers
#print axioms Desc.K14.Law.point_leadsB_layers
