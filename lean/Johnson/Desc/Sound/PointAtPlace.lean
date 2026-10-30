-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtPlace.lean: THE DEBT AT "LIN point" AT THE PIECE THAT THE SEAT's OWN LIST HOLDS AT PLACE 1: the law of Johnson/Desc/Sound/PointAtOcEnd.lean JOINED TO "the pieces hold the shared chain's own blocks as a description lays them" (piece_retype_at, Johnson/Desc/K14/Law/FlatRetype.lean).
One theorem. A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K13/ and K14/.
WHY. A law that speaks of a text which nothing calls counts for nothing. point_leadsB_at_ocEnd speaks of seatedPiece b1 base d ext err in a list f :: seatedPiece … :: r, at letters base, ext, err, r. HERE THE LIST IS A LETTER l, AND WHAT IS KNOWN OF f :: l IS WHAT OfDesc SAYS OF A DESCRIPTION's PIECES (its clause on the shared chain):
their blocks are the flat list of (chainOf c P tests last).retype, each with the test below the prime in front, lifted. THEN: the piece at place 1 IS seatedPiece b1 (its base) d (its extractor) (its errors), and the debt holds OF IT, IN l, at the tables' own terms.
  hps: that clause, to the letter of piece_retype_at's premise (read, not shown here: Lean takes OfDesc's field b₂ for it at the fold's description over the base).
  hdat: THE DATA OF THE PIECE AT PLACE 1: one written round d · no round behind · its base above lo and above W's and the index masks' trees: FACTS ON THE TILING OF THE FILE's ROUNDS: PREMISES: nobody's over the base.
WHAT STAYS OF "it is the description's piece": hdat · that the piece's extractor is the table's (the chain rule's matter).

Limits. As PointAtOcEnd.lean's. NO MEMBER IS SHOWN.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtOcEnd
import Johnson.Desc.K14.Law.FlatRetype

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Chain Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound (Frame Piece below onQ₂ actQ stepPt strsOfAct SitsAt extS MsgT Mem Sending CellsOf
  ocEnd tiedMeaning tiedNumbers sampledBelow)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **The debt at "LIN point", of the piece that the seat's own list holds at place 1.** -/
theorem point_leadsB_at_place (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (e' : Nat)
    (d : RDT) {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (split : Bool)
    (lo : Nat) (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (l : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
    -- THE SEAT: the pieces hold the shared chain's own blocks, as the description lays them: retyped, the test below the prime in front, lifted
    (c : Model.Verify.Chains) (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hps : (f :: l).map (·.b) = (((chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder.map below).map
      (Block.lift Prod.snd fun t s => (t.1, s)))
    -- the data of the piece at place 1: one written round, none behind; its base
    (hdat : ∀ q, (f :: l)[1]? = some q → q.ds = [d] ∧ q.back = [] ∧ lo ≤ q.base ∧ N₁.w.1 < q.base ∧ N₁.index.1 < q.base)
    (gOf : P₁ → Nat → GE)
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
    ∃ (base : Nat) (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))),
      l = seatedPiece b1 base d ext err :: r ∧
      (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ (tiedNumbers N₁ Ns) f l 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁)
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f
        l fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f l 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f l 1).2 a)) w)
      ((vecMaps d P.par.S.kCol).err ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  obtain ⟨q, hq, hqb⟩ := piece_retype_at (f :: l) c P b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl hps 0 b1 rfl
  obtain ⟨hds, hback, hlo, hw, hi⟩ := hdat q hq
  cases l with
  | nil => cases hq
  | cons q' r =>
    have e : q' = q := Option.some.inj hq
    subst e
    obtain ⟨b0, base, ds, back, ext, err⟩ := q'
    simp only at hqb hds hback hlo hw hi
    subst hqb hds hback
    exact ⟨base, ext, err, r, rfl,
      point_leadsB_at_ocEnd cs G arr get smp₁ ms₁ xW decT₁ smp₂ ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl
        e' base d hd ext err N₁ Ns links ps split f r gOf lo err₂ eM rank held Pw hlin matC Mg₁ Mg₀ Pm₀ stOf₂ bookOf₂
        ha hix hroom hk hr he hle hM hJ h2 h3 hbelow hlo hw hi hxW hsW hst hbook htab hsh hg hH⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_at_place
