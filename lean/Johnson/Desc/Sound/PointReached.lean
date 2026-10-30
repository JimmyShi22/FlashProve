-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointReached.lean: THE LAW AT "LIN point" WITH ONE LETTER MORE BESIDE THE FIRST CHAIN's LAST PROMISE: A FACT R ON WHAT WAS HANDED TO THE SHARED CHAIN (meant: "the first chain's last state is reached"). Two definitions' worth of small lemmas and four theorems. A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K13/ and K14/.
WORDS. "The verifier's state": the value that the verifier carries between two sub-protocols. "Promise": the condition on the state and the oracles under which a sub-protocol's law is asked.
WHY. In the tables as planned, the public items which ride the whole first chain leave its promise: their facts come from "reached" instead, by one induction along the verifier's fold. Some of them are spent BEYOND the chain, through the first chain's last promise (ocEnd): here: "the tree at the place z of the book bears the number z" and "every message has a place at a tree that is there", which pay the premise hbook at the reader of words wordsFirst (Johnson/Desc/Sound/WordsAt.lean). So the joint must carry "reached" beside ocEnd.
  ocWith Oc R := fun p y => Oc p y ∧ R p: R READS NO ORACLE, AND WHAT WAS HANDED TO THE CHAIN STAYS: so it costs nothing to carry: ocWith_readsBelow · ocWith_rides.
  hW_reached · point_leadsB_reached · point_leadsB_place_reached · point_leadsBN_cap_reached: the four of Johnson/Desc/Sound/PointFenced.lean, word for word, but that (1) the slot's own condition is ocWith (ocEnd …) R in the promise in front AND behind · (2) hbook is asked under R too: A WEAKER PREMISE.
At R := fun _ => True they are the fenced four's like.

Limits. As PointFenced.lean's. R is a letter: nothing says what it is. ONE SUB-PROTOCOL's CLAUSE, UNDER PREMISES. NO MEMBER IS SHOWN. It rests, through the count of the key's lost points, on the files under ThirdParty/ (lean/LIMITS.md, L15).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointFenced

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
  ocEnd ocEnd_pub tiedMeaning tiedNumbers LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt EvalLaid laidOf laidOf_ok evalLaidB evalLaidB_iff wSitsItem wSitsB wSitsL
  wSeatB wSitsB_gives witOf matBy RowsTrue WRow)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **The slot's own condition with a fact on what was handed beside it.** -/
def ocWith (Oc : P₁ → Strs → Prop) (R : P₁ → Prop) : P₁ → Strs → Prop := fun p y => Oc p y ∧ R p

/-- It reads of the oracles what Oc reads. -/
theorem ocWith_readsBelow (lo : Nat) (Oc : P₁ → Strs → Prop) (R : P₁ → Prop)
    (h : VerifiableInference.Desc.Sound.OcReadsBelow lo Oc) :
    VerifiableInference.Desc.Sound.OcReadsBelow lo (ocWith Oc R) :=
  fun p y y' h1 h2 hy => ⟨h p y y' h1 h2 hy.1, hy.2⟩

section
variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ : List Mem) (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
  (Pw : Where) (wSeat : Nat × Nat) (matC : Cells → Nat → Nat → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
  (J : JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw wSeat matC Mg₁)
  (get : P₁ → P₀ × First.S) (N₁ : Numbers) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
include J

/-- **hW, with the premise on the words' reader asked INSIDE THE PROMISE alone.** -/
theorem hW_reached (xW : Mem) (lay₀ : VectorLay) (stOf : P₁ → Statement)
    (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hst : ∀ p, stOf p = (get p).2.st) (hlay : lay₀ = linLayW cs Pw.lin)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP p w n = w.tab cs sh (arr j t) j t)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1) (hseat : xW.1.seat xW.2 = wSeat) :
    ∀ p y D, ocEnd get N₁ Mg₁ links ps p y → R p →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → WSits cs arr xW lay₀ stOf tabP p D := by
  intro p y D h hR hm hD
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
    exact hbook p y h hR hm (by rw [← hst']; exact hS.codes) w D.w wSeat.1 wSeat.2 _ hplace hshape

end

/-- **The debt at "LIN point", at the seated piece, at any meaning of the first table that says what the joint says.** -/
theorem point_leadsB_reached (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
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
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        (seatedPiece b1 base d ext err :: r) 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
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
    (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f r gOf lo err₂ eM rank held ha
    hix hroom hk hr he hle hM hJ
    (by show (fun j t p => Mg₁.pin j t (get p)) = _; rw [J.pin]) rfl rfl rfl rfl rfl rfl rfl rfl
    (ocWith_readsBelow lo _ R (ocEndReadsBelow P₁ P₀ _ get lo N₁ Mg₁ links ps hread)) hlo hw hi hxW hsW Pw
    hlin matC (by show (fun p => Mg₁.wrow (get p)) = _; rw [J.wrow]) (by show (fun p => Mg₁.pileOne (get p)) = _; rw [J.pileOne]) rfl
    (fun p y h => hEL_layers cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ J get N₁ links ps h2 p y h.1)
    (fun p y' D h => hg p y' D h.1)
    (fun p y D h => hW_reached cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁ J get N₁ links ps xW (linLayW cs Pw.lin)
      (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) h3 (fun p => hst (get p)) rfl
      R hbook hsh hsW p y D h.1 h.2)
    (fun p w w' => htab (get p) w w') hH

/-- **Of the piece that the seat's own list holds at place 1.** -/
theorem point_leadsB_place_reached (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
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
    -- the first table's meaning: five fields are what the joint says; two tests on the table; the letters that the promise reads read below lo
    (J : JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁)
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    -- the filling's letters, each by its make; one equation on the plan
    (hst : ∀ a, stOf₁ a = a.2.st)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁ links ps p y' →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC) :
    ∃ (base : Nat) (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))),
      l = seatedPiece b1 base d ext err :: r ∧
      (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (actQ (tiedNumbers N₁ Ns) f l 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
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
      point_leadsB_reached cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl
        e' base d hd ext err N₁ Ns links ps split f r gOf lo err₂ eM rank held Pw hlin matC Mg₁ Mg₀ Pm₀ stOf₂ bookOf₂
        ha hix hroom hk hr he hle hM hJ J h2 h3 hread hlo hw hi hxW hsW hst R hbook htab hsh hg hH⟩

/-- **At the cap 128, for up to 64 slots.** -/
theorem point_leadsBN_cap_reached (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
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
    (hle : 2852142980 ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a -
      ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a)
      (2 ^ (codeOf P.par.S.fold.index.code).a -
        ((codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l) + 1) 2852142980)
    -- the first table's meaning: five fields are what the joint says; two tests on the table; the letters that the promise reads read below lo
    (J : JointSays cs G arr smp₁ ms₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁)
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    -- the filling's letters, each by its make; one equation on the plan
    (hst : ∀ a, stOf₁ a = a.2.st)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs →
      ∀ (w : Wit Cells Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) →
      ((get p).2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) →
      (∀ j t, w'.pad j t = w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁ links ps p y' →
      (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y < P.par.S.matrixRows,
      gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC)
    -- THE ARITHMETIC ON THE TWO LISTS (PointCap, K14PointCap.lean), at the release's numbers
    (Wr : Rounds) (hPC : PointCap P.par.S Wr) (hdW : atW Wr 0 = some (d.entry, d.kind)) (n : ℕ) (hn : n ≤ 64) :
    ∃ (base : Nat) (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))),
      l = seatedPiece b1 base d ext err :: r ∧
      (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsBN
      (actQ (tiedNumbers N₁ Ns) f l 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par 2852142980 gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocWith (ocEnd get N₁ Mg₁ links ps) R) split f
        l fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f l 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f l 1).2 a)) w)
      n (Err.cap 128 (uLT (ckP .two) [d])) := by
  obtain ⟨base, ext, err, r, hl, h⟩ := point_leadsB_place_reached (Cl' := Cl') (F := F) cs G arr get smp₁ ms₁ xW smp₂
    ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl 2852142980 d hd N₁ Ns links ps split lo f l c tests last
    hps hdat gOf err₂ eM rank held Pw hlin matC Mg₁ Mg₀ Pm₀ stOf₂ bookOf₂ ha hix hroom hk hr (by decide) hle hM hJ J
    h2 h3 hread hxW hsW hst R hbook htab hsh hg hH
  refine ⟨base, ext, err, r, hl, ?_⟩
  have hef : efIx P.par err₂ eM rank 2852142980 = efReal := by
    unfold efIx
    exact efForm_eq hPC.1
  rw [hef] at h
  exact leadsBN_at_cap hPC d hdW _ rfl _ _ _ h n hn

/-- **It rides wherever Oc rides and what was handed stays.** -/
theorem ocWith_rides {S₂ B : Type} (Oc : P₁ → Strs → Prop) (R : P₁ → Prop) (strs : B → Strs)
    (a b : (P₁ × S₂) × B) (hand : b.1.1 = a.1.1) (hO : Oc b.1.1 (strs b.2))
    (h : ocWith Oc R a.1.1 (strs a.2)) : ocWith Oc R b.1.1 (strs b.2) :=
  ⟨hO, hand ▸ h.2⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.ocWith_readsBelow
#print axioms Desc.K14.Law.ocWith_rides
#print axioms Desc.K14.Law.hW_reached
#print axioms Desc.K14.Law.point_leadsB_reached
#print axioms Desc.K14.Law.point_leadsB_place_reached
#print axioms Desc.K14.Law.point_leadsBN_cap_reached
