-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointLayersAtCap.lean: THE DEBT AT "LIN point" AT ANY MEANING OF THE FIRST TABLE THAT SAYS WHAT THE FIRST JOINT SAYS (JointSays, Johnson/Desc/Sound/PointAtLayers.lean): (1) OF THE PIECE THAT THE SEAT's OWN LIST HOLDS AT PLACE 1 · (2) AT THE CAP 128 OF THE WRITTEN ROUND, FOR UP TO 64 SLOTS. Two theorems. A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K13/ and K14/.
They are PointAtPlace.lean's and PointAtCap.lean's, word for word, with the first table's meaning a LETTER Mg₁ in the place of the named term mg1Joint: so that the law's last forms can be called at the one term into which the kinds' layers are composed. The proofs are theirs, over point_leadsB_layers.
  point_leadsB_place_layers · point_leadsBN_cap_layers.

Limits. As these two files' and PointAtLayers.lean's. ONE BLOCK's CLAUSE, UNDER PREMISES. NO MEMBER IS SHOWN. It rests, through the count of the key's lost points, on the files under ThirdParty/ (lean/LIMITS.md, L15).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtLayers
import Johnson.Desc.K14.Law.FlatRetype
import Johnson.Goal.Numbers.K14PointCap

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
  ocEnd tiedMeaning tiedNumbers LettersReadBelow)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **Of the piece that the seat's own list holds at place 1.** -/
theorem point_leadsB_place_layers (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (hbook : ∀ (a : P₀ × First.S) (w : Wit Cells Tok MsgT) n j t sh, a.2.book.place[n]? = some (j, t) →
      (a.2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ a w n = w.tab cs sh (arr j t) j t)
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
        (ocEnd get N₁ Mg₁ links ps) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par e' gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ Mg₁ links ps) split f
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
      point_leadsB_layers cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl
        e' base d hd ext err N₁ Ns links ps split f r gOf lo err₂ eM rank held Pw hlin matC Mg₁ Mg₀ Pm₀ stOf₂ bookOf₂
        ha hix hroom hk hr he hle hM hJ J h2 h3 hread hlo hw hi hxW hsW hst hbook htab hsh hg hH⟩

/-- **At the cap 128, for up to 64 slots.** -/
theorem point_leadsBN_cap_layers (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (hbook : ∀ (a : P₀ × First.S) (w : Wit Cells Tok MsgT) n j t sh, a.2.book.place[n]? = some (j, t) →
      (a.2.st.oracles[n]?).map (·.shape) = some sh → tabP₁ a w n = w.tab cs sh (arr j t) j t)
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
        (ocEnd get N₁ Mg₁ links ps) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get Mg₁
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par 2852142980 gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ Mg₁ links ps) split f
        l fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f l 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f l 1).2 a)) w)
      n (Err.cap 128 (uLT (ckP .two) [d])) := by
  obtain ⟨base, ext, err, r, hl, h⟩ := point_leadsB_place_layers (Cl' := Cl') (F := F) cs G arr get smp₁ ms₁ xW smp₂
    ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl 2852142980 d hd N₁ Ns links ps split lo f l c tests last
    hps hdat gOf err₂ eM rank held Pw hlin matC Mg₁ Mg₀ Pm₀ stOf₂ bookOf₂ ha hix hroom hk hr (by decide) hle hM hJ J
    h2 h3 hread hxW hsW hst hbook htab hsh hg hH
  refine ⟨base, ext, err, r, hl, ?_⟩
  have hef : efIx P.par err₂ eM rank 2852142980 = efReal := by
    unfold efIx
    exact efForm_eq hPC.1
  rw [hef] at h
  exact leadsBN_at_cap hPC d hdW _ rfl _ _ _ h n hn

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsB_place_layers
#print axioms Desc.K14.Law.point_leadsBN_cap_layers
