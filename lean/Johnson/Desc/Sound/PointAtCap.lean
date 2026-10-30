-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointAtCap.lean: THE DEBT AT "LIN point", OF THE PIECE THAT THE SEAT's OWN LIST HOLDS AT PLACE 1, IN THE PLAIN FORM FOR A BATCH AT ONE LIST OF ERRORS: THE CAP 128 OF THE WRITTEN ROUND, FOR EVERY NUMBER OF SLOTS UP TO 64. One theorem: ONE CALL that joins two files: the law in two parts
(point_leadsB_at_place, Johnson/Desc/Sound/PointAtPlace.lean) and the arithmetic on the two lists of errors at the release's numbers (leadsBN_at_cap, efForm_eq: Johnson/Goal/Numbers/K14PointCap.lean).
WHAT IT SAYS: under the law's premises AT THE RADIUS e' := 2852142980 and PointCap P.par.S Wr (the shape's table is the release's; at every written round with the entry and kind of the written list's round 0 the key's part once and a slot's part N times lie beneath the cap): the piece at place 1 IS seatedPiece b1 …
and its reduction has LeadsBN ‹the acting part's key› ‹placesAll's on₂ at border 1› ‹the step› n (Err.cap 128 …), n ≤ 64.
WHAT IT DOES NOT SAY: anything of the chain: it is ONE BLOCK's clause. That the piece's own errors ARE the cap (they come back under "there is"). That 64 is the plan's number of requests. NONE OF THE 128 AT THIS ROUND IS PROOF OF WORK (the written round's work is 0: K14Rounds.point, Johnson/Goal/Numbers/K14RoundsAt.lean: PointCap does not carry that fact); hd's payer is k14_rounds_real (the same file), not point_cap_real. That the premises can be met together: NO MEMBER IS SHOWN. PointCap has members (point_cap_real | point_cap_key: by the kernel, at
the written lists of a proof file and a key file).

Limits. As PointAtPlace.lean's and K14PointCap.lean's. It rests, through the count of the key's lost points, on the files under ThirdParty/ (lean/LIMITS.md, L15).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtPlace
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
  ocEnd tiedMeaning tiedNumbers sampledBelow)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- **The debt at "LIN point", of the seat's own piece, at the cap 128, for up to 64 slots.** -/
theorem point_leadsBN_at_cap (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
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
    (hH : HeldTie P.par err₂ eM rank held matC)
    -- THE ARITHMETIC ON THE TWO LISTS (K14PointCap.lean), at the release's numbers
    (Wr : Rounds) (hPC : PointCap P.par.S Wr) (hdW : atW Wr 0 = some (d.entry, d.kind)) (n : ℕ) (hn : n ≤ 64) :
    ∃ (base : Nat) (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
      (err : Err (uLT (ckP .two) [d])) (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))),
      l = seatedPiece b1 base d ext err :: r ∧
      (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsBN
      (actQ (tiedNumbers N₁ Ns) f l 1).2
      (onQ₂ (tiedNumbers N₁ Ns) (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f
        l 1)
      (stepPt (tiedNumbers N₁ Ns)
        (tiedMeaning get (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁)
          (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin) (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q))
        rg omW P.par 2852142980 gOf err₂ eM rank held Pw matC Mg₀))
        (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
        (ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw N₁.w matC Mg₁) links ps) split f
        l fun a w =>
        extS cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) split 1
          ((actQ (tiedNumbers N₁ Ns) f l 1).2 a).1
          (strsOfAct F ((actQ (tiedNumbers N₁ Ns) f l 1).2 a)) w)
      n (Err.cap 128 (uLT (ckP .two) [d])) := by
  obtain ⟨base, ext, err, r, hl, h⟩ := point_leadsB_at_place (Cl' := Cl') (F := F) cs G arr get smp₁ ms₁ xW decT₁ smp₂
    ms₂ c₀ stOf₁ tabP₁ rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl 2852142980 d hd N₁ Ns links ps split lo f l c tests last
    hps hdat gOf err₂ eM rank held Pw hlin matC Mg₁ Mg₀ Pm₀ stOf₂ bookOf₂ ha hix hroom hk hr (by decide) hle hM hJ h2
    h3 hbelow hxW hsW hst hbook htab hsh hg hH
  refine ⟨base, ext, err, r, hl, ?_⟩
  have hef : efIx P.par err₂ eM rank 2852142980 = efReal := by
    unfold efIx
    exact efForm_eq hPC.1
  rw [hef] at h
  exact leadsBN_at_cap hPC d hdW _ rfl _ _ _ h n hn

end Desc.K14.Law

#print axioms Desc.K14.Law.point_leadsBN_at_cap
