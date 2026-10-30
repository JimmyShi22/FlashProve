-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/JointFilling.lean: THE WEIGHTS' CLAIM ACROSS THE FIRST JOINT: ONE SENTENCE ON BOTH SIDES: the first table's and the shared table's records of meanings, NAMED, at which (1) the joint's relation and the tie's are one term and (2) the twelve equations of letters of point_leadsB_joint
(Johnson/Desc/Sound/PointAtJoint.lean) are rfl. Three definitions, seven theorems. (THE FIRST TABLE's DOOR IS USED: mg1Joint merges wSitsMore (Johnson/Desc/K13/Law/SitsDoor.lean) into the filling of the door and lays the item "K13.wSits" := K13's wSitsB cs Pw && wSeatB wSeat; a letter wSeat: W's seat; pubJoint: the public items' tests as one term). ("No mark" is spent: mgJoint lays unmarked1 too: TWELVE equations by rfl). A joint
build of K13's and K14's files.

  THE READER IS A FAMILY in the first chain's pair a = (public part, record): a witness's matrix is what its cells hold (matC w.cells); its words are the first chain's statement's at a; typed at the first chain's own numbers (Pw.lin).
  mg1Joint: the FIRST table's meaning: meaningSig with pileOne a _ w := ALL ROWS ON THE TABLE OF a's RECORD ARE TRUE at that reader (RowsTrue, Johnson/Desc/K13/Law/Letters.lean) · wrow a _ w := that file's WRow at these words · THE TWO PUBLIC ITEMS evalLaid | frontOk := K13's tests with code evalLaidB | frontOkB (Johnson/Desc/K13/Law/Bools.lean): in BOTH directions by that file's "if and only if" (a filling in the maker's direction alone gives the spender nothing).
  mgJoint: the SHARED table's: mgPoint with claimM | ev := these two sentences through get.
  tied_is_joint: tiedMeaning get (mg1Joint …) (mgJoint …) = mgJoint …: rfl.
  hEL_at_ocEnd: AT Oc := THE FIRST CHAIN's WHOLE PROMISE AT ITS LAST BORDER (ocEnd, Johnson/Desc/Sound/TieEnd.lean), at mg1Joint, AT A RECORD WITHOUT A MARK: (Eval) is laid: from ONE TEST ON THE PROMISE's TABLE (evalLaid is among the public items at the last border): so hEL is EXCHANGED for that test.
  point_leadsB_at_joint: point_leadsB_joint's conclusion where the shared table's two records are mgJoint | pmPoint: twelve rfl.
AT WHICH BORDERS THE TWO FILLED ITEMS OF THE FIRST TABLE ARE OPEN, AND WHETHER THEY CAN BE TRUE THERE OF AN HONEST WITNESS (BY READING, NOT BY A RUN): pileOne: from behind the block that joins the pending rows ("M:3") to the chain's end: at each the record's table holds
the one joined row: true of the honest matrix and words, IF THE WORDS AT THE OLDER PLACES STAY ACROSS W's SENDING (a debt that K13's files name on whoever fills the reader) · wrow: opened by no row of the first chain: read at the joint alone.

Limits. Fillings and unfoldings. NO LAW OF A BLOCK. NO MEMBER. stOf₁, tabP₁, matC, Pw and mgPoint's letters stay letters.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtJoint
import Johnson.Desc.Sound.PointAtFilling
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.K13.Law.Bools
import Johnson.Desc.K13.Law.SitsDoor
import Johnson.Desc.K13.Law.SitsAt
import Johnson.Desc.K13.Law.SeatMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ promQ actQ shIt ownItem stepPt strsOf strsOfAct OcReadsBelow
  pinJT SitsAt decodesOf pinWOf extS wTab MsgT Mem Sending meaningSig tiedMeaning CellsOf ocEnd ocEnd_pub)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning ItemS)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt witOf matBy vecAt RowsTrue WRow EvalLaid laidOf evalLaidB frontOkB
  evalLaidB_iff wSitsItem wSitsMore wSitsB wSeatB)

variable {P₁ P₀ Xi Cells Tok : Type}

/-- The public items' tests: three of K13's laid; the rest as they were. -/
def pubJoint (cs : OnBytes.Codes) (Pw : Where) (wSeat : Nat × Nat) (pub₀ : Pub → P₀ × First.S → Bool) :
    Pub → P₀ × First.S → Bool := fun q a =>
  if q = wSitsItem then wSitsB cs Pw a.2 && wSeatB wSeat a.2
  else match q with
    | .evalLaid => evalLaidB Pw a.2
    | .frontOk => frontOkB Pw a.2
    | q => pub₀ q a

theorem pubJoint_wSits (cs : OnBytes.Codes) (Pw : Where) (wSeat : Nat × Nat) (pub₀ : Pub → P₀ × First.S → Bool)
    (a : P₀ × First.S) : pubJoint cs Pw wSeat pub₀ wSitsItem a = (wSitsB cs Pw a.2 && wSeatB wSeat a.2) := by
  unfold pubJoint
  rw [if_pos rfl]

theorem pubJoint_evalLaid (cs : OnBytes.Codes) (Pw : Where) (wSeat : Nat × Nat)
    (pub₀ : Pub → P₀ × First.S → Bool) (a : P₀ × First.S) :
    pubJoint cs Pw wSeat pub₀ .evalLaid a = evalLaidB Pw a.2 := by
  unfold pubJoint
  rw [if_neg (by decide)]

/-- **The first table's meaning, with the claim on the matrix and (Eval) laid as terms, through the record's own rows.** -/
noncomputable def mg1Joint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (Pw : Where) (wSeat : Nat × Nat) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) : Meaning P₀ (Wit Cells Tok MsgT) :=
  { meaningSig cs G arr smp₁ ms₁ decT₁ Mg₁ with
    pileOne := fun a _ w =>
      RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
        (fun w' : Wit Cells Tok MsgT => witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf₁ a) (tabP₁ a w')))
        a.2 w
    wrow := fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w))
    more := Mg₁.more.merge wSitsMore
    pub := pubJoint cs Pw wSeat Mg₁.pub }

/-- **The shared table's meaning: mgPoint, with the claim and (Eval) at the sentences that the joint hands on.** -/
noncomputable def mgJoint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (lay₀ : VectorLay)
    (stOf : P₁ → Statement) (tabP : P₁ → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (p : Par) (e' : Nat)
    (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (Pw : Where) (matC : Cells → Nat → Nat → GE)
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  { mgPoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ lay₀ stOf tabP rg omW p e' gOf err₂ eM rank held
      (fun q => laidOf Pw (get q).2) matC Mg₀ with
    unmarked1 := fun q => (get q).2.failed = none
    ev := fun q _ w => WRow Pw (get q).2 (wordsOn (stOf q) (tabP q w))
    claimM := fun q _ w =>
      RowsTrue (nR := Pw.lin.matrixRows) (k := Pw.lin.kCol)
        (fun w' : Wit Cells Tok MsgT => witOf (matBy Pw.lin.kCol (matC w'.cells)) (wordsOn (stOf q) (tabP q w')))
        (get q).2 w }

/-- **The joint's meaning and the tie's are one term.** -/
theorem tied_is_joint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₁ : List Mem) (xW : Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem) (lay₀ : VectorLay)
    (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (rg : Wit Cells Tok MsgT → Words GE) (omW : Wit Cells Tok MsgT → Nat → GE) (p : Par) (e' : Nat)
    (gOf : P₁ → Nat → GE) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (Pw : Where) (wSeat : Nat × Nat) (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) :
    tiedMeaning get
        (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁)
        (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ lay₀ (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) rg omW p
          e' gOf err₂ eM rank held Pw matC Mg₀) =
      mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ lay₀ (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) rg omW p e'
        gOf err₂ eM rank held Pw matC Mg₀ := rfl

section
variable (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms₁ : List Mem) (decT₁ : CellsOf → P₀ × First.S → Option Cells)
  (stOf₁ : P₀ × First.S → Statement) (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
  (Pw : Where) (wSeat : Nat × Nat) (matC : Cells → Nat → Nat → GE) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))

/-- What the filling says at the item that came through the door. -/
theorem pub_wSits (a : P₀ × First.S) :
    (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁).pub wSitsItem a =
      (wSitsB cs Pw a.2 && wSeatB wSeat a.2) := pubJoint_wSits cs Pw wSeat Mg₁.pub a

/-- What it says at evalLaid. -/
theorem pub_evalLaid (a : P₀ × First.S) :
    (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁).pub .evalLaid a = evalLaidB Pw a.2 :=
  pubJoint_evalLaid cs Pw wSeat Mg₁.pub a

/-- **hEL, at the slot's own condition that is meant**: the first chain's whole promise at its last border, at mg1Joint, at a record without a mark, gives that (Eval) is laid: from one test on the promise's table. -/
theorem hEL_at_ocEnd (get : P₁ → P₀ × First.S)
    (N₁ : Numbers) (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
    (h2 : Pub.evalLaid ∈ (pubSets (Mg₁.more.merge wSitsMore) links ps)[ps.length]?.getD []) :
    ∀ p y, ocEnd get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) links ps p y →
      (get p).2.failed = none → EvalLaid Pw (get p).2 :=
  fun p y h hm => (evalLaidB_iff Pw _).1
    ((pub_evalLaid cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁ (get p)).symm.trans
      (ocEnd_pub get N₁ (mg1Joint cs G arr smp₁ ms₁ decT₁ stOf₁ tabP₁ Pw wSeat matC Mg₁) links ps p y h hm
        .evalLaid h2))

end

variable {F : Frame}

/-- **The debt at "LIN point" at the joint's own filling: the twelve equations of letters are rfl.** -/
theorem point_leadsB_at_joint (cs : OnBytes.Codes) (G : FileDescription Xi) (arr : Nat → Nat → Nat)
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
    (Pw : Where) (hlin : Pw.lin = P.par.S) (matC : Cells → Nat → Nat → GE)
    -- THE FILLING: TWO EQUATIONS: the items' and the promise's meanings ARE the two named records
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St)
    (stOf₂ : St → OnBytes.Statement) (bookOf₂ : St → OnBytes.TreeBook)
    (hMg : Mg = mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ lay₀ stOf tabP rg omW P.par e' gOf err₂ eM rank held Pw
      matC Mg₀)
    (hPm : Pm = pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held stOf₂ bookOf₂ Pm₀)
    (hOc : OcReadsBelow lo Oc) (hlo : lo ≤ base) (hw : N.w.1 < base) (hi : N.index.1 < base)
    (hxW : xW ∈ ms₁) (hsW : SitsAt xW N.w.1 N.w.2)
    -- THE STEP BACK FROM (Eval): K13's letters and ties (Johnson/Desc/K13/Law/PointStepBack.lean)
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
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) := by
  subst hMg hPm
  exact point_leadsB_joint cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ lay₀ stOf tabP rg omW P b1 b2 b3 b4 b5 b6 b7 b8 hbl
    e' base d hd ext err N _ _ Oc split f r gOf lo err₂ eM rank held ha hix hroom hk hr he hle hM hJ rfl rfl rfl
    rfl rfl rfl rfl rfl rfl hOc hlo hw hi hxW hsW Pw hlin matC rfl rfl rfl hEL hg hW htab hH

end Desc.K14.Law

#print axioms Desc.K14.Law.tied_is_joint
#print axioms Desc.K14.Law.pub_wSits
#print axioms Desc.K14.Law.pub_evalLaid
#print axioms Desc.K14.Law.hEL_at_ocEnd
#print axioms Desc.K14.Law.point_leadsB_at_joint
