-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/PointAtLedgerS5.lean: THE LEDGER's PREMISE AT BLOCK 1, AT THE LEDGER's OWN
FILLING, FROM ANOTHER FILE's LAW AT "LIN point" AT THE TABLES' OWN TERMS. One theorem: ONE TERM
that applies point_at_ledger (Johnson/Desc/K14/Law/PointAtLedger.lean) to point_leadsB_reader
(PointReader.lean). A JOINING OF THESE TWO FILES' THEOREMS: no chance is counted here.

  uAt_next             where the chain's statement has no message yet, the reader of the state
                       (uAt p notedU, PointAtK14Closed.lean) is "o_u noted as the message to come".
  (That pmPoint meets PromFits, and tiedMeaning … (mgJoint …) MeanFits at rg := rgOf, omW := omWK,
  is shown inside the term, by rfl field by field: these two have no names of their own.)
  point_ledger_at_ocEnd   **the premise that LedgerPaysOwn asks at block 1**
                       (Johnson/Desc/Sound/SharedJointCountLedgerOwn.lean), TO THE LETTER: key :=
                       keyAt Prod.snd N.lo f l 1 · the condition onQ₂ at pmK · the step stepAt at
                       mgK, pmK and extOf … exK · δK, δO := that law's two lists of errors.
THE LETTERS AS THEY ARE LAID: N := tiedNumbers N₁ Ns · the ledger's Pm₀ := pmPoint …, Mg₀ :=
tiedMeaning … (mgJoint …) · decT₂ := decK P.par err₂ eM rank held · ms := ms₂ · the number of o_u
:= 0 · split := true · that law's rg := rgOf cs arr mem rd, omW := omWK cs arr mem rd nO P, stOf₂ :=
the state's statement, bookOf₂ := bkR of the state's book.
  sharedX_size | sharedX_point   THE TWO PREMISES ON THE LETTER X ARE MET AT X :=
                       sharedX (Johnson/Desc/Sound/SharedX.lean): by its membX01 and sharedX_k14.
THE FIRST TABLE's MEANING IS A LETTER, Mg₁. Of it are asked: four equations (hpin, hwrow,
hevalLaid, hwSits: its pins, its row on W and two of its public tests are what the joint says) ·
hpile: what the step back from the evaluation proves gives Mg₁'s OWN sentence on the pending rows
(one direction; inside the promise, under R, at a state without a mark) · h2, h3 (two tests on the
table) · hread (the letters that the promise reads read below lo). So the law can be taken at the
composed meaning of the first table, and not at one named filling alone.
THE SLOT's OWN CONDITION is ocWith (ocEnd …) R: the first chain's last promise WITH A LETTER R
BESIDE IT, a fact on what was handed to the shared chain (meant: "it is a reached last state of the
first chain"). WITH IT THE LAW COVERS ONLY THE STATES THAT MEET THAT PROMISE AND R. So
hbook (the words' reader reads by the book) is asked INSIDE THAT PROMISE AND UNDER R ALONE, at a
state without a mark whose codes are cs: in that form it can be paid at the reader that is meant.
R is a letter: nothing here says what it is; at R := fun _ => False the law says nothing.
Limits. THAT LAW's OTHER PREMISES STAND HERE, to the letter (cut by program), and
three more: hS (the shape splits) · hsz, hX (the letter X: X 1 gives "no message yet"; a yes of a
piece that holds "LIN point" hands X 1 on to X 2). Nothing on "own 1 pt = δK + n δO", the front
block or the ten blocks behind. NO MEMBER. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointAtLedger
import Johnson.Desc.Sound.PointAtOcEnd
import Johnson.Desc.Sound.PointReader
import Johnson.Desc.Sound.SharedJointCountLedgerOwn
import Johnson.Desc.Sound.SharedX

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack (sigOf)
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open Fence (sharedX sharedX_parts sharedX_k14 membX01)

/-- With no message yet, the reader uAt of the state is "the message to come". -/
theorem uAt_next (p : Par) (s : St) (h : s.st.oracles.size = 0) :
    uAt p notedU s = withNext p s := by
  unfold uAt notedU
  rw [h]
  simp

/-- hsz at X := sharedX (Johnson/Desc/Sound/SharedX.lean). -/
theorem sharedX_size (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (s : St)
    (h : sharedX P sentU layU layO 1 s = true) : s.st.oracles.size = 0 :=
  (membX01 sentU.size s 1 (Nat.le_refl 1)).1 ((sharedX_parts P sentU layU layO 1 s).1 h).2.2.1

variable {P₁ P₀ Xi Cells Tok Cl' : Type} {F : Frame}

/-- hX at X := sharedX: at any piece that holds the block. -/
theorem sharedX_point (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (sentU : Array OracleNotice)
    (hU : withU P.S = some sentU) (layU layO : TreeLay)
    (hlU : layTrees P.codes sentU = some layU)
    (hlO : layTrees P.codes (withOmega P.S) = some layO)
    (hS : P.par.S.sharedSplitNeeded = true) (hm : P.par.S.masksAhead = true)
    (x : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)) (hx : x.b = heldW b1.retype)
    (a : (P₁ × St) × F.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × F.E.Str)
    (ho : x.ior.red.out a τ = some y) (h : sharedX P sentU layU layO 1 a.1.2 = true) :
    sharedX P sentU layU layO 2 y.1.2 = true := by
  obtain ⟨rs, gs, hd⟩ := held_yes x b1.retype hx a τ y ho
  exact sharedX_k14 P b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU layU layO hlU hlO hS hm 0 b1 rfl _ _ rs
    gs hd h

/-- **The ledger's premise at block 1.** -/
theorem point_ledger_at_ocEnd
    (cs : OnBytes.Codes)
    (G : FileDescription Xi)
    (arr : Nat → Nat → Nat)
    (get : P₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
    (ms₁ : List Mem)
    (xW : Mem)
    (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms₂ : List Mem)
    (c₀ : Cells)
    (stOf₁ : P₀ × First.S → Statement)
    (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
    (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (e' : Nat)
    (base : Nat)
    (d : RDT)
    {ns a0 : Nat}
    (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok
      MsgT)
    (err : Err (uLT (ckP .two) [d]))
    (N₁ : Numbers)
    (Ns : NumbersS)
    (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place)
    (f : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT))
    (r : List (Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)))
    (gOf : P₁ → Nat → GE)
    (lo : Nat)
    (err₂ eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) → Fin (P.par.S.fold.index.code.r +
      P.par.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 P.par.S.fold err₂ eM rank).Row × Fin P.par.S.fold.index.code.ell → GE) →
      Option Cells)
    (Pw : Where)
    (hlin : Pw.lin = P.par.S)
    (matC : Cells → Nat → Nat → GE)
    (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT))
    (Pm₀ : PromMeaning St)
    (ha : P.par.S.fold.index.code.logN ≤ 32)
    (hix : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hk : 0 < (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l - 1)
    (hr : (codeOf P.par.S.fold.index.code).r + (codeOf P.par.S.fold.index.code).l ≤ 2 ^ (codeOf
      P.par.S.fold.index.code).a)
    (he : 0 < e')
    (hle : e' ≤ eM)
    (hM : eM < 2 ^ (codeOf P.par.S.fold.index.code).a - ((codeOf P.par.S.fold.index.code).r +
      (codeOf P.par.S.fold.index.code).l) + 1)
    (hJ : InJohnson (2 ^ (codeOf P.par.S.fold.index.code).a) (2 ^ (codeOf
      P.par.S.fold.index.code).a - ((codeOf P.par.S.fold.index.code).r + (codeOf
      P.par.S.fold.index.code).l) + 1) e')
    (hpin : Mg₁.pin = fun j t a y w => pinJT cs G arr smp₁ ms₁ j t a y w)
    (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
    (hevalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2)
    (hwSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB cs Pw a.2 && wSeatB N₁.w a.2))
    (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
    (hlo : lo ≤ base)
    (hw : N₁.w.1 < base)
    (hi : N₁.index.1 < base)
    (hxW : xW ∈ ms₁)
    (hsW : SitsAt xW N₁.w.1 N₁.w.2)
    (hst : ∀ a, stOf₁ a = a.2.st)
    (R : P₁ → Prop)
    (hbook : ∀ p y, ocEnd get N₁ Mg₁
      links ps p y → R p → (get p).2.failed = none → (get p).2.st.codes = cs → ∀ (w : Wit Cells Tok
      MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) → ((get p).2.st.oracles[n]?).map
      (·.shape) = some sh → tabP₁ (get p) w n = w.tab cs sh (arr j t) j t)
    (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) → (∀ j t, w'.pad j t =
      w.pad j t) → tabP₁ a w' = tabP₁ a w)
    (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
    (hg : ∀ p y' D, ocEnd get N₁ Mg₁
      links ps p y' → (get p).2.failed = none → laidOf Pw (get p).2 = some D → ∀ y <
      P.par.S.matrixRows, gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry
      y)).sum)
    (hH : HeldTie P.par err₂ eM rank held matC)
    (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get
      p).2.failed = none → pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w)
    (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (n nO : ℕ) (bkR : TreeBook → TreeBook) (X : ℕ → St → Bool)
    (hS : P.par.S.sharedSplitNeeded = true)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hX : ∀ (x : Piece (ckP .two) F (P₁ × St) Cl' (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → X 1 a.1.2 = true → X 2 y.1.2 = true) :
    (seatedPiece (Cl' := Cl') (F := F) (P₁ := P₁) b1 base d ext err).ior.red.LeadsB
      (keyAt Prod.snd (tiedNumbers N₁ Ns).lo f (seatedPiece b1 base d ext err :: r) 1)
      (onQ₂ (tiedNumbers N₁ Ns)
        (pmK cs G smp₂ ms₂ (decK P.par err₂ eM rank held) bkR
          (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held (fun s : St => s.st)
            (fun s : St => bkR s.book) Pm₀) n 0 nO P X)
        (ocWith (ocEnd get N₁ Mg₁
          links ps) R)
        true f (seatedPiece b1 base d ext err :: r) 1)
      (stepAt (tiedNumbers N₁ Ns)
        (mgK cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held)
          (tiedMeaning get Mg₁
            (mgJoint cs G arr get smp₁ ms₁ xW smp₂ ms₂ (linLayW cs Pw.lin)
              (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf cs arr mem rd)
              (omWK cs arr mem rd nO P) P.par e' gOf err₂ eM rank held Pw matC Mg₀))
          mem rd e' n nO P)
        (pmK cs G smp₂ ms₂ (decK P.par err₂ eM rank held) bkR
          (pmPoint cs G smp₂ ms₂ P.par err₂ eM rank held (fun s : St => s.st)
            (fun s : St => bkR s.book) Pm₀) n 0 nO P X)
        (ocWith (ocEnd get N₁ Mg₁
          links ps) R)
        true f (seatedPiece b1 base d ext err :: r)
        (extOf (tiedNumbers N₁ Ns) f (seatedPiece b1 base d ext err :: r)
          (exK cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) c₀ (tiedNumbers N₁ Ns) F)) 1)
      ((vecMaps d P.par.S.kCol).err
        ((efIx P.par err₂ eM rank e' * Fintype.card GE ^ P.par.S.kLo, ()) : Nat × Unit))
      ((vecMaps d P.par.S.kCol).err
        ((P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1), ()) : Nat × Unit)) :=
  point_at_ledger cs G arr smp₂ ms₂ (decK P.par err₂ eM rank held) bkR (tiedNumbers N₁ Ns) _ _ _
    mem rd e' n nO P X true (uAt P.par notedU) f _
    ⟨rfl, rfl, rfl, fun _ h => (Bool.and_eq_true_iff.1 h).1⟩
    ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
    (uAt_next P.par) b1 b2 b3 b4 b5 b6 b7 b8 hbl hS _ rfl hsz (hX _ rfl) _ _ _ _
    (point_leadsB_reader
      cs G arr get smp₁ ms₁ xW smp₂ ms₂ c₀ stOf₁ tabP₁ (rgOf cs arr mem rd) (omWK cs arr mem
      rd nO P) P b1 b2 b3 b4 b5 b6 b7 b8 hbl e' base d hd ext err N₁ Ns links ps true f r gOf lo
      err₂ eM rank held Pw hlin matC
      Mg₁ Mg₀ Pm₀
      (fun s : St => s.st) (fun s : St => bkR s.book) ha hix hroom hk hr he hle hM hJ
      hpin hwrow hevalLaid hwSits h2 h3
      hread hlo hw hi hxW hsW hst R
        hbook
      htab hsh hg hH hpile)

end Desc.K14.Law

#print axioms Desc.K14.Law.sharedX_size
#print axioms Desc.K14.Law.sharedX_point
#print axioms Desc.K14.Law.point_ledger_at_ocEnd
