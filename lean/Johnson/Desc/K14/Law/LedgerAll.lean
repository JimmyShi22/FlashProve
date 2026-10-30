-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerAll.lean: THE LEDGER's RULE AT ONE FILLING, AS ONE TERM, OVER THE TWELVE
PIECES OF THE SHARED CHAIN. One theorem: ledgerPaysOwn
(Johnson/Desc/Sound/SharedJointCountLedgerOwn.lean) applied to point_ledger_at_ocEnd (block 1:
Johnson/Desc/K14/Law/PointAtLedgerS5.lean) and share_seamed (blocks 2 to 11:
Johnson/Desc/K14/Law/LedgerSeamRow.lean). A joining of these three files' theorems: no chance
is counted here.

THE ROW: f :: PT :: MM: f the front block's piece; PT := seatedPiece b1 base d ext err ("LIN
point"); MM the ten pieces behind it.
THE FILLING, AS SIX EQUATIONS OF LETTERS, each met by rfl at the terms that it names: eN : N =
tiedNumbers N₁ Ns · eD : decT₂ = decK Q.par err₂ eM rank held · eO : Oc = ocWith (ocEnd get N₁ Mg₁
links ps) R (the first chain's whole promise at its last border, with a letter R beside it) · eP :
Pm₀ = pmPoint … · eM₀ : Mg₀ = tiedMeaning get Mg₁ (mgJoint …) · hn0 : nU = 0. PmZ, MgZ, X and R stay
free letters. Mg₁, THE FIRST TABLE's MEANING, IS A LETTER TOO: what is asked of it:
Johnson/Desc/K14/Law/PointAtLedgerS5.lean's head.
  decK_key     the decoder decK reads the chain's state through its key alone.
  ledger_all   EachLawsBNOwn … slots own 0 (f :: PT :: MM): each piece has LeadsBN at own's entry
               for it, and hands the condition on. slots IS THE NUMBER THAT hown NAMES: own 1 PT =
               δK + slots δO: another number of slots wants another own.
WHAT IS PROVED AND WHAT IS ONLY HANDED THROUGH, PIECE BY PIECE. A piece's law has two halves: the
shared items, with the chance; and what each slot has of its own, which rides for certain.
  0 (the front)      the shared half: proved (from hf1, hfb). "Shape 0 gives shape 1": proved from
                     hZ0, hX01: so whoever lays X owes X 0 s → X 1 s. The own half IS hFR.
  1 ("LIN point")    both halves: proved, under the premises of point_leadsB_reader
                     (PointReader.lean: numbers of the plan; four equations, hpile and three more on
                     the first table's meaning; makes of letters; hg; hH) and hS, hsz, hXb.
  2 to 8, and 11     the shared half: proved, under share_seamed's premises on the plan, the written
                     rounds and the letters; hX (X is handed on) is a premise. The own half IS hRd.
  9 and 10 (the two proximity tests)   NOTHING OF THE LAW IS PROVED HERE: the shared half, with all
                     its chance, IS h9, h10; the own half IS hRd; "lifted" IS hx9, hx10. Only the
                     step from one statement to a batch is the rule's.
WHAT IS OWED IN FRONT OF THE ROW. The condition at border 0 asks PmZ.shape 0, the layout's test and
X 0 of the chain's first state. By hZ0, PmZ.shape 0 must give shape1: THE INSTANCE's KEY HAS THE
PLANNED SIZES. No text tests that in front of block 3 ("(rec_gamma)"): an honest key has them; who
shows it at the chain's start is open.
IDLE FILLINGS. At X := fun _ _ => false, or PmZ.shape 0 := fun _ => false, or R := fun _ => False,
every premise on X, PmZ or R holds and all twelve laws say nothing. EACH LAW COVERS ONLY THE STATES
THAT MEET THE PROMISE, R AMONG IT.
Limits. No cap: the errors are own's entries: letters, but for the five that ho2', ho4', ho5', ho7'
and hown name. e' and eM are bound by he, hle, hM, hJ alone: that e' is the plan's radius is not
said. Nothing ties base2 to base. That the pieces of a description ARE these forms is not shown
here. NO MEMBER: that the premises can be met together is shown nowhere. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointAtLedgerS5
import Johnson.Desc.K14.Law.LedgerSeamRow

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
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

/-- The decoder reads the chain's state through its key alone. -/
theorem decK_key {Cells : Type} (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (c : ℕ → Option (ℕ × List UInt64)) (s s' : St) (hk : s'.loc.key = s.loc.key) :
    decK p err₂ eM rank held c s' = decK p err₂ eM rank held c s := by
  have e : recAt p err₂ eM rank s' = recAt p err₂ eM rank s := by
    unfold recAt
    rw [hk]
  show decGuard _ _ held c (recAt p err₂ eM rank s') = decGuard _ _ held c (recAt p err₂ eM rank s)
  rw [e]

variable {P₀ : Type}
variable
  {P₁ Cl Xi Cells Tok : Type}
  {Fr : Frame}
variable
  (G : FileDescription Xi)
  (oNo : Mem → ℕ)
  (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (N : NumbersS)
  (Q : P14)
  (Pm₀ : PromMeaning St)
  (Oc : P₁ → Strs → Prop)
  (n nU nO : ℕ)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
variable
  (arr : ℕ → ℕ → ℕ)
  (c₀ : Cells)
  (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT))
  (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
  (e' : ℕ)
  (num : Msg2 → ℕ)
  (sentU : Array OracleNotice)
  (X : ℕ → St → Bool)
variable
  (get : P₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Q.codes s.l).om
    i).Smp)
  (ms₁ : List Mem)
  (xW : Mem)
  (stOf₁ : P₀ × First.S → Statement)
  (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
  (base : Nat)
  (d : RDT)
  {ns a0 : Nat}
  (hd : SendsDraws (toRD d) ns Q.par.S.kCol 0 a0)
  (ext : (P₁ × St) × Fr.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok
    MsgT)
  (err : Err (uLT (ckP .two) [d]))
  (N₁ : Numbers)
  (Ns : NumbersS)
  (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place)
  (gOf : P₁ → Nat → GE)
  (lo : Nat)
  (err₂ eM : Nat)
  (rank : ((Fin Q.par.S.fold.index.v → Bool) → Fin (Q.par.S.fold.index.code.r +
    Q.par.S.fold.index.code.ell) → GE) → Nat)
  (held : ((ixOf2 Q.par.S.fold err₂ eM rank).Row × Fin Q.par.S.fold.index.code.ell → GE) →
    Option Cells)
  (Pw : Where)
  (hlin : Pw.lin = Q.par.S)
  (matC : Cells → Nat → Nat → GE)
  (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
  (MgZ : MeaningS St P₁ (Wit Cells Tok MsgT))
  (PmZ : PromMeaning St)
  (ha : Q.par.S.fold.index.code.logN ≤ 32)
  (hix : Q.par.S.fold.index.ok = true)
  (hroom : Q.par.S.matrixRows * 2 ^ Q.par.S.kLo ≤ Q.par.S.fold.index.plain)
  (hk : 0 < (codeOf Q.par.S.fold.index.code).r + (codeOf Q.par.S.fold.index.code).l - 1)
  (hr : (codeOf Q.par.S.fold.index.code).r + (codeOf Q.par.S.fold.index.code).l ≤ 2 ^ (codeOf
    Q.par.S.fold.index.code).a)
  (he : 0 < e')
  (hle : e' ≤ eM)
  (hM : eM < 2 ^ (codeOf Q.par.S.fold.index.code).a - ((codeOf Q.par.S.fold.index.code).r +
    (codeOf Q.par.S.fold.index.code).l) + 1)
  (hJ : InJohnson (2 ^ (codeOf Q.par.S.fold.index.code).a) (2 ^ (codeOf
    Q.par.S.fold.index.code).a - ((codeOf Q.par.S.fold.index.code).r + (codeOf
    Q.par.S.fold.index.code).l) + 1) e')
  (hpin : Mg₁.pin = fun j t a y w => pinJT Q.codes G arr smp₁ ms₁ j t a y w)
  (hwrow : Mg₁.wrow = fun a _ w => WRow Pw a.2 (wordsOn (stOf₁ a) (tabP₁ a w)))
  (hevalLaid : ∀ a, Mg₁.pub .evalLaid a = evalLaidB Pw a.2)
  (hwSits : ∀ a, Mg₁.pub wSitsItem a = (wSitsB Q.codes Pw a.2 && wSeatB N₁.w a.2))
  (h2 : Pub.evalLaid ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
  (h3 : wSitsItem ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
  (hread : LettersReadBelow lo N₁ Mg₁ ((openSets links ps (start links))[ps.length]?.getD []))
  (hloB : lo ≤ base)
  (hw : N₁.w.1 < base)
  (hi : N₁.index.1 < base)
  (hxW : xW ∈ ms₁)
  (hsW : SitsAt xW N₁.w.1 N₁.w.2)
  (hst : ∀ a, stOf₁ a = a.2.st)
  (R : P₁ → Prop)
  (hbook : ∀ p y, ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed = none → (get
    p).2.st.codes = Q.codes → ∀ (w : Wit
      Cells
    Tok MsgT) n j t sh, (get p).2.book.place[n]? = some (j, t) → ((get p).2.st.oracles[n]?).map
    (·.shape) = some sh → tabP₁ (get p) w n = w.tab Q.codes sh (arr j t) j t)
  (htab : ∀ a (w w' : Wit Cells Tok MsgT), (∀ n, w'.msg n = w.msg n) → (∀ j t, w'.pad j t =
    w.pad j t) → tabP₁ a w' = tabP₁ a w)
  (hsh : Pw.lin.w = (xW.1.l.get xW.2).1)
  (hg : ∀ p y' D, ocEnd get N₁ Mg₁ links ps p y' → (get p).2.failed = none → laidOf Pw (get p).2 =
    some D → ∀ y <
    Q.par.S.matrixRows, gOf p y = (D.row.g.map fun t => OnBytes.Model.Reading.gl.val (t.entry
    y)).sum)
  (hH : HeldTie Q.par err₂ eM rank held matC)
  (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed
    = none → pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w)
variable
  (c2 c3 c4 c5 c6 c7 c8 c11 : Block St Cl)
  (f x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (base2 : ℕ)
  (d21 d22 : RDT)
  (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT → Wit
    Cells Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22]))
  (base4 : ℕ)
  (d4 : RDT)
  (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er4 : Err (uLT (ckP .two) [d4]))
  (base5 : ℕ)
  (d51 d52 : RDT)
  (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT → Wit
    Cells Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52]))
  (base7 : ℕ)
  (d7 : RDT)
  (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (ht : Tiled (pc2 c2 base2 d21 d22 ex2 er2) [x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51
    d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])
  (hlo : ∀ m, N.lo ≤ (N.tenant m).1)
  (tU : (N.tenant .oU).1 < x3.base)
  (tO : (N.tenant .oOmega).1 < x6.base)
  (tS : (N.tenant .oSp).1 < x6.base)
  (hS : Q.S.sharedSplitNeeded = true)
  (hnum : num .oU = nU)
  (h2c : DecidesAs c2 b2)
  (h3c : DecidesAs c3 b3)
  (h4c : DecidesAs c4 b4)
  (h5c : DecidesAs c5 b5)
  (h6c : DecidesAs c6 b6)
  (h7c : DecidesAs c7 b7)
  (h8c : DecidesAs c8 b8)
  (h2r : c2.rounds = b2.rounds)
  (h3r : c3.rounds = b3.rounds)
  (h4r : c4.rounds = b4.rounds)
  (h5r : c5.rounds = b5.rounds)
  (h6r : c6.rounds = b6.rounds)
  (h8r : c8.rounds = b8.rounds)
  (hx3 : x3.b = heldW c3)
  (hx6 : x6.b = heldW c6)
  (hx8 : x8.b = heldW c8)
  (hx11 : x11.b = heldW c11)
  (he11 : Exact (fun d : St => untestedL d.st) c11)
  (xU xO : Mem)
  (hU : mem nU = some xU)
  (hO : mem nO = some xO)
  (mU : xU ∈ ms)
  (mO : xO ∈ ms)
  (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
  (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (hUw : withU Q.S = some sentU)
  (hn0 : nU = 0)
  (hnO : nO = nU + sentU.size)
  (hX : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) (onQ₂ N (pmK Q.codes G (smpSt Q.codes
    oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f ((seatedPiece (W := Wit Cells
    Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err) :: [(pc2 c2 base2 d21 d22 ex2
    er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7
    ex7 er7), x8, x9, x10, x11])) [b1, b2, b3, b4, b5, b6, b7, b8] X)
  (hoU : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 → oNo z = nU)
  (rad2 : ℕ → ℕ)
  (hC2 : condPort (parU Q sentU) rad2 = true)
  (he12 : d21.entry = seedEntry (parU Q sentU))
  (hk12 : d21.kind = .seeds)
  (e2 : ℕ)
  (he2 : errPort (parU Q sentU) rad2 ≤ e2)
  (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem)
  (new2 : List Mem)
  (entry2 : ∀ k, (memK2 k).1.l.get (memK2 k).2 = (shapeAt (parU Q sentU) k, rad2 k.val))
  (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
  (hno2 : ∀ k, sampledAt (parU Q sentU) k → oNo (memK2 k) = nU + k.val)
  (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
  (hSh2 : ∀ x ∈ new2, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c2) base2
    d21 d22 (parU Q sentU).coordinates e2).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew2 : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new2)
  {ns4 : ℕ}
  (hd4 : SendsDraws (toRD d4) ns4 0 n Q.par.S.fold.index.code.logN)
  (ho4 : d4.opens = [])
  (e4 : ℕ)
  (he4 : (2 ^ Q.par.S.fold.index.code.logN - e' - 1) ^ n ≤ e4)
  (rad5 : ℕ → ℕ)
  (hC5 : condPort (parO Q) rad5 = true)
  (he15 : d51.entry = seedEntry (parO Q))
  (hk15 : d51.kind = .seeds)
  (e5 : ℕ)
  (he5 : errPort (parO Q) rad5 ≤ e5)
  (memK5 : Fin (shapesOf (parO Q)).length → Mem)
  (new5 : List Mem)
  (entry5 : ∀ k, (memK5 k).1.l.get (memK5 k).2 = (shapeAt (parO Q) k, rad5 k.val))
  (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
  (hno5 : ∀ k, sampledAt (parO Q) k → oNo (memK5 k) = nO + k.val)
  (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
  (hSh5 : ∀ x ∈ new5, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c5) base5
    d51 d52 (parO Q).coordinates e5).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 →
    x ∈ new5)
  (xS : Mem)
  (mS : xS ∈ ms)
  (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
  {ns7 a7 : ℕ}
  (hd7 : SendsDraws (toRD d7) ns7 Q.par.S.kRow 0 a7)
  (e7 : ℕ)
  (he7 : Q.par.S.kRow * Fintype.card GE ^ (Q.par.S.kRow - 1) ≤ e7)
  (own : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (ho2' : own 2 (pc2 c2 base2 d21 d22 ex2 er2) = ((seedMaps d21 d22 (parU Q
    sentU).coordinates).err ((e2, ()) : ℕ × Unit)))
  (ho4' : own 4 (pc1 c4 base4 d4 ex4 er4) = (posMaps d4 Q.par.S.fold.index.code.logN n).err
    ((e4, ()) : ℕ × Unit))
  (ho5' : own 5 (pc2 c5 base5 d51 d52 ex5 er5) = ((seedMaps d51 d52 (parO Q).coordinates).err
    ((e5, ()) : ℕ × Unit)))
  (ho7' : own 7 (pc1 c7 base7 d7 ex7 er7) = (vecMaps d7 Q.par.S.kRow).err ((e7, ()) : ℕ × Unit))
  (h9 : ClauseAt N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q)
    (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
    ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err)
    :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5
    er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK Q.codes G arr (smpSt Q.codes
    oNo stSh) ms decT₂ c₀ N Fr) 9 x9 (own 9 x9))
  (h10 : ClauseAt N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q)
    (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ n nU nO Q X) Oc true f
    ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err)
    :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5
    er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11]) (exK Q.codes G arr (smpSt Q.codes
    oNo stSh) ms decT₂ c₀ N Fr) 10 x10 (own 10 x10))

set_option quotPrecheck false in
local notation "PT" => seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1
  base d ext err
set_option quotPrecheck false in
local notation "MM" =>
  [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4, pc2 c5 base5 d51 d52 ex5 er5, x6,
    pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11]
set_option quotPrecheck false in
local notation "PK" =>
  pmK (P14.codes Q) G (smpSt (P14.codes Q) oNo stSh) ms decT₂ (shiftBook (NumbersS.lo N)) Pm₀ n nU
    nO Q X
set_option quotPrecheck false in
local notation "MK" =>
  mgK (P14.codes Q) G arr (smpSt (P14.codes Q) oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q
set_option quotPrecheck false in
local notation "EK" => exK (P14.codes Q) G arr (smpSt (P14.codes Q) oNo stSh) ms decT₂ c₀ N Fr

include G oNo ms decT₂ N Q Pm₀ Oc n nU nO b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀ mem rd e' num
  sentU X get smp₁ ms₁ xW stOf₁ tabP₁ base d hd ext err N₁ Ns links ps gOf lo err₂ eM rank
  held Pw hlin matC Mg₁ MgZ PmZ ha hix hroom hk hr he hle hM hJ hpin hwrow hevalLaid hwSits h2 h3
    hread hloB hw hi hxW hsW
  hst R hbook htab hsh hg hH hpile c2 c3 c4 c5 c6 c7 c8 c11 f x3 x6 x8 x9 x10 x11 base2 d21 d22
    ex2 er2
  base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hS hnum h2c h3c h4c h5c
  h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU sO hUw hn0 hnO hX
  hoU rad2 hC2 he12 hk12 e2 he2 memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 hd4 ho4 e4 he4 rad5
  hC5 he15 hk15 e5 he5 memK5 new5 entry5 all5 hno5 htree5 hSh5 hnew5 xS mS sS hd7 e7 he7 own ho2'
  ho4' ho5' ho7' h9 h10

/-- **The ledger's rule at one filling, over the twelve pieces.** -/
theorem ledger_all (slots : ℕ)
    (eN : N = tiedNumbers N₁ Ns) (eD : decT₂ = decK Q.par err₂ eM rank held)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eP : Pm₀ = pmPoint Q.codes G (smpSt Q.codes oNo stSh) ms Q.par err₂ eM rank held
      (fun s : St => s.st) (fun s : St => shiftBook N.lo s.book) PmZ)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd nO Q) Q.par e' gOf err₂ eM rank held Pw matC MgZ))
    (hsr : SampleRides MgZ num) (hS12 : ∀ s, PmZ.shape 11 s = true → PmZ.shape 12 s = true)
    (hZ0 : ∀ s, PmZ.shape 0 s = true → shape1 Q.par s = true ∧ notedU s = false)
    (hX01 : ∀ s, X 0 s = true → X 1 s = true)
    (hx9 : ∃ b₀ : Block St Cl, x9.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (hx10 : ∃ b₀ : Block St Cl, x10.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (hop : ∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j)
    (hf1 : ∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) (hfb : (PT).base = f.base)
    (hFR : FrontRides N (MK) (PK) Oc true f ((PT) :: MM))
    (hown : own 1 (PT) = Err.add
      ((vecMaps d Q.par.S.kCol).err
        ((efIx Q.par err₂ eM rank e' * Fintype.card GE ^ Q.par.S.kLo, ()) : Nat × Unit))
      (Err.times slots ((vecMaps d Q.par.S.kCol).err
        ((Q.par.S.kCol * Fintype.card GE ^ (Q.par.S.kCol - 1), ()) : Nat × Unit))))
    (hRd : EachRides N (MK) (PK) Oc true f ((PT) :: MM) (EK) 2 MM)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hXb : ∀ (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → X 1 a.1.2 = true → X 2 y.1.2 = true) :
    EachLawsBNOwn (keyAt Prod.snd N.lo f ((PT) :: MM)) (onQ₂ N (PK) Oc true f ((PT) :: MM))
      (stepAt N (MK) (PK) Oc true f ((PT) :: MM) (extOf N f ((PT) :: MM) (EK))) slots own 0
      (f :: (PT) :: MM) := by
  have hlift : ∀ x ∈ MM, ∃ b₀ : Block St Cl, x.b = b₀.lift Prod.snd fun t s => (t.1, s) := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨below c2, rfl⟩
    · exact ⟨below c3, hx3⟩
    · exact ⟨below c4, rfl⟩
    · exact ⟨below c5, rfl⟩
    · exact ⟨below c6, hx6⟩
    · exact ⟨below c7, rfl⟩
    · exact ⟨below c8, hx8⟩
    · exact hx9
    · exact hx10
    · exact ⟨below c11, hx11⟩
  subst eP eM₀ eO eD eN hn0
  have H2 := share_seamed
    G oNo ms _ _ Q _ _ n _ nO b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ _ mem rd e' num sentU X c2 c3 c4
    c5 c6 c7 c8 c11 f _ x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4 ex4 er4 base5 d51 d52
    ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hS (decK_key Q.par err₂ eM rank held) hsr hnum h2c
    h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU sO
    hUw rfl hnO hX hoU rad2 hC2 he12 hk12 e2 he2 memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 hd4
    ho4 e4 he4 rad5 hC5 he15 hk15 e5 he5 memK5 new5 entry5 all5 hno5 htree5 hSh5 hnew5 xS mS sS
    hd7 e7 he7 hS12 own ho2' ho4' ho5' ho7' h9 h10
  have H1 := point_ledger_at_ocEnd (Cl' := Cl) (F := Fr)
    Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms c₀ stOf₁ tabP₁ Q b1 b2 b3 b4
    b5 b6 b7 b8 hbl e' base d hd ext err N₁ Ns links ps f MM gOf lo err₂ eM rank held Pw hlin matC
    Mg₁ MgZ PmZ ha hix hroom hk hr he hle hM hJ hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi
      hxW hsW hst R hbook htab hsh
    hg hH hpile mem rd n nO (shiftBook (tiedNumbers N₁ Ns).lo) X hS hsz hXb
  refine ledgerPaysOwn P₁ St Cl (Wit Cells Tok MsgT) (ckP .two) Fr _ _ _ _ true slots f (PT) _ _ _
    own _ _ ht hlift hop hf1 hfb (fun s h => ?_) hFR (fun a w => ?_) hown H1 H2 hRd
  · have h' : (PmZ.shape 0 s && (layX Q 0 s && X 0 s)) = true := h
    obtain ⟨h0, hb⟩ := Bool.and_eq_true_iff.1 h'
    obtain ⟨hl, hx⟩ := Bool.and_eq_true_iff.1 hb
    obtain ⟨z1, z2⟩ := hZ0 s h0
    show ((shape1 Q.par s && !notedU s) && (layX Q 1 s && X 1 s)) = true
    rw [z1, z2, hX01 s hx, layX_codes Q 0 1 s s rfl hl]
    rfl
  · exact extS_id _ _ _ _ _ _ _ _ true 0 (by decide) _ _ _

end Desc.K14.Law

#print axioms Desc.K14.Law.decK_key
#print axioms Desc.K14.Law.ledger_all
