-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerAtCap.lean: THE TWELVE PIECES OF THE SHARED CHAIN, EACH WITH ITS LAW FOR
A BATCH AT THE CAP 128, FOR UP TO 64 SLOTS, AT ONE FILLING, WITH THE RADIUS WRITTEN. Two theorems.
A joining of other files' laws: no chance is counted here.

  ledger_at_cap    EachLawsBN … slots 0 (f :: PT :: MM) (Johnson/Desc/Sound/KeysByMake.lean): each
                   piece has LeadsBN for slots slots at its own err; by hcap that err is Err.cap 128
                   of its written rounds; slots ≤ 64. THE TERM: eachLawsBN_atCap 128
                   (Johnson/Desc/Sound/SharedJointCountLedger.lean) applied to hcap, to
                   eachOwnBelow_all (Johnson/Goal/Numbers/K14OwnAllAt.lean) and to ledger_all
                   (Johnson/Desc/K14/Law/LedgerAll.lean).
  cap_roads_meet   the law at "LIN point" at the cap as it is found in the seat's own list of pieces
                   (point_ledger_at_cap, Johnson/Desc/K14/Law/PointAtLedgerCap.lean) has the form
                   of clause 1 of that end, to the letter. It costs hps (the pieces hold the shared
                   chain's own blocks as a description lays them). ledger_at_cap does not need it: a
                   statement does not hold its proof: this theorem is a check that the two fit.
WHAT IS LAID, AGAINST ledger_all: e' := 2852142980 (in the law at "LIN point", in "near" and in
"LOC"'s count alike) · n := Q.S.fold.columns · own := ownAll Q sentU rad2 rad5 slots r9 r10: so the
counts at 2, 4, 5, 7 stand WITH EQUALITY (errPort …; (2 ^ logN - 2852142980 - 1) ^ columns; kRow ·
q ^ (kRow - 1)). NO PREMISES ANY MORE: he, he2, he4, he5, he7, ho2', ho4', ho5', ho7', hown; and hd,
hd4, hd7 (what the three written rounds send and draw), which follow from hKR and the ties.
WORK IS COUNTED IN THE CAP. At "LOC" the share 2⁻¹ ^ 128 holds only with the written round's bits of
work (28 at the release's list); "LIN point" and "LIN zeta" bear none; the two rounds of seeds bear
the sendings' own.
WHAT IS NEW AMONG THE PREMISES: hcap (each piece's err is the cap) · hIx (the shape's table is the
release's) · hdW, t2, t4, t5, t7: THE ENTRY AND THE KIND, and no more, of d, d21, d4, d51, d7 are
those of the rounds 0, 1, 3, 4, 6 of a written list Wr (d22, d52 are tied to nothing) · hn (slots ≤
64) · hOB, hKR, hNB (three tests at Wr; of hKR's letters rad and work nothing is asked here) · b9,
b10 (the two proximity tests' entries are below 2⁻¹ ^ 128: no file beneath pays them).
WHAT IS PROVED AND WHAT IS ONLY HANDED THROUGH: as in LedgerAll.lean's head: AT 9 AND 10 NOTHING OF
THE LAW IS PROVED: it is h9, h10, with hRd, hx9, hx10 and b9, b10.
Limits. All of ledger_all's other premises stand, the six equations of letters among them. That the
seated description's Q, d, Wr are the written ones; that the planner takes its prices at that
radius; that slots is the plan's number; who makes the promise at border 0: not said. eM, err₂,
rank stay letters. The full size alone. No instance is shown at which all premises hold together.
It is not "128 bits a step": it says that UNDER THESE PREMISES each of the twelve clauses holds at
the cap. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerAll
import Johnson.Desc.K14.Law.PointAtLedgerCap
import Johnson.Goal.Numbers.K14OwnAllAt

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
  (nU nO : ℕ)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
variable
  (arr : ℕ → ℕ → ℕ)
  (c₀ : Cells)
  (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT))
  (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
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
  (hle : 2852142980 ≤ eM)
  (hM : eM < 2 ^ (codeOf Q.par.S.fold.index.code).a - ((codeOf Q.par.S.fold.index.code).r +
    (codeOf Q.par.S.fold.index.code).l) + 1)
  (hJ : InJohnson (2 ^ (codeOf Q.par.S.fold.index.code).a) (2 ^ (codeOf
    Q.par.S.fold.index.code).a - ((codeOf Q.par.S.fold.index.code).r + (codeOf
    Q.par.S.fold.index.code).l) + 1) 2852142980)
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
  (slots : ℕ) (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds))
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
    oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀ Q.S.fold.columns nU nO Q X) Oc true f ((seatedPiece
    (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err) :: [(pc2 c2
    base2 d21 d22 ex2 er2), x3, (pc1 c4 base4 d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6,
    (pc1 c7 base7 d7 ex7 er7), x8, x9, x10, x11])) [b1, b2, b3, b4, b5, b6, b7, b8] X)
  (hoU : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 → oNo z = nU)
  (rad2 : ℕ → ℕ)
  (hC2 : condPort (parU Q sentU) rad2 = true)
  (he12 : d21.entry = seedEntry (parU Q sentU))
  (hk12 : d21.kind = .seeds)
  (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem)
  (new2 : List Mem)
  (entry2 : ∀ k, (memK2 k).1.l.get (memK2 k).2 = (shapeAt (parU Q sentU) k, rad2 k.val))
  (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
  (hno2 : ∀ k, sampledAt (parU Q sentU) k → oNo (memK2 k) = nU + k.val)
  (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
  (hSh2 : ∀ x ∈ new2, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c2) base2
    d21 d22 (parU Q sentU).coordinates (errPort (parU Q sentU) rad2)).ShownAll G Q.codes x.1.l
    x.1.seat)
  (hnew2 : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new2)
  (ho4 : d4.opens = [])
  (rad5 : ℕ → ℕ)
  (hC5 : condPort (parO Q) rad5 = true)
  (he15 : d51.entry = seedEntry (parO Q))
  (hk15 : d51.kind = .seeds)
  (memK5 : Fin (shapesOf (parO Q)).length → Mem)
  (new5 : List Mem)
  (entry5 : ∀ k, (memK5 k).1.l.get (memK5 k).2 = (shapeAt (parO Q) k, rad5 k.val))
  (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
  (hno5 : ∀ k, sampledAt (parO Q) k → oNo (memK5 k) = nO + k.val)
  (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
  (hSh5 : ∀ x ∈ new5, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) c5) base5
    d51 d52 (parO Q).coordinates (errPort (parO Q) rad5)).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 →
    x ∈ new5)
  (xS : Mem)
  (mS : xS ∈ ms)
  (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
  (h9 : ClauseAt N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
    Q.S.fold.columns nO Q) (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀
    Q.S.fold.columns nU nO Q X) Oc true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F
    := Fr) (P₁ := P₁) b1 base d ext err) :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4
    d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10,
    x11]) (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 9 x9 ((ownAll Q sentU
    rad2 rad5 slots r9 r10) 9 x9))
  (h10 : ClauseAt N (mgK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
    Q.S.fold.columns nO Q) (pmK Q.codes G (smpSt Q.codes oNo stSh) ms decT₂ (shiftBook N.lo) Pm₀
    Q.S.fold.columns nU nO Q X) Oc true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F
    := Fr) (P₁ := P₁) b1 base d ext err) :: [(pc2 c2 base2 d21 d22 ex2 er2), x3, (pc1 c4 base4
    d4 ex4 er4), (pc2 c5 base5 d51 d52 ex5 er5), x6, (pc1 c7 base7 d7 ex7 er7), x8, x9, x10,
    x11]) (exK Q.codes G arr (smpSt Q.codes oNo stSh) ms decT₂ c₀ N Fr) 10 x10 ((ownAll Q sentU
    rad2 rad5 slots r9 r10) 10 x10))

set_option quotPrecheck false in
local notation "PT" => seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1
  base d ext err
set_option quotPrecheck false in
local notation "MM" =>
  [pc2 c2 base2 d21 d22 ex2 er2, x3, pc1 c4 base4 d4 ex4 er4, pc2 c5 base5 d51 d52 ex5 er5, x6,
    pc1 c7 base7 d7 ex7 er7, x8, x9, x10, x11]
set_option quotPrecheck false in
local notation "PK" =>
  pmK (P14.codes Q) G (smpSt (P14.codes Q) oNo stSh) ms decT₂ (shiftBook (NumbersS.lo N)) Pm₀
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) nU nO Q X
set_option quotPrecheck false in
local notation "MK" =>
  mgK (P14.codes Q) G arr (smpSt (P14.codes Q) oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) nO Q
set_option quotPrecheck false in
local notation "EK" => exK (P14.codes Q) G arr (smpSt (P14.codes Q) oNo stSh) ms decT₂ c₀ N Fr

include G oNo ms decT₂ N Q Pm₀ Oc nU nO b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀ mem rd num sentU X
  get smp₁ ms₁ xW stOf₁ tabP₁ base d ext err N₁ Ns links ps gOf lo err₂ eM rank held Pw hlin
  matC Mg₁ MgZ PmZ ha hix hroom hk hr hle hM hJ hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi
    hxW hsW hst R hbook htab hsh
  hg hH hpile hS hn0

/-- **The two roads at block 1 meet**: the law at "LIN point" at the cap, found in the seat's own
list of pieces, has clause 1's form to the letter. -/
theorem cap_roads_meet
    (eN : N = tiedNumbers N₁ Ns) (eD : decT₂ = decK Q.par err₂ eM rank held)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eP : Pm₀ = pmPoint Q.codes G (smpSt Q.codes oNo stSh) ms Q.par err₂ eM rank held
      (fun s : St => s.st) (fun s : St => shiftBook N.lo s.book) PmZ)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd nO Q) Q.par 2852142980 gOf err₂ eM rank held Pw matC MgZ))
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hXb : ∀ (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → X 1 a.1.2 = true → X 2 y.1.2 = true)
    (ch : Model.Verify.Chains) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hps : (f :: (PT) :: MM).map (·.b) =
      (((chainOf ch Q tests last).retype (Cl' := Cl)).blocksInOrder.map below).map
        (Block.lift Prod.snd fun t s => (t.1, s)))
    (Wr : Rounds) (hIx : indexB Q.par.S = true) (hdW : atW Wr 0 = some (d.entry, d.kind))
    (hn : slots ≤ 64) {rad work : ℕ} (hKR : K14Rounds Q.S Wr rad cMax work)
    (hNB : pointNB Q.S Wr cMax64 64 = true) :
    (PT).ior.red.LeadsBN (keyAt Prod.snd N.lo f ((PT) :: MM) 1)
      (onQ₂ N (PK) Oc true f ((PT) :: MM) 1)
      (stepAt N (MK) (PK) Oc true f ((PT) :: MM) (extOf N f ((PT) :: MM) (EK)) 1) slots
      (Err.cap 128 (uLT (ckP .two) [d])) := by
  have hdat : ∀ q, (f :: (PT) :: MM)[1]? = some q → q.ds = [d] ∧ q.back = [] ∧ lo ≤ q.base ∧
      N₁.w.1 < q.base ∧ N₁.index.1 < q.base := by
    intro q hq
    obtain rfl : (PT) = q := Option.some.inj hq
    exact ⟨rfl, rfl, hloB, hw, hi⟩
  subst eP eM₀ eO eD eN hn0
  obtain ⟨base', ext', err', r', hl, C1⟩ := point_ledger_at_cap (Cl' := Cl) (F := Fr)
    Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms c₀ stOf₁ tabP₁ Q b1 b2 b3 b4
    b5 b6 b7 b8 hbl d (hKR.point d hdW).1 N₁ Ns links ps lo f ((PT) :: MM) ch tests last hps hdat
    gOf err₂ eM rank held Pw hlin matC Mg₁ MgZ PmZ ha hix hroom hk hr hle hM hJ hpin hwrow
      hevalLaid hwSits h2 h3 hread hxW
    hsW hst R hbook htab hsh hg hH hpile Wr (pointCap_of hIx hKR hNB) hdW slots hn mem rd
      Q.S.fold.columns
    nO (shiftBook (tiedNumbers N₁ Ns).lo) X hS hsz hXb
  obtain ⟨h1, -⟩ := List.cons.inj hl
  simp only [seatedPiece, Piece.mk.injEq, heq_eq_eq, true_and] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  exact C1

include slots r9 r10 c2 c3 c4 c5 c6 c7 c8 c11 f x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4
  ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hS hnum h2c h3c h4c h5c h6c h7c
  h8c h2r h3r h4r h5r h6r h8r hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU sO hUw hn0 hnO hX hoU
  rad2 hC2 he12 hk12 memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 ho4 rad5 hC5 he15 hk15 memK5
  new5 entry5 all5 hno5 htree5 hSh5 hnew5 xS mS sS h9 h10

/-- **The twelve at the cap.** -/
theorem ledger_at_cap
    (eN : N = tiedNumbers N₁ Ns) (eD : decT₂ = decK Q.par err₂ eM rank held)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eP : Pm₀ = pmPoint Q.codes G (smpSt Q.codes oNo stSh) ms Q.par err₂ eM rank held
      (fun s : St => s.st) (fun s : St => shiftBook N.lo s.book) PmZ)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd nO Q) Q.par 2852142980 gOf err₂ eM rank held Pw matC MgZ))
    (hsr : SampleRides MgZ num) (hS12 : ∀ s, PmZ.shape 11 s = true → PmZ.shape 12 s = true)
    (hZ0 : ∀ s, PmZ.shape 0 s = true → shape1 Q.par s = true ∧ notedU s = false)
    (hX01 : ∀ s, X 0 s = true → X 1 s = true)
    (hx9 : ∃ b₀ : Block St Cl, x9.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (hx10 : ∃ b₀ : Block St Cl, x10.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (hop : ∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j)
    (hf1 : ∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) (hfb : (PT).base = f.base)
    (hFR : FrontRides N (MK) (PK) Oc true f ((PT) :: MM))
    (hRd : EachRides N (MK) (PK) Oc true f ((PT) :: MM) (EK) 2 MM)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hXb : ∀ (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → X 1 a.1.2 = true → X 2 y.1.2 = true)
    (hcap : EachCapped 128 (f :: (PT) :: MM))
    (Wr : Rounds) (hIx : indexB Q.par.S = true) (hdW : atW Wr 0 = some (d.entry, d.kind))
    (hn : slots ≤ 64) {rad work : ℕ} (hKR : K14Rounds Q.S Wr rad cMax work)
    (hNB : pointNB Q.S Wr cMax64 64 = true)
    (hOB : OursBelow Q Wr sentU rad2 rad5)
    (t2 : Ties Wr 2 [d21, d22]) (t4 : Ties Wr 4 [d4]) (t5 : Ties Wr 5 [d51, d52])
    (t7 : Ties Wr 7 [d7])
    (b9 : Err.Below (r9 x9.ds) ((2 : ENNReal)⁻¹ ^ 128))
    (b10 : Err.Below (r10 x10.ds) ((2 : ENNReal)⁻¹ ^ 128)) :
    EachLawsBN (keyAt Prod.snd N.lo f ((PT) :: MM)) (onQ₂ N (PK) Oc true f ((PT) :: MM))
      (stepAt N (MK) (PK) Oc true f ((PT) :: MM) (extOf N f ((PT) :: MM) (EK))) slots 0
      (f :: (PT) :: MM) := by
  have hef : efIx Q.par err₂ eM rank 2852142980 = efReal := by
    unfold efIx
    exact efForm_eq hIx
  have hown : (ownAll Q sentU rad2 rad5 slots r9 r10) 1 (PT) = Err.add
      ((vecMaps d Q.par.S.kCol).err
        ((efIx Q.par err₂ eM rank 2852142980 * Fintype.card GE ^ Q.par.S.kLo, ()) : Nat × Unit))
      (Err.times slots ((vecMaps d Q.par.S.kCol).err
        ((Q.par.S.kCol * Fintype.card GE ^ (Q.par.S.kCol - 1), ()) : Nat × Unit))) := by
    rw [hef]
    exact own_one Q.S slots d
  exact eachLawsBN_atCap 128 _ _ _ slots (ownAll Q sentU rad2 rad5 slots r9 r10) _ 0 hcap
    (eachOwnBelow_all hOB hKR hNB slots hn r9 r10 f (PT) _ x3 _ _ x6 _ x8 x9 x10 x11
      (fun d' h => by cases h; exact hdW) t2 t4 t5 t7 b9 b10)
    (ledger_all
      G oNo ms decT₂ N Q Pm₀ Oc Q.S.fold.columns nU nO b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀ mem
      rd 2852142980 num sentU X get smp₁ ms₁ xW stOf₁ tabP₁ base d (hKR.point d hdW).1 ext
      err N₁ Ns links ps gOf lo err₂ eM rank held Pw hlin matC Mg₁ MgZ PmZ ha hix hroom hk hr (by
      decide) hle hM hJ hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi hxW hsW hst R hbook
        htab hsh hg hH hpile c2 c3 c4 c5 c6 c7
      c8 c11 f x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4 ex4 er4 base5 d51 d52 ex5 er5
      base7 d7 ex7 er7 ht hlo tU tO tS hS hnum h2c h3c h4c h5c h6c h7c h8c h2r h3r h4r h5r h6r h8r
      hx3 hx6 hx8 hx11 he11 xU xO hU hO mU mO sU sO hUw hn0 hnO hX hoU rad2 hC2 he12 hk12 (errPort
      (parU Q sentU) rad2) (Nat.le_refl _) memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 (hKR.loc
      d4 (t4.2.1 d4 rfl rfl)).1 ho4 ((2 ^ Q.S.fold.index.code.logN - recordRadius - 1) ^
      Q.S.fold.columns) (Nat.le_refl _) rad5 hC5 he15 hk15 (errPort (parO Q) rad5) (Nat.le_refl _)
      memK5 new5 entry5 all5 hno5 htree5 hSh5 hnew5 xS mS sS (hKR.zeta d7 (t7.2.2.2 d7 rfl rfl)).1
      (Q.S.kRow * Fintype.card GE ^ (Q.S.kRow - 1)) (Nat.le_refl _) (ownAll Q sentU rad2 rad5
      slots r9 r10) rfl rfl rfl rfl h9 h10 slots eN eD eO eP eM₀ hsr hS12 hZ0 hX01 hx9 hx10 hop
      hf1 hfb hFR hown hRd hsz hXb)

end Desc.K14.Law

#print axioms Desc.K14.Law.cap_roads_meet
#print axioms Desc.K14.Law.ledger_at_cap
