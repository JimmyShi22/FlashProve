-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerAtSeat.lean: THE LEDGER's TOP AT A ROW THAT HOLDS THE SHARED CHAIN's OWN
BLOCKS: ledger_whole (Johnson/Desc/K14/Law/LedgerWhole.lean) WITH TWENTY-SIX BINDERS FEWER. The top
bears twenty-six binders on the forms of the pieces: eight blocks as letters (c2 … c8, c11), seven
"decides as", six equations on rounds, four "holds in the wrap", "exact" at the end, two "is a
lifted block" at the proximity tests. HERE THE EIGHT LETTERS ARE LAID (c_k := b_k.retype; c11 := the
proximity test's files' own last block, carried, in the flat list's wrap) AND THE EIGHTEEN FACTS
ARE HAD BY PROOF, FROM ONE EQUATION: hps: the row holds the blocks of (chainOf ch Q tests
K12.Seat.last).retype as a description's pieces do; tests is a free list.

  row_holds        what the equation gives without the tiling: the pieces 3, 6, 8, 11 hold the
    carried blocks in the wrap; the pieces 9, 10 hold lifted blocks.
  ledger_whole_at_seat   **the top.** One call of ledger_whole.
THE STATEMENT IS CUT BY PROGRAM out of ledger_whole's own file: its variable blocks, notations and
binders, with the twenty-six struck, c_k replaced by b_k.retype, and tests, hps added (ch is the
top's own letter). No other token is turned.
By calls: tests_two (Johnson/Desc/K14/Law/LedgerFormsAll.lean) · piece_retype_at (FlatRetype.lean) ·
retype_as, last_exact (LedgerForms.lean).
What is not claimed. ALL THE OTHER PREMISES OF ledger_whole STAND. That a file's description has
that chain as its shared chain. No law is paid here: binders are struck. NO MEMBER. No soundness of
a verifier.

-/
import Johnson.Desc.K14.Law.LedgerWhole
import Johnson.Desc.K14.Law.LedgerFormsAll

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
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

section
variable {P₁ Cl Cells Tok : Type} {Fr : Frame}

/-- **What the equation gives without the tiling.** -/
theorem row_holds (c : Model.Verify.Chains) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 t9 t10 : Block St
    Unit)
    (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (f pt x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hps : (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]).map (·.b) =
      (((chainOf c Q [t9, t10] last).retype (Cl' := Cl)).blocksInOrder.map below).map
        (Block.lift Prod.snd fun t s => (t.1, s))) :
    x3.b = heldW b3.retype ∧ x6.b = heldW b6.retype ∧ x8.b = heldW b8.retype ∧
      x11.b = heldW (bareOf (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10])).retype) ∧
      (∃ b₀ : Block St Cl, x9.b = b₀.lift Prod.snd fun t s => (t.1, s)) ∧
      (∃ b₀ : Block St Cl, x10.b = b₀.lift Prod.snd fun t s => (t.1, s)) := by
  have g := piece_retype_at (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) c Q b1 b2 b3 b4 b5
    b6 b7 b8 [t9, t10] last hbl hps
  obtain ⟨q3, e3, h3⟩ := g 2 b3 rfl
  obtain ⟨q6, e6, h6⟩ := g 5 b6 rfl
  obtain ⟨q8, e8, h8⟩ := g 7 b8 rfl
  obtain rfl : x3 = q3 := Option.some.inj e3
  obtain rfl : x6 = q6 := Option.some.inj e6
  obtain rfl : x8 = q8 := Option.some.inj e8
  rw [chainOf_eq c Q b1 b2 b3 b4 b5 b6 b7 b8 [t9, t10] last hbl] at hps
  exact ⟨h3, h6, h8, Option.some.inj (congrArg (fun L => L[11]?) hps),
    ⟨_, Option.some.inj (congrArg (fun L => L[9]?) hps)⟩,
    ⟨_, Option.some.inj (congrArg (fun L => L[10]?) hps)⟩⟩

end

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
  (nU : ℕ)
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
  (err₂ : Nat)
  (rank : ((Fin Q.par.S.fold.index.v → Bool) → Fin (Q.par.S.fold.index.code.r +
    Q.par.S.fold.index.code.ell) → GE) → Nat)
  (held : ((ixOf2 Q.par.S.fold err₂ 2852142980 rank).Row × Fin Q.par.S.fold.index.code.ell → GE) →
    Option Cells)
  (Pw : Where)
  (hlin : Pw.lin = Q.par.S)
  (matC : Cells → Nat → Nat → GE)
  (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
  (MgZ : MeaningS St P₁ (Wit Cells Tok MsgT))
  (PmZ : PromMeaning St)
  (hix : Q.par.S.fold.index.ok = true)
  (hroom : Q.par.S.matrixRows * 2 ^ Q.par.S.kLo ≤ Q.par.S.fold.index.plain)
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
  (hH : HeldTie Q.par err₂ 2852142980 rank held matC)
  (hpile : ∀ p y (w : Wit Cells Tok MsgT), ocEnd get N₁ Mg₁ links ps p y → R p → (get p).2.failed
    = none → pileStep stOf₁ tabP₁ Pw matC (get p) w → Mg₁.pileOne (get p) y w)
  (hpo : ∀ a (y y' : Strs) (w : Wit Cells Tok MsgT), Mg₁.pileOne a y w → Mg₁.pileOne a y' w)
variable
  (slots : ℕ) (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds)) (layU layO : TreeLay)
  (Y : ℕ → St → Bool)
variable
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
  (ht : Tiled (pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2) [x3, (pc1 (b4.retype (Cl' := Cl))
      base4 d4 ex4 er4), (pc2 (b5.retype (Cl' := Cl)) base5 d51
    d52 ex5 er5), x6, (pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7), x8, x9, x10, x11])
  (hlo : ∀ m, N.lo ≤ (N.tenant m).1)
  (tU : (N.tenant .oU).1 < x3.base)
  (tO : (N.tenant .oOmega).1 < x6.base)
  (tS : (N.tenant .oSp).1 < x6.base)
  (hS : Q.S.sharedSplitNeeded = true)
  (hnum : num .oU = nU)
  (xU xO : Mem)
  (hU : mem nU = some xU)
  (hO : mem sentU.size = some xO)
  (mU : xU ∈ ms)
  (mO : xO ∈ ms)
  (sU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
  (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (hUw : withU Q.S = some sentU)
  (hn0 : nU = 0)
  (hoU : ∀ z ∈ ms, SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 → oNo z = nU)
  (rad2 : ℕ → ℕ)
  (hC2 : condPort (parU Q sentU) rad2 = true)
  (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem)
  (new2 : List Mem)
  (entry2 : ∀ k, (memK2 k).1.l.get (memK2 k).2 = (shapeAt (parU Q sentU) k, rad2 k.val))
  (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
  (hno2 : ∀ k, sampledAt (parU Q sentU) k → oNo (memK2 k) = nU + k.val)
  (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
  (hSh2 : ∀ x ∈ new2, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) (b2.retype
      (Cl' := Cl))) base2
    d21 d22 (parU Q sentU).coordinates (errPort (parU Q sentU) rad2)).ShownAll G Q.codes x.1.l
    x.1.seat)
  (hnew2 : ∀ x ∈ ms, SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x ∈ new2)
  (ho4 : d4.opens = [])
  (rad5 : ℕ → ℕ)
  (hC5 : condPort (parO Q) rad5 = true)
  (memK5 : Fin (shapesOf (parO Q)).length → Mem)
  (new5 : List Mem)
  (entry5 : ∀ k, (memK5 k).1.l.get (memK5 k).2 = (shapeAt (parO Q) k, rad5 k.val))
  (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
  (hno5 : ∀ k, sampledAt (parO Q) k → oNo (memK5 k) = sentU.size + k.val)
  (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
  (hSh5 : ∀ x ∈ new5, (sendPiece (W := Wit Cells Tok MsgT) (F := Fr) (heldW (U := P₁) (b5.retype
      (Cl' := Cl))) base5
    d51 d52 (parO Q).coordinates (errPort (parO Q) rad5)).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ ms, SitsAt x (N.tenant m).1 (N.tenant m).2 →
    x ∈ new5)
  (xS : Mem)
  (mS : xS ∈ ms)
  (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)


set_option quotPrecheck false in
local notation "PT" => seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1
  base d ext err
set_option quotPrecheck false in
local notation "MM" =>
  [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := Cl)) base4 d4 ex4
      er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52 ex5 er5, x6,
    pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]
set_option quotPrecheck false in
local notation "PK" =>
  pmK (P14.codes Q) G (smpSt (P14.codes Q) oNo stSh) ms decT₂ (shiftBook (NumbersS.lo N)) Pm₀
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) nU (Array.size sentU) Q
    (XK Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, (places Q sentU).1 hUw⟩,
      shapeAt (parO Q) ⟨0, (places Q sentU).2.1⟩, shapeAt (parO Q) ⟨1, (places Q sentU).2.2 hS⟩, Y)
      (Array.size sentU))
set_option quotPrecheck false in
local notation "MK" =>
  mgK (P14.codes Q) G arr (smpSt (P14.codes Q) oNo stSh) ms decT₂ Mg₀ mem rd 2852142980
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) (Array.size sentU) Q
set_option quotPrecheck false in
local notation "EK" => exK (P14.codes Q) G arr (smpSt (P14.codes Q) oNo stSh) ms decT₂ c₀ N Fr

include G oNo ms decT₂ N Q Pm₀ Oc nU b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀ mem rd num sentU get
    smp₁ ms₁ xW stOf₁ tabP₁ base d ext err N₁ Ns links ps gOf lo err₂ rank held Pw hlin matC Mg₁ MgZ
    PmZ hix hroom hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi hxW hsW hst R hbook htab hsh hg
    hH hpile hpo slots r9 r10 layU layO Y f x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4 d4 ex4
    er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hS hnum xU xO hU hO mU mO sU sO hUw
    hn0 hoU rad2 hC2 memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 ho4 rad5 hC5 memK5 new5 entry5
    all5 hno5 htree5 hSh5 hnew5 xS mS sS

/-- **The ledger's top at a row that holds the shared chain's own blocks.** -/
theorem ledger_whole_at_seat
    (eN : N = tiedNumbers N₁ Ns) (eD : decT₂ = decK Q.par err₂ 2852142980 rank held)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eP : Pm₀ = pmPoint Q.codes G (smpSt Q.codes oNo stSh) ms Q.par err₂ 2852142980 rank held
      (fun s : St => s.st) (fun s : St => shiftBook N.lo s.book) PmZ)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes oNo stSh) ms (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd sentU.size Q) Q.par 2852142980 gOf err₂ 2852142980 rank held Pw
          matC MgZ))
    (M : MeaningS St P₁ (Wit Cells Tok MsgT)) (eMZ : MgZ = mgZ Q.codes arr mem rd num M)
    (P : PromMeaning St) (ePZ : PmZ = pmZ Q.par P)
    (hop : ∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j)
    (hf1 : ∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) (hfb : (PT).base = f.base)
    (hcap : EachCapped 128 (f :: (PT) :: MM))
    (Wr : Rounds) (hIx : indexB Q.par.S = true) (hdW : atW Wr 0 = some (d.entry, d.kind))
    (hn : slots ≤ 64) {rad work : ℕ} (hKR : K14Rounds Q.S Wr rad cMax work)
    (hN64 : pointNB Q.S Wr cMax64 64 = true)
    (hOB : OursBelow Q Wr sentU rad2 rad5)
    (t2 : Ties Wr 2 [d21, d22]) (t4 : Ties Wr 4 [d4]) (t5 : Ties Wr 5 [d51, d52])
    (t7 : Ties Wr 7 [d7]) {fl : ℕ}
    (hsL : sendsLB fl ⟨Q.set, Q.scope, Q.codes, Q.S, 0, [(1, 0)]⟩ Wr = true)
    (b9 : Err.Below (r9 x9.ds) ((2 : ENNReal)⁻¹ ^ 128))
    (b10 : Err.Below (r10 x10.ds) ((2 : ENNReal)⁻¹ ^ 128))
    (hlU : layTrees Q.codes sentU = some layU)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (hm : Q.par.S.masksAhead = true)
    (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)
    (hok : Q.S.ok = true) (ch : Model.Verify.Chains)
    (hY01 : ∀ s, Y 0 s = true → Y 1 s = true)
    (hY12 : ∀ (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → Y 1 a.1.2 = true → Y 2 y.1.2 = true)
    (hYH : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) (onQ₂ N (PK) Oc true f ((PT) :: MM))
      [b1, b2, b3, b4, b5, b6, b7, b8] Y)
    (hb2 : base ≤ base2)
    (nWU : arr N.w.1 N.w.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2)
    (nWS : arr N.w.1 N.w.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2)
    (nIU : arr N.index.1 N.index.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2)
    (nIS : arr N.index.1 N.index.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2)
    (ev9 : EvKept N (MK) (PK) Oc true f ((PT) :: MM) (EK) 9)
    (ev10 : EvKept N (MK) (PK) Oc true f ((PT) :: MM) (EK) 10)
    (πA : P12)
    (hbA : Alike (VerifiableInference.Desc.Sound.held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts πA :
      Block T12 Unit))) x9.b)
    (heA : πA.early = true)
    (ha1A : πA.answers = 1)
    (hms : ∀ z ∈ ms, oNo z = 0 ∨ oNo z = sentU.size ∨ oNo z = sentU.size + 1)
    (t₁A t₂A cA : ℕ)
    (LA mCA mSA mWA : Sg → ℕ → ℕ)
    (radA : Sg → ℕ)
    (rdNA : ℕ → ℕ)
    (dBA : RDT)
    (dtA : List RDT)
    (eA : ℕ)
    (εtA : Err (uLT (ckP .two) dtA))
    (rA : Fmt.M1.Stage → ℕ)
    (h0A : x9.back = [])
    (hdsA : x9.ds = dBA :: dtA)
    (herrA : HEq (r9 x9.ds) ((eA, εtA) : Err (uLT (ckP .two) (dBA :: dtA))))
    (hAA : AtPlace Fr πA (VerifiableInference.Desc.numAt t₁A t₂A cA) LA mCA mSA mWA radA x9.base
      dBA dtA εtA)
    (hrA : ∀ s, radA s = rA s.st)
    (hjA : johOk πA rA = true)
    (hb1A : batOneOk πA = true)
    (hleA : batV0 πA rA * (bsRound .two dBA.entry dBA.kind).w ≤ eA)
    (hoA : πA.nums.ownMask = false)
    (hPA : ownLabelsB πA = true)
    (n2A : ∀ n, n < πA.nums.free → VerifiableInference.Desc.numAt t₁A t₂A cA (.own n) < x9.base)
    (n3A : ∀ c' n, (c' + 1, n) ∈ πA.before → VerifiableInference.Desc.numAt t₁A t₂A cA (.taken c'
      n) < x9.base)
    (hftA : πA.nums.firstTree = Q.par.toGPar.firstTree)
    (hl : Q.codes.lengthsOk = true)
    (hn1 : num .oOmega = sentU.size)
    (hn2 : num .oSp = sentU.size + 1)
    (hmS : mem (sentU.size + 1) = some xS)
    (coreA : TupleNine Q.codes G ms N (pmE decT₂ Pm₀ Q Q.S.fold.columns nU sentU.size (shapeAt
      (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q sentU).2.1⟩,
      shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) Oc oNo Q sentU layU layO f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err)
      :: [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := Cl)) base4
          d4 ex4 er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52 ex5 er5,
      x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) mem rd πA t₁A t₂A cA radA
          rdNA x9)
    (hNA : ((mineS N ms true 9).map (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapSA : apartAt N arr true 9 (.msg .oSp) = true)
    (hapOA : apartAt N arr true 9 (.msg .oOmega) = true)
    (sbA : ∀ m, m = Msg2.oOmega ∨ m = .oSp → SentBefore N f ((seatedPiece (W := Wit Cells Tok
      MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err) :: [pc2 (b2.retype (Cl' := Cl))
          base2 d21 d22 ex2 er2,
      x3, pc1 (b4.retype (Cl' := Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52
          ex5 er5, x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8,
      x9, x10, x11]) 9 x9 m)
    (hY10A : ∀ a τ b, onQ₂ N (pmX Q.codes G ms N (pmE decT₂ Pm₀ Q Q.S.fold.columns nU sentU.size
      (shapeAt (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q
      sentU).2.1⟩, shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) oNo Q sentU layU layO) Oc
      true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d
      ext err) :: [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' :=
          Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52
      ex5 er5, x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) 9 a →
          x9.ior.red.out a τ = some b →
      Y 10 b.1.2 = true)
    (πB : P12)
    (hbB : Alike (VerifiableInference.Desc.Sound.held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts πB :
      Block T12 Unit))) x10.b)
    (heB : πB.early = true)
    (ha1B : πB.answers = 1)
    (t₁B t₂B cB : ℕ)
    (LB mCB mSB mWB : Sg → ℕ → ℕ)
    (radB : Sg → ℕ)
    (rdNB : ℕ → ℕ)
    (dBB : RDT)
    (dtB : List RDT)
    (eB v₀B : ℕ)
    (εtB : Err (uLT (ckP .two) dtB))
    (h0B : x10.back = [])
    (hdsB : x10.ds = dBB :: dtB)
    (herrB : HEq (r10 x10.ds) ((eB, εtB) : Err (uLT (ckP .two) (dBB :: dtB))))
    (hAB : AtPlaceOwn Fr πB (VerifiableInference.Desc.numAt t₁B t₂B cB) LB mCB mSB mWB radB
      x10.base dBB dtB εtB)
    (hPayB : PayPub πB radB dBB.entry.rows v₀B)
    (h1B : Fmt.dsOf dBB.entry dBB.kind = [.elem, .trits 0])
    (hlogB : dBB.entry.logN ≤ 64)
    (hleB : v₀B * (bsRound .two dBB.entry dBB.kind).w ≤ eB)
    (hoB : πB.nums.ownMask = true)
    (hPB : ownLabelsB πB = true)
    (n2B : ∀ n, n < πB.nums.free → VerifiableInference.Desc.numAt t₁B t₂B cB (.own n) < x10.base)
    (n3B : ∀ c' n, (c' + 1, n) ∈ πB.before → VerifiableInference.Desc.numAt t₁B t₂B cB (.taken c'
      n) < x10.base)
    (hftB : πB.nums.firstTree = Q.par.toGPar.firstTree)
    (coreB : TupleTen Q.codes G ms N (pmE decT₂ Pm₀ Q Q.S.fold.columns nU sentU.size (shapeAt
      (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q sentU).2.1⟩,
      shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) Oc oNo Q sentU layU layO f
      ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext err)
      :: [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := Cl)) base4
          d4 ex4 er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52 ex5 er5,
      x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) mem rd πB t₁B t₂B cB radB
          rdNB x10)
    (hNB : ((mineS N ms true 10).map (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapOB : apartAt N arr true 10 (.msg .oOmega) = true)
    (sbB : SentBefore N f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁)
      b1 base d ext err) :: [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype
          (Cl' := Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := Cl))
      base5 d51 d52 ex5 er5, x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) 10
          x10 .oOmega)
    (hY11B : ∀ a τ b, onQ₂ N (pmX Q.codes G ms N (pmE decT₂ Pm₀ Q Q.S.fold.columns nU sentU.size
      (shapeAt (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q
      sentU).2.1⟩, shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) oNo Q sentU layU layO) Oc
      true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d
      ext err) :: [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' :=
          Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52
      ex5 er5, x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) 10 a →
          x10.ior.red.out a τ = some b
      → Y 11 b.1.2 = true)
    (tests : List (Block St Unit))
    (hps : (f :: (PT) :: MM).map (·.b) =
      (((chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder.map
          below).map
        (Block.lift Prod.snd fun t s => (t.1, s))) :
    EachLawsBN (keyAt Prod.snd N.lo f ((PT) :: MM)) (onQ₂ N (PK) Oc true f ((PT) :: MM))
      (stepAt N (MK) (PK) Oc true f ((PT) :: MM) (extOf N f ((PT) :: MM) (EK))) slots 0
      (f :: (PT) :: MM) := by
  obtain ⟨t9, t10, rfl⟩ := tests_two ch Q b1 b2 b3 b4 b5 b6 b7 b8 tests
      VerifiableInference.Desc.K12.Seat.last hbl f (PT) _ x3 _ _ x6 _ x8 x9 x10 x11 hps
  obtain ⟨q3, q6, q8, q11, q9, q10⟩ := row_holds ch Q b1 b2 b3 b4 b5 b6 b7 b8 t9 t10
      VerifiableInference.Desc.K12.Seat.last hbl f (PT) _ x3 _ _ x6 _ x8 x9 x10 x11 hps
  exact ledger_whole G oNo ms decT₂ N Q Pm₀ Oc nU b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀ mem rd num
      sentU get smp₁ ms₁ xW stOf₁ tabP₁ base d ext err N₁ Ns links ps gOf lo err₂ rank held Pw hlin
      matC Mg₁ MgZ PmZ hix hroom hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi hxW hsW hst R
      hbook htab hsh hg hH hpile hpo slots r9 r10 layU layO Y b2.retype b3.retype b4.retype
      b5.retype b6.retype b7.retype b8.retype (bareOf (VerifiableInference.Desc.K12.Seat.last ([b1,
      b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10])).retype) f x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2
      base4 d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 ht hlo tU tO tS hS hnum (retype_as b2)
      (retype_as b3) (retype_as b4) (retype_as b5) (retype_as b6) (retype_as b7) (retype_as b8) rfl
      rfl rfl rfl rfl rfl q3 q6 q8 q11 (last_exact _) xU xO hU hO mU mO sU sO hUw hn0 hoU rad2 hC2
      memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 ho4 rad5 hC5 memK5 new5 entry5 all5 hno5 htree5
      hSh5 hnew5 xS mS sS eN eD eO eP eM₀ M eMZ P ePZ q9 q10 hop hf1 hfb hcap Wr hIx hdW hn hKR hN64
      hOB t2 t4 t5 t7 hsL b9 b10 hlU hlO hm hp hok ch hY01 hY12 hYH hb2 nWU nWS nIU nIS ev9 ev10 πA
      hbA heA ha1A hms t₁A t₂A cA LA mCA mSA mWA radA rdNA dBA dtA eA εtA rA h0A hdsA herrA hAA hrA
      hjA hb1A hleA hoA hPA n2A n3A hftA hl hn1 hn2 hmS coreA hNA hapSA hapOA sbA hY10A πB hbB heB
      ha1B t₁B t₂B cB LB mCB mSB mWB radB rdNB dBB dtB eB v₀B εtB h0B hdsB herrB hAB hPayB h1B hlogB
      hleB hoB hPB n2B n3B hftB coreB hNB hapOB sbB hY11B

end Desc.K14.Law

#print axioms Desc.K14.Law.row_holds
#print axioms Desc.K14.Law.ledger_whole_at_seat
