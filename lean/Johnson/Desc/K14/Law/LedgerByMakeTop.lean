-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerByMakeTop.lean: THE LEDGER's TOP AT THE MAKER's CUT: ledger_whole_at_sh
(Johnson/Desc/K14/Law/LedgerAtSeat.lean) WITH 7 PREMISES ON ITS ROW OF PIECES STRUCK: ht · ho4 · hop
· hf1 · hfb · hcap · hps: they are facts of how the pieces of a description (the IOP as written in
Lean) are made. One call of ledger_whole_at_sh.
THE STATEMENT IS CUT BY PROGRAM out of ledger_whole_at_sh's own file: its variable blocks, notations
and binders, with these struck, the letter Fr replaced by the frame of the cut (frameAt Dw (allOf
Dw) Dw.key₂ Tt.ft₂), and the binders of the make added. No other token is turned.
IN THEIR PLACE: a description Fd with Fd.data fileN = .ok Dw and Fd.sealLast (IT ENTERS BY ITS DATA
AND ITS DECLARED ROUNDS ALONE: no type of a state of Fd's is asked to be the ledger's) · Tt: a Three
at Dw that is the maker's cut (IsCut) at blocks whose declared rounds are Fd's (g₁ g₂ g₃) · AtCap
rest₂t · hrow: the shared row's blocks are the seated chain's, below and lifted · N.lo = Dw.t₁ ·
hpf, hlf: THE TWO EQUATIONS OF LETTERS: the cut's shared row IS f :: PT :: MM.
  front_of_chain   the seated chain's first block says "ok" and declares no round: by its text
By calls: row_of_cut · front_of_tiled · sends_declare · send_facts · none_opened
(Johnson/Desc/K14/Law/LedgerRowOfCut.lean).
  fieldF                     the proof file's description by the maker's own text (ProofFile.fileDescBy)
  at ANY seat of the shared chain whose state is the kind's St and whose chain is the seated chain
  ledger_whole_fills_field   **THE LEDGER's END IS RowsTiedR.shared_joint_count's SENTENCE, IN
  THE FIELD's OWN TEXT, AT THE FIELD's OWN LIST OF PIECES**: TT := atDesc F₀ (piecesAt (ckP .two) F₀
  Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd), F₀ := fieldF …: EachLawsBN
  (keyAt Prod.snd Dw.t₁ TT.p₂ TT.l₂) (onQ₂ …) (stepAt …) slots 0 (TT.p₂ :: TT.l₂): g₁ g₂ g₃ · hcut ·
  hcp · hrow are gone there (seat_layer, Johnson/Desc/K14/Law/LedgerSeatLayer.lean); in: the three
  chains' sub-protocols by name (h₁f h₂f h₃f)
What is not claimed. That the table's (PLR).on₂ | (PLR).Q₂ are onQ₂ | stepAt at this filling.
That the seated description is fieldF at some seat (LedgerSeatIs.lean says it of onlineDescription's). ALL
THE OTHER PREMISES OF ledger_whole_at_sh STAND. That letters with hpf, hlf exist (row_by_make with
row_forms_all give them). No law is paid here: binders are struck. NO MEMBER. No soundness of a
verifier.

-/
import Johnson.Desc.K14.Law.LedgerAtSh
import Johnson.Desc.K14.Law.LedgerSeatLayer
import Johnson.Desc.ProofFile.Frames1

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


/-- **The seated chain's first block says "ok" and declares no round.** -/
theorem front_of_chain {Cl : Type} (ch : Model.Verify.Chains) (Q : P14) (tests : List (Block St
    Unit))
    (last : List (Block St Unit) → Block St Unit) :
    ∃ (fb : Block St Cl) (restB : List (Block St Cl)),
      ((chainOf ch Q tests last).retype (Cl' := Cl)).blocksInOrder = fb :: restB ∧
      (∀ s rs gs, fb.decide s rs gs = .ok s) ∧ fb.rounds = [] :=
  ⟨_, _, rfl, fun _ _ _ => rfl, rfl⟩

section ByMake

variable (rU rO rSp t₁A : ℕ) (layU layO : TreeLay) (sentU : Array OracleNotice)
variable {P₀ : Type}
variable
  {P₁ Cl Xi Cells Tok : Type}
variable
  {XiF : Type} (Fd : FileDescription XiF) (fileN : String) (Dw : WholeD) {Yt S₁t S₃t X₁t X₂t : Type}
  (Tt : Three (ckP .two) Dw (allOf Dw) Yt S₁t (P₁ × St) S₃t X₁t X₂t Cl (Wit Cells Tok MsgT))
variable
  (G : FileDescription Xi)
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
  (ext : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Tr (uLT (ckP .two) [d]) → Wit
      Cells Tok MsgT → Wit Cells Tok
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
  (slots : ℕ) (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds))
  (Y : ℕ → St → Bool)
variable
  (f x3 x6 x8 x9 x10 x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) Cl (Wit
      Cells Tok MsgT))
  (base2 : ℕ)
  (d21 d22 : RDT)
  (ex2 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d21,
      d22]) → Wit Cells Tok MsgT → Wit
    Cells Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22]))
  (base4 : ℕ)
  (d4 : RDT)
  (ex4 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d4]) →
      Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er4 : Err (uLT (ckP .two) [d4]))
  (base5 : ℕ)
  (d51 d52 : RDT)
  (ex5 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d51,
      d52]) → Wit Cells Tok MsgT → Wit
    Cells Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52]))
  (base7 : ℕ)
  (d7 : RDT)
  (ex7 : (P₁ × St) × (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).E.Str → Iop.Tr (uLT (ckP .two) [d7]) →
      Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (hlo : ∀ m, N.lo ≤ (N.tenant m).1)
  (tU : (N.tenant .oU).1 < x3.base)
  (tO : (N.tenant .oOmega).1 < x6.base)
  (tS : (N.tenant .oSp).1 < x6.base)
  (hS : Q.S.sharedSplitNeeded = true)
  (hnum : num .oU = nU)
  (hUw : withU Q.S = some sentU)
  (hn0 : nU = 0)
  (hoU : ∀ z ∈ (msSh Q.S rU rO rSp t₁A layU layO), SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 →
      (oNoSh sentU.size) z = nU)
  (rad2 : ℕ → ℕ)
  (hC2 : condPort (parU Q sentU) rad2 = true)
  (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem)
  (new2 : List Mem)
  (entry2 : ∀ k, (memK2 k).1.l.get (memK2 k).2 = (shapeAt (parU Q sentU) k, rad2 k.val))
  (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
  (hno2 : ∀ k, sampledAt (parU Q sentU) k → (oNoSh sentU.size) (memK2 k) = nU + k.val)
  (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
  (hSh2 : ∀ x ∈ new2, (sendPiece (W := Wit Cells Tok MsgT) (F := (frameAt Dw (allOf Dw) Dw.key₂
      Tt.ft₂)) (heldW (U := P₁) (b2.retype
      (Cl' := Cl))) base2
    d21 d22 (parU Q sentU).coordinates (errPort (parU Q sentU) rad2)).ShownAll G Q.codes x.1.l
    x.1.seat)
  (hnew2 : ∀ x ∈ (msSh Q.S rU rO rSp t₁A layU layO), SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x
      ∈ new2)
  (rad5 : ℕ → ℕ)
  (hC5 : condPort (parO Q) rad5 = true)
  (memK5 : Fin (shapesOf (parO Q)).length → Mem)
  (new5 : List Mem)
  (entry5 : ∀ k, (memK5 k).1.l.get (memK5 k).2 = (shapeAt (parO Q) k, rad5 k.val))
  (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
  (hno5 : ∀ k, sampledAt (parO Q) k → (oNoSh sentU.size) (memK5 k) = sentU.size + k.val)
  (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
  (hSh5 : ∀ x ∈ new5, (sendPiece (W := Wit Cells Tok MsgT) (F := (frameAt Dw (allOf Dw) Dw.key₂
      Tt.ft₂)) (heldW (U := P₁) (b5.retype
      (Cl' := Cl))) base5
    d51 d52 (parO Q).coordinates (errPort (parO Q) rad5)).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ (msSh Q.S rU rO rSp t₁A layU layO), SitsAt x
      (N.tenant m).1 (N.tenant m).2 →
    x ∈ new5)


set_option quotPrecheck false in
local notation "PT" => seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := (frameAt Dw (allOf
    Dw) Dw.key₂ Tt.ft₂)) (P₁ := P₁) b1
  base d ext err
set_option quotPrecheck false in
local notation "MM" =>
  [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := Cl)) base4 d4 ex4
      er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52 ex5 er5, x6,
    pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]
set_option quotPrecheck false in
local notation "PK" =>
  pmK (P14.codes Q) G (smpSt (P14.codes Q) (oNoSh sentU.size) stSh) (msSh Q.S rU rO rSp t₁A layU
      layO) decT₂ (shiftBook (NumbersS.lo N)) Pm₀
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) nU (Array.size sentU) Q
    (XK Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, (places Q sentU).1 hUw⟩,
      shapeAt (parO Q) ⟨0, (places Q sentU).2.1⟩, shapeAt (parO Q) ⟨1, (places Q sentU).2.2 hS⟩, Y)
      (Array.size sentU))
set_option quotPrecheck false in
local notation "MK" =>
  mgK (P14.codes Q) G arr (smpSt (P14.codes Q) (oNoSh sentU.size) stSh) (msSh Q.S rU rO rSp t₁A layU
      layO) decT₂ Mg₀ mem rd 2852142980
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) (Array.size sentU) Q
set_option quotPrecheck false in
local notation "EK" => exK (P14.codes Q) G arr (smpSt (P14.codes Q) (oNoSh sentU.size) stSh) (msSh
    Q.S rU rO rSp t₁A layU layO) decT₂ c₀ N (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂)

include rU rO rSp t₁A layU layO sentU G decT₂ N Q Pm₀ Oc nU b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀
    mem rd num get smp₁ ms₁ xW stOf₁ tabP₁ base d ext err N₁ Ns links ps gOf lo err₂ rank held Pw
    hlin matC Mg₁ MgZ PmZ hix hroom hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi hxW hsW hst R
    hbook htab hsh hg hH hpile hpo slots r9 r10 Y f x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4
    d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 hlo tU tO tS hS hnum hUw hn0 hoU rad2 hC2
    memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 rad5 hC5 memK5 new5 entry5 all5 hno5 htree5
    hSh5 hnew5

/-- **The ledger's top at the maker's cut.** -/
theorem ledger_whole_by_make
    (eN : N = tiedNumbers N₁ Ns) (eD : decT₂ = decK Q.par err₂ 2852142980 rank held)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eP : Pm₀ = pmPoint Q.codes G (smpSt Q.codes (oNoSh sentU.size) stSh) (msSh Q.S rU rO rSp t₁A
        layU layO) Q.par err₂ 2852142980 rank held
      (fun s : St => s.st) (fun s : St => shiftBook N.lo s.book) PmZ)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes (oNoSh sentU.size) stSh) (msSh Q.S rU rO
          rSp t₁A layU layO) (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd sentU.size Q) Q.par 2852142980 gOf err₂ 2852142980 rank held Pw
          matC MgZ))
    (M : MeaningS St P₁ (Wit Cells Tok MsgT)) (eMZ : MgZ = mgZ Q.codes arr mem rd num M)
    (P : PromMeaning St) (ePZ : PmZ = pmZ Q.par P)
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
    (hY12 : ∀ (x : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) Cl (Wit Cells
        Tok MsgT)), x.b = heldW b1.retype →
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
    (hms : ∀ z ∈ (msSh Q.S rU rO rSp t₁A layU layO), (oNoSh sentU.size) z = 0 ∨ (oNoSh sentU.size) z
        = sentU.size ∨ (oNoSh sentU.size) z = sentU.size + 1)
    (t₂A : ℕ)
    (LA mCA mSA mWA : Sg → ℕ → ℕ)
    (rdNA : ℕ → ℕ)
    (dBA : RDT)
    (dtA : List RDT)
    (eA : ℕ)
    (εtA : Err (uLT (ckP .two) dtA))
    (rA : Fmt.M1.Stage → ℕ)
    (h0A : x9.back = [])
    (hdsA : x9.ds = dBA :: dtA)
    (herrA : HEq (r9 x9.ds) ((eA, εtA) : Err (uLT (ckP .two) (dBA :: dtA))))
    (hAA : AtPlace (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) πA (VerifiableInference.Desc.numAt t₁A t₂A
        1) LA mCA mSA mWA (fun s => rA
        s.st) x9.base
      dBA dtA εtA)
    (hjA : johOk πA rA = true)
    (hb1A : batOneOk πA = true)
    (hleA : batV0 πA rA * (bsRound .two dBA.entry dBA.kind).w ≤ eA)
    (hoA : πA.nums.ownMask = false)
    (hPA : ownLabelsB πA = true)
    (n2A : ∀ n, n < πA.nums.free → VerifiableInference.Desc.numAt t₁A t₂A 1 (.own n) < x9.base)
    (n3A : ∀ c' n, (c' + 1, n) ∈ πA.before → VerifiableInference.Desc.numAt t₁A t₂A 1 (.taken c'
      n) < x9.base)
    (hftA : πA.nums.firstTree = Q.par.toGPar.firstTree)
    (hl : Q.codes.lengthsOk = true)
    (hn1 : num .oOmega = sentU.size)
    (hn2 : num .oSp = sentU.size + 1)
    (hNA : ((mineS N (msSh Q.S rU rO rSp t₁A layU layO) true 9).map
        (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapSA : apartAt N arr true 9 (.msg .oSp) = true)
    (hapOA : apartAt N arr true 9 (.msg .oOmega) = true)
    (hY10A : ∀ a τ b, onQ₂ N (pmX Q.codes G (msSh Q.S rU rO rSp t₁A layU layO) N (pmE decT₂ Pm₀ Q
        Q.S.fold.columns nU sentU.size
      (shapeAt (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q
      sentU).2.1⟩, shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) (oNoSh sentU.size) Q sentU
          layU layO) Oc
      true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := (frameAt Dw (allOf Dw)
          Dw.key₂ Tt.ft₂)) (P₁ := P₁) b1 base d
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
    (t₂B : ℕ) (rB : Fmt.M1.Stage → ℕ)
    (LB mCB mSB mWB : Sg → ℕ → ℕ)
    (rdNB : ℕ → ℕ)
    (dBB : RDT)
    (dtB : List RDT)
    (eB v₀B : ℕ)
    (εtB : Err (uLT (ckP .two) dtB))
    (h0B : x10.back = [])
    (hdsB : x10.ds = dBB :: dtB)
    (herrB : HEq (r10 x10.ds) ((eB, εtB) : Err (uLT (ckP .two) (dBB :: dtB))))
    (hAB : AtPlaceOwn (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) πB (VerifiableInference.Desc.numAt t₁A
        t₂B 1) LB mCB mSB mWB (fun s => rB
        s.st)
      x10.base dBB dtB εtB)
    (hPayB : PayPub πB (fun s => rB s.st) dBB.entry.rows v₀B)
    (h1B : Fmt.dsOf dBB.entry dBB.kind = [.elem, .trits 0])
    (hlogB : dBB.entry.logN ≤ 64)
    (hleB : v₀B * (bsRound .two dBB.entry dBB.kind).w ≤ eB)
    (hoB : πB.nums.ownMask = true)
    (hPB : ownLabelsB πB = true)
    (n2B : ∀ n, n < πB.nums.free → VerifiableInference.Desc.numAt t₁A t₂B 1 (.own n) < x10.base)
    (n3B : ∀ c' n, (c' + 1, n) ∈ πB.before → VerifiableInference.Desc.numAt t₁A t₂B 1 (.taken c'
      n) < x10.base)
    (hftB : πB.nums.firstTree = Q.par.toGPar.firstTree)
    (hNB : ((mineS N (msSh Q.S rU rO rSp t₁A layU layO) true 10).map
        (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapOB : apartAt N arr true 10 (.msg .oOmega) = true)
    (hY11B : ∀ a τ b, onQ₂ N (pmX Q.codes G (msSh Q.S rU rO rSp t₁A layU layO) N (pmE decT₂ Pm₀ Q
        Q.S.fold.columns nU sentU.size
      (shapeAt (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q
      sentU).2.1⟩, shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) (oNoSh sentU.size) Q sentU
          layU layO) Oc
      true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := (frameAt Dw (allOf Dw)
          Dw.key₂ Tt.ft₂)) (P₁ := P₁) b1 base d
      ext err) :: [pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' :=
          Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := Cl)) base5 d51 d52
      ex5 er5, x6, pc1 (b7.retype (Cl' := Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) 10 a →
          x10.ior.red.out a τ = some b
      → Y 11 b.1.2 = true)
    (tests : List (Block St Unit))
    (hpA : (proximityTestKind guardedProximityTestParts πA : Block T12 Unit).planOk = true)
    (hrd : ∀ z m part i, rd z m part i = H2K.Pin.tabP Q.codes (z.1.l.get z.2).1 m part i)
    (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf ch Q tests
          VerifiableInference.Desc.K12.Seat.last).blocksInOrder)
    (hloG : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁A)
    (hN : N.tenant = tenantSh t₁A layU layO)
    (hdG : ∀ j o, G.oracleAt j = some o → ∀ e ∈ (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂).all, e.no = j
        → e.a ≤ o.logLength)
    (hFU : SeatFits G Q.codes (sendingU Q.S rU t₁A layU layO).l (sendingU Q.S rU t₁A layU
        layO).seat)
    (hFO : SeatFits G Q.codes (sendingO Q.S rO rSp t₁A layU layO).l (sendingO Q.S rO rSp t₁A layU
        layO).seat)
    (hB9 : ∀ m, SentBefore N f ((PT) :: MM) 9 x9 m)
    (hTU : VerifiableInference.Desc.K1.Tie Q.codes Q.S.fold.u)
    (hTS : VerifiableInference.Desc.K1.Tie Q.codes Q.S.sharedSplit)
    (hmU : mem 0 = some (memSh Q.S rU rO rSp t₁A layU layO .oU))
    (hmSp : mem (sentU.size + 1) = some (memSh Q.S rU rO rSp t₁A layU layO .oSp))
    (fU9 : 0 < Q.S.fold.u.mainRows ∧ (Q.S.fold.u.maskRows = 0 → Q.codes.mask.size ≤
        Q.S.fold.u.maskCode))
    (fSp9 : ∀ a₀ rest, πA.nums.stages = a₀ :: rest → 0 < Q.S.sharedSplit.maskRows ∧
      Q.codes.base.size ≤ Q.S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit9 : ∀ a₀ rest, πA.nums.stages = a₀ :: rest →
      rA (H2K.Pub.sgOf a₀).st < (rU + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.fold.u) ∧
      rA (H2K.Pub.sgOf a₀).st < (rSp + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes
          Q.S.sharedSplit))
    (hYc9 : ∀ s : St, Y 9 s = true →
      (∀ z, s.st.oracles[0]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.fold.u → m.id = 0 →
        H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
      ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.sharedSplit →
        m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true)
    (hjB : johOk πB rB = true)
    (hpB : (proximityTestKind guardedProximityTestParts πB : Block T12 Unit).planOk = true)
    (hB10 : ∀ m, SentBefore N f ((PT) :: MM) 10 x10 m)
    (hTO : VerifiableInference.Desc.K1.Tie Q.codes Q.S.omega)
    (hmO : mem sentU.size = some (memSh Q.S rU rO rSp t₁A layU layO .oOmega))
    (fO10 : 0 < Q.S.omega.mainRows ∧ (Q.S.omega.maskRows = 0 → Q.codes.mask.size ≤
        Q.S.omega.maskCode))
    (fSp10 : ∀ a₀ rest, πB.nums.stages = a₀ :: rest → 0 < Q.S.sharedSplit.maskRows ∧
      Q.codes.base.size ≤ Q.S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit10 : ∀ a₀ rest, πB.nums.stages = a₀ :: rest →
      rB (H2K.Pub.sgOf a₀).st < (rO + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.omega) ∧
      rB (H2K.Pub.sgOf a₀).st < (rSp + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes
          Q.S.sharedSplit))
    (hYc10 : ∀ s : St, Y 10 s = true →
      (∀ z, s.st.oracles[sentU.size]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.omega → m.id =
          sentU.size →
        H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
      ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.sharedSplit →
        m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true)
    (hDw : Fd.data fileN = .ok Dw) (hsl : Fd.sealLast = true)
    (b₁t : Block S₁t Cl) (l₁t : List (Block S₁t Cl)) (b₂t : Block (P₁ × St) Cl)
    (l₂t : List (Block (P₁ × St) Cl)) (b₃t : Block S₃t Cl) (l₃t : List (Block S₃t Cl))
    (rest₁t : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt Dw (allOf Dw) Dw.key₁ Tt.ft₁) S₁t (Wit Cells Tok MsgT) ds)
    (rest₂t : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ Tt.ft₂) (P₁ × St) (Wit Cells Tok MsgT) ds)
    (rest₃t : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt Dw (allOf Dw) Dw.key₃ Tt.ft₃) S₃t (Wit Cells Tok MsgT) ds)
    (rS : Fmt.RoundView) (g₁ : (b₁t :: l₁t).map (·.rounds) = Fd.first.blocksInOrder.map (·.rounds))
    (g₂ : (b₂t :: l₂t).map (·.rounds) = Fd.shared.blocksInOrder.map (·.rounds))
    (g₃ : (b₃t :: l₃t).map (·.rounds) = Fd.second.blocksInOrder.map (·.rounds))
    (hcut : Tt.IsCut b₁t l₁t b₂t l₂t b₃t l₃t rest₁t rest₂t rest₃t rS) (hcp : AtCap rest₂t)
    (hrow : b₂t :: l₂t = (((chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last).retype (Cl'
        := Cl)).blocksInOrder.map below).map
      (Block.lift Prod.snd fun t s => (t.1, s)))
    (hloD : N.lo = Dw.t₁) (hpf : Tt.p₂ = f) (hlf : Tt.l₂ = (PT) :: MM) :
    EachLawsBN (keyAt Prod.snd N.lo f ((PT) :: MM)) (onQ₂ N (PK) Oc true f ((PT) :: MM))
      (stepAt N (MK) (PK) Oc true f ((PT) :: MM) (extOf N f ((PT) :: MM) (EK))) slots 0
      (f :: (PT) :: MM) := by
  obtain ⟨q1, q2, q3, q4, q5, -⟩ := row_of_cut Fd fileN Dw hDw hsl Tt b₁t l₁t b₂t l₂t b₃t l₃t rest₁t
    rest₂t rest₃t rS g₁ g₂ g₃ hcut hcp
  rw [hpf, hlf] at q1 q2 q3 q4 q5
  have hps := q1.trans hrow
  obtain ⟨fb, restB, hflat, hokF, hrF⟩ := front_of_chain (Cl := Cl) ch Q tests
    VerifiableInference.Desc.K12.Seat.last
  have hbk : f.b = (below fb).lift Prod.snd fun (t : P₁ × St) (s : St) => (t.1, s) := by
    have h' := hps
    rw [hflat] at h'
    exact Option.some.inj (congrArg List.head? h')
  obtain ⟨hf1, hfb⟩ := front_of_tiled f (PT) MM fb hbk q2 hokF hrF
  have T1 := q2.2.2.2.2
  have T2 := T1.2.2.2.2
  have T3 := T2.2.2.2.2
  have T4 := T3.2.2.2.2
  have hop : ∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j := fun x hx d₀ hd₀ j hj => by
    rw [hloD]
    exact q3 x (.tail _ (.tail _ hx)) d₀ hd₀ j hj
  have A4 : Along (RoundIs (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)) b4.rounds [d4] :=
    q5 _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have hl4 : b4.rounds.length = 1 := T4.1.1.symm
  obtain ⟨r4, hr4⟩ := List.length_eq_one_iff.1 hl4
  have ho4 := none_opened Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b4 (by simp) _ r4 hr4 d4 A4
  exact ledger_whole_at_sh (rU := rU) (rO := rO) (rSp := rSp) (t₁A := t₁A) (layU := layU) (layO :=
      layO) (sentU := sentU) (G := G) (decT₂ := decT₂) (N := N) (Q := Q) (Pm₀ := Pm₀) (Oc := Oc) (nU
      := nU) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) (b7 := b7) (b8 := b8)
      (hbl := hbl) (arr := arr) (c₀ := c₀) (Mg₀ := Mg₀) (mem := mem) (rd := rd) (num := num) (get :=
      get) (smp₁ := smp₁) (ms₁ := ms₁) (xW := xW) (stOf₁ := stOf₁) (tabP₁ := tabP₁) (base := base)
      (d := d) (ext := ext) (err := err) (N₁ := N₁) (Ns := Ns) (links := links) (ps := ps) (gOf :=
      gOf) (lo := lo) (err₂ := err₂) (rank := rank) (held := held) (Pw := Pw) (hlin := hlin) (matC
      := matC) (Mg₁ := Mg₁) (MgZ := MgZ) (PmZ := PmZ) (hix := hix) (hroom := hroom) (hpin := hpin)
      (hwrow := hwrow) (hevalLaid := hevalLaid) (hwSits := hwSits) (h2 := h2) (h3 := h3) (hread :=
      hread) (hloB := hloB) (hw := hw) (hi := hi) (hxW := hxW) (hsW := hsW) (hst := hst) (R := R)
      (hbook := hbook) (htab := htab) (hsh := hsh) (hg := hg) (hH := hH) (hpile := hpile) (hpo :=
      hpo) (slots := slots) (r9 := r9) (r10 := r10) (Y := Y) (f := f) (x3 := x3) (x6 := x6) (x8 :=
      x8) (x9 := x9) (x10 := x10) (x11 := x11) (base2 := base2) (d21 := d21) (d22 := d22) (ex2 :=
      ex2) (er2 := er2) (base4 := base4) (d4 := d4) (ex4 := ex4) (er4 := er4) (base5 := base5) (d51
      := d51) (d52 := d52) (ex5 := ex5) (er5 := er5) (base7 := base7) (d7 := d7) (ex7 := ex7) (er7
      := er7) (ht := T2) (hlo := hlo) (tU := tU) (tO := tO) (tS := tS) (hS := hS) (hnum := hnum)
      (hUw := hUw) (hn0 := hn0) (hoU := hoU) (rad2 := rad2) (hC2 := hC2) (memK2 := memK2) (new2 :=
      new2) (entry2 := entry2) (all2 := all2) (hno2 := hno2) (htree2 := htree2) (hSh2 := hSh2)
      (hnew2 := hnew2) (ho4 := ho4) (rad5 := rad5) (hC5 := hC5) (memK5 := memK5) (new5 := new5)
      (entry5 := entry5) (all5 := all5) (hno5 := hno5) (htree5 := htree5) (hSh5 := hSh5) (hnew5 :=
      hnew5) (eN := eN) (eD := eD) (eO := eO) (eP := eP) (eM₀ := eM₀) (M := M) (eMZ := eMZ) (P := P)
      (ePZ := ePZ) (hop := hop) (hf1 := hf1) (hfb := hfb) (hcap := q4) (Wr := Wr) (hIx := hIx) (hdW
      := hdW) (hn := hn) (hKR := hKR) (hN64 := hN64) (hOB := hOB) (t2 := t2) (t4 := t4) (t5 := t5)
      (t7 := t7) (hsL := hsL) (b9 := b9) (b10 := b10) (hlU := hlU) (hlO := hlO) (hm := hm) (hp :=
      hp) (hok := hok) (ch := ch) (hY01 := hY01) (hY12 := hY12) (hYH := hYH) (hb2 := hb2) (nWU :=
      nWU) (nWS := nWS) (nIU := nIU) (nIS := nIS) (ev9 := ev9) (ev10 := ev10) (πA := πA) (hbA :=
      hbA) (heA := heA) (ha1A := ha1A) (hms := hms) (t₂A := t₂A) (LA := LA) (mCA := mCA) (mSA :=
      mSA) (mWA := mWA) (rdNA := rdNA) (dBA := dBA) (dtA := dtA) (eA := eA) (εtA := εtA) (rA := rA)
      (h0A := h0A) (hdsA := hdsA) (herrA := herrA) (hAA := hAA) (hjA := hjA) (hb1A := hb1A) (hleA :=
      hleA) (hoA := hoA) (hPA := hPA) (n2A := n2A) (n3A := n3A) (hftA := hftA) (hl := hl) (hn1 :=
      hn1) (hn2 := hn2) (hNA := hNA) (hapSA := hapSA) (hapOA := hapOA) (hY10A := hY10A) (πB := πB)
      (hbB := hbB) (heB := heB) (ha1B := ha1B) (t₂B := t₂B) (rB := rB) (LB := LB) (mCB := mCB) (mSB
      := mSB) (mWB := mWB) (rdNB := rdNB) (dBB := dBB) (dtB := dtB) (eB := eB) (v₀B := v₀B) (εtB :=
      εtB) (h0B := h0B) (hdsB := hdsB) (herrB := herrB) (hAB := hAB) (hPayB := hPayB) (h1B := h1B)
      (hlogB := hlogB) (hleB := hleB) (hoB := hoB) (hPB := hPB) (n2B := n2B) (n3B := n3B) (hftB :=
      hftB) (hNB := hNB) (hapOB := hapOB) (hY11B := hY11B) (tests := tests) (hps := hps) (hpA :=
      hpA) (hrd := hrd) (hG := hG) (hloG := hloG) (hN := hN) (hdG := hdG) (hFU := hFU) (hFO := hFO)
      (hB9 := hB9) (hTU := hTU) (hTS := hTS) (hmU := hmU) (hmSp := hmSp) (fU9 := fU9) (fSp9 := fSp9)
      (hfit9 := hfit9) (hYc9 := hYc9) (hjB := hjB) (hpB := hpB) (hB10 := hB10) (hTO := hTO) (hmO :=
      hmO) (fO10 := fO10) (fSp10 := fSp10) (hfit10 := hfit10) (hYc10 := hYc10)


end ByMake

/-- **The proof file's description at ANY seat of the shared chain whose state is the kind's and
whose
chain is the seated chain**: the maker's own text (ProofFile.fileDescBy) at a seat spelled field by field.
-/
abbrev fieldF {σ₁ : Type} (oH : ProofFile.SecondHashFunctionArgument) (mkL : ProofFile.LinksBy) (Zp : ProofFile.Pub) (lt : String)
    (st₂ : ProofFile.InstPub → St) (en₂ : St → Option OnBytes.Proof.SharedEnd) (ok₂ : ProofFile.InstPub → Bool)
    (fo₂ : Bool) (si₂ : List String) (Bs : ProofFile.SecondSeat) (getS : σ₁ →
              VerifiableInference.Desc.First.S)
    (startS : ProofFile.InstPub → σ₁) (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl) (ch :
                    Model.Verify.Chains) (Q : P14)
    (tests : List (Block St Unit)) : FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy oH mkL Zp
    { lot := lt, σ := St, start := st₂
      chain := chainOf ch Q tests VerifiableInference.Desc.K12.Seat.last, ended := en₂
      okInst := ok₂, fileOk := fo₂, standIns := si₂ } Bs getS startS cF

section AtField

variable (rU rO rSp t₁A : ℕ) (layU layO : TreeLay) (sentU : Array OracleNotice)
variable {P₀ : Type}
variable
  {Xi Cells Tok : Type}
variable
  {σ₁ : Type} (Dw : WholeD)
variable
  (G : FileDescription Xi)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (N : NumbersS)
  (Q : P14)
  (Pm₀ : PromMeaning St)
  (Oc : (ProofFile.InstPub × σ₁) → Strs → Prop)
  (nU : ℕ)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
variable
  (arr : ℕ → ℕ → ℕ)
  (c₀ : Cells)
  (Mg₀ : MeaningS St (ProofFile.InstPub × σ₁) (Wit Cells Tok MsgT))
  (mem : ℕ → Option Mem)
  (rd : (x : Mem) → ((sigOf Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE)
  (num : Msg2 → ℕ)
variable
  (get : (ProofFile.InstPub × σ₁) → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Q.codes s.l).om
    i).Smp)
  (ms₁ : List Mem)
  (xW : Mem)
  (stOf₁ : P₀ × First.S → Statement)
  (tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT)
  (base : Nat)
  (d : RDT)
  (ext : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Tr (uLT (ckP .two)
            [d]) → Wit Cells Tok MsgT → Wit Cells Tok
    MsgT)
  (err : Err (uLT (ckP .two) [d]))
  (N₁ : Numbers)
  (Ns : NumbersS)
  (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place)
  (gOf : (ProofFile.InstPub × σ₁) → Nat → GE)
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
  (MgZ : MeaningS St (ProofFile.InstPub × σ₁) (Wit Cells Tok MsgT))
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
  (R : (ProofFile.InstPub × σ₁) → Prop)
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
  (slots : ℕ) (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds))
  (Y : ℕ → St → Bool)
variable
  (f x3 x6 x8 x9 x10 x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) ×
      St) ProofFile.Cl (Wit Cells Tok MsgT))
  (base2 : ℕ)
  (d21 d22 : RDT)
  (ex2 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP
            .two) [d21, d22]) → Wit Cells Tok MsgT → Wit
    Cells Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22]))
  (base4 : ℕ)
  (d4 : RDT)
  (ex4 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP
            .two) [d4]) → Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er4 : Err (uLT (ckP .two) [d4]))
  (base5 : ℕ)
  (d51 d52 : RDT)
  (ex5 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP
            .two) [d51, d52]) → Wit Cells Tok MsgT → Wit
    Cells Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52]))
  (base7 : ℕ)
  (d7 : RDT)
  (ex7 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP
            .two) [d7]) → Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (hlo : ∀ m, N.lo ≤ (N.tenant m).1)
  (tU : (N.tenant .oU).1 < x3.base)
  (tO : (N.tenant .oOmega).1 < x6.base)
  (tS : (N.tenant .oSp).1 < x6.base)
  (hS : Q.S.sharedSplitNeeded = true)
  (hnum : num .oU = nU)
  (hUw : withU Q.S = some sentU)
  (hn0 : nU = 0)
  (hoU : ∀ z ∈ (msSh Q.S rU rO rSp t₁A layU layO), SitsAt z (N.tenant .oU).1 (N.tenant .oU).2 →
      (oNoSh sentU.size) z = nU)
  (rad2 : ℕ → ℕ)
  (hC2 : condPort (parU Q sentU) rad2 = true)
  (memK2 : Fin (shapesOf (parU Q sentU)).length → Mem)
  (new2 : List Mem)
  (entry2 : ∀ k, (memK2 k).1.l.get (memK2 k).2 = (shapeAt (parU Q sentU) k, rad2 k.val))
  (all2 : ∀ x ∈ new2, ∃ k, sampledAt (parU Q sentU) k ∧ memK2 k = x)
  (hno2 : ∀ k, sampledAt (parU Q sentU) k → (oNoSh sentU.size) (memK2 k) = nU + k.val)
  (htree2 : ∀ k, ∃ j, ((memK2 k).1.seat (memK2 k).2).1 = base2 + j ∧ j < d21.trees.length)
  (hSh2 : ∀ x ∈ new2, (sendPiece (W := Wit Cells Tok MsgT) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
      (heldW (U := (ProofFile.InstPub × σ₁)) (b2.retype
            (Cl' := ProofFile.Cl))) base2
    d21 d22 (parU Q sentU).coordinates (errPort (parU Q sentU) rad2)).ShownAll G Q.codes x.1.l
    x.1.seat)
  (hnew2 : ∀ x ∈ (msSh Q.S rU rO rSp t₁A layU layO), SitsAt x (N.tenant .oU).1 (N.tenant .oU).2 → x
      ∈ new2)
  (rad5 : ℕ → ℕ)
  (hC5 : condPort (parO Q) rad5 = true)
  (memK5 : Fin (shapesOf (parO Q)).length → Mem)
  (new5 : List Mem)
  (entry5 : ∀ k, (memK5 k).1.l.get (memK5 k).2 = (shapeAt (parO Q) k, rad5 k.val))
  (all5 : ∀ x ∈ new5, ∃ k, sampledAt (parO Q) k ∧ memK5 k = x)
  (hno5 : ∀ k, sampledAt (parO Q) k → (oNoSh sentU.size) (memK5 k) = sentU.size + k.val)
  (htree5 : ∀ k, ∃ j, ((memK5 k).1.seat (memK5 k).2).1 = base5 + j ∧ j < d51.trees.length)
  (hSh5 : ∀ x ∈ new5, (sendPiece (W := Wit Cells Tok MsgT) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
      (heldW (U := (ProofFile.InstPub × σ₁)) (b5.retype
            (Cl' := ProofFile.Cl))) base5
    d51 d52 (parO Q).coordinates (errPort (parO Q) rad5)).ShownAll G Q.codes x.1.l x.1.seat)
  (hnew5 : ∀ m, m = Msg2.oOmega ∨ m = .oSp → ∀ x ∈ (msSh Q.S rU rO rSp t₁A layU layO), SitsAt x
      (N.tenant m).1 (N.tenant m).2 →
    x ∈ new5)


set_option quotPrecheck false in
local notation "PT" => seatedPiece (W := Wit Cells Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw
    (allOf Dw) Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1
  base d ext err
set_option quotPrecheck false in
local notation "MM" =>
  [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' := ProofFile.Cl)) base4
      d4 ex4
      er4, pc2 (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5, x6,
    pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]
set_option quotPrecheck false in
local notation "PK" =>
  pmK (P14.codes Q) G (smpSt (P14.codes Q) (oNoSh sentU.size) stSh) (msSh Q.S rU rO rSp t₁A layU
      layO) decT₂ (shiftBook (NumbersS.lo N)) Pm₀
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) nU (Array.size sentU) Q
    (XK Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, (places Q sentU).1 hUw⟩,
      shapeAt (parO Q) ⟨0, (places Q sentU).2.1⟩, shapeAt (parO Q) ⟨1, (places Q sentU).2.2 hS⟩, Y)
      (Array.size sentU))
set_option quotPrecheck false in
local notation "MK" =>
  mgK (P14.codes Q) G arr (smpSt (P14.codes Q) (oNoSh sentU.size) stSh) (msSh Q.S rU rO rSp t₁A layU
      layO) decT₂ Mg₀ mem rd 2852142980
    (FoldeqShape.columns (LinShape.fold (P14.S Q))) (Array.size sentU) Q
set_option quotPrecheck false in
local notation "EK" => exK (P14.codes Q) G arr (smpSt (P14.codes Q) (oNoSh sentU.size) stSh) (msSh
    Q.S rU rO rSp t₁A layU layO) decT₂ c₀ N (frameAt Dw (allOf Dw) Dw.key₂ 0)

include rU rO rSp t₁A layU layO sentU G decT₂ N Q Pm₀ Oc nU b1 b2 b3 b4 b5 b6 b7 b8 hbl arr c₀ Mg₀
    mem rd num get smp₁ ms₁ xW stOf₁ tabP₁ base d ext err N₁ Ns links ps gOf lo err₂ rank held Pw
    hlin matC Mg₁ MgZ PmZ hix hroom hpin hwrow hevalLaid hwSits h2 h3 hread hloB hw hi hxW hsW hst R
    hbook htab hsh hg hH hpile hpo slots r9 r10 Y f x3 x6 x8 x9 x10 x11 base2 d21 d22 ex2 er2 base4
    d4 ex4 er4 base5 d51 d52 ex5 er5 base7 d7 ex7 er7 hlo tU tO tS hS hnum hUw hn0 hoU rad2 hC2
    memK2 new2 entry2 all2 hno2 htree2 hSh2 hnew2 rad5 hC5 memK5 new5 entry5 all5 hno5 htree5
    hSh5 hnew5

/-- **The ledger's end IS RowsTiedR.shared_joint_count's sentence, at its own list of pieces.** -/
theorem ledger_whole_fills_field
    (eN : N = tiedNumbers N₁ Ns) (eD : decT₂ = decK Q.par err₂ 2852142980 rank held)
    (eO : Oc = ocWith (ocEnd get N₁
      Mg₁ links ps) R)
    (eP : Pm₀ = pmPoint Q.codes G (smpSt Q.codes (oNoSh sentU.size) stSh) (msSh Q.S rU rO rSp t₁A
        layU layO) Q.par err₂ 2852142980 rank held
      (fun s : St => s.st) (fun s : St => shiftBook N.lo s.book) PmZ)
    (eM₀ : Mg₀ = tiedMeaning get
      Mg₁
      (mgJoint Q.codes G arr get smp₁ ms₁ xW (smpSt Q.codes (oNoSh sentU.size) stSh) (msSh Q.S rU rO
          rSp t₁A layU layO) (linLayW Q.codes Pw.lin)
        (fun q => stOf₁ (get q)) (fun q => tabP₁ (get q)) (rgOf Q.codes arr mem rd)
        (omWK Q.codes arr mem rd sentU.size Q) Q.par 2852142980 gOf err₂ 2852142980 rank held Pw
          matC MgZ))
    (M : MeaningS St (ProofFile.InstPub × σ₁) (Wit Cells Tok MsgT)) (eMZ : MgZ = mgZ Q.codes arr mem rd
              num M)
    (P : PromMeaning St) (ePZ : PmZ = pmZ Q.par P)
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
    (hY12 : ∀ (x : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
        ProofFile.Cl (Wit Cells Tok MsgT)), x.b = heldW b1.retype →
      ∀ a τ y, x.ior.red.out a τ = some y → Y 1 a.1.2 = true → Y 2 y.1.2 = true)
    (hYH : HandsAt (Cl := ProofFile.Cl) (Cells := Cells) (Tok := Tok) (onQ₂ N (PK) Oc true f ((PT) :: MM))
      [b1, b2, b3, b4, b5, b6, b7, b8] Y)
    (hb2 : base ≤ base2)
    (nWU : arr N.w.1 N.w.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2)
    (nWS : arr N.w.1 N.w.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2)
    (nIU : arr N.index.1 N.index.2 ≠ arr (N.tenant .oU).1 (N.tenant .oU).2)
    (nIS : arr N.index.1 N.index.2 ≠ arr (N.tenant .oSp).1 (N.tenant .oSp).2)
    (ev9 : EvKept N (MK) (PK) Oc true f ((PT) :: MM) (EK) 9)
    (ev10 : EvKept N (MK) (PK) Oc true f ((PT) :: MM) (EK) 10)
    (πA : P12)
    (hbA : Alike (VerifiableInference.Desc.Sound.held (P := (ProofFile.InstPub × σ₁)) (Seat.onGu (proximityTestKind
              guardedProximityTestParts πA :
            Block T12 Unit))) x9.b)
    (heA : πA.early = true)
    (ha1A : πA.answers = 1)
    (hms : ∀ z ∈ (msSh Q.S rU rO rSp t₁A layU layO), (oNoSh sentU.size) z = 0 ∨ (oNoSh sentU.size) z
        = sentU.size ∨ (oNoSh sentU.size) z = sentU.size + 1)
    (t₂A : ℕ)
    (LA mCA mSA mWA : Sg → ℕ → ℕ)
    (rdNA : ℕ → ℕ)
    (dBA : RDT)
    (dtA : List RDT)
    (eA : ℕ)
    (εtA : Err (uLT (ckP .two) dtA))
    (rA : Fmt.M1.Stage → ℕ)
    (h0A : x9.back = [])
    (hdsA : x9.ds = dBA :: dtA)
    (herrA : HEq (r9 x9.ds) ((eA, εtA) : Err (uLT (ckP .two) (dBA :: dtA))))
    (hAA : AtPlace (frameAt Dw (allOf Dw) Dw.key₂ 0) πA (VerifiableInference.Desc.numAt t₁A t₂A 1)
        LA mCA mSA mWA (fun s => rA
        s.st) x9.base
      dBA dtA εtA)
    (hjA : johOk πA rA = true)
    (hb1A : batOneOk πA = true)
    (hleA : batV0 πA rA * (bsRound .two dBA.entry dBA.kind).w ≤ eA)
    (hoA : πA.nums.ownMask = false)
    (hPA : ownLabelsB πA = true)
    (n2A : ∀ n, n < πA.nums.free → VerifiableInference.Desc.numAt t₁A t₂A 1 (.own n) < x9.base)
    (n3A : ∀ c' n, (c' + 1, n) ∈ πA.before → VerifiableInference.Desc.numAt t₁A t₂A 1 (.taken c'
      n) < x9.base)
    (hftA : πA.nums.firstTree = Q.par.toGPar.firstTree)
    (hl : Q.codes.lengthsOk = true)
    (hn1 : num .oOmega = sentU.size)
    (hn2 : num .oSp = sentU.size + 1)
    (hNA : ((mineS N (msSh Q.S rU rO rSp t₁A layU layO) true 9).map
        (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapSA : apartAt N arr true 9 (.msg .oSp) = true)
    (hapOA : apartAt N arr true 9 (.msg .oOmega) = true)
    (hY10A : ∀ a τ b, onQ₂ N (pmX Q.codes G (msSh Q.S rU rO rSp t₁A layU layO) N (pmE decT₂ Pm₀ Q
        Q.S.fold.columns nU sentU.size
      (shapeAt (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q
      sentU).2.1⟩, shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) (oNoSh sentU.size) Q sentU
          layU layO) Oc
      true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
                Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1 base d
      ext err) :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' :=
                ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52
      ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) 9 a →
          x9.ior.red.out a τ = some b →
      Y 10 b.1.2 = true)
    (πB : P12)
    (hbB : Alike (VerifiableInference.Desc.Sound.held (P := (ProofFile.InstPub × σ₁)) (Seat.onGomega (proximityTestKind
              guardedProximityTestParts πB :
            Block T12 Unit))) x10.b)
    (heB : πB.early = true)
    (ha1B : πB.answers = 1)
    (t₂B : ℕ) (rB : Fmt.M1.Stage → ℕ)
    (LB mCB mSB mWB : Sg → ℕ → ℕ)
    (rdNB : ℕ → ℕ)
    (dBB : RDT)
    (dtB : List RDT)
    (eB v₀B : ℕ)
    (εtB : Err (uLT (ckP .two) dtB))
    (h0B : x10.back = [])
    (hdsB : x10.ds = dBB :: dtB)
    (herrB : HEq (r10 x10.ds) ((eB, εtB) : Err (uLT (ckP .two) (dBB :: dtB))))
    (hAB : AtPlaceOwn (frameAt Dw (allOf Dw) Dw.key₂ 0) πB (VerifiableInference.Desc.numAt t₁A t₂B
        1) LB mCB mSB mWB (fun s => rB
        s.st)
      x10.base dBB dtB εtB)
    (hPayB : PayPub πB (fun s => rB s.st) dBB.entry.rows v₀B)
    (h1B : Fmt.dsOf dBB.entry dBB.kind = [.elem, .trits 0])
    (hlogB : dBB.entry.logN ≤ 64)
    (hleB : v₀B * (bsRound .two dBB.entry dBB.kind).w ≤ eB)
    (hoB : πB.nums.ownMask = true)
    (hPB : ownLabelsB πB = true)
    (n2B : ∀ n, n < πB.nums.free → VerifiableInference.Desc.numAt t₁A t₂B 1 (.own n) < x10.base)
    (n3B : ∀ c' n, (c' + 1, n) ∈ πB.before → VerifiableInference.Desc.numAt t₁A t₂B 1 (.taken c'
      n) < x10.base)
    (hftB : πB.nums.firstTree = Q.par.toGPar.firstTree)
    (hNB : ((mineS N (msSh Q.S rU rO rSp t₁A layU layO) true 10).map
        (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapOB : apartAt N arr true 10 (.msg .oOmega) = true)
    (hY11B : ∀ a τ b, onQ₂ N (pmX Q.codes G (msSh Q.S rU rO rSp t₁A layU layO) N (pmE decT₂ Pm₀ Q
        Q.S.fold.columns nU sentU.size
      (shapeAt (parU Q sentU) ⟨0, ((places Q sentU).1 hUw)⟩, shapeAt (parO Q) ⟨0, (places Q
      sentU).2.1⟩, shapeAt (parO Q) ⟨1, ((places Q sentU).2.2 hS)⟩, Y)) (oNoSh sentU.size) Q sentU
          layU layO) Oc
      true f ((seatedPiece (W := Wit Cells Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
                Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) b1 base d
      ext err) :: [pc2 (b2.retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2 er2, x3, pc1 (b4.retype (Cl' :=
                ProofFile.Cl)) base4 d4 ex4 er4, pc2 (b5.retype (Cl' := ProofFile.Cl)) base5 d51 d52
      ex5 er5, x6, pc1 (b7.retype (Cl' := ProofFile.Cl)) base7 d7 ex7 er7, x8, x9, x10, x11]) 10 a →
          x10.ior.red.out a τ = some b
      → Y 11 b.1.2 = true)
    (tests : List (Block St Unit))
    (hpA : (proximityTestKind guardedProximityTestParts πA : Block T12 Unit).planOk = true)
    (hrd : ∀ z m part i, rd z m part i = H2K.Pin.tabP Q.codes (z.1.l.get z.2).1 m part i)
    (hG : VerifiableInference.Desc.oraclesOf G.shared.blocksInOrder =
      VerifiableInference.Desc.oraclesOf (chainOf ch Q tests
          VerifiableInference.Desc.K12.Seat.last).blocksInOrder)
    (hloG : (VerifiableInference.Desc.oraclesOf G.first.blocksInOrder).length = t₁A)
    (hN : N.tenant = tenantSh t₁A layU layO)
    (hdG : ∀ j o, G.oracleAt j = some o → ∀ e ∈ (frameAt Dw (allOf Dw) Dw.key₂ 0).all, e.no = j →
        e.a ≤ o.logLength)
    (hFU : SeatFits G Q.codes (sendingU Q.S rU t₁A layU layO).l (sendingU Q.S rU t₁A layU
        layO).seat)
    (hFO : SeatFits G Q.codes (sendingO Q.S rO rSp t₁A layU layO).l (sendingO Q.S rO rSp t₁A layU
        layO).seat)
    (hB9 : ∀ m, SentBefore N f ((PT) :: MM) 9 x9 m)
    (hTU : VerifiableInference.Desc.K1.Tie Q.codes Q.S.fold.u)
    (hTS : VerifiableInference.Desc.K1.Tie Q.codes Q.S.sharedSplit)
    (hmU : mem 0 = some (memSh Q.S rU rO rSp t₁A layU layO .oU))
    (hmSp : mem (sentU.size + 1) = some (memSh Q.S rU rO rSp t₁A layU layO .oSp))
    (fU9 : 0 < Q.S.fold.u.mainRows ∧ (Q.S.fold.u.maskRows = 0 → Q.codes.mask.size ≤
        Q.S.fold.u.maskCode))
    (fSp9 : ∀ a₀ rest, πA.nums.stages = a₀ :: rest → 0 < Q.S.sharedSplit.maskRows ∧
      Q.codes.base.size ≤ Q.S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit9 : ∀ a₀ rest, πA.nums.stages = a₀ :: rest →
      rA (H2K.Pub.sgOf a₀).st < (rU + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.fold.u) ∧
      rA (H2K.Pub.sgOf a₀).st < (rSp + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes
          Q.S.sharedSplit))
    (hYc9 : ∀ s : St, Y 9 s = true →
      (∀ z, s.st.oracles[0]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.fold.u → m.id = 0 →
        H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
      ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.sharedSplit →
        m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true)
    (hjB : johOk πB rB = true)
    (hpB : (proximityTestKind guardedProximityTestParts πB : Block T12 Unit).planOk = true)
    (hB10 : ∀ m, SentBefore N f ((PT) :: MM) 10 x10 m)
    (hTO : VerifiableInference.Desc.K1.Tie Q.codes Q.S.omega)
    (hmO : mem sentU.size = some (memSh Q.S rU rO rSp t₁A layU layO .oOmega))
    (fO10 : 0 < Q.S.omega.mainRows ∧ (Q.S.omega.maskRows = 0 → Q.codes.mask.size ≤
        Q.S.omega.maskCode))
    (fSp10 : ∀ a₀ rest, πB.nums.stages = a₀ :: rest → 0 < Q.S.sharedSplit.maskRows ∧
      Q.codes.base.size ≤ Q.S.sharedSplit.code ∧
      (layO.shapes.getD (layO.tree.getD 1 0) default).logN ≤ a₀.Z.a)
    (hfit10 : ∀ a₀ rest, πB.nums.stages = a₀ :: rest →
      rB (H2K.Pub.sgOf a₀).st < (rO + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes Q.S.omega) ∧
      rB (H2K.Pub.sgOf a₀).st < (rSp + 1) * 2 ^ ((H2K.Pub.sgOf a₀).C.a - aOf Q.codes
          Q.S.sharedSplit))
    (hYc10 : ∀ s : St, Y 10 s = true →
      (∀ z, s.st.oracles[sentU.size]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.omega → m.id =
          sentU.size →
        H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true) ∧
      ∀ z, s.st.oracles[sentU.size + 1]? = some z → ∀ m : H2K.First.Seat1, m.sh = Q.S.sharedSplit →
        m.id = sentU.size + 1 → H2K.Pin.ok (H2K.Pin.sampleL Q.codes m z) = true)
    (oH : ProofFile.SecondHashFunctionArgument) (mkL : ProofFile.LinksBy) (Zp : ProofFile.Pub) (lt : String) (st₂ : ProofFile.InstPub → St)
    (en₂ : St → Option OnBytes.Proof.SharedEnd) (ok₂ : ProofFile.InstPub → Bool) (fo₂ : Bool)
    (si₂ : List String) (Bs : ProofFile.SecondSeat) (getS : σ₁ → VerifiableInference.Desc.First.S) (startS
              : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl)
    (c₁ : Block (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₁ (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl) (k₁ : List (Block (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₁ (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl))
    (c₂ : Block (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂ (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl) (k₂ : List (Block (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂ (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl))
    (c₃ : Block (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₃ (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl) (k₃ : List (Block (fieldF oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₃ (fieldF oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).Cl))
    (h₁f : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).first.blocksInOrder = c₁ ::
        k₁) (h₂f : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).shared.blocksInOrder = c₂ :: k₂)
    (h₃f : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).second.blocksInOrder = c₃
        :: k₃)
    (e₁ : (i : ℕ) → (ds : List RDT) → ((fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch
        Q tests).XiPub × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₁)
        ×
      (frameAt Dw (allOf Dw) Dw.key₁ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) → (Wit Cells Tok MsgT) →
          (Wit Cells Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) → (((fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        ch Q tests).XiPub × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).S₁) × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂) ×
      (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) → (Wit Cells Tok MsgT) →
          (Wit Cells Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) → (((fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        ch Q tests).XiPub × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
        tests).S₁ × (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₂) ×
        (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).S₃) ×
      (frameAt Dw (allOf Dw) Dw.key₃ (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q
          tests).lastChainFirstTreeNumber).E.Str → Iop.Tr (uLT (ckP .two) ds) → (Wit Cells Tok MsgT) →
      (Wit Cells Tok MsgT))
    (dW wEnd : (Wit Cells Tok MsgT)) (fileN : String) (hDw : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂
        si₂ Bs getS startS cF ch Q tests).data fileN = .ok Dw)
    (hsl : (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests).sealLast = true)
        (hloD : N.lo = Dw.t₁) (hpf : (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
        cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
        cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ = f)
    (hlf : (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt
        (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁
        c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂ = (PT) :: MM) :
    EachLawsBN (keyAt Prod.snd Dw.t₁ (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
        cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
        cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
        (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt
        (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁
        c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂) (onQ₂ N (PK) Oc true
        (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt
        (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁
        c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ (atDesc (fieldF oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap
        e₂) (restCap e₃) dW wEnd)).l₂)
      (stepAt N (MK) (PK) Oc true (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
          ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
          cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
          (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt
          (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁
          c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂ (extOf N (atDesc (fieldF
          oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two)
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃
          k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ (atDesc (fieldF oH mkL Zp lt st₂
          en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt
          st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
          (restCap e₂) (restCap e₃) dW wEnd)).l₂ (EK))) slots 0
      ((atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP
          .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂
          k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂ :: (atDesc (fieldF oH mkL Zp
          lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL
          Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
          (restCap e₂) (restCap e₃) dW wEnd)).l₂) := by
  obtain ⟨g₁, g₂, g₃, hcut, hcp, hrow⟩ := seat_layer (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF ch Q tests) Dw (ckP .two) c₁ k₁ c₂ k₂ c₃ k₃ h₁f h₂f h₃f e₁
    e₂ e₃ dW wEnd
  have H := ledger_whole_by_make (Fd := (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
      ch Q tests)) (fileN := fileN) (Dw := Dw) (Tt := (atDesc (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂
      si₂ Bs getS startS cF ch Q tests) (piecesAt (ckP .two) (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂
      si₂ Bs getS startS cF ch Q tests) Dw c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃)
      dW wEnd))) (rU := rU) (rO := rO) (rSp := rSp) (t₁A := t₁A) (layU := layU) (layO := layO)
      (sentU := sentU) (G := G) (decT₂ := decT₂) (N := N) (Q := Q) (Pm₀ := Pm₀) (Oc := Oc) (nU :=
      nU) (b1 := b1) (b2 := b2) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) (b7 := b7) (b8 := b8)
      (hbl := hbl) (arr := arr) (c₀ := c₀) (Mg₀ := Mg₀) (mem := mem) (rd := rd) (num := num) (get :=
      get) (smp₁ := smp₁) (ms₁ := ms₁) (xW := xW) (stOf₁ := stOf₁) (tabP₁ := tabP₁) (base := base)
      (d := d) (ext := ext) (err := err) (N₁ := N₁) (Ns := Ns) (links := links) (ps := ps) (gOf :=
      gOf) (lo := lo) (err₂ := err₂) (rank := rank) (held := held) (Pw := Pw) (hlin := hlin) (matC
      := matC) (Mg₁ := Mg₁) (MgZ := MgZ) (PmZ := PmZ) (hix := hix) (hroom := hroom) (hpin := hpin)
      (hwrow := hwrow) (hevalLaid := hevalLaid) (hwSits := hwSits) (h2 := h2) (h3 := h3) (hread :=
      hread) (hloB := hloB) (hw := hw) (hi := hi) (hxW := hxW) (hsW := hsW) (hst := hst) (R := R)
      (hbook := hbook) (htab := htab) (hsh := hsh) (hg := hg) (hH := hH) (hpile := hpile) (hpo :=
      hpo) (slots := slots) (r9 := r9) (r10 := r10) (Y := Y) (f := f) (x3 := x3) (x6 := x6) (x8 :=
      x8) (x9 := x9) (x10 := x10) (x11 := x11) (base2 := base2) (d21 := d21) (d22 := d22) (ex2 :=
      ex2) (er2 := er2) (base4 := base4) (d4 := d4) (ex4 := ex4) (er4 := er4) (base5 := base5) (d51
      := d51) (d52 := d52) (ex5 := ex5) (er5 := er5) (base7 := base7) (d7 := d7) (ex7 := ex7) (er7
      := er7) (hlo := hlo) (tU := tU) (tO := tO) (tS := tS) (hS := hS) (hnum := hnum) (hUw := hUw)
      (hn0 := hn0) (hoU := hoU) (rad2 := rad2) (hC2 := hC2) (memK2 := memK2) (new2 := new2) (entry2
      := entry2) (all2 := all2) (hno2 := hno2) (htree2 := htree2) (hSh2 := hSh2) (hnew2 := hnew2)
      (rad5 := rad5) (hC5 := hC5) (memK5 := memK5) (new5 := new5) (entry5 := entry5) (all5 := all5)
      (hno5 := hno5) (htree5 := htree5) (hSh5 := hSh5) (hnew5 := hnew5) (eN := eN) (eD := eD) (eO :=
      eO) (eP := eP) (eM₀ := eM₀) (M := M) (eMZ := eMZ) (P := P) (ePZ := ePZ) (Wr := Wr) (hIx :=
      hIx) (hdW := hdW) (hn := hn) (hKR := hKR) (hN64 := hN64) (hOB := hOB) (t2 := t2) (t4 := t4)
      (t5 := t5) (t7 := t7) (hsL := hsL) (b9 := b9) (b10 := b10) (hlU := hlU) (hlO := hlO) (hm :=
      hm) (hp := hp) (hok := hok) (ch := ch) (hY01 := hY01) (hY12 := hY12) (hYH := hYH) (hb2 := hb2)
      (nWU := nWU) (nWS := nWS) (nIU := nIU) (nIS := nIS) (ev9 := ev9) (ev10 := ev10) (πA := πA)
      (hbA := hbA) (heA := heA) (ha1A := ha1A) (hms := hms) (t₂A := t₂A) (LA := LA) (mCA := mCA)
      (mSA := mSA) (mWA := mWA) (rdNA := rdNA) (dBA := dBA) (dtA := dtA) (eA := eA) (εtA := εtA) (rA
      := rA) (h0A := h0A) (hdsA := hdsA) (herrA := herrA) (hAA := hAA) (hjA := hjA) (hb1A := hb1A)
      (hleA := hleA) (hoA := hoA) (hPA := hPA) (n2A := n2A) (n3A := n3A) (hftA := hftA) (hl := hl)
      (hn1 := hn1) (hn2 := hn2) (hNA := hNA) (hapSA := hapSA) (hapOA := hapOA) (hY10A := hY10A) (πB
      := πB) (hbB := hbB) (heB := heB) (ha1B := ha1B) (t₂B := t₂B) (rB := rB) (LB := LB) (mCB :=
      mCB) (mSB := mSB) (mWB := mWB) (rdNB := rdNB) (dBB := dBB) (dtB := dtB) (eB := eB) (v₀B :=
      v₀B) (εtB := εtB) (h0B := h0B) (hdsB := hdsB) (herrB := herrB) (hAB := hAB) (hPayB := hPayB)
      (h1B := h1B) (hlogB := hlogB) (hleB := hleB) (hoB := hoB) (hPB := hPB) (n2B := n2B) (n3B :=
      n3B) (hftB := hftB) (hNB := hNB) (hapOB := hapOB) (hY11B := hY11B) (tests := tests) (hpA :=
      hpA) (hrd := hrd) (hG := hG) (hloG := hloG) (hN := hN) (hdG := hdG) (hFU := hFU) (hFO := hFO)
      (hB9 := hB9) (hTU := hTU) (hTS := hTS) (hmU := hmU) (hmSp := hmSp) (fU9 := fU9) (fSp9 := fSp9)
      (hfit9 := hfit9) (hYc9 := hYc9) (hjB := hjB) (hpB := hpB) (hB10 := hB10) (hTO := hTO) (hmO :=
      hmO) (fO10 := fO10) (fSp10 := fSp10) (hfit10 := hfit10) (hYc10 := hYc10)
    (hDw := hDw) (hsl := hsl) (b₁t := VerifiableInference.Desc.Sound.held c₁) (l₁t := k₁.map
        VerifiableInference.Desc.Sound.held) (b₂t := VerifiableInference.Desc.Sound.held c₂)
    (l₂t := k₂.map VerifiableInference.Desc.Sound.held) (b₃t := VerifiableInference.Desc.Sound.held
        c₃) (l₃t := k₃.map VerifiableInference.Desc.Sound.held) (rest₁t := restCap e₁)
    (rest₂t := restCap e₂) (rest₃t := restCap e₃) (rS := sealRound) (g₁ := g₁) (g₂ := g₂) (g₃ := g₃)
    (hcut := hcut) (hcp := hcp) (hrow := hrow) (hloD := hloD) (hpf := hpf) (hlf := hlf)
  rw [hpf, hlf, ← hloD]
  exact H

end AtField

end Desc.K14.Law
