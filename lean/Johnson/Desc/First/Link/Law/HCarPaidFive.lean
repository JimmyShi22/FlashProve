-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarPaidFive.lean (kind K10; namespace P5J): `hCar_paid` (HCarPaid.lean)
AT LINK 0, AT THE FIVE-LIST: the closing's files' law at link 0 stands at loFive · kbFive (at the
six-list hCar would ask a witness for the word of the one message that is no member); HCarPaid.lean
pays at loAt 0, the six-list: the two do not meet.
Here the payers that name the list are carried to loFive · kbFive · seatFiveAt (At.pseats Zp)
  ·
noFiveAt (At.seats Zp) (At.pseats Zp). Theorems. It changes no other file.

  `five_is_six`: each of the five seats is the six-list's seat at a place of the six-list.
  `AtMgA.hr_five` (zero_hr; row_at_laid | hr_at_laid) ·
  `AtMgA.hord_five` (keptOrd_five) · `AtMgA.hPl_five` (hB_at_k10 at the
  six-list, through five_is_six) · `AtMgA.hShp_five` (the clause «shapes» of
  hX_five_head).
  `AtMgA.hCar_paid_five`: **THE FIELD hCar OF K10Heavy AT THE CLOSED CONSTANT's LETTERS AT LINK 0,
    AT
    THE FIVE-LIST, THE PAYERS LAID IN.** The payers that name no list (hW · hTie · the mask's three
      ·
    hFront's clauses · hBelow · hsB) are HCarPaid.lean's own, at l := 0.
Limits. ITS NAMED PREMISES ARE hCar_paid's AT THE FIVE-LIST, AND TWO MORE: the six-list's hM₆ | hZ₆
(hX_five_head takes them). At the second hash function. Nothing on soundness.


-/
import Johnson.Desc.First.Link.Law.HCarPaid
import Johnson.P5J.K10HXHead
import Johnson.LPFE1R.PlanSevenFive
import Johnson.P5J.HingeFiveAtMg
import Johnson.Desc.First.Close.Law.LinkZeroKept

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts FoldData bookAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks noK10 seatK10 rdK ShapesAre
  posOf keptOrd_full maskTree maskPart maskShape maskA maskSkip rdBK wrK LayoutAgrees layAt sizesM
  sizesZ loFive kbFive loSix seatsMain seatsOfLink zero_hr keptOrd_five HCarField hCar_heavy SbV
  slV ZV faK10 Par pullOf placeFull dBat dEps dTwo closeFrame noFiveAt)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt hB_at_k10 ld_at_laid keptRowsAt keptNosOf
  seatFiveAt keptRows_of_pub hr_at_laid row_at_laid batchAt bookAt_of_onQ SitsIn planClosedB mWRaw)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes atFirstBook atFirstSeats atFirstFits
  placesBelowB)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.First.K2Caller (carryAtZ places_of_promise SeatFitAt doorZ)
open _root_.Tw.K2 (switchNotices)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

theorem five_is_six (ps : List P5T.PSeat) (i : Fin loFive.length) :
    ∃ j : Fin (loAt 0).length, seatFiveAt ps i = seatK10 (loAt 0) ps 0 j := by
  obtain ⟨i, hi⟩ := i
  have hi' : i < 5 := hi
  interval_cases i
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩
  · exact ⟨⟨2, by decide⟩, rfl⟩
  · exact ⟨⟨4, by decide⟩, rfl⟩
  · exact ⟨⟨5, by decide⟩, rfl⟩

theorem AtMgA.hr_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ r', ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL 0 = some r' →
      (∃ t₀, stageOf (gsAt 0) 219 = stageOf r'.g t₀) ∧
      (∀ n, keptRowsAt r'.lo r'.mem r'.kp n =
        keptRowsAt loFive (memMain loFive) (fun a => kbFive a.1 = true) n) ∧
      r'.rad ≤ radFull := by
  intro r' hr
  obtain ⟨-, -, e3, -, -⟩ := hr_at_laid h.toAtMg.scope h.toAtMg.laid 0 r' hr
  obtain ⟨-, z2, z3⟩ := zero_hr r' (row_at_laid h.toAtMg.scope h.toAtMg.laid 0 r' hr)
  exact ⟨⟨219, by rw [e3]⟩, z2, z3⟩

theorem AtMgA.hord_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ r', ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL 0 = some r' → ∀ i : Fin loFive.length,
      memMain loFive i → kbFive i = true →
      (keptNosOf loFive kbFive)[r'.kept.idxOf i.val]? = some (posOf loFive i) :=
  fun r' hr => keptOrd_five r' (row_at_laid h.toAtMg.scope h.toAtMg.laid 0 r' hr)

theorem AtMgA.hPl_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ b : {i // memMain loFive i},
      LFull.places[noFiveAt (At.seats Zp) (At.pseats Zp) b.1]? =
        some (seatFiveAt (At.pseats Zp) b.1) := by
  intro b
  obtain ⟨j, hj⟩ := five_is_six (At.pseats Zp) b.1
  have e : noFiveAt (At.seats Zp) (At.pseats Zp) b.1 =
      (At.seats Zp).idxOf (seatFiveAt (At.pseats Zp) b.1) := rfl
  rw [e, hj]
  exact (hB_at_k10 h.toAtMg.scope h.toAtMg.laid (ld_at_laid h.toAtMg.scope h.toAtMg.laid)
    (by decide : (0 : ℕ) < 25) j).2.1

theorem AtMgA.hShp_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 0]? = some p)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) →
      ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr →
        ShapesAre (rdK a.1).2.2 Gr loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) :=
  fun z a hx => (h.hX_five_head p hp hM hZ hM₆ hZ₆ z a hx).shapes

/-- **THE FIELD hCar OF K10Heavy AT THE CLOSED CONSTANT's LETTERS, AT LINK 0, AT THE FIVE-LIST
  loFive: THE PAYERS LAID IN; WHAT HAS NO PAYER HERE STAYS A NAMED PREMISE.** -/
theorem AtMgA.hCar_paid_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt
      0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt
      0).get i).1 = (stageOf (gsAt 0) 219).Z)
    (keep : (sigOf (At.cs Zp) loFive).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G.Row B ≃ Fin
      n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)
      n num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) loFive).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp Wp)
    (L : List (BatFoldCaller GE))
    (smpD : ProofFile.InstPub × TS → (i : Fin loFive.length) → Option ((sigOf (At.cs Zp) loFive).om
            i).Smp)
    (σ₀ : (sigOf (At.cs Zp) loFive).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × TS → Option (CellsM numsFull))
    (c₀ : (CellsM numsFull))
    (tokOf : ProofFile.InstPub × TS → At.Tok)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ).G.A, ((sigOf (At.cs Zp) loFive).om a.1).Z.S), ((sigOf (At.cs Zp) loFive).om as.1.1).Z.D →
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).Sh.Cin.J → GE)
    {Cl : Type}
    (Pr : Par)
    (b : Block TS Cl)
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (ProofFile.InstPub × TS) × (Frame.E FR).Str → Iop.Tr (uLT (ckP .two)
            ds) → Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller
      keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (hp : At.ps[ixK10 0]? = some p)
    (hk : p.kind = KindName.K10)
    (hpl : p.link.getD 0 = 0)
    (hbase : base = (At.N Zp cF).treesAt At.ps[ixK10 0]?)
    (hbD : base ≤ D.t₁)
    (hgood : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).Good)
    (hLA : LayoutAgrees loFive kbFive)
    (hle : (gsAt 0).h ≤ (gsAt 0).k)
    (hSit : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 0)) loFive (seatFiveAt (At.pseats Zp)))
    (hS : ∀ b : {i // memMain loFive i}, SeatFitAt (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) loFive
      (seatFiveAt (At.pseats Zp)) b.1)
    (hpos : 2 ^ (stageOf (gsAt 0) 219).C.a ≤ 2 ^ (ProofFile.pAtK2 Zp 0).logN)
    (hPC : ∀ b : {i // memMain loFive i}, planClosedB (F0T OnBytes.secondHashFunction Zp Np cF) LFull (noFiveAt
                  (At.seats Zp) (At.pseats Zp) b.1) (seatFiveAt (At.pseats Zp) b.1) (aOf (At.cs Zp) (loFive.get
                  b.1).1) = true)
    (hGf : ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) → ∀ Gf, (rdK a.1).2.1.groups[(rdK
      a.1).2.1.link]? = some Gf → Gf.k = (gsAt 0).k ∧ Gf.h = (gsAt 0).h)
    (hDoor : ∀ z (a a' : TS × (Frame.E FR).Str) es rs, XK h 0 ((z, a.1), a.2) → closeFrame (rdK
      a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 es rs = .ok (rdBK a'.1) → a'.1 = wrK a.1 (rdBK a'.1).1
      (rdBK a'.1).2 → (∀ t, doorZ Zp 0 a'.1 = some t → (ProofFile.pAtK2 Zp 0).stands = .head → ∀ b,
      a'.1.here ≠ .head b) ∧ ∀ t fx', doorZ Zp 0 a'.1 = some t →
      VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) t = some fx' → ∃ Bk,
      VerifiableInference.Desc.First.K2.bookAt (VerifiableInference.Desc.First.K2.par9 (ProofFile.pAtK2 Zp
      0)).firstTree fx'.st t.book t.roots (switchNotices fx'.T fx'.others) = some Bk)
    (h2 : ∀ z (a : TS × (Frame.E FR).Str), (XK h 0) ((z, a.1), a.2) → ∃ (zz : (ZV (groupLayK (At.cs
      Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num).D) (v : ((sigOf (At.cs Zp)
      loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB
      keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp).Wit × Wp), (((sigOf (At.cs Zp)
      loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB
      keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp).over A₀).relR ((batX
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller keep
      (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (faK10 (F0T OnBytes.secondHashFunction Zp Np
      cF) (At.cs Zp) loFive (seatFiveAt (At.pseats Zp)) (groupLayK (At.cs Zp) loFive (stageOf (gsAt
      0) 219) radFull kbFive hM hZ) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) keep (pullOf (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ)) n num ((1 : Fin 3), (1 : GE)) A₀ (placeFull
      (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ (fun b : TS × (Frame.E FR).Str
      => mWRaw (At.cs Zp) loFive (memMain loFive) (stageOf (gsAt 0) 219) radFull (fun i => layAt
      (sizesM loFive kbFive) i.val) (fun i => layAt (sizesZ loFive) i.val) hM hZ (fun a => kbFive
      a.1 = true) (strsOf FR b.2) (maskTree 0) (maskSkip 0) (maskA 0)) z a).1 zz).2, ((ldBrG
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G ((groupLayK (At.cs
      Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive hM hZ) n num)).kp E₀).map (e₀, wordsOf (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp)
      loFive (seatFiveAt (At.pseats Zp)) (strsOf FR a.2))).2) v) :
    HCarField (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np
      cF) (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) L (At.smp Zp) smpD σ₀ st₀ e₀ (fun b : TS
      × (Frame.E FR).Str => mWRaw (At.cs Zp) loFive (memMain loFive) (stageOf (gsAt 0) 219) radFull
      (fun i => layAt (sizesM loFive kbFive) i.val) (fun i => layAt (sizesZ loFive) i.val) hM hZ
      (fun a => kbFive a.1 = true) (strsOf FR b.2) (maskTree 0) (maskSkip 0) (maskA 0)) (At.arr Zp)
      (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b base ex ix ρ (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 0) p (XK h 0) O (noFiveAt (At.seats Zp) (At.pseats Zp)) row k' := by
  have hl : (0 : ℕ) < 25 := by decide
  obtain ⟨m1, m2, m3⟩ := h.hMask_paid 0 hl
  unfold HCarField
  exact hCar_heavy (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep n num A₀ w₀ w₁ _ _ L (At.smp Zp)
    smpD σ₀ st₀ e₀ (At.arr Zp) (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b base ex ix ρ (At.N Zp cF)
    (mgAtAll h) fullLinks At.ps (ixK10 0) p (XK h 0) O _ row k' Zp Z.lay 0 D h.hW_paid (maskTree 0)
    (maskPart 0) (maskSkip 0) (maskA 0) LFull (maskShape 0) (h.hTie_paid 0 p hp hk hpl)
    h.hr_five hgood hLA hle h.hord_five hS h.hPl_five
    (h.hsB_paid 0 hl _ _ hSit base hbase) hbD hpos m1 m2 m3 (h.hShp_five p hp hM hZ hM₆ hZ₆)
    (k10_hCfX_at h 0 _ _ hSit) hPC
    (fun z a hx => by
      obtain ⟨f1, f2, f3, f4, f5⟩ := h.hFront_paid 0 hl (ixK10_is 0 hl).symm z a hx
      exact ⟨f1, f2, f3, f4, f5, h.hBelow_paid 0 hl base hbase z a hx, hGf z a hx⟩)
    hDoor h2

end P5J

#print axioms P5J.five_is_six
#print axioms P5J.AtMgA.hr_five
#print axioms P5J.AtMgA.hord_five
#print axioms P5J.AtMgA.hPl_five
#print axioms P5J.AtMgA.hShp_five
#print axioms P5J.AtMgA.hCar_paid_five
