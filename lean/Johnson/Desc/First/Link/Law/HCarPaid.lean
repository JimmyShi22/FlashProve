-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
hCar_paid's premise hDoor has the closing's own yes, as HCarHeavy.lean's has.


Johnson/Desc/First/Link/Law/HCarPaid.lean (kind K10; namespace P5J): THE PREMISES OF
  `hCar_heavy`
(Johnson/Desc/First/Link/Law/HCarHeavy.lean: the field hCar of `K10Heavy` in its own text) AT THE
  CLOSED
CONSTANT's LETTERS, ONE THEOREM A PREMISE, EACH IN THAT PREMISE's OWN FORM, BY CALLS OF THE LEMMAS
  THAT
HAVE PAID THEM. At: Z := Zp · lay := Z.lay · m := l · D := the head's D · Lp := the written plan's
  list
LFull · cs := At.cs Zp · lo := loAt l · gs := gsAt l · kb := kbW l · seat := seatK10 (loAt l)
(At.pseats Zp) l · no := noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l · X := XK h l · tree | tnF |
shF0 | aF | skip := maskTree l | maskPart l | maskShape l | maskA l | maskSkip l. Theorems. It
  changes
no other file.

  `AtMgA.hW_paid` (wholeAt_of_laid) · `AtMgA.hTie_paid`
  (k10_carry_behind) · `AtMgA.hr_paid` (hr_at_laid; keptRows_of_pub) ·
  `AtMgA.hord_paid` (keptOrd_full; row_at_laid) ·
  `AtMgA.hPl_paid` (hB_at_k10) · `AtMgA.hMask_paid` (hfs · hfa · hfskip:
  mask_letters_at) · `AtMgA.hShp_paid` (the clause «shapes» of hX_paid) ·
  `AtMgA.hFront_paid`: hFront's six clauses but the last (the frame's group's two numbers, which
  stays a premise hGf): «in step» (places_of_promise) · the three tests
  (FoldFacts at the written list; ft_at_switch) · the plan's list at the
  frame's mask (mask_at_letters).
  `AtMgA.hsB_paid` («below the base» at every message's seat: the table's
    fence test, `fenceFit_at`, at «it sits among the sampled whose pin is open») ·
    `AtMgA.hBelow_paid` (the first places of the plan's list name trees below the base:
    below_at; bookAt_of_onQ) · **`AtMgA.hCar_paid`: THE FIELD hCar OF K10Heavy AT THE CLOSED
    CONSTANT's LETTERS (as `HCarField ‹the 45›`, HCarField.lean), AT THE LIST loAt l, THE PAYERS
    LAID IN**; the typed letters that no payer names stay letters.

Limits. The links 0 … 24 at the list loAt l (at l = 0: the six-list; the five-list is not treated).
  hCar_paid's NAMED PREMISES, NOT PAID HERE: the place's three (hp · hk · hpl) · hbase (the base is
  the table's count of trees at K10's place) · hbD (the base is at most the first chain's number of
  trees) · hgood · hLA · hle · hSit · hS · hpos · hPC · hGf · hDoor · h2. At the format's second
  hash function. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HCarHeavy
import Johnson.Desc.First.Link.Law.HCarField
import Johnson.P5J.K10VCfAt
import Johnson.P5T.FenceAtMg
import Johnson.Desc.First.FenceFit
import Johnson.P5J.K10SeatsAt
import Johnson.P5J.K10CarryOut
import Johnson.P5J.MaskLettersAtMg
import Johnson.LPFE1R.TableClosed
import Johnson.Desc.First.Close.Law.KeptOrderFull
import Johnson.P1L20R.FrameFourAll
import Johnson.Top.H0.K2Caller.PlacesOf

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
  sizesZ HCarField hCar_heavy SbV slV ZV faK10 Par pullOf placeFull dBat dEps dTwo closeFrame)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt hB_at_k10 ld_at_laid keptRowsAt keptNosOf
  keptRows_of_pub hr_at_laid row_at_laid batchAt bookAt_of_onQ SitsIn planClosedB mWRaw)
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

theorem AtMgA.hW_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : ProofFile.wholeAt Zp = some D :=
  P1M2.wholeAt_of_laid h.laid

theorem AtMgA.hTie_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ)
    (p : VerifiableInference.Desc.Place)
    (hp : At.ps[ixK10 l]? = some p) (hk : p.kind = KindName.K10) (hpl : p.link.getD 0 = l) :
    ∀ (s : (ProofFile.InstPub × TS) × (Frame.E FR).Str) w,
      relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
        (outsQ fullLinks At.ps (ixK10 l)) s w → carryAtZ Zp Z.lay l s.1 (strsOf FR s.2) w := by
  intro s w hw
  have := k10_carry_behind h (ixK10 l) p hp hk s w hw
  rwa [hpl] at this

theorem AtMgA.hr_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) :
    ∀ r', ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL l = some r' →
      (∃ t₀, stageOf (gsAt l) 219 = stageOf r'.g t₀) ∧
      (∀ n, keptRowsAt r'.lo r'.mem r'.kp n =
        keptRowsAt (loAt l) (memMain (loAt l)) (fun a => kbW l a.1 = true) n) ∧
      r'.rad ≤ radFull := by
  intro r' hr
  obtain ⟨-, e2, e3, e4, e5⟩ := hr_at_laid h.toAtMg.scope h.toAtMg.laid l r' hr
  exact ⟨⟨219, by rw [e3]⟩, keptRows_of_pub r' (loAt l) (kbW l) e2 e4, e5⟩

theorem AtMgA.hord_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    ∀ r', ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL l = some r' → ∀ i : Fin (loAt l).length,
      memMain (loAt l) i → kbW l i = true →
      (keptNosOf (loAt l) (kbW l))[r'.kept.idxOf i.val]? = some (posOf (loAt l) i) :=
  fun r' hr => keptOrd_full l hl r' (row_at_laid h.toAtMg.scope h.toAtMg.laid l r' hr)

theorem AtMgA.hPl_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    ∀ b : {i // memMain (loAt l) i},
      LFull.places[noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l b.1]? =
        some (seatK10 (loAt l) (At.pseats Zp) l b.1) :=
  fun b => (hB_at_k10 h.toAtMg.scope h.toAtMg.laid
    (ld_at_laid h.toAtMg.scope h.toAtMg.laid) hl b.1).2.1

theorem AtMgA.hMask_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    LFull.shapes[maskTree l]? = some (maskShape l) ∧ (maskShape l).logN = maskA l ∧
      (maskShape l).mainWidth + ((maskShape l).maskSymbols.extract 0 (maskPart l)).foldl (· + ·) 0 =
        maskSkip l :=
  (h.toAtMg.mask_letters_at l hl).2

theorem AtMgA.hShp_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 l]? = some p)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      ∀ Gr, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some Gr →
        ShapesAre (rdK a.1).2.2 Gr (loAt l) (kbW l)
          (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) :=
  fun z a hx => (h.hX_paid LFull (ld_at_laid h.toAtMg.scope h.toAtMg.laid) h.fold_full l hl p hp hM
    hZ z a hx).shapes

/-- hFront's clauses, but the frame's group's two numbers. -/
theorem AtMgA.hFront_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (hix : batchAt fullLinks At.ps l + 3 = ixK10 l) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      a.1.book.place.size = a.1.st.oracles.size ∧
      atFirstBook (VerifiableInference.Desc.First.K2.par9 (ProofFile.pAtK2 Zp l)).firstTree a.1 = true ∧
      atFirstSeats LFull a.1 = true ∧ atFirstFits a.1 = true ∧
      ∀ mk, (rdK a.1).2.1.mask = some mk → LFull.places[mk]? = some (maskTree l, maskPart l) := by
  intro z a hx
  obtain ⟨hon, hr, hu'⟩ := hx
  have hu : a.1.failed = none := not_not.1 hu'
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  refine ⟨places_of_promise (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l)
    ((z, a.1), a.2) hon hu', ?_, h.fold_full.seatsCarried (ixK10 l) _ hr hu,
    h.fold_full.bookFits (ixK10 l) _ hr hu, fun mk hmk => ?_⟩
  · rw [P1L20.ft_at_switch O.pub l]
    exact h.fold_full.bookInOrder (ixK10 l) _ hr hu
  · obtain ⟨mk', h1, h2, -⟩ := h.toAtMg.mask_at_letters hl ((z, a.1), a.2) (by rw [hix]; exact hr)
    have h1' : (rdK a.1).2.1.mask = some mk' := h1
    rw [hmk] at h1'
    rw [Option.some.inj h1']
    exact h2

/-- «Below the base» at every message's seat, from «it sits among the sampled whose pin is open». -/
theorem AtMgA.hsB_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
    (hSit : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 l)) lo seat) (base : ℕ)
    (hbase : base = (At.N Zp cF).treesAt At.ps[ixK10 l]?) : ∀ i, (seat i).1 < base := by
  intro i
  rw [hbase]
  exact VerifiableInference.Desc.First.fenceFit_at _ _ _ h.toAtMg.fence (ixK10 l) (ix_le l hl) _
    (hSit i).2

/-- The new clause of hFront: the first places of the plan's list name trees below the base. -/
theorem AtMgA.hBelow_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (base : ℕ) (hbase : base = (At.N Zp cF).treesAt At.ps[ixK10 l]?) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      placesBelowB LFull a.1.book.place.size base = true := by
  intro z a hx
  have hb := h.below_at l hl ((z, a.1), a.2) hx
  obtain ⟨hon, -, hu'⟩ := hx
  have e := bookAt_of_onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l)
    ((z, a.1), a.2) hon (not_not.1 hu')
  unfold bookAt at e
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  rw [hbase, ← e.1.1]
  exact hb

/-- **THE FIELD hCar OF K10Heavy AT THE CLOSED CONSTANT's LETTERS, AT THE LIST loAt l: THE PAYERS
LAID IN; WHAT HAS NO PAYER HERE STAYS A NAMED PREMISE.** -/
theorem AtMgA.hCar_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).Z)
    (keep : (sigOf (At.cs Zp) (loAt l)).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G.Row B ≃
      Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) n num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) (loAt l)).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G
      ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num)).kp Wp)
    (L : List (BatFoldCaller GE))
    (smpD : ProofFile.InstPub × TS → (i : Fin (loAt l).length) → Option ((sigOf (At.cs Zp) (loAt l)).om
            i).Smp)
    (σ₀ : (sigOf (At.cs Zp) (loAt l)).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × TS → Option (CellsM numsFull))
    (c₀ : (CellsM numsFull))
    (tokOf : ProofFile.InstPub × TS → At.Tok)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).G.A, ((sigOf (At.cs Zp) (loAt l)).om a.1).Z.S), ((sigOf (At.cs Zp) (loAt l)).om
      as.1.1).Z.D → (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).Sh.Cin.J → GE)
    {Cl : Type}
    (Pr : Par)
    (b : Block TS Cl)
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (ProofFile.InstPub × TS) × (Frame.E FR).Str → Iop.Tr (uLT (ckP .two)
            ds) → Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).foldCaller
      keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num) ((1 : Fin 3), (1 :
      GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT
      dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (hp : At.ps[ixK10 l]? = some p) (hk : p.kind = KindName.K10) (hpl : p.link.getD 0 = l)
    (hbase : base = (At.N Zp cF).treesAt At.ps[ixK10 l]?) (hbD : base ≤ D.t₁)
    (hgood : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).Good)
    (hLA : LayoutAgrees (loAt l) (kbW l)) (hle : (gsAt l).h ≤ (gsAt l).k)
    (hSit : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 l)) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l))
    (hS : ∀ b : {i // memMain (loAt l) i}, SeatFitAt (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp)
      (loAt l)
      (seatK10 (loAt l) (At.pseats Zp) l) b.1)
    (hpos : 2 ^ (stageOf (gsAt l) 219).C.a ≤ 2 ^ (ProofFile.pAtK2 Zp l).logN)
    (hPC : ∀ b : {i // memMain (loAt l) i}, planClosedB (F0T OnBytes.secondHashFunction Zp Np cF) LFull
      (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l b.1) (seatK10 (loAt l) (At.pseats Zp) l b.1)
      (aOf (At.cs Zp) ((loAt l).get b.1).1) = true)
    (hGf : ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) → ∀ Gf,
      (rdK a.1).2.1.groups[(rdK a.1).2.1.link]? = some Gf →
        Gf.k = (gsAt l).k ∧ Gf.h = (gsAt l).h)
    (hDoor : ∀ z (a a' : TS × (Frame.E FR).Str) es rs, XK h l ((z, a.1), a.2) →
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 es rs = .ok (rdBK a'.1) →
      a'.1 = wrK a.1 (rdBK a'.1).1 (rdBK a'.1).2 →
      (∀ t, doorZ Zp l a'.1 = some t → (ProofFile.pAtK2 Zp l).stands = .head →
        ∀ b, a'.1.here ≠ .head b) ∧
      ∀ t fx', doorZ Zp l a'.1 = some t →
        VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp l) t = some fx' →
        ∃ Bk, VerifiableInference.Desc.First.K2.bookAt
          (VerifiableInference.Desc.First.K2.par9 (ProofFile.pAtK2 Zp l)).firstTree fx'.st t.book t.roots
          (switchNotices fx'.T fx'.others) = some Bk)
    (h2 : ∀ z (a : TS × (Frame.E FR).Str), (XK h l) ((z, a.1), a.2) → ∃ (zz : (ZV (groupLayK (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num).D) (v : ((sigOf (At.cs Zp)
      (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
      (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num)).kp).Wit ×
      Wp), (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n
      num)).kp).over A₀).relR ((batX ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n
      num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ w₀ w₁)
      (faK10 (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l)
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (namesOf (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l)
      (At.pseats Zp) l)) keep (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ)) n num ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt
      l).k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) (loAt l)
      (memMain (loAt l)) (stageOf (gsAt l) 219) radFull (fun i => layAt (sizesM (loAt l) (kbW l))
      i.val) (fun i => layAt (sizesZ (loAt l)) i.val) hM hZ (fun a => (kbW l) a.1 = true) (strsOf FR
      b.2) (maskTree l) (maskSkip l) (maskA l)) z a).1 zz).2, ((ldBrG (groupLayK (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) n num)).kp E₀).map (e₀, wordsOf (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (loAt l) (seatK10
                  (loAt l) (At.pseats Zp) l) (strsOf FR a.2))).2) v) :
    HCarField (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp
      Np cF) (seatK10 (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) L (At.smp Zp) smpD σ₀
      st₀ e₀ (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) (loAt l) (memMain (loAt l)) (stageOf
      (gsAt l) 219) radFull (fun i => layAt (sizesM (loAt l) (kbW l)) i.val) (fun i => layAt (sizesZ
      (loAt l)) i.val) hM hZ (fun a => kbW l a.1 = true) (strsOf FR b.2) (maskTree l) (maskSkip l)
      (maskA l)) (At.arr Zp) (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b base ex ix ρ (At.N Zp cF)
      (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) O (noK10 (At.seats Zp) (loAt l) (At.pseats
      Zp) l) row k' := by
  obtain ⟨m1, m2, m3⟩ := h.hMask_paid l hl
  unfold HCarField
  exact hCar_heavy (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep n num A₀ w₀ w₁ _ _ L (At.smp Zp)
    smpD σ₀ st₀ e₀ (At.arr Zp) (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b base ex ix ρ (At.N Zp cF)
    (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) O _ row k' Zp Z.lay l D h.hW_paid (maskTree l)
    (maskPart l) (maskSkip l) (maskA l) LFull (maskShape l) (h.hTie_paid l p hp hk hpl)
    (h.hr_paid l) hgood hLA hle (h.hord_paid l hl) hS (h.hPl_paid l hl)
    (h.hsB_paid l hl _ _ hSit base hbase) hbD hpos m1 m2 m3 (h.hShp_paid l hl p hp hM hZ)
    (k10_hCfX_at h l _ _ hSit) hPC
    (fun z a hx => by
      obtain ⟨f1, f2, f3, f4, f5⟩ := h.hFront_paid l hl (ixK10_is l hl).symm z a hx
      exact ⟨f1, f2, f3, f4, f5, h.hBelow_paid l hl base hbase z a hx, hGf z a hx⟩)
    hDoor h2

end P5J

#print axioms P5J.AtMgA.hW_paid
#print axioms P5J.AtMgA.hTie_paid
#print axioms P5J.AtMgA.hr_paid
#print axioms P5J.AtMgA.hord_paid
#print axioms P5J.AtMgA.hPl_paid
#print axioms P5J.AtMgA.hMask_paid
#print axioms P5J.AtMgA.hShp_paid
#print axioms P5J.AtMgA.hFront_paid
#print axioms P5J.AtMgA.hsB_paid
#print axioms P5J.AtMgA.hBelow_paid
#print axioms P5J.AtMgA.hCar_paid
