-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsFirstWhole.lean: WHAT THE ASSEMBLY OF K4's LAW LEAVES AT THE FIRST GROUP
(`K4FirstAt`, Johnson/Road/K4/K04LawOf.lean),
AT THE WIDER MEANING
`mgWide 𝔇 E Mg₀` AND THE DATA OFF ITS OWN PARAMETERS: THE TWIN OF K4PinsLaterWhole.lean AND OF THE
FOUR FILES BENEATH IT, IN ONE FILE. The statements and proofs are cut BY PROGRAM out of the later
group's own texts: what parts: the value (`(….atRecF X p).toPlan4K`), the structure `K4PlanFitF` (no
seam), the closed law `k4PlanFitF_fast` (one test), `forms_pinsF`. No draw, no count.

  `planFitF_congr`, `fitF_wide`: the field fit. `idx_at_v7F`, `maskF_wide`: the field mask.
    `formsF_wide`: the field forms.
  **`firstAt_whole`**: `Nonempty (K4FirstAt x links ps k (2 * g) q (k4DataWide 𝔇 E Mg₀) (mgWide 𝔇 E
    Mg₀) z)`: ALL TEN LETTERS LAID; SEVEN OF THE TWELVE FIELDS CONCLUDED BY CALLS (tiesM · fit ·
    rides · encIs · rwMat · mask · forms); FIVE ARE BINDERS: B · hla · hV · NE (facts on the public
    parameters) · reqT (three ties on the data's letters for the request).

OBJECT: `k4DataWide 𝔇 E Mg₀`, `mgWide 𝔇 E Mg₀`. USER: `firstAt_scope_at`
(Johnson/Road/K4/K4PinsFirstScope.lean); meant: the top theorem of K4's law at the wider meaning
(its binder on the first group). LETTERS: as named. NOTHING IN IT ASKS THAT THE
GROUP IS THE FIRST.

Limits. K04_law IS NOT PROVED BY THIS. B, hla, hV, NE, reqT, left, four AND st ARE NOT CONCLUDED.
TEN NAMED EQUATIONS ON 𝔇's PARAMETERS AND ONE LINE ON 𝔇.H (asked as it is spent)
ARE PREMISES. TEN TESTS: WHAT EACH HAS ANSWERED, WHERE, AND WITH WHICH NEGATIVE TESTS IS NOT
SAID HERE. NO MEMBER IS SHOWN. IT SPEAKS AT THE WIDER MEANING: it counts only when the bridge to the
meaning that counts is paid. TWO LETTERS STAND FOR THE PUBLIC FILES (Pb, Zp), tied by
`publicOf`'s return alone.
-/
import Johnson.Road.K4.K4PinsLaterWhole
import Johnson.Road.K4.FormsAtPinsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public publicOf)
open VerifiableInference.PlanWritten (PublicSteps)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open VerifiableInference.OnPublicFiles (LeftQ)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Wit Strs Claim Link K9.LinkHoles K9.statesOfLink
  K9.readersOfLink
  K9.segAt? K9.maskSeat)
open OnBytes.Desc.First.K4.Total (frontB)
open OnBytes.Road.K4.InT (StatesAt oneRowB readsThereB)
open VerifiableInference.Desc.First.FillBare (lookLeftB)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.Look (Place szOf pubAt stepOf Stored.entries Stored.NoRec)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.Desc.K13.Law (matOfCells)
open Meaning (seatsOf seatBy fLay laidThere)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (EShapes EBook0 ESeats ECodes openMaskB maskFitsB recPlanOf readsArrayP
  maskPlanB arraysPlanB maskEllP openAllB)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open OnBytes.Model.Verify (layerShape)
open OnBytes.Model (Forest.elems)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls LayPub tlAt)
open OnBytes.Model.Layer (Lay Pub Own)
open OnBytes.Model (HTailF2)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4.InT (InTAsks)
open Cb.Pv.Tail (Size)
open Inst.Model.Layout (kRef hRef)

/-- `K4PlanFitF` rides along equations of its letters. -/
theorem planFitF_congr {X : Public} {p : Par} (x : Place) (q : LayPub)
    {D D' : Sent} (hD : D' = D) (rad : OracleShape → ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (seatT' : Fin (sigListCalls D' rad x.link).length → ℕ × ℕ)
    (hs : ∀ (j : Fin (sigListCalls D' rad x.link).length)
      (j' : Fin (sigListCalls D rad x.link).length), j.1 = j'.1 → seatT' j = seatT j')
    (posI : ℕ → Bool × ℕ × ℕ) (oW : Cb.OMsg Cb.Gl.E)
    (enc : (Fin hRef → Fin (2 ^ kRef) → Cb.Gl.E) → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E)
    {arr arr' : ℕ → ℕ → ℕ} (ha : arr' = arr) {ms ms' : List Mem} (hm : ms' = ms)
    {N N' : Numbers} (hN : N' = N) (m nM nR nC first : ℕ) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (hd : ℕ)
    (F : K4PlanFitF (X := X) (p := p) x q D rad seatT posI oW enc wOf arr ms N m nM nR nC first s
      seat hd) :
    K4PlanFitF (X := X) (p := p) x q D' rad seatT' posI oW enc wOf arr' ms' N' m nM nR nC first s
      seat hd := by
  subst hD ha hm hN
  obtain rfl : seatT' = seatT := funext fun j => hs j j rfl
  exact F

section
variable {Xi P Tok : Type} {nR : ℕ}

/-- **`K4PlanFitF` at the wider meaning's own parameters.** -/
theorem fitF_wide {pol KL : ByteArray} {tk : Array Nat} (Z : ProofFile.Pub) (radM : ℕ → ℕ → ℕ)
    (𝔇 : MgData Xi P Tok hRef (2 ^ kRef) nR Z.p.X) (E : WideData P)
    (Mg₀ : Meaning P (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)) (p : Par)
    (Q1 : 𝔇.sent = sentAt Z) (Q2 : 𝔇.arr = arrAt Z) (Q3 : 𝔇.ms = P5T.msAtR Z radM)
    (Q4s : 𝔇.N.sent = (numbersAt Z).sent) (Q4i : 𝔇.N.index = (numbersAt Z).index)
    (Q6 : ∀ l j, 𝔇.seat3 l false j = P6T.seatCallsT (seatsAt Z) (sentAt Z) l j)
    (hf : firstFastB Z p.g = true) (hg : p.g < 12) (x : Place)
    (hx : x.link = 2 * p.g) (hG : Z.p.X.G[p.g]? = some p.hp) (posI : ℕ → Bool × ℕ × ℕ)
    (St' : PublicSteps pol KL Z.p.X) (B : RefPub Z.p.X p.g)
    (hP : p.P = { Z.p.X.layers with tokv := tk }) (P0 : PlaceIs x p 0)
    (hgr : 2 * p.g / stepOf Z.p.X = p.g) (hhd : 2 * p.g ≠ headLink Z.p.X) :
    K4PlanFitF (X := Z.p.X) (p := p) x (pubAt Z.p.X (2 * p.g / stepOf Z.p.X))
      (sentOf (k4DataWide 𝔇 E Mg₀)) (k4DataWide 𝔇 E Mg₀).L3.rad
      (fun j => (k4DataWide 𝔇 E Mg₀).L3.seat x.link false j.1) posI (k4DataWide 𝔇 E Mg₀).L3.oW
      Stored.entries (k4DataWide 𝔇 E Mg₀).L3.wOf (k4DataWide 𝔇 E Mg₀).arr
      (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N (2 * p.g) (szOf p.hp.tl).NM
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).m)
      ((Finset.range (szOf p.hp.tl).NM).sup (szOf p.hp.tl).k) 0 (_root_.Meaning.sizesOf Z.p.X)
      (seatBy (fLay (sentAt Z).layout (numAt Z)) Z.p.X (_root_.Meaning.sizesOf Z.p.X))
      (k4DataWide 𝔇 E Mg₀).hd :=
  planFitF_congr x _ (D := sentAt Z) Q1 𝔇.rad3 (seatTAt Z 𝔇.rad3 x.link) _
    (fun j j' e => by
      show 𝔇.seat3 x.link false j.1 = P6T.seatCallsT (seatsAt Z) (sentAt Z) x.link j'.1
      rw [Q6, e])
    posI _ Stored.entries _ Q2 Q3 rfl _ _ _ _ _ _ _ _
    (k4PlanFitF_fast Z radM Q4s Q4i p hf hg x hx hG 𝔇.rad3 posI _ Stored.entries _
      (headLink Z.p.X) St' B hP P0 hgr hhd)

end

section
variable [scl : Scl]

/-- **The first group's value's entry v7 of the index masks is an entry of the witness's own
table.** -/
theorem idx_at_v7F {Cells Tok : Type} (A : PinPlan Cells) (n' : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m n : ℕ) (cs : OnBytes.Codes)
    (h : IndexFit cs A.posI ms N n) (hv : v7 < n) :
    ∃ u, memAt ms N.index = some u ∧ ∀ w : Wit Cells Tok MsgT,
      ((A.seatN n' N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K.toL.plan.idxAt
          (partOf cs arr ms N m w)
          ((A.seatN n' N tl y nM nR nC n0 ns nx v7).atRecF X p).toPlan4K.toL.plan.v7 =
        memTab cs arr w u (A.posI v7).1 (A.posI v7).2.1 (A.posI v7).2.2 := by
  obtain ⟨u, hu, H⟩ := idx_of_fit (Tok := Tok) A arr ms N m n cs h
  exact ⟨u, hu, fun w => H w v7 hv⟩

end

section
variable [scl : Scl] {Fr : Frame} {Xi Tok : Type} {nR : ℕ} {X : Public}

/-- **The field mask at the first group's value.** -/
theorem maskF_wide (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nR X)
    (E : WideData ProofFile.InstPub)
    (Mg₀ Mg : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)) (z : ProofFile.InstPub)
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k m : ℕ) (p : Par)
    (xL : Place) (nM nRr nC : ℕ)
    (eS : EShapes Mg E.d12.M) (eB : EBook0 Mg) (eSe : ESeats Mg E.d12.L) (eC : ECodes Mg 𝔇.cs)
    (hO : openMaskB Mg.more links ps (k + 1) = true)
    (hF : maskFitsB 𝔇.cs E.d12.M E.d12.L (𝔇.N.msgsAt ps[k + 1]?) (𝔇.N.treesAt ps[k + 1]?)
      𝔇.N.indexNo (rowsBefore E.dP.fvs m) = true)
    (hT : indexTieB 𝔇.cs E.d12.M E.d12.L.places 𝔇.ms 𝔇.N (rowsBefore E.dP.fvs m + 1) = true) :
    ∀ (b : S × Fr.E.Str) w,
      onQ (k4DataWide 𝔇 E Mg₀).N Mg links ps (fun s => (z, s)) (k + 1) b → b.1.failed = none →
      ((k4DataWide 𝔇 E Mg₀).rw13 (z, b.1) w).mask
          ⟨(k4DataWide 𝔇 E Mg₀).N.indexNo,
            Rec.nextNoP (k4DataWide 𝔇 E Mg₀).d12.M ((k4DataWide 𝔇 E Mg₀).N.msgsAt ps[k + 1]?)
              (k4DataWide 𝔇 E Mg₀).N.indexNo (k4DataWide 𝔇 E Mg₀).fvs m⟩ =
        (qkFAt (k4DataWide 𝔇 E Mg₀) p m xL (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo))
          Stored.entries nM nRr nC (rowsBefore E.dP.fvs m)
            (rowsBefore E.dP.fvs m)).toPlan4K.toL.plan.full.msg
          (partOf (sentOf (k4DataWide 𝔇 E Mg₀)).codes (k4DataWide 𝔇 E Mg₀).arr
            (k4DataWide 𝔇 E Mg₀).ms (k4DataWide 𝔇 E Mg₀).N m w)
          (qkFAt (k4DataWide 𝔇 E Mg₀) p m xL (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo))
            Stored.entries nM nRr nC (rowsBefore E.dP.fvs m)
            (rowsBefore E.dP.fvs m)).toPlan4K.toL.plan.full.c7 := by
  obtain ⟨sh, u, hM, hq, hu, hsh, hst, hI⟩ := indexTie_of_B hT
  have hmr : maskRowsAt E.d12.M 𝔇.N.indexNo = sh.maskRows := by
    unfold maskRowsAt
    rw [hM]
    rfl
  rw [← hmr] at hI
  obtain ⟨u', hu', hidx⟩ := idx_at_v7F (Tok := Tok)
    (pinAt (k4DataWide 𝔇 E Mg₀) xL (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)) Stored.entries)
    xL.ns 𝔇.N p.hp.tl (VerifiableInference.Desc.First.Look.pubAt X
      (m / VerifiableInference.Desc.First.Look.stepOf X)).y nM nRr nC
    (OnBytes.Model.Forest.elems X.layers.y.fo) p.hp.ns (rowsBefore E.dP.fvs m)
    (rowsBefore E.dP.fvs m) X p 𝔇.arr 𝔇.ms m (rowsBefore E.dP.fvs m + 1) 𝔇.cs hI
    (Nat.lt_succ_self _)
  obtain rfl : u' = u := Option.some.inj (hu'.symm.trans hu)
  exact woMaskTie 𝔇.N Mg z links ps (k + 1) m E.d12.M E.d12.L 𝔇.cs E.dP.fvs sh 𝔇.N.index _
    (partOf 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N m) u' (posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)
      (rowsBefore E.dP.fvs m)) nR 𝔇.P13.lin.kCol 𝔇.arr 𝔇.mat13 eS eB eSe eC hO hF hM hq
    ⟨Nat.le_refl _, hsh, hst, by rw [hmr]; rfl⟩ hidx

end

section
variable [scl : Scl] {Fr : Frame} {Xi Tok : Type} {nR : ℕ} {X : Public}
  (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nR X) (E : WideData ProofFile.InstPub)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT))

/-- the data -/
local notation "𝐃" => k4DataWide 𝔇 E Mg₀
/-- the meaning -/
local notation "𝐌" => mgWide 𝔇 E Mg₀

/-- **The field forms at the first group's value.** -/
theorem formsF_wide (z : ProofFile.InstPub) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k m : ℕ) (x : Bool × Par)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT))
    (xL : Place) (posI : ℕ → Bool × ℕ × ℕ) (nM nRr nC nx v7 : ℕ)
    (Em : K4Means (𝐌) (𝐃)) {Hh : K9.LinkHoles} {l : Link S Claim}
    (hRd : (𝐃).Rd m = K9.readersOfLink Hh l)
    (hruns : (𝐃).runs m 3 "own" = [(2, "front"), (2, "back")])
    {pl : VerifiableInference.Desc.Place} (H : AtK4 links ps k m pl) {lm : ℕ}
    (Kf : K4Front (𝐌) z links ps m (parOf x).P.y.fo lm 0 (LeftQ (parOf x).hp.ns)) {ns : ℕ}
    (hnsD : (𝐃).nsOf m = some ns)
    (hBf : frontB (!(parOf x).k3Runs) (parOf x).P (parOf x).hp (parOf x).g (parOf x).P.y.fo =
      true)
    (left : ∀ a : S × Fr.E.Str, onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) k a →
      a.1.failed = none → lookLeftB a.1 = true)
    (four : ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ a τ fo o G',
      onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) k a → a.1.failed = none →
      Yes seatS (parOf x) (twinOf q B') a τ fo o G' →
      (∀ o', (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' →
        (parOf x).hp.nU.getD 2 0 ≤ o'.v.K3) ∧
      (∀ A, K9.segAt? (behindOf seatS (twinOf q B') a τ o G').1 = some A →
        (K9.maskSeat ((𝐃).N.sent m 0) A).isSome = true) ∧
      (∀ G o', (behindOf seatS (twinOf q B') a τ o G').1.fork? = some G →
        (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' → oneRowB G o'.v.iU3 = true) ∧
      ∀ A o', K9.segAt? (behindOf seatS (twinOf q B') a τ o G').1 = some A →
        (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' →
        readsThereB A o'.v.iU3 ((parOf x).hp.nU.getD 2 0) = true)
    (st : ∀ s : S, StatesAt (K9.statesOfLink l) 2 (parOf x) "front" s ∧
      StatesAt (K9.statesOfLink l) 2 (parOf x) "back" s)
    (hO : openAllB (𝐃).moreL links ps k m = true)
    (hArr : readsArrayP (parOf x).hp (𝐃).D3.shape (𝐃).D3.layout ((𝐃).D3.arrayOf.getD m #[]) m
      ((𝐃).sd.trees m) = true)
    (hMask : maskPlanB (pinAt (𝐃) xL posI Stored.entries) ((𝐃).N.sent m 0)
      (recPlanOf (𝐃) (𝐃).sd) ((𝐃).N.msgsAt ps[k]?) m = true)
    (hCells : arraysPlanB (pinAt (𝐃) xL posI Stored.entries) (parOf x).hp.tl ((𝐃).N.sent m 0)
      (recPlanOf (𝐃) (𝐃).sd) ((𝐃).N.msgsAt ps[k]?) m = true)
    (hell : xL.ns ≤ maskEllP (pinAt (𝐃) xL posI Stored.entries))
    (hsits : SitsIn (sigListCalls (sentOf (𝐃)) (𝐃).L3.rad xL.link)
      (fun j => (𝐃).L3.seat xL.link false j.1) (𝐃).ms (𝐃).N m)
    (hcov : Covers (parOf x).hp.tl nM nRr nC)
    (hl : xL.link = m) (hs : xL.ns = (parOf x).hp.ns) (huL : 𝔇.uL = uLAt X (namesOf 𝔇.built))
    (htl : tlAt X m = some (parOf x).hp.tl) :
    ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ b w,
      ((qkFAt (𝐃) (parOf x) m xL posI Stored.entries nM nRr nC nx v7).lettersOfF (Fr := Fr)
        (partOf (sentOf (𝐃)).codes (𝐃).arr (𝐃).ms (𝐃).N m) (parOf x) 0 (parOf x).P.y.fo
        (LeftQ (parOf x).hp.ns) (tableOn0 (𝐃).N (𝐌) z links ps k)
        (keptFrom (tableOn0 (𝐃).N (𝐌) z links ps k) (parOf x) (twinOf q B'))
        (tableCtx0 (𝐃).N (𝐌) z m)
        (decOf (sentOf (𝐃)).codes (𝐃).G (𝐃).smp (𝐃).ms (𝐃).decT (𝐃).N z m)).on' b →
      onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) (𝐃).N (𝐌) (fun s => (z, s)) (.formsT m 3 "own") b w →
      FormsT seatS ((qkFAt (𝐃) (parOf x) m xL posI Stored.entries nM nRr nC nx v7).toPlan4K.semOf
        (partOf (sentOf (𝐃)).codes (𝐃).arr (𝐃).ms (𝐃).N m) (parOf x).hp.tl)
        (frontRun (parOf x)) formsBack b.1 w := by
  intro B' hB b w hon
  have asks := Riders.asks_of_means (q := twinOf q B') (par := parOf x) Em H Kf rfl hnsD hBf left
    (four B' hB) st
  exact forms_pinsF (pinAt (𝐃) xL posI Stored.entries) xL.ns (pubAt X (m / stepOf X)).y nM nRr nC
    (Forest.elems X.layers.y.fo) (parOf x).hp.ns nx v7 Em hRd hruns rfl rfl asks hO hArr hMask
    hCells hell hsits hcov (hns_of_front H Kf (Nat.le_of_eq hs.symm))
    (hSt_built 𝔇 E Mg₀ (pinAt (𝐃) xL posI Stored.entries) Em huL rfl hl hO
      (fun a τ fo o G' ha hu Y => by
        obtain ⟨_, _, As, _⟩ := asks a τ fo o G' ha hu Y
        exact As.sized)
      htl hCells) b w hon

end

variable [scl : Scl] {Fr : Frame} {Xi : Type} {nR : ℕ} (Zp : ProofFile.Pub)
  (𝔇 : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nR Zp.p.X) (E : WideData ProofFile.InstPub)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT)) (x : Bool × Par)

/-- the data -/
local notation "𝐃" => k4DataWide 𝔇 E Mg₀
/-- the meaning -/
local notation "𝐌" => mgWide 𝔇 E Mg₀
set_option quotPrecheck false in
/-- the seats of the symbols -/
local notation "𝐬" => seatBy (fLay (sentAt Zp).layout (numAt Zp)) Zp.p.X
  (_root_.Meaning.sizesOf Zp.p.X)

set_option quotPrecheck false in
/-- where the value reads the index masks -/
local notation "𝐩" => posFree (maskRowsAt E.d12.M 𝔇.N.indexNo)
set_option quotPrecheck false in
/-- the number of the segment's entry of the index masks -/
local notation "𝐯" => rowsBefore E.dP.fvs (2 * (parOf x).g)

/-- **`K4FirstAt` at the wider meaning, whole but for five fields and three binders on runs and
states.** -/
theorem firstAt_whole {Pb : VerifierAndGoals.PublicFiles} {ly : Option ByteArray}
    {tk : Array Nat} (radM : ℕ → ℕ → ℕ)
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k : ℕ)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (hg : (parOf x).g < 12) (z : ProofFile.InstPub)
    (h : publicOf Pb.pol Pb.KL ly = .ok Zp.p.X)
    (hn : 2 * (parOf x).g ≠ (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr)
    (h0 : 2 * (parOf x).g % (if Zp.p.X.p4 then 2 else 1) = 0)
    (hplan : Zp.p.X.G[2 * (parOf x).g / (if Zp.p.X.p4 then 2 else 1)]? = some (parOf x).hp)
    (hpc : VerifiableInference.Desc.K3.pieceAt Zp.p.X (2 * (parOf x).g) false = 2)
    (hy : (parOf x).P.y = Zp.p.X.y) (h4 : Zp.p.X.p4 = true)
    (hG : Zp.p.X.G[(parOf x).g]? = some (parOf x).hp)
    (St' : PublicSteps Pb.pol Pb.KL Zp.p.X) (B : RefPub Zp.p.X (parOf x).g)
    (hP : (parOf x).P = { Zp.p.X.layers with tokv := tk })
    (hf : firstFastB Zp (parOf x).g = true)
    (hla : (layerShape Zp.p.X.P).la = 16) (hV : (parOf x).P.V = ppref.V)
    (NE : EmbNums (parOf x).P.y) (reqT : ReqTies (𝐃).reqB (𝐃).reqW (𝐃).H.req (𝐃).put)
    (Q1 : 𝔇.sent = sentAt Zp) (Q2 : 𝔇.arr = arrAt Zp) (Q3 : 𝔇.ms = P5T.msAtR Zp radM)
    (Q4s : 𝔇.N.sent = (numbersAt Zp).sent) (Q4i : 𝔇.N.index = (numbersAt Zp).index)
    (Q6 : ∀ l j, 𝔇.seat3 l false j = P6T.seatCallsT (seatsAt Zp) (sentAt Zp) l j)
    (Q5 : ∀ w, (𝔇.H.hid w).MG (parOf x).g =
      _root_.Meaning.mgOf Zp.p.X.y
        (ownW 𝔇.arr 𝔇.ms 𝔇.N (_root_.Meaning.sizesOf Zp.p.X) (𝐬) 𝔇.cs w) (parOf x).g)
    {seats : List (ℕ × ℕ)} (Q7 : 𝔇.smp = smpNamed 𝔇.cs seats) (Q8 : Stored.NoRec 𝔇.decT)
    (Q10 : 𝔇.mat13 = matOfCells nR 𝔇.P13.lin.kCol)
    (eS : EShapes (𝐌) E.d12.M) (eB : EBook0 (𝐌)) (eSe : ESeats (𝐌) E.d12.L) (eC : ECodes (𝐌) 𝔇.cs)
    (hO : openMaskB (𝐌).more links ps (k + 1) = true)
    (hF : maskFitsB 𝔇.cs E.d12.M E.d12.L (𝔇.N.msgsAt ps[k + 1]?) (𝔇.N.treesAt ps[k + 1]?)
      𝔇.N.indexNo (𝐯) = true)
    (hT : indexTieB 𝔇.cs E.d12.M E.d12.L.places 𝔇.ms 𝔇.N (𝐯 + 1) = true)
    (Em : K4Means (𝐌) (𝐃)) {Hh : K9.LinkHoles} {l : Link S Claim}
    (hRd : (𝐃).Rd (2 * (parOf x).g) = K9.readersOfLink Hh l)
    (hruns : (𝐃).runs (2 * (parOf x).g) 3 "own" = [(2, "front"), (2, "back")])
    {pl : VerifiableInference.Desc.Place} (H : AtK4 links ps k (2 * (parOf x).g) pl) {lm : ℕ}
    (Kf : K4Front (𝐌) z links ps (2 * (parOf x).g) (parOf x).P.y.fo lm 0
      (LeftQ (parOf x).hp.ns)) {ns : ℕ} (hnsD : (𝐃).nsOf (2 * (parOf x).g) = some ns)
    (hBf : frontB (!(parOf x).k3Runs) (parOf x).P (parOf x).hp (parOf x).g (parOf x).P.y.fo =
      true)
    (left : ∀ a : S × Fr.E.Str, onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) k a →
      a.1.failed = none → lookLeftB a.1 = true)
    (four : ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ a τ fo o G',
      onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) k a → a.1.failed = none →
      Yes seatS (parOf x) (twinOf q B') a τ fo o G' →
      (∀ o', (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' →
        (parOf x).hp.nU.getD 2 0 ≤ o'.v.K3) ∧
      (∀ A, K9.segAt? (behindOf seatS (twinOf q B') a τ o G').1 = some A →
        (K9.maskSeat ((𝐃).N.sent (2 * (parOf x).g) 0) A).isSome = true) ∧
      (∀ G o', (behindOf seatS (twinOf q B') a τ o G').1.fork? = some G →
        (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' → oneRowB G o'.v.iU3 = true) ∧
      ∀ A o', K9.segAt? (behindOf seatS (twinOf q B') a τ o G').1 = some A →
        (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' →
        readsThereB A o'.v.iU3 ((parOf x).hp.nU.getD 2 0) = true)
    (st : ∀ s : S, StatesAt (K9.statesOfLink l) 2 (parOf x) "front" s ∧
      StatesAt (K9.statesOfLink l) 2 (parOf x) "back" s)
    (hOa : openAllB (𝐃).moreL links ps k (2 * (parOf x).g) = true)
    (hArr : readsArrayP (parOf x).hp (𝐃).D3.shape (𝐃).D3.layout
      ((𝐃).D3.arrayOf.getD (2 * (parOf x).g) #[]) (2 * (parOf x).g)
      ((𝐃).sd.trees (2 * (parOf x).g)) = true)
    (hMask : ∀ xL : Place, xL.link = 2 * (parOf x).g → xL.ns = (parOf x).hp.ns →
      maskPlanB (pinAt (𝐃) xL (𝐩) Stored.entries) ((𝐃).N.sent (2 * (parOf x).g) 0)
        (recPlanOf (𝐃) (𝐃).sd) ((𝐃).N.msgsAt ps[k]?) (2 * (parOf x).g) = true)
    (hCells : ∀ xL : Place, xL.link = 2 * (parOf x).g → xL.ns = (parOf x).hp.ns →
      arraysPlanB (pinAt (𝐃) xL (𝐩) Stored.entries) (parOf x).hp.tl
        ((𝐃).N.sent (2 * (parOf x).g) 0) (recPlanOf (𝐃) (𝐃).sd) ((𝐃).N.msgsAt ps[k]?)
        (2 * (parOf x).g) = true)
    (hell : ∀ xL : Place, xL.link = 2 * (parOf x).g → xL.ns = (parOf x).hp.ns →
      xL.ns ≤ maskEllP (pinAt (𝐃) xL (𝐩) Stored.entries))
    (huL : 𝔇.uL = uLAt Zp.p.X (namesOf 𝔇.built)) :
    Nonempty (K4FirstAt x links ps k (2 * (parOf x).g) q (𝐃) (𝐌) z) := by
  obtain ⟨xL, hl, hs, P0, hW⟩ :=
    ties_of_plan (𝐃).L3 (parOf x) h hn h0 hplan (Nat.mul_mod_right 2 _) hpc hy rfl rfl
  have F := fitF_wide Zp radM 𝔇 E Mg₀ (parOf x) Q1 Q2 Q3 Q4s Q4i Q6 hf hg xL hl hG (𝐩) St' B hP P0
    (group_at h4 _) hn
  exact ⟨{
    xL := xL
    posI := 𝐩
    enc := Stored.entries
    sz := _root_.Meaning.sizesOf Zp.p.X
    seat := 𝐬
    nM := _
    nRr := _
    nC := _
    nx := 𝐯
    v7 := 𝐯
    B := B
    hla := hla
    hV := hV
    NE := NE
    tiesM := ties_wide 𝔇 E Mg₀ hW Q5
    fit := F
    reqT := reqT
    rides := rides_wide 𝔇 E Mg₀ z Q7 Q8
    encIs := encIs_wide 𝔇 E Mg₀
    rwMat := rwMat_wide 𝔇 E Mg₀ Q10
    mask := maskF_wide 𝔇 E Mg₀ (𝐌) z links ps k (2 * (parOf x).g) (parOf x) xL _ _ _ eS eB eSe eC
      hO hF hT
    forms := formsF_wide 𝔇 E Mg₀ z links ps k (2 * (parOf x).g) x q xL (𝐩) _ _ _ (𝐯) (𝐯) Em hRd
      hruns H Kf hnsD hBf left four st hOa hArr (hMask xL hl hs) (hCells xL hl hs)
      (hell xL hl hs) F.sits (covers_top (parOf x).hp.tl) hl hs huL (tlAt_plan hn h0 hplan) }⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planFitF_congr
#print axioms OnBytes.Road.K4.fitF_wide
#print axioms OnBytes.Road.K4.idx_at_v7F
#print axioms OnBytes.Road.K4.maskF_wide
#print axioms OnBytes.Road.K4.formsF_wide
#print axioms OnBytes.Road.K4.firstAt_whole
