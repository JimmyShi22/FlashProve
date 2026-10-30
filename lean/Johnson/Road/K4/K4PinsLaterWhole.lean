-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsLaterWhole.lean: WHAT THE ASSEMBLY OF K4's LAW LEAVES AT A LATER GROUP
(`K4LaterAt`, Johnson/Road/K4/K04LawOf.lean), AT THE WIDER MEANING `mgWide 𝔇 E Mg₀` AND THE DATA OFF
ITS OWN PARAMETERS, WITH ALL TEN LETTERS LAID AND SEVEN OF THE EIGHT FIELDS CONCLUDED BY CALLS:
`laterAt_closed` (K4PinsLaterClosed.lean) with its binder forms paid by `forms_wide`
(K4PinsFormsAtWide.lean). B (`RefPub`) stays a binder. The line on what 𝔇.H reads off a
witness is asked as it is spent. A gathering of calls. No draw, no count.

  **`laterAt_whole`**: `Nonempty (K4LaterAt x links ps k (2 * g) q (k4DataWide 𝔇 E Mg₀) (mgWide 𝔇 E
    Mg₀) hg z)`. ITS BINDERS ARE THE LIST OF WHAT IS OWED: those of `laterAt_closed` but forms ·
    `K4Means` at the wider meaning · the table's two lines at K4's place (`AtK4`, `K4Front`) · two
      lines on the term's readers of the runs · the term's number of slots at the segment is there ·
      SIX MORE TESTS (`frontB` · `openAllB` · `readsArrayP` · and, at every place with the segment's
      number as its link and the plan's number of slots: `maskPlanB` · `arraysPlanB` · "the number
      of slots is at most the mask row's length") · ONE MORE NAMED EQUATION (𝔇.uL = `uLAt X (namesOf
      𝔇.built)`) · AND THREE BINDERS ON RUNS AND STATES: left, four, st.

OBJECT: `k4DataWide 𝔇 E Mg₀`, `mgWide 𝔇 E Mg₀`. USER: `laterAt_wide_scope`
(Johnson/Road/K4/K4PinsLaterScope.lean); meant: the top theorem of K4's law at the wider meaning
(its binder on the later groups). LETTERS: as named.

Limits. K04_law IS NOT PROVED BY THIS. B, left, four AND st ARE NOT CONCLUDED. TEN NAMED EQUATIONS
ON 𝔇's PARAMETERS AND ONE LINE ON 𝔇.H ARE PREMISES. TWELVE TESTS: WHAT EACH HAS ANSWERED, WHERE, AND
WITH WHICH NEGATIVE TESTS IS NOT SAID HERE (a list not named here holds them); not all were asked at
these very letters. NO MEMBER IS SHOWN: that the binders can hold together is shown at no
parameters. IT SPEAKS AT THE WIDER MEANING: it counts only when the bridge to the meaning that
counts is paid. TWO LETTERS STAND FOR THE PUBLIC FILES (Pb, Zp), tied by `publicOf`'s return alone.

-/
import Johnson.Road.K4.K4PinsLaterClosed
import Johnson.Road.K4.K4PinsFormsAtWide

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
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

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

/-- **`K4LaterAt` at the wider meaning, whole but for B and three binders on runs and states.** -/
theorem laterAt_whole {Pb : VerifierAndGoals.PublicFiles} {ly : Option ByteArray}
    {tk : Array Nat} (radM : ℕ → ℕ → ℕ)
    (links : List ModelPart) (ps : List VerifiableInference.Desc.Place) (k : ℕ)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT))
    (hg : (parOf x).g < 12) (z : ProofFile.InstPub) (hg0 : 0 < (parOf x).g)
    (h : publicOf Pb.pol Pb.KL ly = .ok Zp.p.X)
    (hn : 2 * (parOf x).g ≠ (if Zp.p.X.p4 then 2 else 1) * Zp.p.X.NGr)
    (h0 : 2 * (parOf x).g % (if Zp.p.X.p4 then 2 else 1) = 0)
    (hplan : Zp.p.X.G[2 * (parOf x).g / (if Zp.p.X.p4 then 2 else 1)]? = some (parOf x).hp)
    (hpc : VerifiableInference.Desc.K3.pieceAt Zp.p.X (2 * (parOf x).g) false = 2)
    (hy : (parOf x).P.y = Zp.p.X.y) (h4 : Zp.p.X.p4 = true)
    (hG : Zp.p.X.G[(parOf x).g]? = some (parOf x).hp)
    (St' : PublicSteps Pb.pol Pb.KL Zp.p.X) (B : RefPub Zp.p.X (parOf x).g)
    (hP : (parOf x).P = { Zp.p.X.layers with tokv := tk })
    (hc : commonFastB Zp = true) (hf : firstFastB Zp (parOf x).g = true)
    (hm : seamFastB Zp (parOf x).g = true)
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
    Nonempty (K4LaterAt x links ps k (2 * (parOf x).g) q (𝐃) (𝐌) hg z) :=
  laterAt_closed Zp 𝔇 E Mg₀ x radM (𝐌) links ps k q hg z hg0 h hn h0 hplan hpc hy h4 hG St'
    B hP hc hf hm Q1 Q2 Q3 Q4s Q4i Q6 Q5 Q7 Q8 Q10 eS eB eSe eC hO hF hT
    fun xL hl hs P0 =>
      forms_wide 𝔇 E Mg₀ z links ps k (2 * (parOf x).g) x q hg xL (𝐩) _ _ _ (𝐯) (𝐯) Em hRd hruns H
        Kf hnsD hBf left four st hOa hArr (hMask xL hl hs) (hCells xL hl hs) (hell xL hl hs)
        (fit_wide Zp radM 𝔇 E Mg₀ (parOf x) Q1 Q2 Q3 Q4s Q4i Q6 hc hf hm hg0 hg xL hl hG (𝐩) St' B
          hP P0 (group_at h4 _) hn).sits
        (covers_top (parOf x).hp.tl) hl hs huL (tlAt_plan hn h0 hplan)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laterAt_whole
