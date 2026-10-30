-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K04LawFront.lean: THE KIND K4's SHARE OF THE CHAIN OF PROMISES IN THE SECOND
FORM, WITH WHAT IS ASKED ALONG THE IOP's RUN ASKED AT THE TWELVE BORDERS IN FRONT OF K4 ALONE.
One statement with its proof: `k04_law_full` (K04LawFull.lean) with its binder Sp paid
by `sp_of_front_pub` (SpendsOfFrontPub.lean: `sp_of_front` typed anew at "reached,
and Pp of the public part"). No new argument.

FIRST. NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE: 𝔇 AND Ew ARE LETTERS. UNDER THE BINDERS OF
`k04_of_head` (Johnson/Road/K4/K04OfHead.lean: the head `AtMgA`, a filling 𝔏, three equations on
the flat lists) THEY ARE HAD AT THE HEAD's OWN 𝔇: that theorem reaches this statement by calls. A
MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
K04_law IS NOT PROVED BY THIS. ITS END IS AT THE COMPOSED
MEANING `mgAll 𝔇 mgBase` OVER A LETTER 𝔇; what it calls speaks at the wider meaning, one side of a
bridge. WHAT IS HARD IS A BINDER: W0, R0, L7.

  `k04_law_front`: the end of `k04_law_full`, to the letter.

Sp of `k04_law_full` asks, at K4's twenty-four borders, at every state that the IOP's run reaches
there without a mark: the fifteen facts and four names' tests where these are open. IN
ITS PLACE, AT THE TWELVE BORDERS 28 g + 4 ALONE, at every state reached there without a mark whose
public part meets Pp: W0: the fifteen facts (`WideFacts`) · R0: the test of "pile.room" at the
segment's own number · L7: the test of "K8.lay7" at the segment's own number. WHY THAT IS ENOUGH, AS
OTHER FILES SAY IT
(that it is enough is what Lean says in
accepting the call below): a state reached behind K4 comes of one reached in front by an accepting
run of K4's sub-protocol, which keeps all that the fifteen, the room's test and the seven fields
read; "K8.funsThird" behind K4 is made by that run; and by decisions of the kernel at the wider
door's written lists "K8.onThird" is open at neither border, "K8.funsThird" not in front,
"pile.room" and "K8.lay7" at the segment's own number alone.

Limits. EVERY BINDER IS A PREMISE. SHOWN TOGETHER AT NO DATA. The second hash function and the
reference sizes alone. Nothing on soundness.
-/
import Johnson.Road.K4.K04LawFull
import Johnson.Road.K4.SpendsOfFrontPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop
open OnBytes OnBytes.Flat OnBytes.Maker KObj
open OnBytes.Model (Fork WsLay)
open OnBytes.Model.Verify (Public)
open VerifiableInference.OnPublicFiles (LeftQ)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.InT (StatesAt)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block FileDescription KindName Wit Claim Link K9.LinkHoles K9.statesOfLink)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf start openSets)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K13.Law (lowBits)
open Inst.Model (Scl ppref)
open Meaning.Emb (EmbNums)
open OnBytes.Model.Verify (layerShape)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (LW)
open Cb.Pv.Tail (Size)
open OnBytes.Model (Forest.elems)
open OnBytes.Desc.First.K4 (formsBack)
open VerifiableInference.PlanWritten (PublicSteps publicSteps_of)
open VerifiableInference.Desc.First (readsOpen moreItem)
open VerifiableInference.Desc.First.Look (pubAt stepOf)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open VerifiableInference.Desc.K13.Law (matOfCells)

open VerifiableInference.Desc.First (classA pubWide FoldData FoldFacts)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)

variable {Xi : Type}

/-- **WHAT IS ASKED ALONG THE RUN IS ASKED IN FRONT OF K4 ALONE.** W0, R0,
L7 STAY. NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE: 𝔇 AND Ew ARE LETTERS. Under the binders of
`k04_of_head` (Johnson/Road/K4/K04OfHead.lean: the head `AtMgA`, a filling, three equations) they
are had at the head's own 𝔇; A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction;
SIDE LIBRARY AtFullSide/Top/). -/
theorem k04_law_front {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D (allOf D) (descAt Z A B c) X₁ X₂
      (Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT)}
    (hT : OfDesc _ T) (file : String) (hD : (descAt Z A B c).data file = .ok D)
    (hs : (descAt Z A B c).sealLast = true) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) (hcap : AtCap rest₁)
    (hok : VerifiableInference.Desc.blocksOk c.blocksInOrder = true)
    {Xp : Public} (hW : Bs.G₀.W = Xp)
    {nQ : ℕ} (𝔇 : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ Xp)
    (Ew : WideData ProofFile.InstPub) (hnR : nQ = hRef) (hkC : 𝔇.P13.lin.kCol = kRef)
    (hH : isLay 𝔇.links (headLink Xp) = false)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str →
      Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT → Wit (CellsK hRef (2 ^ kRef)) ℕ MsgT)
    (hE : ∀ g, g < 12 → ∀ a b w, E (28 * g + 4) a b w = w) (lw : ℕ → LW Cb.Gl.E)
    (Fl : K4Fill 𝔇 Ew Z c)
    (Sn : ∀ g, g < 12 → ∀ x b, K4Here c Z Bs.G₀ g x b →
      K4NamedW 𝔇 Ew (28 * g + 4) (2 * g) (parOf x) (c.blocksInOrder.map fun b => b.oracles.flatMap id)
        (Forest.elems Xp.y.fo))
    (hNf : ∀ g, g < 12 →
      Rec.nextFitsB (k4DataWide 𝔇 Ew mgBase).cs (k4DataWide 𝔇 Ew mgBase).d12.M
      ((k4DataWide 𝔇 Ew mgBase).N.msgsAt (flatPlacesOf linksFull true)[28 * g + 4 + 1]?)
        (k4DataWide 𝔇 Ew mgBase).N.indexNo (k4DataWide 𝔇 Ew mgBase).free0
        (k4DataWide 𝔇 Ew mgBase).fvs (2 * g) = true)
    (Pf : K4PinsFill 𝔇 Z)
    (Pt : ∀ g, g < 12 → ∀ x b, K4Here c Z Bs.G₀ g x b →
      K4PinsTests 𝔇 Ew Z (28 * g + 4) g (parOf x))
    (W : WrittenAt Z)
    (reqT : ReqTies (k4DataWide 𝔇 Ew mgBase).reqB (k4DataWide 𝔇 Ew mgBase).reqW
      (k4DataWide 𝔇 Ew mgBase).H.req (k4DataWide 𝔇 Ew mgBase).put)
    (Pp : ProofFile.InstPub → Prop)
    (W0 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none → WideFacts 𝔇 Ew a.1)
    (R0 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none →
        Johnson.Desc.First.Walk.Tied.roomIsB Ew.dP.free0 Ew.dP.fvs (2 * g) a.1.2 = true)
    (L7 : ∀ g, g < 12 → ∀ a : (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str,
      RchPub (descAt Z A B c) Pp (28 * g + 4) a → a.1.2.failed = none →
        ((Ew.dP.tl (2 * g)).any fun tlP =>
          VerifiableInference.Desc.First.K8.Ready.lay7B tlP a.1.2) = true) :
    KindTiedR 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true)
      (RchPub (descAt Z A B c) Pp) E (T.p₁ :: T.l₁) KindName.K4 :=
  k04_law_full hS hR O hT file hD hs b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc hcap hok hW 𝔇 Ew hnR
    hkC hH E hE lw Fl Sn hNf Pf Pt W reqT Pp
    (sp_of_front_pub 𝔇 Ew hS hR O Pp W0 R0 L7)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_law_front
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_law_front
