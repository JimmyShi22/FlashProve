-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K04LawFull.lean: THE KIND K4's SHARE OF THE CHAIN OF PROMISES IN THE SECOND FORM,
WITH THE TWO FAMILIES `K4LaterAt` AND `K4FirstAt` CALLED. WHAT IS HARD IS
STILL A BINDER: Sp (facts on every state that the IOP's run reaches at K4's borders). One statement
with its proof: `k04_law_at` (K04LawAt.lean) with its two families `K4LaterAt` and `K4FirstAt` paid
by two joins in other files. No new argument.

FIRST. NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE: 𝔇 AND Ew ARE LETTERS. UNDER THE BINDERS OF
`k04_of_head` (Johnson/Road/K4/K04OfHead.lean: the head `AtMgA`, a filling 𝔏, three equations on
the flat lists) THEY ARE HAD AT THE HEAD's OWN 𝔇: that theorem reaches this statement by calls. A
MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
K04_law IS NOT PROVED BY THIS. ITS END IS AT THE COMPOSED
MEANING `mgAll 𝔇 mgBase` OVER A LETTER 𝔇; WHAT IT CALLS SPEAKS AT THE WIDER MEANING `mgWide 𝔇 Ew
mgBase`, one side of a bridge: what the bridge spends is a binder here (Sp).

  `k04_law_full`: `KindTiedR 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (RchPub
    (descAt Z A B c) Pp) E (T.p₁ :: T.l₁) KindName.K4`, at every condition Pp on the public part, at
    tokens := ℕ.

LL := `laterAt_wide_scope` (Johnson/Road/K4/K4PinsLaterScope.lean), LF :=
`firstAt_wide_scope` (K4PinsFirstScope.lean): each ends in the family's sentence to the letter, in
the goals' scope at the opening, at the member that `K4Here` names. IN THEIR PLACE: Pf:
`K4PinsFill`: EIGHT NAMED EQUATIONS ON 𝔇 (sent, arr, ms, the numbers' sent and index, seat3, mat13,
uL) AND ONE LINE ON WHAT ITS READER OF THE HIDDEN INTEGERS RETURNS · Pt: `K4PinsTests`: SIX TESTS A
GROUP · W: `WrittenAt`: five equations: the public part's plan is the written one (in the seam's
test's and one more's stead, which are theorems under it) · reqT: `ReqTies`: lines that tie the
request's readers: three sentences over all public parts, no test with code; at the closed constant
they are `reqTies_const` (an unfolding and three rewritings): NOT OF THE HARD SORT.

WHAT IS LEFT, ALL OF IT. ON THE PIECES AND THE FILES: hS, hR, O, hT, hD, hs, hc, hcap, hok, hW ·
EQUATIONS AND LINES ON 𝔇 AND Ew: hnR, hkC, hH, Fl (`K4Fill`), Pf · ON THE EXTRACTOR: hE · TESTS: Sn
(`K4NamedW`), hNf, Pt · W · reqT · Sp: THE TIGHT LIST: what the bridge spends at K4's own
twenty-four borders (`K4Spends`, K04LawR.lean) · lw (idle).

Limits. EVERY BINDER IS A PREMISE. SHOWN TOGETHER AT NO DATA. The second hash function and the
reference sizes alone. Nothing on soundness.
-/
import Johnson.Road.K4.K04LawAt
import Johnson.Road.K4.K4PinsFirstScope

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

/-- **THE TWO FAMILIES `K4LaterAt` AND `K4FirstAt` ARE CALLED.** Sp STAYS.
NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE: 𝔇 AND Ew ARE LETTERS. Under the binders of
`k04_of_head` (Johnson/Road/K4/K04OfHead.lean: the head `AtMgA`, a filling, three equations) they
are had at the head's own 𝔇; A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction;
SIDE LIBRARY AtFullSide/Top/). -/
theorem k04_law_full {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
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
    (Sp : ∀ g, g < 12 → ∀ j, j = 28 * g + 4 ∨ j = 28 * g + 4 + 1 →
      ∀ a : (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str,
        RchPub (descAt Z A B c) Pp j a → a.1.2.failed = none → K4Spends 𝔇 Ew j a.1) :
    KindTiedR 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true)
      (RchPub (descAt Z A B c) Pp) E (T.p₁ :: T.l₁) KindName.K4 :=
  k04_law_at hS hR O hT file hD hs b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc hcap hok hW 𝔇 Ew hnR hkC
    hH E hE lw Fl Sn hNf
    (fun g hg hg0 q _ x b h z =>
      laterAt_wide_scope hS hR O hW 𝔇 Ew hg hg0 h Fl (Sn g hg x b h) Pf (Pt g hg x b h)
        W q z)
    (fun q _ x b h z =>
      firstAt_wide_scope hS hR O hW 𝔇 Ew h Fl (Sn 0 (by decide) x b h) Pf
        (Pt 0 (by decide) x b h) reqT q z)
    Pp Sp

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_law_full
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_law_full
