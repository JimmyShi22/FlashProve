-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04LawAt.lean: THE KIND K4's SHARE OF THE CHAIN OF PROMISES IN THE SECOND FORM, AT
THE COMPOSED MEANING `mgAll 𝔇 mgBase`, WITH K4's DATA A TERM OVER THAT MEANING's DATA 𝔇.
One statement with its proof: `k04_law_R` (K04LawR.lean) called at Dk := `k4DataWide 𝔇 Ew
mgBase`, with three of its binders paid by theorems. No new argument. IT PAYS NOTHING OF WEIGHT.

FIRST. NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE: 𝔇 AND Ew ARE LETTERS. UNDER THE BINDERS OF
`k04_of_head` (Johnson/Road/K4/K04OfHead.lean: the head `AtMgA`, a filling 𝔏, three equations on
the flat lists) THEY ARE HAD AT THE HEAD's OWN 𝔇: that theorem reaches this statement by calls. A
MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
K04_law IS NOT PROVED BY THIS. ITS END IS AT THE COMPOSED MEANING ITSELF; ITS BINDERS ON THE MEANING
ARE ASKED AT THE WIDER MEANING `mgWide 𝔇 Ew mgBase`: it is no reference form:
it is one side of a bridge: a law shown at it counts only when the bridge is paid.

  `k04_law_at`: `KindTiedR 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (RchPub
    (descAt Z A B c) Pp) E (T.p₁ :: T.l₁) KindName.K4`, at every condition Pp on the public part.

(0) THE PUBLIC PARAMETERS ARE A LETTER Xp WITH ONE BINDER hW : Bs.G₀.W = Xp: the
closed constant `AtMgA.𝔇` is indexed by the public part's own parameters, while the opening's base
comes out of an "there is": so a caller carries no structure across an equation of types. (1) Dk IS
NO LETTER: `k4DataWide 𝔇 Ew mgBase` (Johnson/Road/K4/K4MeansAtWide.lean): of its 34 data 27 are
fields of 𝔇 or Ew (H with the decoder laid in), two are fields of 𝔇's public data (nsOf, sd), two
are terms off the public parameters (hd, nextOf), and three are the meaning's own (base := the
base's "in order", worthBase, moreL := the wider meaning's door); hnR and hkC are equations on
𝔇: its pile's witness has the reference sizes. (2) `K4Means` IS NO BINDER: `k4Means_mgWide`: all its
equations hold at the wider meaning at that term, under hH (the output head's segment is no
feed-forward segment) and two lines on the base's sentences, which hold at `mgBase` by its text. (3)
THE FAMILY `K4RowAt` IS NO BINDER: `rowAt_wide_scope` (Johnson/Road/K4/K4RowAtWideScope.lean): all
its seventeen fields, in the goals' scope at the opening, from Fl (`K4Fill`: equations and lines on
𝔇 and Ew: SHOWN AT NO 𝔇; `k4Fill_all` (Johnson/Road/K4/K4FillAll.lean) has it at the own 𝔇 of the
head `AtMgA`; a member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/)) and Sn (`K4NamedW`: nine tests on public data a
group). For that `K4Here` (K04Tied.lean) bears one field more: the member's segment is 2 g. (4)
hWi, WHAT A YES OF THE PUBLIC ITEM "K13.pileWithin" GIVES, IS NO BINDER:
`within_mgWide` (K04Within.lean): proved, at every 𝔇, Ew and base.

WHAT STAYS, OF WEIGHT: the families `K4LaterAt` and `K4FirstAt` at the term (LL, LF): forms, mask,
tiesM, fit, rides, encIs, rwMat, reqT · Sp: WHAT THE BRIDGE SPENDS AT K4's OWN TWENTY-FOUR BORDERS
(`K4Spends`, K04LawR.lean: the tight list); `k04_law_at_fold`: the corollary under the one
structure `FoldFacts` with `FoldTies`, `RoomOpen`, `K8Open`. AND WHAT IS NO BINDER AND IS OWED ALL
THE SAME: see K04LawR.lean's head.

Limits. EVERY BINDER IS A PREMISE. SHOWN TOGETHER AT NO DATA. The second hash function and the
reference sizes alone. Nothing on soundness.
-/
import Johnson.Road.K4.K04LawR
import Johnson.Road.K4.K4RowAtWideScope
import Johnson.Road.K4.K04Within

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

variable {Xi Tok : Type}

/-- **K4's SHARE IN THE SECOND FORM AT THE COMPOSED MEANING, K4's DATA A
TERM.** NO MEMBER OF ITS BINDERS IS SHOWN ANYWHERE: 𝔇 AND Ew ARE LETTERS. Under the binders of
`k04_of_head` (Johnson/Road/K4/K04OfHead.lean: the head `AtMgA`, a filling, three equations) they
are had at the head's own 𝔇; A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction;
SIDE LIBRARY AtFullSide/Top/). -/
theorem k04_law_at {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D (allOf D) (descAt Z A B c) X₁ X₂
      (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)}
    (hT : OfDesc _ T) (file : String) (hD : (descAt Z A B c).data file = .ok D)
    (hs : (descAt Z A B c).sealLast = true) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) (hcap : AtCap rest₁)
    (hok : VerifiableInference.Desc.blocksOk c.blocksInOrder = true)
    {Xp : Public} (hW : Bs.G₀.W = Xp)
    {nQ : ℕ} (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nQ Xp)
    (Ew : WideData ProofFile.InstPub) (hnR : nQ = hRef) (hkC : 𝔇.P13.lin.kCol = kRef)
    (hH : isLay 𝔇.links (headLink Xp) = false)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str →
      Wit (CellsK hRef (2 ^ kRef)) Tok MsgT → Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)
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
    (LL : ∀ g, ∀ hg : g < 12, (g == 0) = false → ∀ q, (T.p₁ :: T.l₁)[28 * g + 4]? = some q →
      ∀ x b, ∀ h : K4Here c Z Bs.G₀ g x b,
        ∀ z, Nonempty (K4LaterAt (scl := sclX Xp g) x linksFull (flatPlacesOf linksFull true)
          (28 * g + 4) (2 * g) q (k4DataWide 𝔇 Ew mgBase) (mgWide 𝔇 Ew mgBase)
          (lt_of_eq_of_lt h.hg hg) z))
    (LF : ∀ q, (T.p₁ :: T.l₁)[28 * 0 + 4]? = some q →
      ∀ x b, K4Here c Z Bs.G₀ 0 x b →
        ∀ z, Nonempty (K4FirstAt (scl := sclX Xp 0) x linksFull
          (flatPlacesOf linksFull true) (28 * 0 + 4) (2 * 0) q (k4DataWide 𝔇 Ew mgBase)
          (mgWide 𝔇 Ew mgBase) z))
    (Pp : ProofFile.InstPub → Prop)
    (Sp : ∀ g, g < 12 → ∀ j, j = 28 * g + 4 ∨ j = 28 * g + 4 + 1 →
      ∀ a : (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str,
        RchPub (descAt Z A B c) Pp j a → a.1.2.failed = none → K4Spends 𝔇 Ew j a.1) :
    KindTiedR 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true)
      (RchPub (descAt Z A B c) Pp) E (T.p₁ :: T.l₁) KindName.K4 := by
  subst hW
  exact k04_law_R hS hR O hT file hD hs b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc hcap hok
    (k4DataWide 𝔇 Ew mgBase) hnR hkC 𝔇 Ew
    (k4Means_mgWide 𝔇 Ew mgBase hH (fun _ _ _ _ h => h) (fun _ _ _ => rfl)) E hE lw
    (fun g hg q _ x b h z => rowAt_wide_scope 𝔇 Ew hS hR O rfl hg h.mem h.link Fl (Sn g hg x b h) q
      z)
    (within_mgWide 𝔇 Ew mgBase) hNf LL LF Pp Sp
/-- **THE COROLLARY, UNDER `FoldFacts`, `FoldTies`, `RoomOpen`
AND `K8Open`.** -/
theorem k04_law_at_fold {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {D : WholeD} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D (allOf D) (descAt Z A B c) X₁ X₂
      (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)}
    (hT : OfDesc _ T) (file : String) (hD : (descAt Z A B c).data file = .ok D)
    (hs : (descAt Z A B c).sealLast = true) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) (hcap : AtCap rest₁)
    (hok : VerifiableInference.Desc.blocksOk c.blocksInOrder = true)
    {Xp : Public} (hW : Bs.G₀.W = Xp)
    {nQ : ℕ} (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nQ Xp)
    (Ew : WideData ProofFile.InstPub) (hnR : nQ = hRef) (hkC : 𝔇.P13.lin.kCol = kRef)
    (hH : isLay 𝔇.links (headLink Xp) = false)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str →
      Wit (CellsK hRef (2 ^ kRef)) Tok MsgT → Wit (CellsK hRef (2 ^ kRef)) Tok MsgT)
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
    (LL : ∀ g, ∀ hg : g < 12, (g == 0) = false → ∀ q, (T.p₁ :: T.l₁)[28 * g + 4]? = some q →
      ∀ x b, ∀ h : K4Here c Z Bs.G₀ g x b,
        ∀ z, Nonempty (K4LaterAt (scl := sclX Xp g) x linksFull (flatPlacesOf linksFull true)
          (28 * g + 4) (2 * g) q (k4DataWide 𝔇 Ew mgBase) (mgWide 𝔇 Ew mgBase)
          (lt_of_eq_of_lt h.hg hg) z))
    (LF : ∀ q, (T.p₁ :: T.l₁)[28 * 0 + 4]? = some q →
      ∀ x b, K4Here c Z Bs.G₀ 0 x b →
        ∀ z, Nonempty (K4FirstAt (scl := sclX Xp 0) x linksFull
          (flatPlacesOf linksFull true) (28 * 0 + 4) (2 * 0) q (k4DataWide 𝔇 Ew mgBase)
          (mgWide 𝔇 Ew mgBase) z))
    (Pp : ProofFile.InstPub → Prop) (d : FoldData) (reqW : ProofFile.InstPub → Array UInt32)
    (Ff : FoldFacts (RchPub (descAt Z A B c) Pp)
      (fun a : (ProofFile.InstPub × S) × (frameAt D (allOf D) D.key₁ T.ft₁).E.Str => a.1) d reqW linksFull
      (flatPlacesOf linksFull true))
    (Tf : FoldTies 𝔇 Ew d reqW)
    (hRo : RoomOpen (Fr := frameAt D (allOf D) D.key₁ T.ft₁) 𝔇 Ew mgBase linksFull
      (flatPlacesOf linksFull true) (fun a => a) (RchPub (descAt Z A B c) Pp))
    (hK8 : K8Open (Fr := frameAt D (allOf D) D.key₁ T.ft₁) 𝔇 Ew mgBase linksFull
      (flatPlacesOf linksFull true) (fun a => a) (RchPub (descAt Z A B c) Pp)) :
    KindTiedR 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true)
      (RchPub (descAt Z A B c) Pp) E (T.p₁ :: T.l₁) KindName.K4 := by
  subst hW
  exact k04_law_R_fold hS hR O hT file hD hs b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r hc hcap hok
    (k4DataWide 𝔇 Ew mgBase) hnR hkC 𝔇 Ew
    (k4Means_mgWide 𝔇 Ew mgBase hH (fun _ _ _ _ h => h) (fun _ _ _ => rfl)) E hE lw
    (fun g hg q _ x b h z => rowAt_wide_scope 𝔇 Ew hS hR O rfl hg h.mem h.link Fl (Sn g hg x b h) q
      z)
    (within_mgWide 𝔇 Ew mgBase) hNf LL LF Pp d reqW Ff Tf hRo hK8

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k04_law_at
#print axioms OnBytes.Road.K4.k04_law_at_fold
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
set_option pp.proofs true in
#check @OnBytes.Road.K4.k04_law_at
