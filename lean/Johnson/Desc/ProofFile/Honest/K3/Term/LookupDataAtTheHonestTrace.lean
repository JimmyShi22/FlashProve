-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupDataAtTheHonestTrace.lean: the honest side of the kind
"lookup" (K3): at every lookup of a public part in scope, what the lookup's row is handed off the
honest trace of a served request is a lawful lookup instance.

The row's reader is the one of the lot theLotInst id weights (Honest/K3/LotInst.lean). The index is a
letter: its type W₀ and its reader weights are arguments.

What is defined.
  lookupWitness: what the row at a site is handed, as a function of the challenges heard.
  InputHoldsTheHonestTrace: the four premises on the input.
  LookupDataIsLawful: the four conclusions at a site.
What is shown.
  lookupDataIsLawfulOfHonestKeysAndBits: the relation after the challenge follows from honest keys
    and bits.
  lookupDataAtTheHonestTrace: the conclusions at every site.
  lookupDataAtLiveFiles: the same, its public premises paid where the verifier's test on the files
    says yes.
  libraryKeysAndBitsAtLayers, …AtAttention, …AtTheHead: the keys are the library's joint vector and
    the bits its reading (FillsAt). The digits' fellow is in Term/DigitsPublicPremises.lean.

Not claimed: that a verifier's block accepts; anything on soundness, completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftAtCallsMid
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ShapeIsFsPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeFillAt
import Johnson.Desc.ProofFile.Honest.K3.Term.DigitsPublicPremises
import Johnson.Desc.ProofFile.Honest.K3.Term.HeadPublicDataAgree
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.SiteRng
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Desc.ProofFile.InstOf
import Johnson.HonestTrace.PlanOwnersInScope
import Johnson.Goal.HonestTrace.FromCellsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.HonestTrace (cellOf entryOf theTrace ServesAt fromG fromA fromH nuFrom fsAt kvZ)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Road (Hd.shapeA)
open OnBytes.Slice (GE)
open Inst.Model (Instance ppref ScalesAndPolicy)
open ProofFile.Honest.K3.Law (siteData mid_of_meets)
open ProofFile.Honest.K3.Law.Exchange (FillsAt)

variable {W₀ Rc : Type}

/-- **What the lookup's row at a site is handed**, at the lot theLotInst id weights. -/
abbrev lookupWitness (Zp : Pub) (weights : W₀ → Weights) (s : Site)
    (t : Local W₀ Rc Inst Cells) : Ask :=
  askOf (sourcesAt id weights (reqAt Zp) Zp) (whoOf s) t

/-- **The input holds the honest trace of a served request.** -/
structure InputHoldsTheHonestTrace (Zp : Pub) (weights : W₀ → Weights)
    (t : Local W₀ Rc Inst Cells) (i : Cm.Idx) (x : Instance ppref) : Prop where
  /-- the index serves the request -/
  requestIsServed : ServesAt Zp.p.X i x
  /-- the input's trace is the specification's, read by labels -/
  traceIsTheHonestTrace : t.trace = ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩
  /-- the reader of the index yields the index's entries -/
  weightsAreTheIndex : weights t.w₀ = ⟨entryOf i⟩
  /-- the input's instance is read as the request -/
  instanceIsTheRequest : ProofFile.instOf t.x = some x

/-- **A lawful lookup instance at a site.** -/
structure LookupDataIsLawful (Zp : Pub) (s : Site) (witness : Ask) : Prop where
  /-- the site's shape is the one that the plan holds for it -/
  shapeIsThePlans : ShapeIsFs Zp.p.X s
  /-- behind the lookup's first round the data no longer move -/
  settledAtTheFirstRound : Ask.Settled s.at_.base witness
  /-- keys and bits are honest, at all challenges heard -/
  keysAndBitsAreHonest : ∀ heard, ∃ L : LookIn, witness heard = L.hidden ∧ L.Meets s.shape s.p.lm
  /-- the specification's relation after the challenge, at all challenges -/
  relationAfterTheChallenge : ∀ heard ds, (siteData s witness heard ds).Mid

/-- **The relation after the challenge follows from honest keys and bits.** -/
theorem lookupDataIsLawfulOfHonestKeysAndBits (Zp : Pub) (s : Site) (hs : s ∈ lookSites Zp)
    (witness : Ask) (shape : ShapeIsFs Zp.p.X s) (settled : Ask.Settled s.at_.base witness)
    (honest : ∀ heard, ∃ L : LookIn, witness heard = L.hidden ∧ L.Meets s.shape s.p.lm) :
    LookupDataIsLawful Zp s witness := by
  refine ⟨shape, settled, honest, fun heard ds => ?_⟩
  obtain ⟨L, e, M⟩ := honest heard
  show (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta) (witness heard)
    (ptsOf s.at_.face s.at_.base (heard ++ ds))).Mid
  rw [e]
  exact mid_of_meets L s.shape s.p.lm s.p.first (FastLaw.sites_ok Zp s hs).2 M _

section
variable {Zl : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {Zp : Pub}
  {weights : W₀ → Weights} {t : Local W₀ Rc Inst Cells} {i : Cm.Idx} {x : Instance ppref}

/-- On the calls the data do not move at all. -/
theorem settledOnTheCalls (Zp : Pub) (weights : W₀ → Weights) (t : Local W₀ Rc Inst Cells)
    (s : Site) (hw : ∀ link rng, whoOf s ≠ .digits link rng) :
    Ask.Settled s.at_.base (lookupWitness Zp weights s t) :=
  askOf_settled _ _ t _ fun link rng e => absurd e (hw link rng)

/-- **A group's layers.** -/
theorem honestKeysAndBitsAtLayers (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (I : InputHoldsTheHonestTrace Zp weights t i x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = false) (hc : s.caller = .layers) (hg : s.group < 12)
    (heard : List Fmt.Drawn) :
    ∃ L : LookIn, lookupWitness Zp weights s t heard = L.hidden ∧ L.Meets s.shape s.p.lm := by
  obtain ⟨e1, e2, e3⟩ := Law.Spec.site_layers Zp s hs hd hc
  have hB : ShapeIsFs Zp.p.X s := Law.AtThr.shapeIsFs_of_public h s hs
  have hsh : Zp.p.X.y.fo = s.shape := Option.some.inj (e1.symm.trans hB)
  have S := I.requestIsServed
  have hm := ownG_meets (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h S) (OnBytes.HonestTrace.lookPub_in_scope hZ hR h)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h S)
    (OnBytes.HonestTrace.planesLaid_in_scope hZ hR h i x) hg (id : Cells → Cells) weights
    (fun y : Inst => headPub Zp.p.X (reqAt Zp y).1 (reqAt Zp y).2)
  rw [hsh, ← e2] at hm
  refine ⟨_, ?_, hm⟩
  show askOf (tiedOwnSources Zp.p.X id weights (reqAt Zp)) (whoOf s) t heard = _
  rw [e3]
  show ((tiedOwnSources Zp.p.X id weights (reqAt Zp)).layers s.group t.trace
    (weights t.w₀)).hidden = _
  rw [I.traceIsTheHonestTrace, I.weightsAreTheIndex]
  rfl

/-- **A group's attention.** -/
theorem honestKeysAndBitsAtAttention (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (I : InputHoldsTheHonestTrace Zp weights t i x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = false) (hc : s.caller = .attention) (hg : s.group < 12)
    (heard : List Fmt.Drawn) :
    ∃ L : LookIn, lookupWitness Zp weights s t heard = L.hidden ∧ L.Meets s.shape s.p.lm := by
  obtain ⟨e1, e2, e3⟩ := Law.Spec.site_attention Zp s hs hd hc
  have hB : ShapeIsFs Zp.p.X s := Law.AtThr.shapeIsFs_of_public h s hs
  have hsh : fsAt Zp.p.X s.group = s.shape := Option.some.inj (e1.symm.trans hB)
  have S := I.requestIsServed
  have hm := ownA_meets (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h S) (OnBytes.HonestTrace.lookPub_in_scope hZ hR h)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h S)
    (OnBytes.HonestTrace.planesLaid_in_scope hZ hR h i x) hg (id : Cells → Cells) weights
    (fun y : Inst => headPub Zp.p.X (reqAt Zp y).1 (reqAt Zp y).2)
  rw [hsh, ← e2] at hm
  refine ⟨_, ?_, hm⟩
  show askOf (tiedOwnSources Zp.p.X id weights (reqAt Zp)) (whoOf s) t heard = _
  rw [e3]
  show ((tiedOwnSources Zp.p.X id weights (reqAt Zp)).attention s.group t.trace).hidden = _
  rw [I.traceIsTheHonestTrace]
  rfl

/-- **The head.** The public data of the row are those of reqAt, not the structure pubHAt. -/
theorem honestKeysAndBitsAtTheHead (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (I : InputHoldsTheHonestTrace Zp weights t i x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = false) (hc : s.caller = .head) (heard : List Fmt.Drawn) :
    ∃ L : LookIn, lookupWitness Zp weights s t heard = L.hidden ∧ L.Meets s.shape s.p.lm :=
  headLookMeetsAtTheSiteShape hZ hR h I.requestIsServed s hs hd hc id weights t
    I.traceIsTheHonestTrace I.weightsAreTheIndex I.instanceIsTheRequest heard

/-- **At every lookup of a public part in scope, what the row is handed off the honest trace of a
served request is a lawful lookup instance.** The premise samplingRoundsStandInFront is a test with
code on the public part's table of places, which the three premises on the files do not bind: they
speak of Zp.p.X alone. -/
theorem lookupDataAtTheHonestTrace (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (samplingRoundsStandInFront : rngFrontB Zp = true)
    (I : InputHoldsTheHonestTrace Zp weights t i x) :
    ∀ s ∈ lookSites Zp, LookupDataIsLawful Zp s (lookupWitness Zp weights s t) := by
  intro s hs
  have hB : ShapeIsFs Zp.p.X s := Law.AtThr.shapeIsFs_of_public h s hs
  have settled : Ask.Settled s.at_.base (lookupWitness Zp weights s t) :=
    askOf_settled _ _ t _ fun link r e =>
      rng_front Zp samplingRoundsStandInFront s hs r (who_digits s link r e)
  refine lookupDataIsLawfulOfHonestKeysAndBits Zp s hs _ hB settled fun heard => ?_
  cases hd : s.digits with
  | true => exact honestKeysAndBitsAtTheDigits hZ hR h weights t s hs hd heard
  | false =>
    cases hc : s.caller with
    | layers =>
      exact honestKeysAndBitsAtLayers hZ hR h I s hs hd hc
        (groupIsBelowTwelve hZ hR h s hs hd (by rw [hc]; exact fun e => nomatch e)) heard
    | attention =>
      exact honestKeysAndBitsAtAttention hZ hR h I s hs hd hc
        (groupIsBelowTwelve hZ hR h s hs hd (by rw [hc]; exact fun e => nomatch e)) heard
    | head => exact honestKeysAndBitsAtTheHead hZ hR h I s hs hd hc heard

/-- **The same at live files**: the files are in scope, the verifier's test on them says yes, and Zp
is the public part that they make. -/
theorem lookupDataAtLiveFiles (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Zl) = true)
    (hP : ProofFile.pubPlain OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL = .ok Zp)
    (I : InputHoldsTheHonestTrace Zp weights t i x) :
    ∀ s ∈ lookSites Zp, LookupDataIsLawful Zp s (lookupWitness Zp weights s t) :=
  lookupDataAtTheHonestTrace hZ hR (publicReturnsAtLiveFiles hZ hR hL hP)
    (samplingRoundsStandInFrontAtLiveFiles hZ hR hL hP) I

/-! ## The library's key vectors and readings, sort by sort -/

/-- **A group's layers: the keys are the library's joint vector, the bits its reading.** -/
theorem libraryKeysAndBitsAtLayers (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (I : InputHoldsTheHonestTrace Zp weights t i x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = false) (hc : s.caller = .layers) (hg : s.group < 12) (mask : Nat → GE)
    (theta : GE)
    (heard : List Fmt.Drawn) :
    FillsAt s (lookupWitness Zp weights s t)
      (lookG Zp.p.X s.group ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ⟨entryOf i⟩)
      (OnBytes.Ends.G.kvG Zp.p.X.layers s.group
        (fromG Zp.p.X (cellOf Zp.p.X (theTrace Zp.p.X i x)) (entryOf i) s.group))
      (nuFrom Zp.p.X (cellOf Zp.p.X (theTrace Zp.p.X i x)) (2 * s.group) mask) theta heard :=
  Law.Exchange.fills_layers Zp id weights (reqAt Zp) s hs hd hc t
    (Law.AtThr.shapeIsFs_of_public h s hs) (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h I.requestIsServed)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h I.requestIsServed)
    hg
    I.traceIsTheHonestTrace I.weightsAreTheIndex mask theta heard

/-- **A group's attention.** -/
theorem libraryKeysAndBitsAtAttention (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (I : InputHoldsTheHonestTrace Zp weights t i x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = false) (hc : s.caller = .attention) (hg : s.group < 12) (mask : Nat → GE)
    (theta : GE)
    (heard : List Fmt.Drawn) :
    FillsAt s (lookupWitness Zp weights s t)
      (lookA Zp.p.X s.group ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩)
      (OnBytes.Ends.A.kvA (Hd.shapeA Zp.p.X s.group) (fsAt Zp.p.X s.group)
        (fromA Zp.p.X (cellOf Zp.p.X (theTrace Zp.p.X i x)) s.group))
      (nuFrom Zp.p.X (cellOf Zp.p.X (theTrace Zp.p.X i x)) (2 * s.group + 1) mask) theta heard :=
  Law.Exchange.fills_attention Zp id weights (reqAt Zp) s hs hd hc t
    (Law.AtThr.shapeIsFs_of_public h s hs) (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h I.requestIsServed)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h I.requestIsServed)
    hg
    I.traceIsTheHonestTrace mask theta heard

/-- **The head**, at the public data that the row itself reads: those of reqAt. -/
theorem libraryKeysAndBitsAtTheHead (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (I : InputHoldsTheHonestTrace Zp weights t i x) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = false) (hc : s.caller = .head) (mask : Nat → GE) (theta : GE)
    (heard : List Fmt.Drawn) :
    FillsAt s (lookupWitness Zp weights s t)
      (lookH Zp.p.X (headPub Zp.p.X (reqAt Zp t.x).1 (reqAt Zp t.x).2)
        ⟨cellOf Zp.p.X (theTrace Zp.p.X i x)⟩ ⟨entryOf i⟩)
      (OnBytes.Ends.H.kvH (headPub Zp.p.X (reqAt Zp t.x).1 (reqAt Zp t.x).2)
        (fromH Zp.p.X (cellOf Zp.p.X (theTrace Zp.p.X i x)) (entryOf i)))
      (nuFrom Zp.p.X (cellOf Zp.p.X (theTrace Zp.p.X i x)) 24 mask) theta heard :=
  Law.Exchange.fills_head Zp id weights (reqAt Zp) s hs hd hc t
    (Law.AtThr.shapeIsFs_of_public h s hs) (OnBytes.HonestTrace.planLabels_in_scope hZ hR h)
    (OnBytes.HonestTrace.planOwners_in_scope hZ hR h)
    (OnBytes.HonestTrace.namesFit_theTrace hZ hR h I.requestIsServed)
    (OnBytes.HonestTrace.meetsAll_theTrace hZ hR h I.requestIsServed)
    I.traceIsTheHonestTrace I.weightsAreTheIndex mask theta heard

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupDataIsLawfulOfHonestKeysAndBits
#print axioms ProofFile.Honest.K3.Term.honestKeysAndBitsAtLayers
#print axioms ProofFile.Honest.K3.Term.honestKeysAndBitsAtAttention
#print axioms ProofFile.Honest.K3.Term.lookupDataAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.lookupDataAtLiveFiles
#print axioms ProofFile.Honest.K3.Term.libraryKeysAndBitsAtLayers
#print axioms ProofFile.Honest.K3.Term.libraryKeysAndBitsAtAttention
#print axioms ProofFile.Honest.K3.Term.libraryKeysAndBitsAtTheHead
