-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/DigitsPublicPremises.lean: the kind "lookup" (K3): the public
premises of the lookups on the digits hold at public files in scope, and so what such a lookup's row
is handed is a lawful lookup instance at every cells and every drawn matrix.

What is shown.
  tailHoldsAtLook: what holds at every plan's record of a smallness test holds at tlOf X link, where
    lookAt returns on the digits.
  linkIsBelowTwentyFiveAtSite, groupIsBelowTwelve: a site's link and group, in scope.
  digitsTailComesFromPieces: FromPieces at a site on the digits.
  digitColumnsFitAtSite, digitWidthFitsAtSite: DigitColsFit and MzFits at a site on the digits.
  samplingRoundsStandInFrontAtLiveFiles: the test rngFrontB accepts at files in scope that pass the
    live test, at the public part that the plain road makes.
  digitsKeysAndBitsAreHonest, digitsRelationAfterTheChallenge, digitsFillingIsTheLibrarys,
    digitsAreSettled: what a site on the digits is handed.

Why the round in front has premises of its own. lookSites reads the field cuts of the public part,
and the three premises on the files name only its field p.X. rngFrontB is therefore a premise of
the general laws, and is shown here where the live test says yes.

Not claimed: that a verifier's block accepts; anything on soundness, completeness or zero knowledge.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeFillAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ShapeIsFsPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngHeadPaid
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.SiteRng
import Johnson.Desc.ProofFile.Honest.K3.Law.MeetsMid
import Johnson.Desc.ProofFile.Honest.K3.Law.AtSite
import Johnson.Desc.ProofFile.Honest.K3.LotInst
import Johnson.Desc.ProofFile.Honest.K8.AddressLaw
import Johnson.Desc.First.Look.ColsAt
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicNM
import Johnson.HonestTrace.PlanOwnersInScope
import Johnson.Goal.Meaning.PlanNames
import Johnson.P5J.HeadOfLive
import Johnson.AtFull.Desc.SpotsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (MzFits labelAt Seg MatName kvZ)
open OnBytes.Slice (GE)
open ProofFile.Honest.K8 (DigitColsFit mz_allRows)
open ProofFile.Honest.K3.Law (siteData)
open ProofFile.Honest.K3.Law.Exchange (FillsAt)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Look (lookAt)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc (spotsWritten spots_written)

/-! ## 1 A law of the plans' records at a link -/

/-- **What holds at every plan's record of a smallness test holds at the link's**, where lookAt
returns on the digits. -/
theorem tailHoldsAtLook {X : OnBytes.Model.Verify.Public} {Q : HTailF2 → Prop}
    (hG : ∀ (g : ℕ) (hp : OnBytes.Model.Layer.HPlan2), X.G[g]? = some hp → Q hp.tl)
    (hA : ∀ (g : ℕ) (a : OnBytes.Attention.Plan), X.A[g]? = some a → Q a.seam.tl)
    (hH : Q X.H.tl) {i : ℕ} {pl : VerifiableInference.Desc.First.Look.Place}
    (h : lookAt X i true = some pl) : Q (tlOf X i) := by
  unfold lookAt at h
  unfold tlOf linkH stepOf
  dsimp only at h
  by_cases h1 : (i == (if X.p4 = true then 2 else 1) * X.NGr) = true
  · rw [if_pos h1]
    exact hH
  · rw [if_neg h1] at h ⊢
    by_cases h2 : (i % (if X.p4 = true then 2 else 1) == 0) = true
    · rw [if_pos h2] at h ⊢
      obtain ⟨hp, hh, _⟩ := Option.bind_eq_some_iff.1 h
      rw [hh]
      exact hG _ hp hh
    · rw [if_neg h2] at h ⊢
      obtain ⟨a, ha, _⟩ := Option.bind_eq_some_iff.1 h
      rw [ha]
      exact hA _ a ha

/-! ## 2 How many plans there are -/

/-- What an Except-valued mapM returns is as long as its list. -/
theorem exceptMapLength {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    rfl
  | x :: l, r, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, _, h⟩ := Fo.BatRows.bindE_ok h
    obtain ⟨r', h2, h⟩ := Fo.BatRows.bindE_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    simp [exceptMapLength f l r' h2]

/-- The attention configuration has one plan for each group. -/
theorem attentionPlansSize {P : OnBytes.Model.PolScan} {y : OnBytes.Model.Layer.Lay}
    {s : OnBytes.Model.Layer.Scales} {mq : ℕ → ℕ} {c : OnBytes.Attention.Config}
    (h : OnBytes.Attention.config P y s mq = .ok c) : c.plans.size = y.NGr := by
  unfold OnBytes.Attention.config at h
  obtain ⟨lines, h1, h⟩ := Fo.BatRows.bindE_ok h
  obtain ⟨_, _, h⟩ := Fo.BatRows.bindE_ok h
  obtain ⟨_, _, h⟩ := Fo.BatRows.bindE_ok h
  obtain ⟨plans, h2, h⟩ := Fo.BatRows.bindE_ok h
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨_, _, h⟩ := Fo.BatRows.bindE_ok h
    obtain rfl := Except.ok.inj h
    have e := exceptMapLength _ _ _ h2
    simpa using e

/-- An attention plan's number is below the number of groups. -/
theorem attentionIndexIsBelowGroups {pol KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (h : publicOf pol KL layout = .ok X) {g : ℕ}
    {a : OnBytes.Attention.Plan} (hg : X.A[g]? = some a) : g < X.NGr := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := Fo.Pub.publicOf_cut pol KL layout X h
  rw [k7] at hg
  have e0 : ∃ a0, A0[g]? = some a0 := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, by simpa using e1⟩
  obtain ⟨a0, e1⟩ := e0
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 e1
    rw [attentionPlansSize k9] at hl
    exact hl
  · simp at e1

/-- A link at which lookAt returns, at twelve groups with attention links, is one of the 25. -/
theorem linkIsBelowTwentyFive {X : OnBytes.Model.Verify.Public} (h4 : X.p4 = true)
    (hN : X.NGr = 12) (hG : X.G.size = 12)
    (hA : ∀ (g : ℕ) (a : OnBytes.Attention.Plan), X.A[g]? = some a → g < 12) {i : ℕ} {d : Bool}
    {pl : VerifiableInference.Desc.First.Look.Place} (h : lookAt X i d = some pl) : i < 25 := by
  have es : (if X.p4 = true then 2 else 1) = 2 := by
    rw [h4]
    rfl
  unfold lookAt at h
  dsimp only at h
  rw [es, hN] at h
  by_cases h1 : (i == 2 * 12) = true
  · have e := beq_iff_eq.1 h1
    omega
  · rw [if_neg h1] at h
    by_cases h2 : (i % 2 == 0) = true
    · rw [if_pos h2] at h
      obtain ⟨hp, hh, _⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hh
      rw [hG] at hl
      omega
    · rw [if_neg h2] at h
      obtain ⟨a, ha, _⟩ := Option.bind_eq_some_iff.1 h
      have e := hA _ a ha
      omega

/-! ## 3 At a site, in scope -/

section
variable {Zl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {Zp : Pub}

/-- In scope: attention links, twelve groups, twelve plans of layers, attention plans below twelve. -/
theorem publicNumbersInScope (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) :
    Zp.p.X.p4 = true ∧ Zp.p.X.NGr = 12 ∧ Zp.p.X.G.size = 12 ∧
      ∀ (g : ℕ) (a : OnBytes.Attention.Plan), Zp.p.X.A[g]? = some a → g < 12 := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hZ hR h
  exact ⟨h4, hN, (Meaning.plans_size h).trans hN, fun g a hg => by
    have e := attentionIndexIsBelowGroups h hg
    omega⟩

/-- **A site's link is one of the 25.** -/
theorem linkIsBelowTwentyFiveAtSite (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) (s : Site)
    (hs : s ∈ lookSites Zp) : s.link < 25 := by
  obtain ⟨h4, hN, hG, hA⟩ := publicNumbersInScope hZ hR h
  obtain ⟨pl, h1, _⟩ := Law.Spec.sites_look Zp s hs
  exact linkIsBelowTwentyFive h4 hN hG hA h1

/-- **Off the head, a site's group is below twelve**, on the calls and on the digits. -/
theorem groupIsBelowTwelveOffTheHead (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) (s : Site)
    (hs : s ∈ lookSites Zp) (hc : s.caller ≠ .head) : s.group < 12 := by
  obtain ⟨h4, hN, -, -⟩ := publicNumbersInScope hZ hR h
  have hl := linkIsBelowTwentyFiveAtSite hZ hR h s hs
  obtain ⟨pl, _, _, e3, e4, _⟩ := Law.Spec.sites_look Zp s hs
  have es : (if Zp.p.X.p4 = true then 2 else 1) = 2 := by
    rw [h4]
    rfl
  unfold callerOf at e3 e4
  dsimp only at e3 e4
  rw [es, hN] at e3 e4
  by_cases h1 : (s.link == 2 * 12) = true
  · rw [if_pos h1] at e3
    exact absurd e3 hc
  · rw [if_neg h1] at e4
    have hne : s.link ≠ 24 := fun e => h1 (by rw [e]; rfl)
    have e5 : s.group = s.link / 2 := by
      rw [e4]
      split <;> rfl
    omega

/-- **At a site on the calls of layers or attention the group is below twelve.** -/
theorem groupIsBelowTwelve (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) (s : Site) (hs : s ∈ lookSites Zp)
    (_hd : s.digits = false) (hc : s.caller ≠ .head) : s.group < 12 :=
  groupIsBelowTwelveOffTheHead hZ hR h s hs hc

/-- **At a site on the digits the link's record is what the maker of the two calls returned**, up
to the fields that the tests do not read. -/
theorem digitsTailComesFromPieces (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) :
    Fo.ZPlan.FromPieces (tlOf Zp.p.X s.link) := by
  obtain ⟨pl, h1, _⟩ := Law.Spec.sites_look Zp s hs
  rw [hd] at h1
  exact tailHoldsAtLook (Q := Fo.ZPlan.FromPieces) (Fo.ZPlan.public_G_from h)
    (Fo.ZPlan.public_A_from h) (Fo.ZPlan.public_H_from h) h1

/-- The first matrix of every link below 25 has a label. -/
theorem firstMatrixHasALabel (X : OnBytes.Model.Verify.Public) {k : ℕ} (hk : k < 25) :
    (labelAt X k 0).isSome = true := by
  have hσ : ∃ σ, Seg.ofNo 12 k = some σ := by
    unfold Seg.ofNo
    split_ifs <;> first | exact ⟨_, rfl⟩ | omega
  obtain ⟨σ, e⟩ := hσ
  have hp : ∀ a b c d : ℕ, 0 < (MatName.all a b c d σ).length := by
    intro a b c d
    cases σ <;> simp [MatName.all]
  unfold labelAt
  rw [e]
  show (((MatName.all _ _ _ _ σ)[0]?).map MatName.label).isSome = true
  rw [List.getElem?_eq_getElem (hp _ _ _ _)]
  rfl

/-- **The digits' columns fit the matrices' rows of cells** at a site on the digits. -/
theorem digitColumnsFitAtSite (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = true) : DigitColsFit (tlOf Zp.p.X s.link) := by
  obtain ⟨pl, h1, _⟩ := Law.Spec.sites_look Zp s hs
  rw [hd] at h1
  have hc : OnBytes.DgP.colsTest (tlOf Zp.p.X s.link) = true :=
    tailHoldsAtLook (Q := fun tl => OnBytes.DgP.colsTest tl = true) (Fo.ZPlan.public_G_cols h)
      (Fo.ZPlan.public_A_cols h) (Fo.ZPlan.public_H_cols h) h1
  have hn : (tlOf Zp.p.X s.link).NM = (tlOf Zp.p.X s.link).mats.size :=
    tailHoldsAtLook (Q := fun tl => tl.NM = tl.mats.size) (Fo.PubNM.public_G_NM h)
      (Fo.PubNM.public_A_NM h) (Fo.PubNM.public_H_NM h) h1
  have hk := linkIsBelowTwentyFiveAtSite hZ hR h s hs
  have hl := (OnBytes.HonestTrace.planLabels_in_scope hZ hR h).names s.link hk 0
  have h0 : (nameAt (tlOf Zp.p.X s.link).mats 0).isSome = true := by
    rw [hl]
    exact firstMatrixHasALabel _ hk
  have hp : 0 < (tlOf Zp.p.X s.link).mats.size := by
    unfold nameAt at h0
    cases hm : (tlOf Zp.p.X s.link).mats[0]? with
    | none =>
      rw [hm] at h0
      cases h0
    | some M =>
      obtain ⟨l, _⟩ := Array.getElem?_eq_some_iff.1 hm
      exact l
  exact ⟨hc, by omega, hn⟩

/-- **The digits' width is the number of all rows of cells** at a site on the digits. -/
theorem digitWidthFitsAtSite (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = true) : MzFits (tlOf Zp.p.X s.link) :=
  mz_allRows _ (digitColumnsFitAtSite hZ hR h s hs hd)

end

/-! ## 4 The round that samples the matrix -/

/-- The number inside link l at which the lookup on the digits stands, at twelve groups. -/
def digitsPiece (l : ℕ) : ℕ := if l = 24 then 8 else 7

/-- The same of the lookup on the calls: for the control below. -/
def callsPiece (l : ℕ) : ℕ := if l = 24 then 3 else 2

/-- At a table of places: link l's sampling round stands in front of the K3 place at piece l. -/
def roundStandsInFrontAtLink (ps : List Spot) (piece : ℕ → ℕ) (l : ℕ) : Bool :=
  match rngIn ps l, baseIn ps (⟨1, some l, piece l, .K3⟩ : Place) with
  | some r, some n => decide (r < n)
  | _, _ => false

/-- The same at each of the 25 links. -/
def roundsStandInFront (ps : List Spot) (piece : ℕ → ℕ) : Bool :=
  (List.range 25).all (roundStandsInFrontAtLink ps piece)

set_option maxRecDepth 1000000 in
/-- **The closed fact**, by Lean's kernel: at the written places the rounds stand in front of the
lookups on the digits. -/
theorem roundsStandInFrontWritten : roundsStandInFront spotsWritten digitsPiece = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: the lookups on the calls stand in front of the rounds. -/
theorem roundsStandBehindTheCalls : roundsStandInFront spotsWritten callsPiece = false := by
  decide +kernel

/-- What a site with a sampling round says of its address. -/
theorem siteRoundAndBase {X : OnBytes.Model.Verify.Public} {ps : List Spot}
    {x : ℕ × Bool × Place} {s : Site} (hs : siteAt X ps x = some s) {r : ℕ}
    (hr : s.rng = some r) :
    x.2.1 = true ∧ s.link = x.1 ∧ rngIn ps x.1 = some r ∧ baseIn ps x.2.2 = some s.at_.base := by
  unfold siteAt at hs
  obtain ⟨p, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨n, hn, hs⟩ := Option.bind_eq_some_iff.1 hs
  dsimp only at hs
  split at hs
  · rename_i hx
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 hs
    obtain rfl : r' = r := Option.some.inj hr
    exact ⟨hx, rfl, hr', hn⟩
  · obtain rfl := Option.some.inj hs
    simp at hr

/-- **At the written table the round stands in front of the lookup**, at twelve groups with
attention links. -/
theorem roundInFrontAtWrittenTable {Zp : Pub} (h4 : Zp.p.X.p4 = true) (hN : Zp.p.X.NGr = 12)
    (hc : Zp.cuts = cutWritten) (s : Site) (hs : s ∈ lookSites Zp) (hl : s.link < 25) {r : ℕ}
    (hr : s.rng = some r) : r < s.at_.base := by
  have eps : (spotsOf Zp.cuts).getD [] = spotsWritten := by
    rw [hc, spots_written]
    rfl
  unfold lookSites at hs
  obtain ⟨x, hx, hsx⟩ := List.mem_filterMap.1 hs
  have hsx' : siteAt Zp.p.X spotsWritten x = some s := by
    rw [← eps]
    exact hsx
  obtain ⟨e1, e2, e3, e4⟩ := siteRoundAndBase hsx' hr
  unfold K3Lot.addresses at hx
  obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hx
  obtain ⟨dg, -, rfl⟩ := List.mem_map.1 hi
  dsimp only at e1 e2 e3 e4
  subst e1
  subst e2
  have ep : VerifiableInference.Desc.K3.pieceAt Zp.p.X s.link true = digitsPiece s.link := by
    by_cases e : s.link = 24 <;>
      simp [VerifiableInference.Desc.K3.pieceAt, VerifiableInference.Desc.K3.isHead, digitsPiece,
        h4, hN, e]
  rw [ep] at e4
  have hall := List.all_eq_true.1
    (show (List.range 25).all (roundStandsInFrontAtLink spotsWritten digitsPiece) = true from
      roundsStandInFrontWritten) s.link (List.mem_range.2 hl)
  unfold roundStandsInFrontAtLink at hall
  rw [e3, e4] at hall
  exact of_decide_eq_true hall

section
variable {Zl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Zp : Pub}

/-- **At live files in scope the public part's table of stretches is the written one.** -/
theorem cutsAreWrittenAtLiveFiles (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Zl) = true)
    (hP : ProofFile.pubPlain OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL = .ok Zp) :
    Zp.cuts = cutWritten := by
  obtain ⟨Zq, Np, cF, x, hh⟩ := P5J.head_of_live Zl hZ hR hL
  obtain rfl : Zq = Zp := Except.ok.inj (hh.laid.pub.symm.trans hP)
  exact Law.AtThr.cuts_head hh

/-- **At live files in scope publicOf returns the plain road's public record.** -/
theorem publicReturnsAtLiveFiles (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Zl) = true)
    (hP : ProofFile.pubPlain OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL = .ok Zp) :
    publicOf Zl.pol Zl.KL (some Zl.lay) = .ok Zp.p.X := by
  obtain ⟨Zq, Np, cF, x, hh⟩ := P5J.head_of_live Zl hZ hR hL
  obtain rfl : Zq = Zp := Except.ok.inj (hh.laid.pub.symm.trans hP)
  exact hh.toAtMg.pubOne

/-- **At live files in scope the test rngFrontB accepts.** -/
theorem samplingRoundsStandInFrontAtLiveFiles (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Zl) = true)
    (hP : ProofFile.pubPlain OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL = .ok Zp) :
    rngFrontB Zp = true := by
  have hX := publicReturnsAtLiveFiles hZ hR hL hP
  have hc := cutsAreWrittenAtLiveFiles hZ hR hL hP
  obtain ⟨h4, hN, -, -⟩ := publicNumbersInScope (Zp := Zp) hZ hR hX
  unfold rngFrontB rngFrontOn
  refine List.all_eq_true.2 fun s hs => ?_
  cases hr : s.rng with
  | none => rfl
  | some r =>
    exact decide_eq_true (roundInFrontAtWrittenTable h4 hN hc s hs
      (linkIsBelowTwentyFiveAtSite hZ hR hX s hs) hr)

/-- **At live files in scope there is a site on the digits at each of the 25 links.** So the laws
of this file are not empty there. -/
theorem digitSitesExistAtLiveFiles (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Zl) = true)
    (hP : ProofFile.pubPlain OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL = .ok Zp) (l : ℕ) (hl : l < 25) :
    ∃ s ∈ lookSites Zp, s.link = l ∧ s.digits = true := by
  obtain ⟨Zq, Np, cF, x, hh⟩ := P5J.head_of_live Zl hZ hR hL
  obtain rfl : Zq = Zp := Except.ok.inj (hh.laid.pub.symm.trans hP)
  obtain ⟨s, hs, e1, e2, _⟩ := Law.AtThr.site_digits hh l hl true
  exact ⟨s, hs, e1, e2⟩

end

/-! ## 5 What a site on the digits is handed -/

section
variable {W₀ Rc Xi Tr' : Type} {Zl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}
  {lay : Option ByteArray} {Zp : Pub}

/-- **Where the test accepts, what a site is handed is settled at the site's base.** -/
theorem digitsAreSettled (hF : rngFrontB Zp = true) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (s : Site)
    (hs : s ∈ lookSites Zp) (t : Local W₀ Rc Xi Tr') :
    Ask.Settled s.at_.base (askOf (sourcesAt cells weights req Zp) (whoOf s) t) :=
  askOf_settled _ _ t _ fun link r e => rng_front Zp hF s hs r (who_digits s link r e)

/-- **The digits' keys and bits are honest**, at every input and all challenges heard. -/
theorem digitsKeysAndBitsAreHonest (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (cells : Tr' → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (t : Local W₀ Rc Xi Tr') (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (heard : List Fmt.Drawn) :
    ∃ L : LookIn, askOf (sourcesAt cells weights req Zp) (whoOf s) t heard = L.hidden ∧
      L.Meets s.shape s.p.lm := by
  obtain ⟨r, hr, h1, h2, h3⟩ := Law.Spec.site_digits Zp s hs hd
  have hB : ShapeIsFs Zp.p.X s := Law.AtThr.shapeIsFs_of_public h s hs
  have hsh : s.shape = (tlOf Zp.p.X s.link).f9 := Option.some.inj (hB.symm.trans h1)
  refine ⟨lookZ (tlOf Zp.p.X s.link) (zzOwn Zp.p.X s.link (cells t.trace) (tritsAt heard r)),
    ?_, ?_⟩
  · rw [h3]
    rfl
  · rw [hsh, h2]
    exact digits_meets (digitsTailComesFromPieces h s hs hd)
      (digitWidthFitsAtSite hZ hR h s hs hd) (matsOwn Zp.p.X s.link) _ _

/-- **The specification's relation after the challenge**, at every input and all challenges. -/
theorem digitsRelationAfterTheChallenge (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (cells : Tr' → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (t : Local W₀ Rc Xi Tr') (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (heard ds : List Fmt.Drawn) :
    (siteData s (askOf (sourcesAt cells weights req Zp) (whoOf s) t) heard ds).Mid := by
  obtain ⟨r, hr, h1, h2, h3⟩ := Law.Spec.site_digits Zp s hs hd
  have hB : ShapeIsFs Zp.p.X s := Law.AtThr.shapeIsFs_of_public h s hs
  have hsh : s.shape = (tlOf Zp.p.X s.link).f9 := Option.some.inj (hB.symm.trans h1)
  show (dataAt (fun theta => _root_.Fo.numsF s.shape s.p.lm s.p.first theta)
    (askOf (sourcesAt cells weights req Zp) (whoOf s) t heard)
    (ptsOf s.at_.face s.at_.base (heard ++ ds))).Mid
  rw [h3, hsh, h2]
  exact Law.midZ (digitsTailComesFromPieces h s hs hd) (digitWidthFitsAtSite hZ hR h s hs hd)
    (matsOwn Zp.p.X s.link) _ _ s.p.first _

/-- **The library's key vectors at a site on the digits.** -/
theorem digitsFillingIsTheLibrarys (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (cells : Tr' → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (t : Local W₀ Rc Xi Tr') (s : Site)
    (hs : s ∈ lookSites Zp) (hd : s.digits = true) (mask : ℕ → GE) (theta : GE)
    (heard : List Fmt.Drawn) :
    ∃ r, s.rng = some r ∧
      FillsAt s (askOf (sourcesAt cells weights req Zp) (whoOf s) t)
        (lookZ (tlOf Zp.p.X s.link) (zzOwn Zp.p.X s.link (cells t.trace) (tritsAt heard r)))
        (kvZ (tlOf Zp.p.X s.link)
          (inExt (zzOwn Zp.p.X s.link (cells t.trace) (tritsAt heard r))))
        (nuZm (tlOf Zp.p.X s.link) (zzOwn Zp.p.X s.link (cells t.trace) (tritsAt heard r)) mask)
        theta heard :=
  Law.Exchange.fills_digits Zp cells weights req s hs hd t
    (Law.AtThr.shapeIsFs_of_public h s hs) (digitsTailComesFromPieces h s hs hd) mask theta heard

/-- **The digits of a link's smallness test**, at the lot's own letters: at every input. -/
theorem honestKeysAndBitsAtTheDigits (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok Zp.p.X)
    (weights : W₀ → Weights) (t : Local W₀ Rc Inst Cells) (s : Site) (hs : s ∈ lookSites Zp)
    (hd : s.digits = true) (heard : List Fmt.Drawn) :
    ∃ L : LookIn, askOf (sourcesAt id weights (reqAt Zp) Zp) (whoOf s) t heard = L.hidden ∧
      L.Meets s.shape s.p.lm :=
  digitsKeysAndBitsAreHonest hZ hR h id weights (reqAt Zp) t s hs hd heard

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.tailHoldsAtLook
#print axioms ProofFile.Honest.K3.Term.attentionIndexIsBelowGroups
#print axioms ProofFile.Honest.K3.Term.linkIsBelowTwentyFiveAtSite
#print axioms ProofFile.Honest.K3.Term.groupIsBelowTwelveOffTheHead
#print axioms ProofFile.Honest.K3.Term.groupIsBelowTwelve
#print axioms ProofFile.Honest.K3.Term.digitsTailComesFromPieces
#print axioms ProofFile.Honest.K3.Term.firstMatrixHasALabel
#print axioms ProofFile.Honest.K3.Term.digitColumnsFitAtSite
#print axioms ProofFile.Honest.K3.Term.digitWidthFitsAtSite
#print axioms ProofFile.Honest.K3.Term.roundsStandInFrontWritten
#print axioms ProofFile.Honest.K3.Term.roundsStandBehindTheCalls
#print axioms ProofFile.Honest.K3.Term.roundInFrontAtWrittenTable
#print axioms ProofFile.Honest.K3.Term.cutsAreWrittenAtLiveFiles
#print axioms ProofFile.Honest.K3.Term.publicReturnsAtLiveFiles
#print axioms ProofFile.Honest.K3.Term.samplingRoundsStandInFrontAtLiveFiles
#print axioms ProofFile.Honest.K3.Term.digitSitesExistAtLiveFiles
#print axioms ProofFile.Honest.K3.Term.digitsAreSettled
#print axioms ProofFile.Honest.K3.Term.digitsKeysAndBitsAreHonest
#print axioms ProofFile.Honest.K3.Term.digitsRelationAfterTheChallenge
#print axioms ProofFile.Honest.K3.Term.digitsFillingIsTheLibrarys
#print axioms ProofFile.Honest.K3.Term.honestKeysAndBitsAtTheDigits
