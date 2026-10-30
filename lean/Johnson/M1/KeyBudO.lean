-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: what the row of the proximity test on Omega's group owes to BudDebts.
/-
Johnson/M1/KeyBudO.lean: the field bud₂ of BudDebts at a list that stands at the test on G_omega of the key file's shared chain, at every due list of
challenges: the key file's twin of budOwed₂_at_O. The first member's bound is the library's bud_first_KO, the second's bud_rest_apart.

What stays a premise: that the job is at pKO, that the files pass the test protocolDataWellFormed (key_written asks it), and KeySourced. pKO_is ties pKO's place to the written place's; that the two have one number is not shown here. No property of the
protocol is claimed here.
-/
import Johnson.M1.KeyBudU
import E2E.KeyPublic
import Johnson.M1.KeyBudRest
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudOwnAtKey
import Johnson.Desc.ProofFile.Honest.K12.Sim.KeyHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.OwnAnyAtPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1.KeyBud
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.KeyRest (bud_rest_apart)
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull oT o_typed)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeySourced)
open OnBytes.M1 (keyDecl_of_named)

def frontKO : List Fmt.DeclaredRound := declKeyFull.2.1.take 43
def testKO : List Fmt.DeclaredRound := (declKeyFull.2.1.drop 43).take 24
def behindKO : List Fmt.DeclaredRound := declKeyFull.2.1.drop 67

def aloneKO (k : ℕ) : Bool :=
  (openedOf 0 declKeyFull.1 ++ openedOf 1 frontKO ++ openedOf 1 behindKO ++
    openedOf 2 declKeyFull.2.2).all (·.1 != (1, k))

def srcsKO : List Fmt.TreeSource := [.own 1, .own 2, .own 7]

set_option maxRecDepth 1000000 in
theorem roots_KO' : rootsOf frontKO = 7 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_KO' : opensFitB true pKO.nums.stages testKO [22, 13, 13] srcsKO 7 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem far_KO : (none :: depths true pKO.nums.stages).length ≤ firstLen pKO.nums.stages + 40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem alone_KO : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf true pKO.nums.stages (firstLen pKO.nums.stages + i)).isSome ||
      aloneKO (7 + ((List.range (firstLen pKO.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf true pKO.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem apart_KO : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf true pKO.nums.stages (firstLen pKO.nums.stages + i)).isSome ||
      decide (7 < 7 + ((List.range (firstLen pKO.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf true pKO.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem no_KO : (opensFitB true pKO.nums.stages testKO [22, 13, 13] srcsKO 8,
    opensFitB true pKO.nums.stages testKO [22, 12, 13] srcsKO 7,
    opensFitB false pKO.nums.stages testKO [22, 13, 13] srcsKO 7) = (false, false, false) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rows_KO' : ∀ r ∈ AtPublicFiles.KeyBook.fullShared, r.1 = ⟨2, none, 10, .K12⟩ → r.2 = 24 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem start_KO : AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullShared ⟨2, none, 10, .K12⟩ = some 43 := by decide +kernel

theorem place_KO : pKO.place = ⟨2, none, 10, .K12⟩ := H2K.JointK.place_of_p12At _ _

set_option maxRecDepth 1000000 in
/-- The seated place is the written place's. -/
theorem pKO_is : pKO.place = H2K.Member.piKOFull.place := by
  decide +kernel

/-- The stages too: one number. -/
theorem pKO_stages : pKO.nums.stages = H2K.Member.piKOFull.nums.stages := rfl

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

local notation "𝔽" => keyFileDescription Xs N Pl

theorem cutAt_KO (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₂ (𝔽).Cl)} {b : Block (𝔽).S₂ (𝔽).Cl}
    (hcut : (𝔽).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨2, none, 10, .K12⟩) :
    pre.flatMap (·.rounds) = frontKO ∧ t.flatMap (·.rounds) = behindKO ∧ b.rounds = testKO := by
  have hd : (𝔽).shared.blocksInOrder.flatMap (·.rounds) = declKeyFull.2.1 :=
    congrArg (fun D => D.2.1) (keyDecl_of_named scope h)
  have hl₁ : (pre.flatMap (·.rounds)).length = 43 := by
    have e := OnBytes.M1.front_shared scope h hcut
    rw [hb, start_KO] at e
    exact (Option.some.inj e).symm
  have hl₂ : b.rounds.length = 24 := by
    have hm : (b.place, b.rounds.length) ∈ AtPublicFiles.KeyBook.fullShared := by
      rw [← (AtPublicFiles.KeyBook.places_named scope h).2.1, hcut]
      exact List.mem_map.2 ⟨b, by simp, rfl⟩
    exact rows_KO' _ hm hb
  rw [hcut, List.flatMap_append, List.flatMap_cons] at hd
  obtain ⟨e1, e2, e3⟩ := cut_lists _ _ _ _ hd
  rw [hl₁] at e1
  rw [hl₁, hl₂] at e2 e3
  exact ⟨e1, e2, e3⟩

theorem alone_is_KO (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₂ (𝔽).Cl)} {b : Block (𝔽).S₂ (𝔽).Cl}
    (hcut : (𝔽).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨2, none, 10, .K12⟩) (k : ℕ) :
    aloneB (𝔽) pre t k = aloneKO k := by
  obtain ⟨e1, e2, -⟩ := cutAt_KO scope h hcut hb
  unfold aloneB aloneKO
  rw [keyDecl_of_named scope h, e1, e2]

/-- **The premises of bud_rest_apart, at the key file.** -/
theorem premises_at_KO (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {W X : Type}
    (J : TestJob W X) (hJ : J.p = pKO) (hfr : J.fresh.isNone = true)
    {pre t : List (Block (𝔽).S₂ (𝔽).Cl)} {b : Block (𝔽).S₂ (𝔽).Cl}
    (hcut : (𝔽).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨2, none, 10, .K12⟩) :
    OpensFit J b.rounds [22, 13, 13] (fun k => srcsKO.getD k (.own 0)) (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ i, (ProofFile.Honest.K12.depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        ∀ k, k < [22, 13, 13].length → ∀ n,
          ProofFile.Honest.srcOf 1 ((fun k => srcsKO.getD k (.own 0)) k) = (1, n) →
          n ≠ rootsOf (pre.flatMap (·.rounds)) + sentBefore J (firstLen J.p.nums.stages + i)) ∧
      ∀ i, (ProofFile.Honest.K12.depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        aloneB (𝔽) pre t (rootsOf (pre.flatMap (·.rounds)) +
          sentBefore J (firstLen J.p.nums.stages + i)) = true := by
  obtain ⟨e1, -, e3⟩ := cutAt_KO scope h hcut hb
  have hst : J.p.nums.stages = pKO.nums.stages := by rw [hJ]
  have h3 : rootsOf (pre.flatMap (·.rounds)) = 7 := by
    rw [e1]
    exact roots_KO'
  have hdep : ∀ r, ProofFile.Honest.K12.depthAt J r = ProofFile.Honest.K12.depthOf true pKO.nums.stages r := fun r => by
    unfold ProofFile.Honest.K12.depthAt ProofFile.Honest.K12.depthOf
    rw [hfr, hst]
  rw [h3]
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · rw [e3, hfr, hst]
    exact opens_KO'
  · intro i hi j hj n hn
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen pKO.nums.stages + i) =
        ((List.range (firstLen pKO.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf true pKO.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    have hlt : i < 40 := by
      by_contra hc
      have hf := far_KO
      have hn' : ProofFile.Honest.K12.depthOf true pKO.nums.stages (firstLen pKO.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn'] at hi
      cases hi
    have hh := List.all_eq_true.1 apart_KO i (List.mem_range.2 hlt)
    rw [hi] at hh
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at hh
    have hn7 : n ≤ 7 := by
      match j, hj, hn with
      | 0, _, hn =>
        have e : (1 : ℕ) = n := congrArg Prod.snd hn
        omega
      | 1, _, hn =>
        have e : (2 : ℕ) = n := congrArg Prod.snd hn
        omega
      | 2, _, hn =>
        have e : (7 : ℕ) = n := congrArg Prod.snd hn
        omega
    omega
  · intro i hi
    rw [alone_is_KO scope h hcut hb]
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen pKO.nums.stages + i) =
        ((List.range (firstLen pKO.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf true pKO.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    by_cases hlt : i < 40
    · have hh := List.all_eq_true.1 alone_KO i (List.mem_range.2 hlt)
      rw [hi] at hh
      simpa using hh
    · exfalso
      have hf := far_KO
      have hn : ProofFile.Honest.K12.depthOf true pKO.nums.stages (firstLen pKO.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn] at hi
      cases hi

/-- **THE TEST'S ROW ON G_omega OWES NOTHING MORE TO bud₂, AT THE KEY FILE.** -/
theorem budOwed₂_at_KO (scope : VerifierAndGoals.InScope Z = true) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hS : KeySourced Z Xs N Pl) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₂ (𝔽).Cl V W Y Pb) (J : TestJob W Y) (Js : SimJob Pb)
    (hp : J.p = pKO) (hJ : Js.p = pKO) (hfr : J.fresh.isNone = true) (ho : Js.own = true)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due (𝔽) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (𝔽) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  obtain ⟨X₀, m, hX, hm, r1, r2, r3⟩ := hS.source
  obtain rfl : N = rangesNumsFull :=
    Except.ok.inj (r2.symm.trans (Johnson.AtFull.KeyBack.rangesNumbers_in_scope scope hX hm))
  obtain rfl : Pl = laterPlacesFull :=
    Except.ok.inj (r3.symm.trans (Johnson.AtFull.KeyBack.laterPlaces_in_scope scope hX hm))
  have h := hS.named
  have hW : Johnson.G.OfPlan.writtenOf "key file" (VerifiableInference.Desc.Key.descriptionFromSource Xs rangesNumsFull laterPlacesFull).roundsDeclaredByBlocks =
      .ok Johnson.G.dryKeyFull := by
    obtain ⟨X₁, m₁, h0, hm₁, hd, -⟩ := h.named
    obtain rfl : X₀ = X₁ := Except.ok.inj (hX.symm.trans h0)
    exact key_written Z scope live X₀ Xs hX hd
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hp' : Js.p = J.p := hJ.trans hp.symm
  have hσt : testSide (keyFileDescription Xs rangesNumsFull laterPlacesFull).shared.blocksInOrder J Js [] = some σ :=
    (side_is_testSide L J Js hpl hrow _).symm.trans hσ
  obtain ⟨b, hf, -, hr, hor⟩ := seat_KO (X := Xs) (N := rangesNumsFull) (P := laterPlacesFull) oT o_typed
  have hf' : ((keyFileDescription Xs rangesNumsFull laterPlacesFull).shared.blocksInOrder.find? fun b => b.place == J.p.place) =
      some b := by
    rw [hp]
    exact hf
  have hbl : σ.block = b := by
    unfold testSide Side.seated at hσt
    rw [hf'] at hσt
    obtain rfl := Option.some.inj hσt
    rfl
  have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
    rw [hbl, hr, hor]
    show _ = H2K.JointK.laidOf J.p
    rw [hp]
    exact zip_laid _ plan_KO
  have Fo : PlaceFactsOwn J.p (dsOne 6) := by
    rw [hp]
    exact facts_KO
  have T := firstPubOwn_any J Js Fo hfr hp' ho
  obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
    have hform := T.form
    unfold formPubB at hform
    cases hs' : J.p.nums.stages with
    | nil => rw [hs'] at hform; cases hform
    | cons a l =>
      cases l with
      | nil => rw [hs'] at hform; cases hform
      | cons b' r' => exact ⟨a, b', r', rfl⟩
  have FP := formPub_of_B J.p s next rest hst T.form
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have := FP.hk
    show s.k = s.h + (s.k - s.h)
    omega
  have hcount : (H2K.JointK.laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    rw [hp]
    exact count_KO
  have hmem : σ.members = [firstMember J Js, restMember J Js] :=
    members_of_seat _ J Js [] σ hσt hzip s next rest hst hcount
  rw [hmem] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  refine hbud _ _ _ (both_of J Js hp' u.number _ _ (fun e => ?_) fun e => ?_)
  · rcases hu with rfl | rfl
    · exact bud_first_KO Xs h.plan hW Js J hp hJ [] σ hσt pre t n hcut hn ρ hρ
    · exact absurd e Nat.one_ne_zero
  · rcases hu with rfl | rfl
    · exact absurd e Nat.zero_ne_one
    · have hrow' : σ.row = testPairs J Js := by
        unfold testSide Side.seated at hσt
        obtain ⟨b', -, rfl⟩ := Option.map_eq_some_iff.1 hσt
        rfl
      have hrT : σ.roundsTo 1 = firstLen J.p.nums.stages := by
        unfold Side.roundsTo
        rw [hrow']
        show (firstPart J : ProofFile.Honest.Part V W Y).moves.length + 0 = firstLen J.p.nums.stages
        rw [Nat.add_zero, first_moves_len]
      have hn' : n = (pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages := by
        rw [hn]
        show _ + σ.roundsTo 1 = _
        rw [hrT]
      subst hn'
      have hshb : σ.block.shaped = true := planOk_shaped h.plan σ.block
        (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self)
      have hlen : σ.block.rounds.length = J.laid.length := by
        rw [← hzip, List.length_zip, shaped_len σ.block hshb, Nat.min_self]
      have hN := trees_rest J pre t σ.block
        (fun x hx => planOk_shaped h.plan x (by rw [hcut]; exact List.mem_append_left _ hx)) hzip T.tables
        T.enough
      rw [← hcut] at hN
      have hbpl : σ.block.place = ⟨2, none, 10, .K12⟩ := by
        rw [side_place hσ, hpl, hp]
        exact place_KO
      obtain ⟨O, hap, ha⟩ := premises_at_KO scope h J hp hfr hcut hbpl
      rw [hN]
      exact bud_rest_apart (V := V) J Js pre t σ.block hcut _ _ _ O s next rest hst hk T.tables hap hlen
        T.enough ρ hρ ha

end OnBytes.M1.KeyBud

#print axioms OnBytes.M1.KeyBud.budOwed₂_at_KO
#print axioms OnBytes.M1.KeyBud.premises_at_KO
#print axioms OnBytes.M1.KeyBud.no_KO
#print axioms OnBytes.M1.KeyBud.pKO_is
