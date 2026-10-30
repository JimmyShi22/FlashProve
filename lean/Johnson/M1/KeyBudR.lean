-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: what the row of the ranges' test owes to BudDebts.
/-
Johnson/M1/KeyBudR.lean: the field bud₁ of BudDebts at a list that stands at the proximity test on the ranges' group of the key file's first chain, at every due list of
challenges: the key file's twin of budOwed_at_L. Premises as at Johnson/M1/KeyBudU.lean.
No property of the protocol is claimed here.
-/
import Johnson.M1.KeyBudU
import Johnson.M1.KeyBudFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1.KeyBud
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.KeyFirst (aloneInFirstChain bound_rest_first_chain)
open H2K.Pub (sgOf)
open H2K.Member (piKRFull)
open Johnson.G.OfPlan (rootsOf)
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open OnBytes.M1 (keyDecl_of_named cut_front)

def frontKR : List Fmt.DeclaredRound := declKeyFull.1.take 18805
def testKR : List Fmt.DeclaredRound := (declKeyFull.1.drop 18805).take 23
def behindKR : List Fmt.DeclaredRound := declKeyFull.1.drop 18828

/-- aloneInFirstChain in written letters. -/
def aloneKR (k : ℕ) : Bool :=
  (openedOf 0 frontKR ++ openedOf 0 behindKR ++ openedOf 1 declKeyFull.2.1 ++
    openedOf 2 declKeyFull.2.2).all (·.1 != (0, k))

def srcsKR : List Fmt.TreeSource := [.own 1]

set_option maxRecDepth 1000000 in
theorem roots_KR : rootsOf frontKR = 2 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_KR : opensFitB false piKRFull.nums.stages testKR [22] srcsKR 2 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem far_KR : (none :: depths false piKRFull.nums.stages).length ≤ firstLen piKRFull.nums.stages + 40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem alone_KR : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf false piKRFull.nums.stages (firstLen piKRFull.nums.stages + i)).isSome ||
      aloneKR (2 + ((List.range (firstLen piKRFull.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf false piKRFull.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem no_KR : (aloneKR 5, opensFitB false piKRFull.nums.stages testKR [21] srcsKR 2,
    opensFitB false piKRFull.nums.stages testKR [22] srcsKR 3) = (false, false, false) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rows_KR : ∀ r ∈ AtPublicFiles.KeyBook.fullFirst, r.1 = ⟨1, none, 5, .K12⟩ → r.2 = 23 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem start_KR : AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullFirst ⟨1, none, 5, .K12⟩ = some 18805 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem first_places_apart : (AtPublicFiles.KeyBook.fullFirst.map (·.1)).Nodup := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

theorem first_apart (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    ((keyFileDescription Xs N Pl).first.blocksInOrder.map (·.place)).Nodup := by
  have e : (keyFileDescription Xs N Pl).first.blocksInOrder.map (·.place) = AtPublicFiles.KeyBook.fullFirst.map (·.1) := by
    rw [← (AtPublicFiles.KeyBook.places_named scope h).1]
    unfold Johnson.RunOne.Sound.rowsOf
    rw [List.map_map]
    rfl
  rw [e]
  exact first_places_apart

theorem front_first (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)} {b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl}
    {t : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)} (hF : (keyFileDescription Xs N Pl).first.blocksInOrder = pre ++ b :: t) :
    AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullFirst b.place = some (pre.flatMap (·.rounds)).length := by
  have hn := first_apart scope h
  rw [hF, List.map_append, List.map_cons] at hn
  have hp : ∀ c ∈ pre, c.place ≠ b.place := fun c hc e =>
    (List.nodup_append.1 hn).2.2 _ (List.mem_map_of_mem hc) _ (List.mem_cons_self ..) e
  rw [← AtPublicFiles.KeyBook.start_named₁ scope h, hF]
  exact cut_front pre b t hp

end

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

local notation "𝔽" => keyFileDescription Xs N Pl

/-- **At a cut at the test's place the rounds are the written ones.** -/
theorem cut_KR (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₁ (𝔽).Cl)} {b : Block (𝔽).S₁ (𝔽).Cl}
    (hcut : (𝔽).first.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨1, none, 5, .K12⟩) :
    pre.flatMap (·.rounds) = frontKR ∧ t.flatMap (·.rounds) = behindKR ∧ b.rounds = testKR := by
  have hd : (𝔽).first.blocksInOrder.flatMap (·.rounds) = declKeyFull.1 :=
    congrArg Prod.fst (keyDecl_of_named scope h)
  have hl₁ : (pre.flatMap (·.rounds)).length = 18805 := by
    have e := front_first scope h hcut
    rw [hb, start_KR] at e
    exact (Option.some.inj e).symm
  have hl₂ : b.rounds.length = 23 := by
    have hm : (b.place, b.rounds.length) ∈ AtPublicFiles.KeyBook.fullFirst := by
      rw [← (AtPublicFiles.KeyBook.places_named scope h).1, hcut]
      exact List.mem_map.2 ⟨b, by simp, rfl⟩
    exact rows_KR _ hm hb
  rw [hcut, List.flatMap_append, List.flatMap_cons] at hd
  obtain ⟨e1, e2, e3⟩ := cut_lists _ _ _ _ hd
  rw [hl₁] at e1
  rw [hl₁, hl₂] at e2 e3
  exact ⟨e1, e2, e3⟩

theorem alone_is_KR (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₁ (𝔽).Cl)} {b : Block (𝔽).S₁ (𝔽).Cl}
    (hcut : (𝔽).first.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨1, none, 5, .K12⟩) (k : ℕ) :
    aloneInFirstChain (𝔽) pre t k = aloneKR k := by
  obtain ⟨e1, e2, -⟩ := cut_KR scope h hcut hb
  unfold aloneInFirstChain aloneKR
  rw [keyDecl_of_named scope h, e1, e2]

/-- **The three named premises, at the key file.** -/
theorem premises_at_KR (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {W X : Type}
    (J : TestJob W X) (hst : J.p.nums.stages = piKRFull.nums.stages) (hfr : J.fresh.isNone = false)
    {pre t : List (Block (𝔽).S₁ (𝔽).Cl)} {b : Block (𝔽).S₁ (𝔽).Cl}
    (hcut : (𝔽).first.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨1, none, 5, .K12⟩) :
    OpensFit J b.rounds [22] (fun k => srcsKR.getD k (.own 0)) (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ k, k < [22].length → ∀ n,
        ProofFile.Honest.srcOf 0 ((fun k => srcsKR.getD k (.own 0)) k) = (0, n) →
        n < rootsOf (pre.flatMap (·.rounds))) ∧
      ∀ i, (ProofFile.Honest.K12.depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        aloneInFirstChain (𝔽) pre t (rootsOf (pre.flatMap (·.rounds)) +
          sentBefore J (firstLen J.p.nums.stages + i)) = true := by
  obtain ⟨e1, -, e3⟩ := cut_KR scope h hcut hb
  have h3 : rootsOf (pre.flatMap (·.rounds)) = 2 := by
    rw [e1]
    exact roots_KR
  have hdep : ∀ r, ProofFile.Honest.K12.depthAt J r = ProofFile.Honest.K12.depthOf false piKRFull.nums.stages r := fun r => by
    unfold ProofFile.Honest.K12.depthAt ProofFile.Honest.K12.depthOf
    rw [hfr, hst]
  rw [h3]
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · rw [e3, hfr, hst]
    exact opens_KR
  · intro j hj n hn
    match j, hj, hn with
    | 0, _, hn =>
      have e : (1 : ℕ) = n := congrArg Prod.snd hn
      omega
  · intro i hi
    rw [alone_is_KR scope h hcut hb]
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen piKRFull.nums.stages + i) =
        ((List.range (firstLen piKRFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf false piKRFull.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    by_cases hlt : i < 40
    · have hh := List.all_eq_true.1 alone_KR i (List.mem_range.2 hlt)
      rw [hi] at hh
      simpa using hh
    · exfalso
      have hf := far_KR
      have hn : ProofFile.Honest.K12.depthOf false piKRFull.nums.stages
          (firstLen piKRFull.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn] at hi
      cases hi

local instance keyBudRInstance1 (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) := ⟨(default, default)⟩
local instance keyBudRInstance2 (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **THE TEST'S ROW OWES NOTHING MORE TO bud₂, AT THE KEY FILE.** -/
theorem budOwed₁_at_KR (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₁ (𝔽).Cl V W Y Pb) (J : TestJob W Y) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (hst : J.p.nums.stages = piKRFull.nums.stages) (hplace : J.p.place = ⟨1, none, 5, .K12⟩)
    {b₀ : Block (𝔽).S₁ (𝔽).Cl} (hf₀ : ((𝔽).first.blocksInOrder.find? fun b => b.place == J.p.place) = some b₀)
    (hpl₀ : b₀.place = J.p.place) (hr₀ : b₀.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor₀ : b₀.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = J.p)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).first.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).first.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due (𝔽) = true →
      L.bud u.number ((ρ.first.drop n).take u.rounds.length)
        (asksFrom (treeAsks (𝔽) ρ 0) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).first.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' : testSide (𝔽).first.blocksInOrder J Js [] = some σ := by
    unfold testSide
    rw [← hpl, ← hrow]
    exact hσ
  obtain ⟨-, f2, -, -, -⟩ := (any_at_place (V := V) J Js Fc _ b₀ hf₀ hpl₀ hr₀ hor₀ hfrN hs ho).2.2 [] σ hσ'
  have f2' : σ.members = [firstMember J Js, restMember J Js] := f2
  rw [f2'] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact hbud _ _ _ (budBoth_of_testBud Js _ _ (first_owes_nothing Js ho _ _))
  · have hσ'' := hσ'
    unfold testSide Side.seated at hσ''
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ''
    have hrowσ : σ.row = testPairs J Js := by rw [← e]
    obtain ⟨s, next, rest, hst'⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
      have hform := Fc.form
      unfold formPubB at hform
      cases hs' : J.p.nums.stages with
      | nil => rw [hs'] at hform; cases hform
      | cons a l =>
        cases l with
        | nil => rw [hs'] at hform; cases hform
        | cons b' r' => exact ⟨a, b', r', rfl⟩
    have FP := formPub_of_B J.p s next rest hst' Fc.form
    have hk : s.k = (sgOf s).h + (sgOf s).g := by
      have := FP.hk
      show s.k = s.h + (s.k - s.h)
      omega
    have hb' : b = b₀ := Option.some.inj (hb.symm.trans hf₀)
    have eb : σ.block = b₀ := by rw [← hb', ← e]
    have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
      rw [eb, hr₀, hor₀]
      show _ = H2K.JointK.laidOf J.p
      exact zip_laid _ Fc.plan
    have hblk : σ.block ∈ (𝔽).first.blocksInOrder := by
      rw [hcut]
      exact List.mem_append_right _ List.mem_cons_self
    have hsh : σ.block.shaped = true := planOk_shaped_first h.plan σ.block hblk
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hsh, Nat.min_self]
    have hT : tablesFitB J = true := by
      rw [tablesFitB_eq, hfrN]
      exact Fc.tab
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped_first h.plan x (by rw [hcut]; exact List.mem_append_left _ hx))
      hzip hT Fc.enough
    rw [← hcut] at hN
    obtain ⟨O, hold, ha⟩ := premises_at_KR scope h J hst hfrN hcut (by rw [eb, hpl₀, hplace])
    have hB := bound_rest_first_chain (V := V) J Js pre t σ.block hcut [22] _ _ O s
      next rest hst' hk hT hold hlen Fc.enough ρ hρ ha
    have l1 : (firstPart J : ProofFile.Honest.Part V W Y).moves.length = firstLen J.p.nums.stages :=
      (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
    have hTo : σ.roundsTo (restMember (V := V) J Js).number = firstLen J.p.nums.stages := by
      unfold Side.roundsTo
      rw [hrowσ]
      show (firstPart J : ProofFile.Honest.Part V W Y).moves.length + 0 = _
      rw [l1]
      rfl
    subst hn
    rw [hTo]
    refine hbud _ _ _ ((both_rest Js _ _).2 ?_)
    rw [hs, hN]
    exact hB

end OnBytes.M1.KeyBud

#print axioms OnBytes.M1.KeyBud.premises_at_KR
#print axioms OnBytes.M1.KeyBud.budOwed₁_at_KR
