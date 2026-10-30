-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: what the row of the proximity test on the folded row's group owes to BudDebts.
/-
Johnson/M1/KeyBudU.lean: the field bud₂ of BudDebts at a list that stands at the test on G_u of the key file's shared chain, at every due list of
challenges: the key file's twin of Johnson/M1/BudU.lean and of Sim/AloneAtU.lean's premises.

  frontKU, testKU, behindKU, aloneKU   the written rounds around the test.
  roots_KU, opens_KU, alone_KU         closed facts, by the kernel.
  cut_KU                               at a cut at the test's place the rounds are the written ones, under KeyNamed, in scope.
  premises_at_KU, budOwed₂_at_KU       the three premises; the field's body.

What stays a premise of budOwed₂_at_KU: that the job's stages are the written place's, PlaceFacts at the job's place, and that the search at the place
finds a block with the test's own rounds and oracles: facts_KU, find_folded, alike_KU (K12's Sim2/RowFolded.lean).
No property of the protocol is claimed here.
-/
import Johnson.M1.KeySendings
import Johnson.Desc.ProofFile.Honest.K12.Sim.AloneAtU
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudRestAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1.KeyBud
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Light.AtU (srcsU)
open H2K.Pub (sgOf)
open H2K.Member (piKUFull)
open Johnson.G.OfPlan (rootsOf)
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open OnBytes.M1 (declChainK keyDecl_of_named front_shared)

def frontKU : List Fmt.DeclaredRound := declKeyFull.2.1.take 8
def testKU : List Fmt.DeclaredRound := (declKeyFull.2.1.drop 8).take 35
def behindKU : List Fmt.DeclaredRound := declKeyFull.2.1.drop 43

/-- aloneB in written letters. -/
def aloneKU (k : ℕ) : Bool :=
  (openedOf 0 declKeyFull.1 ++ openedOf 1 frontKU ++ openedOf 1 behindKU ++
    openedOf 2 declKeyFull.2.2).all (·.1 != (1, k))

set_option maxRecDepth 1000000 in
theorem roots_KU : rootsOf frontKU = 3 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_KU : opensFitB false piKUFull.nums.stages testKU [24, 13] srcsU 3 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem far_KU : (none :: depths false piKUFull.nums.stages).length ≤ firstLen piKUFull.nums.stages + 40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem alone_KU : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf false piKUFull.nums.stages (firstLen piKUFull.nums.stages + i)).isSome ||
      aloneKU (3 + ((List.range (firstLen piKUFull.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf false piKUFull.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The tests can say no: at a tree that the test on G_omega opens, and with one argument of opens_KU turned. -/
theorem no_KU : (aloneKU 2, opensFitB false piKUFull.nums.stages testKU [24, 12] srcsU 3,
    opensFitB false piKUFull.nums.stages testKU [24, 13] srcsU 4) = (false, false, false) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rows_KU : ∀ r ∈ AtPublicFiles.KeyBook.fullShared, r.1 = ⟨2, none, 9, .K12⟩ → r.2 = 35 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem start_KU : AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullShared ⟨2, none, 9, .K12⟩ = some 8 := by decide +kernel

theorem cut_lists {α : Type} (A B C D : List α) (e : A ++ (B ++ C) = D) :
    A = D.take A.length ∧ C = D.drop (A.length + B.length) ∧ B = (D.drop A.length).take B.length := by
  subst e
  refine ⟨(List.take_left' rfl).symm, ?_, ?_⟩
  · rw [← List.drop_drop, List.drop_left' rfl, List.drop_left' rfl]
  · rw [List.drop_left' rfl, List.take_left' rfl]

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

local notation "𝔽" => keyFileDescription Xs N Pl

/-- **At a cut at the test's place the rounds are the written ones.** -/
theorem cut_KU (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₂ (𝔽).Cl)} {b : Block (𝔽).S₂ (𝔽).Cl}
    (hcut : (𝔽).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨2, none, 9, .K12⟩) :
    pre.flatMap (·.rounds) = frontKU ∧ t.flatMap (·.rounds) = behindKU ∧ b.rounds = testKU := by
  have hd : (𝔽).shared.blocksInOrder.flatMap (·.rounds) = declKeyFull.2.1 :=
    congrArg (fun D => D.2.1) (keyDecl_of_named scope h)
  have hl₁ : (pre.flatMap (·.rounds)).length = 8 := by
    have e := OnBytes.M1.front_shared scope h hcut
    rw [hb, start_KU] at e
    exact (Option.some.inj e).symm
  have hl₂ : b.rounds.length = 35 := by
    have hm : (b.place, b.rounds.length) ∈ AtPublicFiles.KeyBook.fullShared := by
      rw [← (AtPublicFiles.KeyBook.places_named scope h).2.1, hcut]
      exact List.mem_map.2 ⟨b, by simp, rfl⟩
    exact rows_KU _ hm hb
  rw [hcut, List.flatMap_append, List.flatMap_cons] at hd
  obtain ⟨e1, e2, e3⟩ := cut_lists _ _ _ _ hd
  rw [hl₁] at e1
  rw [hl₁, hl₂] at e2 e3
  exact ⟨e1, e2, e3⟩

theorem alone_is_KU (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₂ (𝔽).Cl)} {b : Block (𝔽).S₂ (𝔽).Cl}
    (hcut : (𝔽).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨2, none, 9, .K12⟩) (k : ℕ) :
    aloneB (𝔽) pre t k = aloneKU k := by
  obtain ⟨e1, e2, -⟩ := cut_KU scope h hcut hb
  unfold aloneB aloneKU
  rw [keyDecl_of_named scope h, e1, e2]

/-- **The three named premises, at the key file.** -/
theorem premises_at_KU (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {W X : Type}
    (J : TestJob W X) (hst : J.p.nums.stages = piKUFull.nums.stages) (hfr : J.fresh.isNone = false)
    {pre t : List (Block (𝔽).S₂ (𝔽).Cl)} {b : Block (𝔽).S₂ (𝔽).Cl}
    (hcut : (𝔽).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨2, none, 9, .K12⟩) :
    OpensFit J b.rounds [24, 13] (fun k => srcsU.getD k (.own 0)) (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ k, k < [24, 13].length → ∀ n,
        ProofFile.Honest.srcOf 1 ((fun k => srcsU.getD k (.own 0)) k) = (1, n) →
        n < rootsOf (pre.flatMap (·.rounds))) ∧
      ∀ i, (ProofFile.Honest.K12.depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        aloneB (𝔽) pre t (rootsOf (pre.flatMap (·.rounds)) +
          sentBefore J (firstLen J.p.nums.stages + i)) = true := by
  obtain ⟨e1, -, e3⟩ := cut_KU scope h hcut hb
  have h3 : rootsOf (pre.flatMap (·.rounds)) = 3 := by
    rw [e1]
    exact roots_KU
  have hdep : ∀ r, ProofFile.Honest.K12.depthAt J r = ProofFile.Honest.K12.depthOf false piKUFull.nums.stages r := fun r => by
    unfold ProofFile.Honest.K12.depthAt ProofFile.Honest.K12.depthOf
    rw [hfr, hst]
  rw [h3]
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · rw [e3, hfr, hst]
    exact opens_KU
  · intro j hj n hn
    match j, hj, hn with
    | 0, _, hn =>
      have e : (0 : ℕ) = n := congrArg Prod.snd hn
      omega
    | 1, _, hn =>
      have e : (2 : ℕ) = n := congrArg Prod.snd hn
      omega
  · intro i hi
    rw [alone_is_KU scope h hcut hb]
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen piKUFull.nums.stages + i) =
        ((List.range (firstLen piKUFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf false piKUFull.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    by_cases hlt : i < 40
    · have hh := List.all_eq_true.1 alone_KU i (List.mem_range.2 hlt)
      rw [hi] at hh
      simpa using hh
    · exfalso
      have hf := far_KU
      have hn : ProofFile.Honest.K12.depthOf false piKUFull.nums.stages
          (firstLen piKUFull.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn] at hi
      cases hi

local instance keyBudUInstance1 (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) := ⟨(default, default)⟩
local instance keyBudUInstance2 (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **THE TEST'S ROW OWES NOTHING MORE TO bud₂, AT THE KEY FILE.** -/
theorem budOwed₂_at_KU (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₂ (𝔽).Cl V W Y Pb) (J : TestJob W Y) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (hst : J.p.nums.stages = piKUFull.nums.stages) (hplace : J.p.place = ⟨2, none, 9, .K12⟩)
    {b₀ : Block (𝔽).S₂ (𝔽).Cl} (hf₀ : ((𝔽).shared.blocksInOrder.find? fun b => b.place == J.p.place) = some b₀)
    (hpl₀ : b₀.place = J.p.place) (hr₀ : b₀.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor₀ : b₀.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = J.p)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due (𝔽) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (𝔽) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' : testSide (𝔽).shared.blocksInOrder J Js [] = some σ := by
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
    have hblk : σ.block ∈ (𝔽).shared.blocksInOrder := by
      rw [hcut]
      exact List.mem_append_right _ List.mem_cons_self
    have hsh : σ.block.shaped = true := planOk_shaped h.plan σ.block hblk
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hsh, Nat.min_self]
    have hT : tablesFitB J = true := by
      rw [tablesFitB_eq, hfrN]
      exact Fc.tab
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped h.plan x (by rw [hcut]; exact List.mem_append_left _ hx))
      hzip hT Fc.enough
    rw [← hcut] at hN
    obtain ⟨O, hold, ha⟩ := premises_at_KU scope h J hst hfrN hcut (by rw [eb, hpl₀, hplace])
    have hB := bud_rest_file (V := V) J Js pre t σ.block hcut [24, 13] _ _ O s
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

#print axioms OnBytes.M1.KeyBud.roots_KU
#print axioms OnBytes.M1.KeyBud.opens_KU
#print axioms OnBytes.M1.KeyBud.alone_KU
#print axioms OnBytes.M1.KeyBud.no_KU
#print axioms OnBytes.M1.KeyBud.cut_KU
#print axioms OnBytes.M1.KeyBud.premises_at_KU
#print axioms OnBytes.M1.KeyBud.budOwed₂_at_KU
