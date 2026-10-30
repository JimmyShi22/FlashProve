-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: what the row of the own test owes to BudDebts.
/-
Johnson/M1/KeyBudW.lean: the field bud₃ of BudDebts at a list that stands at the proximity test on the own group of the key file's last chain, at every due list of
challenges: the key file's twin of budOwed₃_at_W. Premises as at Johnson/M1/KeyBudU.lean.
No property of the protocol is claimed here.
-/
import Johnson.M1.KeyBudU
import Johnson.M1.KeyBudLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1.KeyBud
open VerifiableInference.Desc (FileDescription Block Place)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.KeyLast (aloneInLastChain bound_rest_last_chain)
open H2K.Pub (sgOf)
open H2K.Member (piKWFull)
open Johnson.G.OfPlan (rootsOf)
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open OnBytes.M1 (keyDecl_of_named cut_front)

def depthsKW : List ℕ := [13, 22, 22]
def srcsKW : List Fmt.TreeSource := [.taken 0 0, .taken 0 5, .taken 1 1]

set_option maxRecDepth 1000000 in
theorem written_aloneK : (openedOf 0 declKeyFull.1 ++ openedOf 1 declKeyFull.2.1).all (fun e => e.1.1 != 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: the test opens the last chain's trees. -/
theorem written_aloneK_bites : (openedOf 2 declKeyFull.2.2).any (fun e => e.1.1 == 2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_KW : opensFitB false piKWFull.nums.stages declKeyFull.2.2 depthsKW srcsKW 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem no_KW : (opensFitB false piKWFull.nums.stages declKeyFull.2.2 [13, 22, 21] srcsKW 0,
    opensFitB false piKWFull.nums.stages declKeyFull.2.2 depthsKW [.taken 0 1, .taken 0 5, .taken 1 1] 0) = (false, false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem second_places_apart : (AtPublicFiles.KeyBook.fullSecond.map (·.1)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
theorem start_KW : AtPublicFiles.KeyBook.startIn AtPublicFiles.KeyBook.fullSecond ⟨3, none, 2, .K12⟩ = some 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rows_KW : ∀ r ∈ AtPublicFiles.KeyBook.fullSecond, r.1 = ⟨3, none, 2, .K12⟩ → r.2 = declKeyFull.2.2.length := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

local notation "𝔽" => keyFileDescription Xs N Pl

theorem second_apart (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    ((𝔽).second.blocksInOrder.map (·.place)).Nodup := by
  have e : (𝔽).second.blocksInOrder.map (·.place) = AtPublicFiles.KeyBook.fullSecond.map (·.1) := by
    rw [← (AtPublicFiles.KeyBook.places_named scope h).2.2]
    unfold Johnson.RunOne.Sound.rowsOf
    rw [List.map_map]
    rfl
  rw [e]
  exact second_places_apart

/-- At a cut at the test's place: no round in front, none behind, and the block's rounds are the chain's. -/
theorem cut_KW (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl)
    {pre t : List (Block (𝔽).S₃ (𝔽).Cl)} {b : Block (𝔽).S₃ (𝔽).Cl}
    (hcut : (𝔽).second.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨3, none, 2, .K12⟩) :
    pre.flatMap (·.rounds) = [] ∧ t.flatMap (·.rounds) = [] ∧ b.rounds = declKeyFull.2.2 := by
  have hd : (𝔽).second.blocksInOrder.flatMap (·.rounds) = declKeyFull.2.2 :=
    congrArg (fun D => D.2.2) (keyDecl_of_named scope h)
  have hl₁ : (pre.flatMap (·.rounds)).length = 0 := by
    have hn := second_apart scope h
    rw [hcut, List.map_append, List.map_cons] at hn
    have hp : ∀ c ∈ pre, c.place ≠ b.place := fun c hc e =>
      (List.nodup_append.1 hn).2.2 _ (List.mem_map_of_mem hc) _ (List.mem_cons_self ..) e
    have e := cut_front pre b t hp
    rw [← hcut, AtPublicFiles.KeyBook.start_named₃ scope h, hb, start_KW] at e
    exact (Option.some.inj e).symm
  have hl₂ : b.rounds.length = declKeyFull.2.2.length := by
    have hm : (b.place, b.rounds.length) ∈ AtPublicFiles.KeyBook.fullSecond := by
      rw [← (AtPublicFiles.KeyBook.places_named scope h).2.2, hcut]
      exact List.mem_map.2 ⟨b, by simp, rfl⟩
    exact rows_KW _ hm hb
  rw [hcut, List.flatMap_append, List.flatMap_cons] at hd
  have e0 := List.eq_nil_of_length_eq_zero hl₁
  rw [e0, List.nil_append] at hd
  have ht : (t.flatMap (·.rounds)).length = 0 := by
    have := congrArg List.length hd
    rw [List.length_append, hl₂] at this
    omega
  have et := List.eq_nil_of_length_eq_zero ht
  rw [et, List.append_nil] at hd
  exact ⟨e0, et, hd⟩

/-- **The public premises, at the key file.** -/
theorem premises_at_KW (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {W Y : Type} (J : TestJob W Y)
    (hst : J.p.nums.stages = piKWFull.nums.stages) (hfr : J.fresh.isNone = false)
    {pre t : List (Block (𝔽).S₃ (𝔽).Cl)} {b : Block (𝔽).S₃ (𝔽).Cl}
    (hcut : (𝔽).second.blocksInOrder = pre ++ b :: t) (hb : b.place = ⟨3, none, 2, .K12⟩) :
    OpensFit J b.rounds depthsKW (fun k => srcsKW.getD k (.own 0)) (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ k, k < depthsKW.length → ∀ n,
        ProofFile.Honest.srcOf 2 ((fun k => srcsKW.getD k (.own 0)) k) = (2, n) →
        n < rootsOf (pre.flatMap (·.rounds))) ∧
      ∀ k, aloneInLastChain (𝔽) pre t k = true := by
  obtain ⟨e1, e2, e3⟩ := cut_KW scope h hcut hb
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · rw [e3, e1, hfr, hst]
    exact opens_KW
  · intro j hj n hn
    match j, hj, hn with
    | 0, _, hn => simp [srcsKW, ProofFile.Honest.srcOf] at hn
    | 1, _, hn => simp [srcsKW, ProofFile.Honest.srcOf] at hn
    | 2, _, hn => simp [srcsKW, ProofFile.Honest.srcOf] at hn
  · intro k
    unfold aloneInLastChain
    rw [e1, e2, keyDecl_of_named scope h]
    have e0 : openedOf 2 ([] : List Fmt.DeclaredRound) = [] := rfl
    rw [e0, List.append_nil, List.append_nil]
    refine List.all_eq_true.2 fun e he => ?_
    have ha := List.all_eq_true.1 written_aloneK e he
    refine bne_iff_ne.2 fun hE => ?_
    rw [hE] at ha
    simp at ha

local instance keyBudWInstance1 (d : Due) (l : List (String × Due)) : Nonempty (Cs d × CsAll l) := ⟨(default, default)⟩
local instance keyBudWInstance2 (d : Due) : Nonempty (Cs d) := ⟨default⟩

/-- **THE OWN TEST's ROW OWES NOTHING MORE TO bud₃, AT THE KEY FILE.** -/
theorem budOwed₃_at_KW (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₃ (𝔽).Cl V W Y Pb) (J : TestJob W Y) {ds : List Fmt.Drawn} (Fc : PlaceFacts J.p ds)
    (hst : J.p.nums.stages = piKWFull.nums.stages) (hplace : J.p.place = ⟨3, none, 2, .K12⟩)
    {b₀ : Block (𝔽).S₃ (𝔽).Cl} (hf₀ : ((𝔽).second.blocksInOrder.find? fun b => b.place == J.p.place) = some b₀)
    (hpl₀ : b₀.place = J.p.place) (hr₀ : b₀.rounds = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds)
    (hor₀ : b₀.oracles = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = J.p)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due (𝔽) = true →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks (𝔽) ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).second.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' : testSide (𝔽).second.blocksInOrder J Js [] = some σ := by
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
    have hblk : σ.block ∈ (𝔽).second.blocksInOrder := by
      rw [hcut]
      exact List.mem_append_right _ List.mem_cons_self
    have hsh : σ.block.shaped = true := planOk_shaped_second h.plan σ.block hblk
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hsh, Nat.min_self]
    have hT : tablesFitB J = true := by
      rw [tablesFitB_eq, hfrN]
      exact Fc.tab
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped_second h.plan x (by rw [hcut]; exact List.mem_append_left _ hx))
      hzip hT Fc.enough
    rw [← hcut] at hN
    obtain ⟨O, hold, ha⟩ := premises_at_KW scope h J hst hfrN hcut (by rw [eb, hpl₀, hplace])
    have hB := bound_rest_last_chain (V := V) J Js pre t σ.block hcut depthsKW _ _ O s
      next rest hst' hk hT hold hlen Fc.enough ρ hρ (fun i _ => ha _)
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

#print axioms OnBytes.M1.KeyBud.opens_KW
#print axioms OnBytes.M1.KeyBud.cut_KW
#print axioms OnBytes.M1.KeyBud.premises_at_KW
#print axioms OnBytes.M1.KeyBud.budOwed₃_at_KW
