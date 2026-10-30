-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15A.lean: THE FACTS ON THE DESCRIPTION AND THE PLAN THAT ROW 1.15 OF THE KEY FILE's TABLES WANTS (the fields of kind II of Left15J, Johnson/RunOne/Law/K12Left15J.lean), EACH AS A THEOREM, GENERAL IN X N P: no numeral of a size is read. Statements with proofs. IT PAYS NO FIELD OF THE TABLES: NO MEMBER OF Left15J IS SHOWN HERE.
OBJECT. Key.descriptionFromSource X N P; its first chain's proximity test (the ranges' test) and that test's place rangesParams N; the maker's 15th piece's base and stretch.
USER. Johnson/RunOne/Law/K12Facts15B.lean (a member of Left15J from these).
LETTERS. m X N P D file c₁ k₁: free. Premises by name: hp: the description's test on the plan says yes · hD: its data are D · hX: the source is made of m · hN: the place's numbers are made of m · q₁: the first chain's flat list is c₁ :: k₁ · hl: the plan has two lookups. All but q₁ and hl are parts of the yes of Key.keyDataAndDecisionAtFixedDigest (Johnson/Desc/Key/SlotIs.lean: laidFixed_is).

  plan_of: the description's test on the plan holds the ranges' test's own. (Another file has the same statement, compiled, over a heavier cone: rng_planOk, Johnson/RunOne/KeySmpStay.lean. This one stands over the chain's list alone.)
  written_of_plan, batOne_of_plan: the place's declared rounds can be written; "BAT" draws one element: two calls each of the kind's files' theorems (Johnson/Desc/K12/Law/BatOneMade.lean).
  nums_of_early: where the place's parameters say "the masks come early" they are the place's numbers' own.
  numbers_parts: what the routine that makes the place's numbers lays: read off its text.
  arm_of: the first fold sends no mask of its own.
  flat_last, behind_ne: the blocks behind the test declare a round: the chain's last block does, by the description's test on the plan.
  not_last: the test is not the chain's last block.
  kind_rounds_ne: the kind's block declares a round.
  stretch_ne: the maker's 15th stretch is not empty.
  trees_take, base_is: GENERAL IN THE DESCRIPTION: the base of the maker's n-th piece of the first chain is the number of roots that the blocks in front declare.
  labels_of: each opening that the first switch declares is one of the chain's own trees, its label is its number, and it lies below every base from the place's first free number on.
  foldl_add, entries_are, free_of_start: the place's first free own number is the number of roots that the 15 blocks in front declare, UNDER ONE EQUATION ON A NUMBER (hs): the plan's first round named as the batching's is the test's own first round.
Limits. hs is shown here of no plan. Nothing on the radii, nothing on errors. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12AtPlaceRow
import Johnson.RunOne.Law.K12AtField
import Johnson.RunOne.Law.PlanPays
import Johnson.Desc.K12.Law.BatOneMade
import Johnson.Desc.K12.Law.MasksPlan
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.K12.FrameLaws
import Johnson.Desc.Sound.DataRounds
import Johnson.Desc.RunLaws
import Johnson.Desc.Key.Desc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (LabelsPub nlAt)
open VerifiableInference.Desc.Key
open H2K.Pub (writtenOf WR)
open H2K.First (batOneOk opensOf)
open Johnson.G.OfPlan (rootsOf Made ownAt onceOpens)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.Law.RoundsInFront
open LPFD (before cutBase cutDs cutDs_inner cutBase_eq)

/-! ## 1 On the place alone -/

section
variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ} {N : H2U.PlaceNums}

/-- (written) The place's declared rounds can be written. -/
theorem written_of_plan (h : (rangesTest laid back N : Block σ Cl).planOk = true) :
    ∃ w0 l, writtenOf (rangesParams N).nums = some (w0 :: l) :=
  H2K.Made.written_of_planOk guardedProximityTestParts (rangesParams N) (PlanPays.rng_pays h).2.2.1

/-- (batOne) "BAT" draws one element and nothing else. -/
theorem batOne_of_plan (h : (rangesTest laid back N : Block σ Cl).planOk = true) :
    batOneOk (rangesParams N) = true :=
  H2K.Made.batOneOk_of_planOk guardedProximityTestParts (rangesParams N) (PlanPays.rng_pays h).2.2.1

end

/-- Where the parameters say "the masks come early" they are made of the place's numbers: the stand-in for a place that cannot be made says "late". -/
theorem nums_of_early (N : H2U.PlaceNums) (h : (rangesParams N).early = true) :
    (rangesParams N).nums = N.nums ∧ N.early = true := by
  unfold rangesParams H2U.proximityTestParametersAt at h ⊢
  by_cases hc : (rangesPlace.chain != N.chain) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h ⊢
    cases ho : H2U.testOracles5 N.nums N.firstGroup with
    | none =>
      try rw [ho] at h
      cases h
    | some os =>
      try rw [ho] at h
      try rw [ho]
      exact ⟨rfl, h⟩

/-- **What the routine that makes the place's numbers lays.** -/
theorem numbers_parts {m : Made} {N : H2U.PlaceNums} (hN : rangesNumbers m = .ok N) :
    N.nums.ownMask = !N.early ∧ N.nums.firstTree = 0 ∧
      (∀ o ∈ N.nums.first, ∃ n, o.2 = Fmt.TreeSource.own n ∧ o.1.tree = n) ∧
      (H2U.batPlaces m.p.chains.key.oneTime.given.plan.rounds).head? = some N.start ∧
      N.nums.free =
        ((m.p.chains.key.oneTime.given.plan.rounds.take N.start).map (·.roots)).foldl (· + ·) 0 ∧
      N.nums.stages = m.p.chains.made.sized.key.ranges.test.stages.map H2U.stageNums := by
  unfold rangesNumbers at hN
  dsimp only at hN
  obtain ⟨ts, _, hN⟩ := exc_bind hN
  obtain ⟨first, hfirst, hN⟩ := exc_bind hN
  have e := Except.ok.inj (show (Except.ok _ : Except String _) = Except.ok first from hfirst)
  cases hb : (H2U.batPlaces m.p.chains.key.oneTime.given.plan.rounds).head? with
  | none =>
    try rw [hb] at hN
    obtain ⟨_, e', _⟩ := exc_bind hN
    cases e'
  | some i =>
    try rw [hb] at hN
    obtain ⟨y, hy, hN⟩ := exc_bind hN
    obtain rfl : i = y := Except.ok.inj hy
    split at hN
    · obtain ⟨_, _, hN⟩ := exc_bind hN
      obtain rfl : _ = N := Except.ok.inj hN
      refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
      intro o ho
      have ho' : o ∈ first := ho
      rw [← e] at ho'
      obtain ⟨t, _, rfl⟩ := List.mem_map.1 ho'
      exact ⟨t.2, rfl, Nat.zero_add _⟩
    · obtain ⟨_, e', _⟩ := exc_bind hN
      cases e'

section
variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
  {m : Made} {N : H2U.PlaceNums}

/-- (arm) The first fold's mask came earlier. -/
theorem arm_of (hN : rangesNumbers m = .ok N) (h : (rangesTest laid back N : Block σ Cl).planOk = true) :
    (rangesParams N).nums.ownMask = false := by
  obtain ⟨hn, he⟩ := nums_of_early N (PlanPays.rng_pays h).1
  rw [hn, (numbers_parts hN).1, he]
  rfl

/-- (labels) **Each opening that the first switch declares is one of the chain's own trees; its label is its number; it lies below every base from the place's first free number on.** -/
theorem labels_of (hN : rangesNumbers m = .ok N) (h : (rangesTest laid back N : Block σ Cl).planOk = true)
    (t₁ t₂ base : ℕ) (hb : (rangesParams N).nums.free ≤ base) :
    LabelsPub (rangesParams N) (numAt t₁ t₂ 0) (nlAt (rangesParams N) 0) base := by
  have ho := arm_of hN h
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays h).1
  obtain ⟨_, hft, hfirst, _, _⟩ := numbers_parts hN
  have M := H2K.Made.masksFixed_of_planOk (rangesParams N) (PlanPays.rng_pays h).2.2.1
  obtain ⟨a', b, rest', w0, w, hs', _, _, hop⟩ := M.made
  intro a rest hs o hmem
  have ea : a' = a := (List.cons.inj (hs'.symm.trans hs)).1
  subst ea
  have hT : H2K.Made.ownTold (rangesParams N).nums = [] := by
    unfold H2K.Made.ownTold
    rw [ho]
    rfl
  rw [hop, hT, List.append_nil] at hmem
  have hfr := M.front o hmem
  obtain ⟨n, e2, e1⟩ := hfirst o (hn ▸ hmem)
  have hft' : (rangesParams N).nums.firstTree = 0 := by rw [hn]; exact hft
  rcases hfr with hf | ⟨h1, _⟩
  · rw [e2] at hf ⊢
    have hlt : n < (rangesParams N).nums.free := (show n < _ ∧ _ from hf).1
    refine ⟨?_, ?_⟩
    · show 0 + n = 0 + (o.1.tree - (rangesParams N).nums.firstTree)
      rw [e1, hft']
      omega
    · show 0 + n < base
      omega
  · rw [ho] at h1
    cases h1

end

/-! ## 2 On the chain's list -/

/-- A chain's flat list ends in its last block, as to the declared rounds. -/
theorem flat_last {S Cl : Type} (c : Chain S Cl) :
    ∃ (A : List (Block S Cl)) (e : Block S Cl), c.blocksInOrder = A ++ [e] ∧ e.rounds = c.last.rounds := by
  unfold Chain.blocksInOrder
  exact ⟨_, _, rfl, rfl⟩

section
variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
  (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))

/-- (plan) The description's test on the plan holds the ranges' test's own. -/
theorem plan_of (hp : (Key.descriptionFromSource X N P).planOk = true) :
    (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true := by
  have hb : (Key.descriptionFromSource X N P).first.blocksInOrder[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 1]? =
      some (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim)) :=
    Johnson.RunOne.Sound.fk_rng_at X N P
  have h1 := ((((Key.descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? hb)).1
  have h2 : ((rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk &&
      (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).hasNoClaimsAndNothingAfter) = true := h1
  exact (Bool.and_eq_true_iff.1 h2).1

/-- A block stands at the number 16. -/
theorem sixteen_lt (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) : 16 < (c₁ :: k₁).length := by
  have h : ((Key.descriptionFromSource X N P).first.blocksInOrder[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 2]?).isSome = true := by
    have e : (Key.descriptionFromSource X N P).first.blocksInOrder[2 + 6 * (Key.lookupsOf X.Y.k.oneTime).length + 2]? =
        (Johnson.RunOne.Sound.fkTail X N)[2]? := Johnson.RunOne.Sound.fk_back_at X N P 2
    rw [e]
    rfl
  rw [hl, q₁] at h
  by_contra hge
  have e0 : (c₁ :: k₁)[2 + 6 * 2 + 2]? = none := List.getElem?_eq_none (by omega)
  rw [e0] at h
  cases h

/-- The test is not the chain's last block. -/
theorem not_last (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) : 15 < k₁.length := by
  have h := sixteen_lt X N P c₁ k₁ q₁ hl
  rw [List.length_cons] at h
  omega

/-- (behind) **The blocks behind the test declare a round.** -/
theorem behind_ne (hp : (Key.descriptionFromSource X N P).planOk = true) (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) :
    ((c₁ :: k₁).drop 16).flatMap (·.rounds) ≠ [] := by
  have hs : (Key.descriptionFromSource X N P).first.last.rounds ≠ [] := by
    have h := (((Key.descriptionFromSource X N P).planOk_ok).1 hp).sealLast
    unfold FileDescription.sealLast at h
    intro h0
    rw [h0] at h
    cases h
  obtain ⟨A, e, hA, he⟩ := flat_last (Key.descriptionFromSource X N P).first
  have h16 := sixteen_lt X N P c₁ k₁ q₁ hl
  rw [← q₁, hA] at h16 ⊢
  have hle : 16 ≤ A.length := by
    rw [List.length_append, List.length_singleton] at h16
    omega
  intro h0
  rw [List.drop_append_of_le_length hle, List.flatMap_append] at h0
  have h1 := (List.append_eq_nil_iff.1 h0).2
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil] at h1
  exact hs (he ▸ h1)

end

/-- The kind's block declares a round. -/
theorem kind_rounds_ne (π : P12) (h : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) :
    (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds ≠ [] := by
  obtain ⟨_, _, _, R, _, _, e⟩ := H2K.Made.rounds_top π.nums _ (VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts π h)
  rw [e]
  exact List.cons_ne_nil _ _

/-! ## 3 On the data -/

/-- Round by round as many trees as roots: so the sums over the first k. -/
theorem trees_take : ∀ (ds : List RDT) (l : List Fmt.DeclaredRound), List.Forall₂ RoundAsG ds l →
    ∀ k, nTrees (ds.take k) = rootsOf (l.take k)
  | _, _, .nil, k => by simp [nTrees, rootsOf]
  | _, _, .cons _ _, 0 => by simp [nTrees, rootsOf]
  | _, _, .cons h t, k + 1 => by
    have ih := trees_take _ _ t k
    unfold nTrees rootsOf at ih ⊢
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, h.2.2.2.1, ih]

section
variable {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD) (h : F.data file = .ok D)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (hf : F.first.blocksInOrder = c₁ :: k₁) (n : ℕ)
  (b : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some b) (hn : n < k₁.length)
  (hne : ((c₁ :: k₁).drop (n + 1)).flatMap (·.rounds) ≠ [])
include h hf hb hne

/-- The data's rounds reach over the n-th block's. -/
theorem data_reach : (((c₁ :: k₁).take n).flatMap (·.rounds)).length + b.rounds.length ≤ D.ds₁.length := by
  have hl : D.ds₁.length = F.roundsDeclaredByBlocks.1.dropLast.length := (roundsOfData F file D h).1.length_eq
  have e : F.roundsDeclaredByBlocks.1 = ((c₁ :: k₁).take n).flatMap (·.rounds) ++
      (b.rounds ++ ((c₁ :: k₁).drop (n + 1)).flatMap (·.rounds)) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [hf, rounds_part (c₁ :: k₁) n b hb]
  have hpos : 0 < (((c₁ :: k₁).drop (n + 1)).flatMap (·.rounds)).length := List.length_pos_iff.2 hne
  rw [hl, List.length_dropLast, e, List.length_append, List.length_append]
  omega

include hn

/-- **The base of the maker's n-th piece of the first chain is the number of roots that the blocks in front declare.** -/
theorem base_is : cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n =
    rootsOf (((c₁ :: k₁).take n).flatMap (·.rounds)) := by
  have hn' : n ≤ (k₁.map (held (P := F.XiPub))).length := by rw [List.length_map]; omega
  have hr := data_reach F file D h c₁ k₁ hf n b hb hne
  have hl : D.ds₁.length = F.roundsDeclaredByBlocks.1.dropLast.length := (roundsOfData F file D h).1.length_eq
  rw [cutBase_eq (k₁.map (held (P := F.XiPub))) n 0 D.ds₁ (held c₁) hn', K12AtPlaceRow.before_held,
    Nat.zero_add, trees_take _ _ (roundsOfData F file D h).1]
  congr 1
  have e2 := rounds_take (c₁ :: k₁) n
  rw [← length_inFront] at e2
  have e1 : F.roundsDeclaredByBlocks.1 = (c₁ :: k₁).flatMap (·.rounds) := by
    show F.first.blocksInOrder.flatMap (·.rounds) = _
    rw [hf]
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left (by rw [← List.length_dropLast, ← hl]; omega), e1]
  exact e2.symm

/-- The maker's n-th stretch is not empty where the n-th block declares a round. -/
theorem stretch_ne_of (hpos : b.rounds ≠ []) :
    cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n ≠ [] := by
  have hr := data_reach F file D h c₁ k₁ hf n b hb hne
  have hb' : ((held c₁ : Block (F.XiPub × F.S₁) F.Cl) :: k₁.map held)[n]? = some (held b) := by
    have : ((c₁ :: k₁).map (held (P := F.XiPub)))[n]? = some (held b) := by
      rw [List.getElem?_map, hb]; rfl
    exact this
  have hn' : n < (k₁.map (held (P := F.XiPub))).length := by rw [List.length_map]; exact hn
  have ed := cutDs_inner (k₁.map (held (P := F.XiPub))) n D.ds₁ (held c₁) (held b) hn' hb'
  rw [K12AtPlaceRow.before_held] at ed
  rw [ed]
  have hp : 0 < b.rounds.length := List.length_pos_iff.2 hpos
  intro h0
  have h1 := congrArg List.length h0
  rw [List.length_take, List.length_drop, List.length_nil] at h1
  have h2 : (held (P := F.XiPub) b).rounds.length = b.rounds.length := rfl
  rw [h2] at h1
  omega

end

section
variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
  (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))
  (file : String) (D : WholeD)

/-- (stretch) **The maker's 15th stretch is not empty.** -/
theorem stretch_ne (hD : (Key.descriptionFromSource X N P).data file = .ok D) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) :
    cutDs D.ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 ≠ [] := by
  refine stretch_ne_of (Key.descriptionFromSource X N P) file D hD c₁ k₁ q₁ 15 _ (K12AtField.rng_at_15 X N P c₁ k₁ q₁ hl)
    (not_last X N P c₁ k₁ q₁ hl) (behind_ne X N P c₁ k₁ hp q₁ hl) ?_
  have hr : (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim)).rounds =
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).rounds :=
    (RngAnyCl.same_k12 (A := Key.Claim) (B := Unit) guardedProximityTestParts (rangesParams N)).rounds
  rw [hr]
  exact kind_rounds_ne _ (PlanPays.rng_pays (plan_of X N P hp)).2.2.1

/-- The base of the maker's 15th piece. -/
theorem base_15 (hD : (Key.descriptionFromSource X N P).data file = .ok D) (hp : (Key.descriptionFromSource X N P).planOk = true)
    (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁) (hl : (Key.lookupsOf X.Y.k.oneTime).length = 2) :
    cutBase 0 D.ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15 =
      rootsOf (((c₁ :: k₁).take 15).flatMap (·.rounds)) :=
  base_is (Key.descriptionFromSource X N P) file D hD c₁ k₁ q₁ 15 _ (K12AtField.rng_at_15 X N P c₁ k₁ q₁ hl)
    (not_last X N P c₁ k₁ q₁ hl) (behind_ne X N P c₁ k₁ hp q₁ hl)

end

/-! ## 4 The place's first free own number -/

theorem foldl_add (l : List ℕ) : ∀ a, l.foldl (· + ·) a = a + l.sum := by
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, List.sum_cons, ih]
    omega

section
variable {m : Made} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

/-- **The rounds of the plan in the parameter bytes are the entries of the rounds that the first chain's blocks declare.** -/
theorem entries_are (hX : sourceOf m = .ok X) (hp : (Key.descriptionFromSource X N P).planOk = true) :
    m.p.chains.key.oneTime.given.plan.rounds = (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.1.map (·.entry) := by
  have Q := ((Key.descriptionFromSource X N P).planOk_ok).1 hp
  have hk : X.Y.k = m.p.chains.key := by
    unfold sourceOf at hX
    obtain ⟨D, _, hX⟩ := exc_bind hX
    obtain ⟨T, _, hX⟩ := exc_bind hX
    cases hX
    rfl
  have hf' : ((fileClauses X N P _ _ _).all (·.2) && _) = true := Q.fileOk
  rw [Bool.and_eq_true] at hf'
  have hc := hf'.1
  unfold fileClauses at hc
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
    decide_eq_true_eq] at hc
  obtain ⟨-, -, -, -, ⟨⟨hd, -⟩, -⟩, -⟩ := hc
  rw [Q.decl₁]
  show _ = X.Y.D.1.map (·.entry)
  rw [hd, hk]
  rfl

variable (c₁ : Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl) (k₁ : List (Block (Key.descriptionFromSource X N P).S₁ (Key.descriptionFromSource X N P).Cl))

/-- (free) **The place's first free own number is the number of roots that the 15 blocks in front declare**, where the plan's first round named as the batching's is the test's own first round (hs). -/
theorem free_of_start (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (q₁ : (Key.descriptionFromSource X N P).first.blocksInOrder = c₁ :: k₁)
    (hs : N.start = (((c₁ :: k₁).take 15).flatMap (·.rounds)).length) :
    (rangesParams N).nums.free = rootsOf (((c₁ :: k₁).take 15).flatMap (·.rounds)) := by
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays (plan_of X N P hp)).1
  obtain ⟨_, _, _, _, hfree, _⟩ := numbers_parts hN
  have e1 : (Key.descriptionFromSource X N P).roundsDeclaredByBlocks.1 = (c₁ :: k₁).flatMap (·.rounds) := by
    show (Key.descriptionFromSource X N P).first.blocksInOrder.flatMap (·.rounds) = _
    rw [q₁]
  have e2 := rounds_take (c₁ :: k₁) 15
  rw [← length_inFront] at e2
  rw [hn, hfree, entries_are hX hp, foldl_add, Nat.zero_add, hs, e1, ← List.map_take, ← e2, List.map_map]
  rfl

end

end Johnson.RunOne.Law.K12Facts15

#print axioms Johnson.RunOne.Law.K12Facts15.written_of_plan
#print axioms Johnson.RunOne.Law.K12Facts15.batOne_of_plan
#print axioms Johnson.RunOne.Law.K12Facts15.nums_of_early
#print axioms Johnson.RunOne.Law.K12Facts15.numbers_parts
#print axioms Johnson.RunOne.Law.K12Facts15.arm_of
#print axioms Johnson.RunOne.Law.K12Facts15.labels_of
#print axioms Johnson.RunOne.Law.K12Facts15.flat_last
#print axioms Johnson.RunOne.Law.K12Facts15.plan_of
#print axioms Johnson.RunOne.Law.K12Facts15.sixteen_lt
#print axioms Johnson.RunOne.Law.K12Facts15.not_last
#print axioms Johnson.RunOne.Law.K12Facts15.behind_ne
#print axioms Johnson.RunOne.Law.K12Facts15.kind_rounds_ne
#print axioms Johnson.RunOne.Law.K12Facts15.trees_take
#print axioms Johnson.RunOne.Law.K12Facts15.data_reach
#print axioms Johnson.RunOne.Law.K12Facts15.base_is
#print axioms Johnson.RunOne.Law.K12Facts15.stretch_ne_of
#print axioms Johnson.RunOne.Law.K12Facts15.stretch_ne
#print axioms Johnson.RunOne.Law.K12Facts15.base_15
#print axioms Johnson.RunOne.Law.K12Facts15.foldl_add
#print axioms Johnson.RunOne.Law.K12Facts15.entries_are
#print axioms Johnson.RunOne.Law.K12Facts15.free_of_start
