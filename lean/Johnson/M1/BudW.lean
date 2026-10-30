-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the row of the request's own proximity test owes to BudDebts, on the last chain.
/-
Johnson/M1/BudW.lean: the field bud₃ of BudDebts (Honest/Law/OwedRule.lean) at a list that stands at the test on the last chain, at every due
list of challenges: the first-chain form is Johnson/M1/BudTestL.lean, over K12/Sim2/StandL.lean; Sim/BudRestAtRun.lean has the
shared chain's. Here: the twins on the last chain, and the closed facts on the written rounds around the test. The bound at the row
is budBoth: containment in what the next round samples, not a count. No property of the protocol is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstAnyAtHeadW
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudRestAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactSide
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsAtSecond
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1.BudW
open VerifiableInference.Desc (FileDescription Block Place Chain)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K12.Light
open H2K.Pub (sgOf)
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP declProofFull)
open VerifiableInference.Desc (Alike₂ alike₂_rounds)
open Johnson.G.OfPlan (rootsOf)

variable {Xi : Type}

/-- No round of the file outside the sub-protocol between pre and t of the last list opens the last chain's tree number k. -/
def aloneInLastChain (F : FileDescription Xi) (pre t : List (Block F.S₃ F.Cl)) (k : ℕ) : Bool :=
  (openedOf 0 F.roundsDeclaredByBlocks.1 ++ openedOf 1 F.roundsDeclaredByBlocks.2.1 ++ openedOf 2 (pre.flatMap (·.rounds)) ++
    openedOf 2 (t.flatMap (·.rounds))).all (·.1 != (2, k))

/-- asks_in_block (ReadsInBlock.lean) at the last chain. -/
theorem asks_in_last_chain {F : FileDescription Xi} (pre t : List (Block F.S₃ F.Cl))
    (b : Block F.S₃ F.Cl) (hcut : F.second.blocksInOrder = pre ++ b :: t) (ρ : Draws)
    (hρ : ρ.due F = true) (k : ℕ) (ha : aloneInLastChain F pre t k = true) :
    ∀ x ∈ treeAsks F ρ 2 k, x ∈ ((readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none) b.rounds
      ((ρ.second.drop (pre.flatMap (·.rounds)).length).take b.rounds.length)).filter fun q =>
        q.src == some (2, k)).map (·.pos) := by
  intro x hx
  unfold treeAsks at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hq, hs⟩ := List.mem_filter.1 hq
  have hs' : q.src = some (2, k) := beq_iff_eq.1 hs
  have off : ∀ e ∈ openedOf 0 F.roundsDeclaredByBlocks.1 ++ openedOf 1 F.roundsDeclaredByBlocks.2.1 ++ openedOf 2 (pre.flatMap (·.rounds)) ++
      openedOf 2 (t.flatMap (·.rounds)), e.1 ≠ (2, k) := fun e he =>
    bne_iff_ne.1 (List.all_eq_true.1 ha e he)
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.second.blocksInOrder.flatMap (·.rounds)) ρ.second = true := hρ.1.2
  have hlen := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at hlen
  unfold allBare bareReads at hq
  rcases List.mem_append.1 hq with hq | hq
  · rcases List.mem_append.1 hq with hq | hq
    · exact absurd hs' (reads_off 0 0 _ _ _ _ (2, k) (fun e he => off e
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))) q hq)
    · exact absurd hs' (reads_off 1 0 _ _ _ _ (2, k) (fun e he => off e
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he)))) q hq)
  · have hq' : q ∈ readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none)
        (pre.flatMap (·.rounds) ++ (b.rounds ++ t.flatMap (·.rounds)))
        (ρ.second.take (pre.flatMap (·.rounds)).length ++
          ((ρ.second.drop (pre.flatMap (·.rounds)).length).take b.rounds.length ++
            (ρ.second.drop (pre.flatMap (·.rounds)).length).drop b.rounds.length)) := by
      rw [List.take_append_drop, List.take_append_drop, ← List.flatMap_cons,
        ← List.flatMap_append, ← hcut]
      exact hq
    rw [readsOf_append 2 F.lastChainFirstTreeNumber _ _ _ _ _ _ (by rw [List.length_take]; omega),
      readsOf_append 2 F.lastChainFirstTreeNumber _ _ _ _ _ _ (by rw [List.length_take, List.length_drop]; omega)] at hq'
    rcases List.mem_append.1 hq' with h | h
    · exact absurd hs' (reads_off 2 F.lastChainFirstTreeNumber _ _ _ _ (2, k) (fun e he => off e
                      (List.mem_append_left _ (List.mem_append_right _ he))) q h)
    · rcases List.mem_append.1 h with h | h
      · exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨h, hs⟩, rfl⟩
      · exact absurd hs' (reads_off 2 F.lastChainFirstTreeNumber _ _ _ _ (2, k) (fun e he => off e
                        (List.mem_append_right _ he)) q h)

/-- bud_rest_file (Sim/BudRestAtRun.lean) at the last chain. -/
theorem bound_rest_last_chain {V W Y Pb : Type} {F : FileDescription Xi} (J : TestJob W Y) (Js : SimJob Pb)
    (pre t : List (Block F.S₃ F.Cl)) (b : Block F.S₃ F.Cl)
    (hcut : F.second.blocksInOrder = pre ++ b :: t) (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource) (sent : ℕ)
    (O : OpensFit J b.rounds depths src₀ sent) (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: next :: rest)
    (hk : s.k = (sgOf s).h + (sgOf s).g) (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, srcOf 2 (src₀ k) = (2, n) → n < sent)
    (hlen : b.rounds.length = J.laid.length)
    (hen : firstLen J.p.nums.stages ≤ J.laid.length) (ρ : Draws) (hρ : ρ.due F = true)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneInLastChain F pre t (sent + sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    budOpened J.p.nums.stages 1
      ((ρ.second.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
        (restMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks F ρ 2) ((restMember (V := V) J Js).rounds.map (·.2.length))
        (sent + sentBefore J (firstLen J.p.nums.stages))) := by
  have hρ' := hρ
  unfold Draws.due at hρ'
  simp only [Bool.and_eq_true] at hρ'
  have h2 : drawsFit (F.second.blocksInOrder.flatMap (·.rounds)) ρ.second = true := hρ'.1.2
  have htot := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at htot
  have hrl : (restMember (V := V) J Js).rounds.length =
      b.rounds.length - firstLen J.p.nums.stages := by
    show (J.laid.drop (firstLen J.p.nums.stages)).length = _
    rw [List.length_drop, hlen]
  have hds : (ρ.second.drop ((pre.flatMap (·.rounds)).length + firstLen J.p.nums.stages)).take
      (restMember (V := V) J Js).rounds.length =
      (((ρ.second.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).drop
        (firstLen J.p.nums.stages)) := by
    rw [List.drop_take, List.drop_drop, hrl]
  have h1 : (((ρ.second.drop (pre.flatMap (·.rounds)).length).take b.rounds.length).take
      (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages := by
    rw [List.length_take, List.length_take, List.length_drop]
    omega
  rw [hds]
  refine bud_sub _ _ _ _ _ _ (bud_own_rest (V := V) J Js b.rounds depths src₀ sent 2 F.lastChainFirstTreeNumber O s next
    rest hst hk hT hold (fun _ _ => none) (fun _ => none) _ _ h1) fun i hi q hq => ?_
  rw [List.take_append_drop]
  have hil : i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hi
    omega
  have hroots : ∀ i, i < ((restMember (V := V) J Js).rounds.map (·.2.length)).length →
      ((restMember (V := V) J Js).rounds.map (·.2.length)).getD i 0 =
        if (depthAt J (firstLen J.p.nums.stages + i)).isSome = true then 1 else 0 :=
    fun i hi => roots_fit J hT _ i hi
  have hsome : (depthAt J (firstLen J.p.nums.stages + i)).isSome = true := by
    have h := hroots i hil
    by_contra hc
    rw [if_neg hc] at h
    omega
  rw [Nat.add_assoc, sent_sum J _ _ hroots i (Nat.le_of_lt hil)] at hq ⊢
  exact asks_in_last_chain pre t b hcut ρ hρ _ (ha i hsome) q hq

/-! ## The written rounds around the test: closed facts by Lean's kernel -/

/-- The test's place on the last chain, as the description seats it. -/
def placeOwn : Place := ⟨3, none, 2, .K12⟩

/-- The written rounds in front of the test on the last chain, and those behind it. -/
def roundsFrontW : List Fmt.DeclaredRound := (WP.second.blocksInOrder.take 2).flatMap (·.rounds)
def roundsBackW : List Fmt.DeclaredRound := (WP.second.blocksInOrder.drop 3).flatMap (·.rounds)

/-- The three trees that the test's first reading round opens: their depths and sources. -/
def depthsW : List ℕ := [13, 22, 22]
def srcsW : List Fmt.TreeSource := [.taken 0 1, .taken 0 82, .taken 1 1]

set_option maxRecDepth 1000000 in
theorem written_index : ((WP.second.blocksInOrder.map (·.place)).zipIdx.filter
    fun x => x.1 == placeOwn).map (·.2) = [2] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No round of the first two chains, and no round of the last chain outside the test, opens a tree of the last chain. -/
theorem written_alone : (openedOf 0 declProofFull.1 ++ openedOf 1 declProofFull.2.1 ++ openedOf 2 roundsFrontW ++
    openedOf 2 roundsBackW).all (fun e => e.1.1 != 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: inside the test the last chain's trees are opened. -/
theorem written_alone_bites : (openedOf 2 declProofFull.2.2).any (fun e => e.1.1 == 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem written_roots : rootsOf roundsFrontW = 0 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_opens_fit : (WP.second.blocksInOrder[2]?).map (fun b =>
             opensFitB false piWFull.nums.stages b.rounds depthsW srcsW 0) = some true := by
  decide +kernel

attribute [local irreducible] P2Law.ProofPlan.WP

/-- Where a place stands once in a list, an index that holds it is that one. -/
theorem index_of_single_place {α : Type} [BEq α] [LawfulBEq α] (l : List α) (a : α) (n m : ℕ)
    (h : (l.zipIdx.filter fun x => x.1 == a).map (·.2) = [m]) (hn : l[n]? = some a) : n = m := by
  have hmem : (a, n) ∈ l.zipIdx := List.mem_zipIdx_iff_getElem?.2 hn
  have hf : (a, n) ∈ l.zipIdx.filter fun x => x.1 == a :=
    List.mem_filter.2 ⟨hmem, beq_self_eq_true _⟩
  have hm := List.mem_map_of_mem (f := fun x : α × ℕ => x.2) hf
  rw [h] at hm
  simpa using hm

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

local notation "𝔽" => P5J.F0T OnBytes.secondHashFunction Zp Np cF

/-- From the written description to the proof file's own, at the last chain. -/
theorem cut_at_W (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (pre t : List (Block (𝔽).S₃ (𝔽).Cl)) (b : Block (𝔽).S₃ (𝔽).Cl)
    (hcut : (𝔽).second.blocksInOrder = pre ++ b :: t) (hb : b.place = placeOwn) :
    pre.flatMap (·.rounds) = roundsFrontW ∧ t.flatMap (·.rounds) = roundsBackW ∧
      (WP.second.blocksInOrder[2]?).map (·.rounds) = some b.rounds := by
  have A := (ProofFile.Honest.K14.planAlike_at_laid h.scope h.laid).second
  rw [hcut] at A
  have A1 := List.forall₂_take_append _ pre (b :: t) A
  have A2 := List.forall₂_drop_append _ pre (b :: t) A
  obtain ⟨bW, tl, hbW, htl, hd⟩ := List.forall₂_cons_right_iff.1 A2
  have hget : WP.second.blocksInOrder[pre.length]? = some bW := by
    have e := congrArg List.head? hd
    rw [List.head?_drop] at e
    exact e
  have hpl : (WP.second.blocksInOrder.map (·.place))[pre.length]? = some placeOwn := by
    rw [List.getElem?_map, hget]
    exact congrArg some (hbW.1.trans hb)
  have h2 : pre.length = 2 := index_of_single_place _ _ _ _ written_index hpl
  rw [h2] at A1 hd hget
  have h3 : WP.second.blocksInOrder.drop 3 = tl := by
    have e := congrArg List.tail hd
    rw [List.tail_drop] at e
    exact e
  refine ⟨(alike₂_rounds _ _ A1).symm, ?_, ?_⟩
  · unfold roundsBackW
    rw [h3]
    exact (alike₂_rounds _ _ htl).symm
  · rw [hget]
    exact congrArg some hbW.2.1

/-- **The public premises of bound_rest_last_chain hold at the proof file's own description, under the head.** -/
theorem premises_at_W (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {W Y : Type} (J : TestJob W Y)
    (hJ : J.p = (fourOf Np).W) (hfr : J.fresh.isNone = false)
    (pre t : List (Block (𝔽).S₃ (𝔽).Cl)) (b : Block (𝔽).S₃ (𝔽).Cl)
    (hcut : (𝔽).second.blocksInOrder = pre ++ b :: t) (hb : b.place = J.p.place) :
    OpensFit J b.rounds depthsW (fun k => srcsW.getD k (.own 0)) (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ k, k < depthsW.length → ∀ n,
        ProofFile.Honest.srcOf 2 ((fun k => srcsW.getD k (.own 0)) k) = (2, n) →
        n < rootsOf (pre.flatMap (·.rounds))) ∧
      ∀ k, aloneInLastChain 𝔽 pre t k = true := by
  have hpl : J.p.place = placeOwn := by
    rw [hJ]
    exact H2K.JointK.place_of_p12At _ _
  obtain ⟨e1, e2, e3⟩ := cut_at_W h pre t b hcut (hb.trans hpl)
  have hst : J.p.nums.stages = piWFull.nums.stages := by
    rw [hJ]
    exact (reads_head_W h).1
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · obtain ⟨bW, hbW, er⟩ := Option.map_eq_some_iff.1 e3
    have q := written_opens_fit
    rw [hbW] at q
    have q' : opensFitB false piWFull.nums.stages bW.rounds depthsW srcsW 0 = true :=
      Option.some.inj q
    rw [er] at q'
    rw [hfr, hst, e1, written_roots]
    exact q'
  · intro j hj n hn
    match j, hj, hn with
    | 0, _, hn => simp [srcsW, ProofFile.Honest.srcOf] at hn
    | 1, _, hn => simp [srcsW, ProofFile.Honest.srcOf] at hn
    | 2, _, hn => simp [srcsW, ProofFile.Honest.srcOf] at hn
  · intro k
    unfold aloneInLastChain
    rw [e1, e2, ProofFile.Honest.K14.decl_at_laid h.scope h.laid]
    refine List.all_eq_true.2 fun e he => ?_
    have ha := List.all_eq_true.1 written_alone e he
    refine bne_iff_ne.2 fun hE => ?_
    rw [hE] at ha
    simp at ha

/-- **THE TEST'S ROW OWES NOTHING MORE TO bud₃**: under the head, at a list that stands at the test on the last chain with the two parts and whose
bud follows from budBoth: the field's body, at every due list of challenges. -/
theorem budOwed₃_at_W (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (𝔽).S₃ (𝔽).Cl V W Y Pb) (J : TestJob W Y) (hp : J.p = (fourOf Np).W)
    (hfrN : J.fresh.isNone = false) (Js : SimJob Pb) (hs : Js.p = (fourOf Np).W)
    (ho : Js.own = false) (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js)
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (𝔽).second.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (𝔽).second.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due 𝔽 = true →
      L.bud u.number ((ρ.second.drop n).take u.rounds.length)
        (asksFrom (treeAsks 𝔽 ρ 2) (u.rounds.map (·.2.length))
          (((rowsOfChain (𝔽).second.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  have hσ' : testSide (𝔽).second.blocksInOrder J Js [] = some σ := by
    unfold testSide
    rw [← hpl, ← hrow]
    exact hσ
  have Fc := facts_head_W h
  rw [← hp] at Fc
  obtain ⟨-, f2, -, -, -⟩ := (first_any_head_W (V := V) h J Js hp hfrN hs ho).2.2 [] σ hσ'
  have f2' : σ.members = [firstMember J Js, restMember J Js] := f2
  rw [f2'] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact hbud _ _ _ (budBoth_of_testBud Js _ _ (first_owes_nothing Js ho _ _))
  · have hσ'' := hσ'
    unfold testSide Side.seated at hσ''
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ''
    have hrowσ : σ.row = testPairs J Js := by rw [← e]
    obtain ⟨s, next, rest, hst⟩ : ∃ s next rest, J.p.nums.stages = s :: next :: rest := by
      have hform := Fc.form
      unfold formPubB at hform
      cases hs' : J.p.nums.stages with
      | nil => rw [hs'] at hform; cases hform
      | cons a l =>
        cases l with
        | nil => rw [hs'] at hform; cases hform
        | cons b' r' => exact ⟨a, b', r', rfl⟩
    have FP := formPub_of_B J.p s next rest hst Fc.form
    have hk : s.k = (sgOf s).h + (sgOf s).g := by
      have := FP.hk
      show s.k = s.h + (s.k - s.h)
      omega
    obtain ⟨b', hf, hpl', hr, hor⟩ := find_own h
    have hb' : b = b' := by
      rw [hp] at hb
      exact Option.some.inj (hb.symm.trans hf)
    have eb : σ.block = b' := by rw [← hb', ← e]
    have hzip : σ.block.rounds.zip σ.block.oracles = J.laid := by
      rw [eb, hr, hor]
      show _ = H2K.JointK.laidOf J.p
      rw [hp]
      exact zip_laid _ (facts_head_W h).plan
    have hblk : σ.block ∈ (𝔽).second.blocksInOrder := by
      rw [hcut]
      exact List.mem_append_right _ List.mem_cons_self
    have hsh : σ.block.shaped = true := planOk_shaped_second h.laid.planOk σ.block hblk
    have hlen : σ.block.rounds.length = J.laid.length := by
      rw [← hzip, List.length_zip, shaped_len σ.block hsh, Nat.min_self]
    have hT : tablesFitB J = true := by
      rw [tablesFitB_eq, hfrN]
      exact Fc.tab
    have hN := trees_rest J pre t σ.block
      (fun x hx => planOk_shaped_second h.laid.planOk x (by rw [hcut]; exact List.mem_append_left _ hx))
      hzip hT Fc.enough
    rw [← hcut] at hN
    obtain ⟨O, hold, ha⟩ := premises_at_W h J hp hfrN pre t σ.block hcut (by rw [eb, hpl', hp])
    have hB := bound_rest_last_chain (V := V) J Js pre t σ.block hcut depthsW _ _ O s
      next rest hst hk hT hold hlen Fc.enough ρ hρ (fun i _ => ha _)
    have l1 : (firstPart J : Part V W Y).moves.length = firstLen J.p.nums.stages :=
      (congrArg List.length (first_moves J)).trans (len_movesFrom J _ _ _)
    have hTo : σ.roundsTo (restMember (V := V) J Js).number = firstLen J.p.nums.stages := by
      unfold Side.roundsTo
      rw [hrowσ]
      show (firstPart J : Part V W Y).moves.length + 0 = _
      rw [l1]
      rfl
    subst hn
    rw [hTo]
    refine hbud _ _ _ ((both_rest Js _ _).2 ?_)
    rw [hs, ← hp, hN]
    exact hB

end Johnson.M1.BudW

#print axioms Johnson.M1.BudW.asks_in_last_chain
#print axioms Johnson.M1.BudW.bound_rest_last_chain
#print axioms Johnson.M1.BudW.written_alone
#print axioms Johnson.M1.BudW.written_alone_bites
#print axioms Johnson.M1.BudW.written_opens_fit
#print axioms Johnson.M1.BudW.premises_at_W
#print axioms Johnson.M1.BudW.budOwed₃_at_W
