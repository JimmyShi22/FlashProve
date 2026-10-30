-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/AloneAtU.lean: THE THREE NAMED PREMISES OF Sim/DebtAtU.lean
HOLD AT THE PROOF FILE's OWN DESCRIPTION, UNDER THE HEAD, at the proximity test on G_u: `OpensFit`
(ColsTerm.lean: the openings that the test's rounds declare are the term's), the earlier trees'
order, and `aloneB` (ReadsInBlock.lean: no round of the file outside the test opens a tree that the
test's second part sends). So the two tops of Sim/DebtAtU.lean stand with no named premise on the
description. Four helper definitions; statements and proofs.

The road. Seven closed facts at the library's written description `WP`
(Johnson/AtFull/ProofPlan/WP.lean) and the written place `piUFull`
(Johnson/Desc/K12/Law/PlacesFull.lean), by an evaluation in Lean's kernel. From there to the proof
file's own description by `decl_at_laid` and `alike_shared_at_laid`
(Johnson/Desc/ProofFile/Honest/K14/WrittenAtHead.lean): under the head it declares the written
rounds, and its shared list is alike to the written one, sub-protocol by sub-protocol, in place,
rounds and oracle messages.

  `frontWU`, `behindWU`, `aloneWU`, `srcsU`   the written rounds in front of the test and behind it;
                 `aloneB` in written letters; the sources of the test's two first trees
  `places_WU`, `roots_WU`, `opens_WU`, `far_WU`, `alone_WU`, `sends_WU`   the closed facts: nine
                 sub-protocols in front; they send three trees; `opensFitB` says yes; the second
                 part sends the chain's trees 3, 4, 5, 6, and nothing outside the test opens one of
                 them
  `no_WU`        each test can say no
  `cut_WU`, `alone_is_WU`   from the written description to the proof file's own
  `premises_at_U`   the three premises
  `budDebts_U_head`, `exact_and_debts_U_head`   the two tops

Over what it stands. A file of the kind K14's authors
(Johnson/Desc/ProofFile/Honest/K14/WrittenAtHead.lean, with WrittenBack.lean beneath it).

Limits.
- TWO OF MANY, AS IN Sim/DebtAtU.lean: of `Good`'s five fields `exact` alone; of what
  `owed_of_threads` asks, `BudDebts` alone, at one row.
- THE SENTENCE's CONDITION `onFreeT` HAS NO KNOWN MEMBER: nothing here shows that it holds at any
  state of a run.
- G_u alone. At G_omega the second member's sentence has no content (`no_pubTies_O`,
  Sim/DebtAtO.lean). The first and the last chain's tests are not treated.
- The written values were printed off the description at the goals' stored public files by Lean's
  evaluator (WP.lean's own limit); that the proof file's description has them is `decl_at_laid`'s
  and `alike_shared_at_laid`'s word, in the goals' scope.
- At a state on entry that is the job's own letter `rec₀`, not shown to be the verifier's. Nothing
  on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.DebtAtU
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.AtU
open VerifiableInference.Desc (FileDescription Block Place Alike₂ alike₂_rounds)
open VerifiableInference.Desc.K12 (P12)
open P2Law.ProofPlan (WP declProofFull)
open H2K.Member (piUFull)
open Johnson.G (codesFull2)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K14 (decl_at_laid alike_shared_at_laid)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The written declared rounds in front of the test on G_u in the shared chain. -/
def frontWU : List Fmt.DeclaredRound := (WP.shared.blocksInOrder.take 9).flatMap (·.rounds)

/-- Those behind it. -/
def behindWU : List Fmt.DeclaredRound := (WP.shared.blocksInOrder.drop 10).flatMap (·.rounds)

/-- `aloneB` (ReadsInBlock.lean) in written letters. -/
def aloneWU (k : ℕ) : Bool :=
  (openedOf 0 declProofFull.1 ++ openedOf 1 frontWU ++ openedOf 1 behindWU ++
    openedOf 2 declProofFull.2.2).all (·.1 != (1, k))

/-- The sources of the test's two first trees. -/
def srcsU : List Fmt.TreeSource := [.own 0, .own 2]

/-! ## 1 By an evaluation in Lean's kernel, at written values -/

set_option maxRecDepth 1000000 in
theorem places_WU : WP.shared.blocksInOrder.map (·.place) =
    [⟨2, none, 0, .frame⟩, ⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩, ⟨2, none, 3, .K14⟩,
      ⟨2, none, 4, .K14⟩, ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩, ⟨2, none, 7, .K14⟩,
      ⟨2, none, 8, .K14⟩, ⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩, ⟨2, none, 11, .frame⟩] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem roots_WU : rootsOf frontWU = 3 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem opens_WU : (WP.shared.blocksInOrder[9]?).map (fun b =>
             opensFitB false piUFull.nums.stages b.rounds [24, 13] srcsU 3) = some true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem far_WU : (none :: depths false piUFull.nums.stages).length ≤
    firstLen piUFull.nums.stages + 40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem alone_WU : (List.range 40).all (fun i =>
    !(ProofFile.Honest.K12.depthOf false piUFull.nums.stages (firstLen piUFull.nums.stages + i)).isSome ||
      aloneWU (3 + ((List.range (firstLen piUFull.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf false piUFull.nums.stages j).isSome).length)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The trees that the second part sends. -/
theorem sends_WU : ((List.range 40).filter fun i =>
    (ProofFile.Honest.K12.depthOf false piUFull.nums.stages
      (firstLen piUFull.nums.stages + i)).isSome).map (fun i =>
      3 + ((List.range (firstLen piUFull.nums.stages + i)).filter fun j =>
        (ProofFile.Honest.K12.depthOf false piUFull.nums.stages j).isSome).length) = [3, 4, 5, 6] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The tests can say no: at a tree that the test on G_omega opens; at one that it sends and opens;
with one argument of `opens_WU` turned. -/
theorem no_WU : (aloneWU 2, aloneWU 7, (WP.shared.blocksInOrder[9]?).map fun b =>
    [opensFitB false piUFull.nums.stages b.rounds [24, 13] srcsU 4,
      opensFitB false piUFull.nums.stages b.rounds [24, 12] srcsU 3,
      opensFitB false piUFull.nums.stages b.rounds [24, 13] [.own 0, .own 1] 3,
      opensFitB true piUFull.nums.stages b.rounds [24, 13] srcsU 3]) =
    (false, false, some [false, false, false, false]) := by
  decide +kernel

/-! ## 2 From the written description to the proof file's own, under the head -/

/-- Whatever cut of the shared list stands at a sub-protocol at the test's place has the written
rounds in front, at it and behind. -/
theorem cut_WU (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (b : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (hb : b.place = ⟨2, none, 9, .K12⟩) :
    pre.flatMap (·.rounds) = frontWU ∧ t.flatMap (·.rounds) = behindWU ∧
      (WP.shared.blocksInOrder[9]?).map (·.rounds) = some b.rounds := by
  have A := alike_shared_at_laid h.scope h.laid
  rw [hcut] at A
  have A1 := List.forall₂_take_append _ pre (b :: t) A
  have A2 := List.forall₂_drop_append _ pre (b :: t) A
  obtain ⟨bW, tl, hbW, htl, hd⟩ := List.forall₂_cons_right_iff.1 A2
  have hget : WP.shared.blocksInOrder[pre.length]? = some bW := by
    have e := congrArg List.head? hd
    rw [List.head?_drop] at e
    exact e
  have hpl : (WP.shared.blocksInOrder.map (·.place))[pre.length]? = some ⟨2, none, 9, .K12⟩ := by
    rw [List.getElem?_map, hget]
    exact congrArg some (hbW.1.trans hb)
  rw [places_WU] at hpl
  have hlt : pre.length < 12 := (List.getElem?_eq_some_iff.1 hpl).1
  have only : ∀ n, n < 12 → ([⟨2, none, 0, .frame⟩, ⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩,
      ⟨2, none, 3, .K14⟩, ⟨2, none, 4, .K14⟩, ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩,
      ⟨2, none, 7, .K14⟩, ⟨2, none, 8, .K14⟩, ⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩,
      ⟨2, none, 11, .frame⟩] : List Place)[n]? = some ⟨2, none, 9, .K12⟩ → n = 9 := by decide
  have h9 : pre.length = 9 := only _ hlt hpl
  rw [h9] at A1 hd hget
  have h10 : WP.shared.blocksInOrder.drop 10 = tl := by
    have e := congrArg List.tail hd
    rw [List.tail_drop] at e
    exact e
  refine ⟨(alike₂_rounds _ _ A1).symm, ?_, ?_⟩
  · unfold behindWU
    rw [h10]
    exact (alike₂_rounds _ _ htl).symm
  · rw [hget]
    exact congrArg some hbW.2.1

theorem alone_is_WU (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (b : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (hb : b.place = ⟨2, none, 9, .K12⟩) (k : ℕ) :
    aloneB (P5J.F0T o Zp Np cF) pre t k = aloneWU k := by
  obtain ⟨e1, e2, -⟩ := cut_WU h pre t b hcut hb
  unfold aloneB aloneWU
  rw [decl_at_laid h.scope h.laid, e1, e2]

/-- **The three named premises of `budDebts_one_row_U` hold at the proof file's own description,
under the head**, at every job at G_u whose fresh table has come earlier, at every cut at the
test's place. -/
theorem premises_at_U (h : P5J.AtMg o Z D r₀ Zp Np cF) {W X : Type} (J : TestJob W X)
    (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false)
    (pre t : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (b : Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t) (hb : b.place = J.p.place) :
    OpensFit J b.rounds [24, 13] (fun k => srcsU.getD k (.own 0))
        (rootsOf (pre.flatMap (·.rounds))) ∧
      (∀ k, k < [24, 13].length → ∀ n,
        ProofFile.Honest.srcOf 1 ((fun k => srcsU.getD k (.own 0)) k) = (1, n) →
        n < rootsOf (pre.flatMap (·.rounds))) ∧
      ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
        aloneB (P5J.F0T o Zp Np cF) pre t (rootsOf (pre.flatMap (·.rounds)) +
          sentBefore J (firstLen J.p.nums.stages + i)) = true := by
  have hpl : J.p.place = ⟨2, none, 9, .K12⟩ := by
    rw [hJ]
    exact H2K.JointK.place_of_p12At _ _
  obtain ⟨e1, -, e3⟩ := cut_WU h pre t b hcut (hb.trans hpl)
  have hst : J.p.nums.stages = piUFull.nums.stages := by
    rw [hJ]
    exact congrArg (·.stages) (nums_head_U h)
  have h3 : rootsOf (pre.flatMap (·.rounds)) = 3 := by
    rw [e1]
    exact roots_WU
  have hdep : ∀ r, depthAt J r = ProofFile.Honest.K12.depthOf false piUFull.nums.stages r := fun r => by
    unfold depthAt ProofFile.Honest.K12.depthOf
    rw [hfr, hst]
  rw [h3]
  refine ⟨opensFit_of_B J _ _ _ _ ?_, ?_, ?_⟩
  · obtain ⟨bW, hbW, er⟩ := Option.map_eq_some_iff.1 e3
    have q := opens_WU
    rw [hbW] at q
    have q' : opensFitB false piUFull.nums.stages bW.rounds [24, 13] srcsU 3 = true :=
      Option.some.inj q
    rw [er] at q'
    rw [hfr, hst]
    exact q'
  · intro j hj n hn
    match j, hj, hn with
    | 0, _, hn =>
      have e : (0 : ℕ) = n := congrArg Prod.snd hn
      omega
    | 1, _, hn =>
      have e : (2 : ℕ) = n := congrArg Prod.snd hn
      omega
  · intro i hi
    rw [alone_is_WU h pre t b hcut (hb.trans hpl)]
    rw [hst] at hi ⊢
    rw [hdep] at hi
    have hsb : sentBefore J (firstLen piUFull.nums.stages + i) =
        ((List.range (firstLen piUFull.nums.stages + i)).filter fun j =>
          (ProofFile.Honest.K12.depthOf false piUFull.nums.stages j).isSome).length := by
      unfold sentBefore
      simp only [hdep]
    rw [hsb]
    by_cases hlt : i < 40
    · have hh := List.all_eq_true.1 alone_WU i (List.mem_range.2 hlt)
      rw [hi] at hh
      simpa using hh
    · exfalso
      have hf := far_WU
      have hn : ProofFile.Honest.K12.depthOf false piUFull.nums.stages
          (firstLen piUFull.nums.stages + i) = none := by
        unfold ProofFile.Honest.K12.depthOf
        exact List.getD_eq_default _ _ (by omega)
      rw [hn] at hi
      cases hi

/-! ## 3 So the two tops of Sim/DebtAtU.lean, with no named premise on the description -/

theorem budDebts_U_head {W₀ Rc Ky Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀) (hJ : J.p = (fourOf Np).U)
    (hs : Js.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (ho : Js.own = false) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js) :
    BudDebts (P5J.F0T o Zp Np cF) Bk
      ({ first := [], shared := [L], second := [] } :
        Sides (P5J.F0T o Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y) := by
  cases hS : L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder with
  | none =>
    refine ⟨fun _ hL => absurd hL List.not_mem_nil, fun L' hL' σ hσ => ?_,
      fun _ hL => absurd hL List.not_mem_nil⟩
    obtain rfl := List.mem_singleton.1 hL'
    rw [hS] at hσ
    cases hσ
  | some σ₀ =>
    have hmem : σ₀.block ∈ (P5J.F0T o Zp Np cF).shared.blocksInOrder := by
      have hh := hS
      unfold Lettered.side Side.seated at hh
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hh
      exact List.mem_of_find?_eq_some hb
    obtain ⟨pre₀, t₀, hcut⟩ := List.append_of_mem hmem
    obtain ⟨O, hold, ha⟩ := premises_at_U h J hJ hfr pre₀ t₀ σ₀.block hcut
      ((side_place hS).trans hpl)
    exact budDebts_one_row_U h Js J hJ hs hfr ho L hpl hrow hbud σ₀ hS pre₀ t₀ hcut [24, 13] _ O
      hold ha

theorem exact_and_debts_U_head {W₀ Rc Ky Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀) (hJ : J.p = (fourOf Np).U)
    (hs : Js.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf 1 x.2).1, (ProofFile.Honest.srcOf 1 x.2).2, x.1.a)) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js)
    (hOn : L.On = onFreeT Face.shared J Js codesFull2 1 (fourOf Np).U.nums.first) :
    (∃ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ) ∧
    (∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      ExactMember Face.shared σ 1 0 L.On L.bud u) ∧
    BudDebts (P5J.F0T o Zp Np cF) Bk
      ({ first := [], shared := [L], second := [] } :
        Sides (P5J.F0T o Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y) := by
  refine ⟨?_, fun σ hσ' u hu => ?_, budDebts_U_head h Js J hJ hs hfr ho L hpl hrow hbud⟩
  · obtain ⟨-, -, hex, -⟩ := rest_exact_head_U (V := Empty) h J Js 1 hJ hfr hs ho hop
    obtain ⟨σ, hσ⟩ := hex []
    exact ⟨σ, (side_is_testSide L J Js hpl hrow _).trans hσ⟩
  · rw [hOn, hbud]
    exact exact_members_U h J Js 1 hJ hfr hs ho hop [] σ
      ((side_is_testSide L J Js hpl hrow _).symm.trans hσ') Face.shared 0 u hu

end ProofFile.Honest.K12.Light.AtU

#print axioms ProofFile.Honest.K12.Light.AtU.frontWU
#print axioms ProofFile.Honest.K12.Light.AtU.behindWU
#print axioms ProofFile.Honest.K12.Light.AtU.aloneWU
#print axioms ProofFile.Honest.K12.Light.AtU.srcsU
#print axioms ProofFile.Honest.K12.Light.AtU.places_WU
#print axioms ProofFile.Honest.K12.Light.AtU.roots_WU
#print axioms ProofFile.Honest.K12.Light.AtU.opens_WU
#print axioms ProofFile.Honest.K12.Light.AtU.far_WU
#print axioms ProofFile.Honest.K12.Light.AtU.alone_WU
#print axioms ProofFile.Honest.K12.Light.AtU.sends_WU
#print axioms ProofFile.Honest.K12.Light.AtU.no_WU
#print axioms ProofFile.Honest.K12.Light.AtU.cut_WU
#print axioms ProofFile.Honest.K12.Light.AtU.alone_is_WU
#print axioms ProofFile.Honest.K12.Light.AtU.premises_at_U
#print axioms ProofFile.Honest.K12.Light.AtU.budDebts_U_head
#print axioms ProofFile.Honest.K12.Light.AtU.exact_and_debts_U_head
