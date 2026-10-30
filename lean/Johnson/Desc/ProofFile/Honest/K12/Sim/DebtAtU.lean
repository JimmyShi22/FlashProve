-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/DebtAtU.lean: AT THE PROXIMITY TEST ON G_u, under the head, AT
ONE LIST OF THE FRAME (`Lettered`, Johnson/Desc/ProofFile/Honest/Rule.lean): the frame's sentence at
both members (the field `exact` of `Good`) at the list's own condition and bound, and `BudDebts`
(Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean) at the sides whose one row is that list.
Statements and proofs; no definition.

  `count_of_ties`   wherever the public ties `PubTiesT` (Sim/TreesExact.lean) hold, the containment
                 gives the count: the second premise of `rest_of_opened` (Sim/BudCount.lean) is paid
                 by `reach_gives_trees` (Sim/TreesReach.lean) from the declared counts
  `exact_members_U`   the sentence at both members of the seated side, at `budBoth`
  `budDebts_one_row_U`   the structure, at that one row
  `sentence_and_debt_U`   both, at one list

Limits.
- THE NAMED PREMISES OF `budDebts_one_row_U` AND `sentence_and_debt_U`, O (`OpensFit`), hold and ha
  (`aloneB`: no round outside the test reads a tree that the second part sends), ARE NOT SHOWN HERE.
  That they hold at the proof file's own description, under the head, at every job at G_u whose
  fresh table has come earlier: `premises_at_U` (Sim/AloneAtU.lean).
- TWO OF MANY. `Lettered.goodAt` asks `Good`, which has five fields: `exact` alone is had here.
  `owed_of_threads` asks, beside `goodAt` and `BudDebts`, the book's word, the seats, the sealing
  round, the roots, the input, the stored tables, that `ready` returns, the threads, `PartsStand`
  and `OnDebts`: none is had here.
- THE SENTENCE's CONDITION `onFreeT` HAS NO KNOWN MEMBER: that `OnFreeT` holds at a state of a run
  is had under premises alone: `onFreeT_head_U_paid` (AtFullSide/K12/OnFreeTAtHeadUPaid.lean)
  (Sim/RestExactAtHeadU.lean's own word: an instance, no member; it counts nothing).
- Both members' sentences at one condition and one bound, `budOpened`, stand at G_u in
  `rest_exact_head_U` already; `exact_members_U` lays them at `budBoth`.
- Of the second member's public premises the head pays seven here (the plan's test; hzip, hc, hst,
  hk, hT, hen).
- `count_of_ties` asks the counts at every round's number (hD). Below `firstLen` `laterOf` yields
  the list's first challenge: there hD can hold only where these rounds declare no position. By
  reading they declare none; no theorem says so.
- One row; the shared chain; G_u alone. At a state on entry that is the job's own letter `rec₀`, not
  shown to be the verifier's. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.DebtAtO
import Johnson.Desc.ProofFile.Honest.K12.Sim.RestExactAtHeadU
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open VerifiableInference.Desc.K12 (P12)
open H2K.Pub (sgOf)
open Johnson.G (codesFull2)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- (1) **Wherever the public ties hold, the containment gives the count.** hD: at each round's
number the challenge has as many positions as the round declares. -/
theorem count_of_ties {W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes)
    (nT : ℕ) (T : PubTiesT J Js K nT) (hOk : StagesOk J.p.nums.stages = true) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ)))
    (hD : ∀ i, (laterOf J.p.nums.stages ds i).poss.length = declared J.p i)
    (h : budOpened J.p.nums.stages 1 ds asks) : budRest J.p.nums.stages ds asks = true := by
  obtain ⟨a, next, nx', rest', hst, -, -, hFit⟩ := reach_gives_trees J.p T.reach
  have hF := hFit (laterOf J.p.nums.stages ds) hD
  refine rest_of_opened J.p.nums.stages hOk ds asks ?_ h
  rw [hst] at hF ⊢
  exact hF

/-- (2) **The sentence at both members of the seated side, at `budBoth`**: the last conjunct of
`rest_exact_head_U` through `exact_bud`. -/
theorem exact_members_U {V W X Pb : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF) (J : TestJob W X)
    (Js : SimJob Pb) (chain : ℕ) (hJ : J.p = (fourOf Np).U) (hfr : J.fresh.isNone = false)
    (hs : Js.p = (fourOf Np).U) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf chain x.2).1, (ProofFile.Honest.srcOf chain x.2).2, x.1.a))
    (fs : List (Fall (P5J.F0T o Zp Np cF).S₂))
    (σ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ) (φ : Face V W Pb)
    (firstTree : ℕ) : ∀ u ∈ σ.members,
      ExactMember φ σ chain firstTree (onFreeT φ J Js codesFull2 chain (fourOf Np).U.nums.first)
        (budBoth Js) u := by
  intro u hu
  obtain ⟨-, -, -, hall⟩ := rest_exact_head_U (V := V) h J Js chain hJ hfr hs ho hop
  obtain ⟨-, -, hE⟩ := hall fs σ hσ
  refine exact_bud (fun ds asks hb => ?_) (hE φ firstTree u hu)
  have h2 := hb.2
  rw [hs, ← hJ] at h2
  exact h2

/-- (3) **`BudDebts` at the sides whose one row is the proximity test on G_u, at the bound
`budBoth`, under the head.** Number 0 owes nothing; number 1 by `debt_rest_all`. Named premises:
the cut, O, hold, ha, at the seated side σ₀. -/
theorem budDebts_one_row_U {W₀ Rc Ky Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀) (hJ : J.p = (fourOf Np).U)
    (hs : Js.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (ho : Js.own = false) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js)
    (σ₀ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ₀)
    (pre₀ t₀ : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre₀ ++ σ₀.block :: t₀)
    (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource)
    (O : OpensFit J σ₀.block.rounds depths src₀ (rootsOf (pre₀.flatMap (·.rounds))))
    (hold : ∀ k, k < depths.length → ∀ n, ProofFile.Honest.srcOf 1 (src₀ k) = (1, n) →
      n < rootsOf (pre₀.flatMap (·.rounds)))
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB (P5J.F0T o Zp Np cF) pre₀ t₀ (rootsOf (pre₀.flatMap (·.rounds)) +
        sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    BudDebts (P5J.F0T o Zp Np cF) Bk
      ({ first := [], shared := [L], second := [] } :
        Sides (P5J.F0T o Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y) where
  bud₁ := fun _ hL => absurd hL List.not_mem_nil
  bud₂ := fun L' hL' => by
    obtain rfl := List.mem_singleton.1 hL'
    intro σ hσ' u hu pre t n hcut' hn ρ hρ
    have eσ : σ₀ = σ := Option.some.inj (hσ.symm.trans hσ')
    subst eσ
    have hp' : Js.p = J.p := hs.trans hJ.symm
    rw [hbud]
    refine both_of J Js hp' u.number _ _ (fun _ => first_owes_nothing Js ho _ _) fun e => ?_
    have T := pubTiesT_head_U h J Js hJ hfr hs ho
    obtain ⟨s, next, nx', rest', hst, -, -, -⟩ := reach_gives_trees J.p T.reach
    have hOk : StagesOk Js.p.nums.stages = true := stagesOk_at_place h Js (Or.inl hs)
    have hk : s.k = (sgOf s).h + (sgOf s).g :=
      (Nat.add_sub_cancel' ((stages_low _ hOk).1 s
        (by rw [hp', hst]; exact List.mem_cons_self))).symm
    have hσt : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ₀ :=
      (side_is_testSide L' J Js hpl hrow _).symm.trans hσ
    obtain ⟨b, hf, -, hr, hor⟩ := find_gu h
    have hb : σ₀.block = b := by
      unfold testSide Side.seated at hσt
      rw [hJ, hf] at hσt
      obtain rfl := Option.some.inj hσt
      rfl
    have hzip : σ₀.block.rounds.zip σ₀.block.oracles = J.laid := by
      rw [hb, hr, hor, zip_laid _ (planOk_head_U h), ← hJ]
      rfl
    have hen : firstLen J.p.nums.stages ≤ J.laid.length := by
      show firstLen J.p.nums.stages ≤ (H2K.JointK.laidOf J.p).length
      rw [T.count]
      exact Nat.le_add_right _ _
    have hd := debt_rest_all L' J Js hpl hrow hbud hp' h.laid.planOk σ₀ hσ pre₀ t₀ hcut hzip
      T.count depths src₀ O s next (nx' :: rest') hst hk T.tables hold hen ha u hu e pre t n hcut'
      hn ρ hρ
    rw [hbud, e] at hd
    have hd' := (both_rest Js _ _).1 hd
    rw [hp'] at hd'
    exact hd'
  bud₃ := fun _ hL => absurd hL List.not_mem_nil

/-- (4) **The field `exact` of `Good` and `BudDebts`, at one list**: at the list's own condition,
`onFreeT` at the shared chain's face and number and the place's own first trees, and its own bound,
`budBoth`. In the letters of `owed_of_threads` for the shared chain. -/
theorem sentence_and_debt_U {W₀ Rc Ky Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀) (hJ : J.p = (fourOf Np).U)
    (hs : Js.p = (fourOf Np).U) (hfr : J.fresh.isNone = false) (ho : Js.own = false)
    (hop : Js.opens = (fourOf Np).U.nums.first.map fun x =>
      ((ProofFile.Honest.srcOf 1 x.2).1, (ProofFile.Honest.srcOf 1 x.2).2, x.1.a)) {Bk : ProverCoinCounts}
    (L : Lettered Bk (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js)
    (hOn : L.On = onFreeT Face.shared J Js codesFull2 1 (fourOf Np).U.nums.first)
    (σ₀ : Side (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hσ : L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ₀)
    (pre₀ t₀ : List (Block (P5J.F0T o Zp Np cF).S₂ (P5J.F0T o Zp Np cF).Cl))
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre₀ ++ σ₀.block :: t₀)
    (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource)
    (O : OpensFit J σ₀.block.rounds depths src₀ (rootsOf (pre₀.flatMap (·.rounds))))
    (hold : ∀ k, k < depths.length → ∀ n, ProofFile.Honest.srcOf 1 (src₀ k) = (1, n) →
      n < rootsOf (pre₀.flatMap (·.rounds)))
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB (P5J.F0T o Zp Np cF) pre₀ t₀ (rootsOf (pre₀.flatMap (·.rounds)) +
        sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    (∀ σ, L.side (P5J.F0T o Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      ExactMember Face.shared σ 1 0 L.On L.bud u) ∧
    BudDebts (P5J.F0T o Zp Np cF) Bk
      ({ first := [], shared := [L], second := [] } :
        Sides (P5J.F0T o Zp Np cF) Bk W₀ Rc Ky Tr X₀ Y) := by
  refine ⟨fun σ hσ' u hu => ?_, budDebts_one_row_U h Js J hJ hs hfr ho L hpl hrow hbud σ₀ hσ pre₀ t₀
    hcut depths src₀ O hold ha⟩
  rw [hOn, hbud]
  exact exact_members_U h J Js 1 hJ hfr hs ho hop [] σ
    ((side_is_testSide L J Js hpl hrow _).symm.trans hσ') Face.shared 0 u hu

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.count_of_ties
#print axioms ProofFile.Honest.K12.Light.exact_members_U
#print axioms ProofFile.Honest.K12.Light.budDebts_one_row_U
#print axioms ProofFile.Honest.K12.Light.sentence_and_debt_U
