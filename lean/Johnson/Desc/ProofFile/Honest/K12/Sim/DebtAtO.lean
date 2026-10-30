-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/DebtAtO.lean: `BudDebts`
(Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean), the frame's debt on the positions asked at every
list of challenges that is due, AT THE SIDES WHOSE ONE ROW IS THE PROXIMITY TEST ON G_omega, at the
bound `budBoth` (Sim/ExactFirstOwn.lean), under the head. Statements and proofs; no definition.

  `debt_rest_all`   `debt_rest` (Sim/DebtBoth.lean) at the arbitrary cut that the field `bud₂` hands
                 its caller: the premises at one cut. General in the description
  `stagesOk_at_place`   `StagesOk` at a job of the simulators that stands at one of the four seated
                 places: `stagesOk_seated` (StagesOfPlan.lean) laid into the first premise of
                 `rest_of_opened` and `test_of_both` (Sim/BudCount.lean)
  `budDebts_one_row_both`   the structure, at that one row
  `no_pubTies_O`   at that place the public premise of the second member's sentence cannot be met

How it stands to `budDebts_one_row` (Sim/BudOwnIsDebt.lean). There the bound is `testBud`, and the
field's text at the member number 1, the count, is a premise that nobody pays. Here the bound is
`budBoth`, and that text, the containment, is concluded.

By what. `cut_at_place` (TreeInFront.lean); `debt_rest`; `debt_first_O` (Sim/BudOwnIsDebt.lean), at
the list with `testBud` for its bound, which has the same place and row and so the same side;
`both_of`, `both_rest` (Sim/BudBoth.lean). Under the head: the field `laid.planOk`; `find_gomega`,
`planOk_head_O`, `count_head_O`, `nums_head_O` (Sim/FirstPubOwnAtHead.lean); `firstPubOwn_at`
(Sim/MeetsOwnAtHead.lean); `zip_laid` (PlaysK12.lean); `stages_low` (Sim/BudCount.lean).

Limits.
- IT PAYS A DEBT AT G_omega FOR A LIST WHOSE SENTENCE AT THE MEMBER NUMBER 1 IS NOT HAD: `BudDebts`
  asks no sentence; `goodAt` does, and at this place `PubTiesT`, the premise of the second member's
  sentence, cannot be met (`no_pubTies_O`). The join at G_omega is no nearer by this file.
- OF THE SECOND MEMBER's PUBLIC PREMISES THE HEAD PAYS SEVEN HERE (the plan's test; hzip, hc, hst,
  hk, hT, hen). FOUR STAY NAMED PREMISES, at the seated side σ₀ and one cut: hcut, O (`OpensFit`),
  hold, ha (`aloneB`). Who could pay these under the head has not been sought.
- ONE ROW. The sides of a filling of record hold many lists: `BudDebts` there asks the like of each.
- The shared chain alone. At G_u the first member owes nothing (`debt_first_earlier`,
  Sim/DebtBoth.lean): no top is typed there.
- `BudDebts` is one of the premises of `owed_of_threads`. Nothing here says that the others hold.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.DebtBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudCount
import Johnson.Desc.ProofFile.Honest.K12.StagesOfPlan
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open VerifiableInference.Desc.K12 (P12)
open H2K.Pub (sgOf)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- (1) **`debt_rest` at the arbitrary cut that `BudDebts.bud₂` hands its caller**: the premises at
one cut (pre₀, t₀); the conclusion is the field's text behind "∀ u ∈ σ.members," at u.number = 1,
its "∀ pre t n" and its cut within. -/
theorem debt_rest_all {Xi V W X Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (L : Lettered Bk F.S₂ F.Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (hpl : L.place = J.p.place) (hrow : L.row = testPairs J Js) (hbud : L.bud = budBoth Js)
    (hp : Js.p = J.p) (hplan : F.planOk = true) (σ : Side F.S₂ F.Cl V W X Pb)
    (hσ : L.side F.shared.blocksInOrder = some σ) (pre₀ t₀ : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre₀ ++ σ.block :: t₀)
    (hzip : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hc : (H2K.JointK.laidOf J.p).length = firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (depths : List ℕ) (src₀ : ℕ → Fmt.TreeSource)
    (O : OpensFit J σ.block.rounds depths src₀ (rootsOf (pre₀.flatMap (·.rounds))))
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: next :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hT : tablesFitB J = true)
    (hold : ∀ k, k < depths.length → ∀ n, ProofFile.Honest.srcOf 1 (src₀ k) = (1, n) →
      n < rootsOf (pre₀.flatMap (·.rounds)))
    (hen : firstLen J.p.nums.stages ≤ J.laid.length)
    (ha : ∀ i, (depthAt J (firstLen J.p.nums.stages + i)).isSome = true →
      aloneB F pre₀ t₀ (rootsOf (pre₀.flatMap (·.rounds)) +
        sentBefore J (firstLen J.p.nums.stages + i)) = true) :
    ∀ u ∈ σ.members, u.number = 1 → ∀ pre t n, F.shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws, ρ.due F = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks F ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro u hu h1 pre t n hcut' hn ρ hρ
  have e1 : pre₀ = pre := cut_at_place hplan pre₀ pre t₀ t σ.block σ.block hcut hcut' rfl
  subst e1
  exact debt_rest L J Js hpl hrow hbud hp hplan σ hσ pre₀ t₀ hcut hzip hc depths src₀ O s next rest
    hst hk hT hold hen ha u hu h1 n hn ρ hρ

/-- (2) **`StagesOk` at a job of the simulators that stands at one of the four seated places, under
the head.** -/
theorem stagesOk_at_place (h : P5J.AtMg o Z D r₀ Zp Np cF) {Pb : Type} (Js : SimJob Pb)
    (hJ : Js.p = (fourOf Np).U ∨ (fourOf Np).O = some Js.p ∨ Js.p = (fourOf Np).W ∨
      Js.p = (fourOf Np).L) : StagesOk Js.p.nums.stages = true := by
  obtain ⟨-, hU, ⟨p, hp, hOo⟩, hW, hL⟩ := stagesOk_seated h
  rcases hJ with e | e | e | e
  · rw [e]
    exact hU
  · have e' : p = Js.p := Option.some.inj (hp.symm.trans e)
    rw [← e']
    exact hOo
  · rw [e]
    exact hW
  · rw [e]
    exact hL

/-- **At the test on G_omega the public premise of the second member's sentence cannot be met**,
under the head: `PubTiesT.reach` gives `ownMask = false`; the seated place has the written place's
numbers, where it is true. -/
theorem no_pubTies_O (h : P5J.AtMg o Z D r₀ Zp Np cF) (hO : (fourOf Np).O = some pO)
    {W X Pb : Type} (J : TestJob W X) (Js : SimJob Pb) (hp : J.p = pO) (K : OnBytes.Codes)
    (nT : ℕ) : ¬ PubTiesT J Js K nT := by
  intro T
  obtain ⟨_, _, _, _, _, hm, _⟩ := reach_gives_trees J.p T.reach
  rw [hp, nums_head_O h hO] at hm
  cases hm

/-- (3) **`BudDebts` at the sides whose one row is the proximity test on G_omega, at the bound
`budBoth`, under the head.** The field's text at number 1 is concluded. Named premises: the cut, O,
hold and ha, at the seated side σ₀. -/
theorem budDebts_one_row_both {W₀ Rc Ky Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (hO : (fourOf Np).O = some pO) (Js : SimJob Ky) (J : TestJob (Common W₀ Rc Ky) X₀)
    (hp : J.p = pO) (hJ : Js.p = pO) (hfr : J.fresh.isNone = true) (ho : Js.own = true) {Bk : ProverCoinCounts}
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
    have hp' : Js.p = J.p := hJ.trans hp.symm
    rw [hbud]
    refine both_of J Js hp' u.number _ _ (fun e => ?_) fun e => ?_
    · have hd := debt_first_O h hO Js J hp hJ { L' with bud := testBud Js } hpl hrow rfl σ₀ hσ u
        hu e pre t n hcut' hn ρ hρ
      rw [e] at hd
      exact hd
    · have T := firstPubOwn_at h hO Js J hp hfr hJ ho
      have hOk : StagesOk Js.p.nums.stages = true :=
        stagesOk_at_place h Js (Or.inr (Or.inl (by rw [hJ]; exact hO)))
      subst hp
      have hstW : J.p.nums.stages = H2K.Member.piOFull.nums.stages :=
        congrArg (·.stages) (nums_head_O h hO)
      obtain ⟨s, next, rest, hlit⟩ :
          ∃ s t rest, H2K.Member.piOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
      have hst : J.p.nums.stages = s :: next :: rest := hstW.trans hlit
      have hk : s.k = (sgOf s).h + (sgOf s).g :=
        (Nat.add_sub_cancel' ((stages_low _ hOk).1 s
          (by rw [hp', hst]; exact List.mem_cons_self))).symm
      have hσt : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js [] = some σ₀ :=
        (side_is_testSide L' J Js hpl hrow _).symm.trans hσ
      obtain ⟨b, hf, -, hr, hor⟩ := find_gomega h hO
      have hb : σ₀.block = b := by
        unfold testSide Side.seated at hσt
        rw [hf] at hσt
        obtain rfl := Option.some.inj hσt
        rfl
      have hzip : σ₀.block.rounds.zip σ₀.block.oracles = J.laid := by
        rw [hb, hr, hor]
        exact zip_laid J.p (planOk_head_O h hO)
      have hd := debt_rest_all L' J Js hpl hrow hbud hp' h.laid.planOk σ₀ hσ pre₀ t₀ hcut hzip
        (count_head_O h hO) depths src₀ O s next rest hst hk T.tables hold T.enough ha u hu e pre t
        n hcut' hn ρ hρ
      rw [hbud, e] at hd
      have hd' := (both_rest Js _ _).1 hd
      rw [hp'] at hd'
      exact hd'
  bud₃ := fun _ hL => absurd hL List.not_mem_nil

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.debt_rest_all
#print axioms ProofFile.Honest.K12.Light.stagesOk_at_place
#print axioms ProofFile.Honest.K12.Light.no_pubTies_O
#print axioms ProofFile.Honest.K12.Light.budDebts_one_row_both
