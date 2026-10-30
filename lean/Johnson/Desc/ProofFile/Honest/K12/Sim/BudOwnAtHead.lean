-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudOwnAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean), at the first member of the proximity test on G_omega, whose first fold sends
its own fresh table: the side's bound on positions `testBud` (Sim/Row.lean) holds at the positions
that the description's own declared rounds read of that table's tree, at every list of challenges
that passes `Draws.due` (Johnson/Desc/ProofFile/Honest/Frame.lean); and `MeetsAt`
(Sim/MeetsOwnAtHead.lean) holds there, at these positions and at that list's own stretch of
challenges. The job is any `TestJob` at the seated place whose first fold sends its own table. It
imports Mathlib.

The statement `bud_first_O` has the text of the field `bud₂` of the record `BudDebts`, which goes
with the frame, at one row and one member: the cut of the shared list, the number n of rounds in
front, the stretch `(ρ.shared.drop n).take …`, and `asksFrom (treeAsks F ρ 1) …`. That record's file
does not lie beneath this one: so its function `Side.roundsTo` is written out here, and nothing in
Lean ties this statement to the record: it is held against it by reading.

  `length_eraseDups`, `different_le`   a list holds no more different numbers than members
  `dealt_flat`   how `H2U.testOracles5` (Johnson/Desc/K12/TestOracles.lean) deals the stated
                 messages to the rounds: in a row they are the first of `sentOracles`
  `first_told`, `p12At_cases`, `oracles_head_O`   so the seated place's first stated message is the
                 fold's own table's: depth 13, 3 words, one tenant, which is not sampled
  `open_OFull`, `roots_OFull`, `cnts_OFull`   at the written place `piOFull`
                 (Johnson/Desc/K12/Law/PlacesFull.lean), by Lean's kernel: a round of the test that
                 samples 51 positions opens the chain's own tree number 7 at the depth 13; the test
                 sends a root; of the first member's six rounds the second alone states a message
  `cut_head_O`   under the head the shared list is cut at the test's place, and the rounds in front
                 send 7 roots
  `asks_head_O`  at every due list of challenges the frame's list of the positions read of the
                 shared chain's tree number 7 has at most 51 members, each below 2 ^ 13
  `bud_first_O`  the bound, in the record's letters
  `front_count`, `drawsFit_cut`, `draws_front`, `cut_at_descN`   lemmas at a description as a letter
  `draws_stretch_O`   the member's own stretch of a due list has the declared form
  `some_at_O`, `meets_at_O`   "something" and `MeetsAt` at any challenges of the declared form
  `meets_due_O`  `MeetsAt` at the frame's own positions and the list's own stretch

By what. That no other round of the file's three chains opens that tree is the library's test
`BookPlan.once` (Johnson/Desc/BookPlan.lean), a clause of `FileDescription.planOk`, which is a field of the
head: `asks_at_block` (TreeInFront.lean), `asks_of_one` (ReadsOfTree.lean). The 7: `plain_free`
(Johnson/Loose/H2K12/FreeAtSeats.lean) and `nums_head_O`. The cut: `shared_cut_omega`
(Johnson/Desc/K12/Law/SitsChains.lean), `cut_at_place`.

Limits.
- 51 of 152: the bound is met with room. Nothing says that it could not be met with fewer random
  values, or that the equation fails beyond it.
- One list of challenges: one request. Nothing on the positions that several requests read.
- `treeAsks` is computed of the declared rounds and the challenges: that a run asks for no position
  beyond that list is the frame's own law, not shown here.
- The front is `bareFront chain m`, made of the stand, not the frame's front.
- The first member alone: `testBud` at the second member is not treated.
- All limits of Sim/MeetsOwnAtHead.lean but the one on written positions and challenges stand.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.MeetsOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session
import Johnson.Loose.H2K12.FreeAtSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Oracle)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St)
open H2K.Member (piOFull)
open H2K.JointK (laidOf pGomega omegaEntry guEntry sharedPre sharedEnd p14N)
open Johnson.G.OfPlan (rootsOf)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

variable {S Cl V W X Pb : Type}

/-! ## 1 Different numbers -/

theorem length_eraseDups : ∀ (n : ℕ) (l : List ℕ), l.length ≤ n → l.eraseDups.length ≤ l.length
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons, List.length_cons, List.length_cons]
    exact Nat.succ_le_succ (Nat.le_trans
      (length_eraseDups n _ (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ h)))
      (List.length_filter_le _ _))

theorem different_le (l : List ℕ) : different l ≤ l.length := length_eraseDups _ l (Nat.le_refl _)

/-! ## 2 The first stated message -/

/-- The fold's own table's message at the written place. -/
def ownTold : Oracle := { logLength := 13, words := 3, tenants := [H2U.maskTenant 0] }

theorem dealt_flat : ∀ (l : List Fmt.DeclaredRound) (A : List (List Oracle)) (R : List Oracle),
    ((l.foldl (fun (acc : List (List Oracle) × List Oracle) r =>
      (acc.2.take r.entry.roots :: acc.1, acc.2.drop r.entry.roots)) (A, R)).1.reverse).flatMap id =
      A.reverse.flatMap id ++ R.take (rootsOf l)
  | [], A, R => by
    show A.reverse.flatMap id = A.reverse.flatMap id ++ R.take 0
    rw [List.take_zero, List.append_nil]
  | r :: l, A, R => by
    rw [List.foldl_cons, dealt_flat l, List.reverse_cons, List.flatMap_append, List.append_assoc]
    refine congrArg _ ?_
    show (R.take r.entry.roots ++ []) ++ (R.drop r.entry.roots).take (rootsOf l) =
      R.take (r.entry.roots + rootsOf l)
    rw [List.append_nil, List.take_add]

theorem roots_OFull :
    (H2U.roundsOfNums piOFull.nums).map (fun l => decide (1 ≤ rootsOf l)) = some true := by
  decide +kernel

theorem first_told (g : ℕ) (os : List (List Oracle))
    (h : H2U.testOracles5 piOFull.nums g = some os) : ∃ rest, os.flatMap id = ownTold :: rest := by
  unfold H2U.testOracles5 at h
  have hr := roots_OFull
  cases hl : H2U.roundsOfNums piOFull.nums with
  | none =>
    rw [hl] at h
    cases h
  | some l =>
    rw [hl] at h hr
    obtain rfl := Option.some.inj h
    have h1 : 1 ≤ rootsOf l := of_decide_eq_true (Option.some.inj hr)
    obtain ⟨m, hm⟩ : ∃ m, rootsOf l = m + 1 := ⟨rootsOf l - 1, by omega⟩
    obtain ⟨T, hT⟩ : ∃ T, piOFull.nums.sentOracles g = ownTold :: T := ⟨_, rfl⟩
    rw [dealt_flat l [] _, hm, hT, List.take_succ_cons]
    exact ⟨_, rfl⟩

theorem p12At_cases (place : VerifiableInference.Desc.Place) (x : H2U.PlaceNums) :
    H2U.proximityTestParametersAt place x = H2U.noP12 place ∨
      ∃ os, H2U.testOracles5 x.nums x.firstGroup = some os ∧ (H2U.proximityTestParametersAt place x).nums = x.nums ∧
        (H2U.proximityTestParametersAt place x).oracles = os := by
  unfold H2U.proximityTestParametersAt
  split
  · exact Or.inl rfl
  · split
    · rename_i os ho
      exact Or.inr ⟨os, ho, rfl, rfl⟩
    · exact Or.inl rfl

/-! ## 3 At the written place -/

theorem open_OFull : (H2U.roundsOfNums piOFull.nums).map
    (fun l => decide (((1, 7), 51, 13) ∈ openedOf 1 l)) = some true := by
  decide +kernel

theorem cnts_OFull : ((thinOf piOFull).take (firstLen piOFull.nums.stages)).map (·.2.length) =
    [0, 1, 0, 0, 0, 0] := by
  decide +kernel

theorem counts_thin (p : P12) : (laidOf p).map (·.2.length) = (thinOf p).map (·.2.length) := by
  unfold thinOf
  rw [List.map_map]
  exact List.map_congr_left fun d _ => (List.length_map _).symm

/-! ## 4 Two lemmas at a description as a letter -/

/-- The number of trees in front, in the frame's letters. -/
theorem front_count {Xi : Type} {F : VerifiableInference.Desc.FileDescription Xi} (hpl : F.planOk = true)
    (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (hcut : F.shared.blocksInOrder = pre ++ b :: t)
    (n k : ℕ) (hn : n = (pre.flatMap (·.rounds)).length)
    (hk : rootsOf (pre.flatMap (·.rounds)) = k) :
    (((rowsOfChain F.shared.blocksInOrder).take n).map (·.2.length)).sum = k := by
  have hsh : ∀ x ∈ pre, x.shaped = true := fun x hx =>
    planOk_shaped hpl x (by rw [hcut]; exact List.mem_append_left _ hx)
  rw [hn, hcut, trees_in_front pre t b hsh, hk]

theorem drawsFit_cut : ∀ (A B : List Fmt.DeclaredRound) (R : List Fmt.Drawn),
    drawsFit (A ++ B) R = true → drawsFit A (R.take A.length) = true ∧
      drawsFit B (R.drop A.length) = true
  | [], _, _, h => ⟨rfl, h⟩
  | _ :: _, _, [], h => by simp [drawsFit] at h
  | a :: A, B, x :: R, h => by
    have h' : (drawFit a x && drawsFit (A ++ B) R) = true := h
    rw [Bool.and_eq_true] at h'
    obtain ⟨i1, i2⟩ := drawsFit_cut A B R h'.2
    refine ⟨?_, i2⟩
    show (drawFit a x && drawsFit A (R.take A.length)) = true
    rw [h'.1, i1]
    rfl

/-- The stretch of a due list at the first rounds of a block of the shared list. -/
theorem draws_front {Xi : Type} {F : VerifiableInference.Desc.FileDescription Xi}
    (pre t : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (hcut : F.shared.blocksInOrder = pre ++ b :: t)
    (A B : List Fmt.DeclaredRound) (hb : b.rounds = A ++ B) (ρ : Draws) (hρ : ρ.due F = true) :
    drawsFit A ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take A.length) = true := by
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true := hρ.1.1.2
  rw [hcut, List.flatMap_append, List.flatMap_cons, hb, List.append_assoc] at h2
  exact (drawsFit_cut _ _ _ (drawsFit_cut _ _ _ h2).2).1

/-! ## 5 Under the head: the place in the list -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {pO : P12}

/-- **The seated place's first stated message; and its `free`, as the place's numbers have it.** -/
theorem oracles_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (∃ rest, pO.oracles.flatMap id = ownTold :: rest) ∧
      ∀ nO, Np.O = some nO → nO.nums = piOFull.nums := by
  have hn := nums_head_O h hO
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  rcases p12At_cases ⟨2, none, 10, .K12⟩ nO with e | ⟨os, ho, e1, e2⟩
  · exfalso
    have hl := congrArg (fun N : H2U.TestNums => N.stages.length) hn
    unfold pGomega at hl
    rw [e] at hl
    exact absurd hl (by decide)
  · have hx : nO.nums = piOFull.nums := e1.symm.trans hn
    refine ⟨?_, fun nO' h' => ?_⟩
    · rw [hx] at ho
      show ∃ rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).oracles.flatMap id = _
      rw [e2]
      exact first_told _ os ho
    · obtain rfl : nO = nO' := Option.some.inj (h1.symm.trans h')
      exact hx

/-- The library's cut of the shared list, at a description as a letter. -/
theorem cut_at_descN {mk : ProofFile.LinksBy} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst)
    (hF : F = H2K.JointK.descN o mk guardedProximityTestParts Zp N c) (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    ∃ (pre₀ t₀ : List (Block F.S₂ F.Cl)) (ω : Block F.S₂ F.Cl),
      F.shared.blocksInOrder = pre₀ ++ ω :: t₀ ∧ ω.place = ⟨2, none, 10, .K12⟩ ∧
        rootsOf (pre₀.flatMap (·.rounds)) = rootsOf
          ((sharedPre ProofFile.Cl Zp.p.chains (p14N Zp N) N ++ [guEntry ProofFile.Cl N]).flatMap
            (·.rounds)) := by
  subst hF
  exact ⟨_, _, _, H2K.JointK.shared_cut_omega ProofFile.Cl _ _ N nO hO,
    H2K.JointK.omegaEntry_place ProofFile.Cl nO, rfl⟩

/-- **The shared list cut at the test's place; the rounds in front send 7 roots.** -/
theorem cut_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    ∃ (pre₀ t₀ : List (Block St ProofFile.Cl)) (ω : Block St ProofFile.Cl),
      (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre₀ ++ ω :: t₀ ∧ ω.place = pO.place ∧
        rootsOf (pre₀.flatMap (·.rounds)) = 7 := by
  obtain ⟨c', e, _, hp', _⟩ := row_at_head h
  have hx := (oracles_head_O h hO).2
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  obtain ⟨pre₀, t₀, ω, a1, a2, a3⟩ := cut_at_descN (P5J.F0T o Zp Np cF) e nO h1
  refine ⟨pre₀, t₀, ω, a1, a2.trans (H2K.JointK.place_of_p12At _ _).symm, a3.trans ?_⟩
  rw [← ((H2K.JointK.plain_free o Z.pol Z.lay Z.KL Zp h.laid.pub ProofFile.pureRoad.links Np c'
    h.laid.places hp').2.1 nO h1).2, hx nO h1]
  rfl

/-- **The positions read of the fold's own tree, at every due list of challenges.** -/
theorem asks_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (ρ : Draws)
    (hρ : ρ.due (P5J.F0T o Zp Np cF) = true) :
    (treeAsks (P5J.F0T o Zp Np cF) ρ 1 7).length ≤ 51 ∧
      ∀ x ∈ treeAsks (P5J.F0T o Zp Np cF) ρ 1 7, x < 2 ^ 13 := by
  obtain ⟨pre₀, t₀, ω, hcut, hpl, h7⟩ := cut_head_O h hO
  obtain ⟨b, hf, hb, hr, hor⟩ := find_gomega h hO
  obtain ⟨p, t, hbt⟩ : ∃ p t : List (Block St ProofFile.Cl),
      (P5J.F0T o Zp Np cF).shared.blocksInOrder = p ++ b :: t :=
    List.append_of_mem (List.mem_of_find?_eq_some hf)
  have hpp : p = pre₀ := cut_at_place h.laid.planOk p pre₀ t t₀ b ω hbt hcut (hb.trans hpl.symm)
  subst hpp
  have hk := planOk_head_O h hO
  obtain ⟨rest, hX⟩ := (oracles_head_O h hO).1
  have hX' : b.oracles.flatMap id = ownTold :: rest := by
    rw [hor, VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts pO hk]
    exact hX
  have he : ((1, rootsOf (p.flatMap (·.rounds))), 51, 13) ∈ openedOf 1 b.rounds := by
    have ho := open_OFull
    rw [← nums_head_O h hO, VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts pO hk] at ho
    rw [h7, hr]
    exact of_decide_eq_true (Option.some.inj ho)
  have key : (treeAsks (P5J.F0T o Zp Np cF) ρ 1 (rootsOf (p.flatMap (·.rounds)))).length ≤ 51 ∧
      ∀ x ∈ treeAsks (P5J.F0T o Zp Np cF) ρ 1 (rootsOf (p.flatMap (·.rounds))), x < 2 ^ 13 :=
    asks_at_block h.laid.planOk p t b hbt ownTold rest hX' rfl 51 13 he ρ hρ
  rw [h7] at key
  exact key

/-! ## 6 The bound, in the record's letters -/

section Job
variable (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (Js : SimJob Pb)
  (J : TestJob W X) (hp : J.p = pO)

include h hO hp in
theorem cnts_head_O :
    (firstMember (V := V) J Js).rounds.map (·.2.length) = [0, 1, 0, 0, 0, 0] := by
  subst hp
  show ((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.2.length) = _
  rw [List.map_take, counts_thin, thin_head_O h hO, ← List.map_take, nums_head_O h hO]
  exact cnts_OFull

include h hO hp in
/-- **`testBud` at the first member, at the positions that the description's declared rounds read,
at every due list of challenges.** n: the rounds of the shared chain in front of the member. -/
theorem bud_first_O (hJ : Js.p = pO) (fs : List (Fall St)) (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    (pre t : List (Block St ProofFile.Cl)) (n : ℕ)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length +
      ((σ.row.take (firstMember (V := V) J Js).number).map fun x => x.1.moves.length).sum)
    (ρ : Draws) (hρ : ρ.due (P5J.F0T o Zp Np cF) = true) :
    testBud Js (firstMember (V := V) J Js).number
      ((ρ.shared.drop n).take (firstMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks (P5J.F0T o Zp Np cF) ρ 1)
        ((firstMember (V := V) J Js).rounds.map (·.2.length))
        (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  obtain ⟨pre₀, t₀, ω, hcut₀, hpl, h7⟩ := cut_head_O h hO
  have hbp : σ.block.place = pO.place := by
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hσ'
    have := beq_iff_eq.1
      (List.find?_some (p := fun b : Block St ProofFile.Cl => b.place == J.p.place) hb)
    rw [hp] at this
    exact this
  have hpp : pre = pre₀ :=
    cut_at_place h.laid.planOk pre pre₀ t t₀ σ.block ω hcut hcut₀ (hbp.trans hpl.symm)
  subst hpp
  have hn' : n = (pre.flatMap (·.rounds)).length := hn
  have hN : (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum = 7 :=
    front_count h.laid.planOk pre t σ.block hcut n 7 hn' h7
  rw [hN, cnts_head_O (V := V) h hO Js J hp]
  refine testBud_own Js _ _ ?_
  obtain ⟨a1, a2⟩ := asks_head_O h hO ρ hρ
  rw [s₀_head_O h hO Js hJ]
  show ((treeAsks (P5J.F0T o Zp Np cF) ρ 1 7).all (fun x => decide (x < 2 ^ 13)) &&
    decide (different (treeAsks (P5J.F0T o Zp Np cF) ρ 1 7) ≤ 152)) = true
  rw [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun x hx => decide_eq_true (a2 x hx),
    Nat.le_trans (different_le _) (Nat.le_trans a1 (by decide))⟩

end Job

/-! ## 7 The list's own stretch of challenges -/

section Due
variable (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (Js : SimJob Pb)
  (J : TestJob W X) (hp : J.p = pO) (hfr : J.fresh.isNone = true)

include h hO hp in
/-- The member's own stretch of a due list has the declared form. -/
theorem draws_stretch_O (b : Block St ProofFile.Cl) (pre t : List (Block St ProofFile.Cl))
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ b :: t)
    (hr : b.rounds = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds)
    (hor : b.oracles = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles) (ρ : Draws)
    (hρ : ρ.due (P5J.F0T o Zp Np cF) = true) :
    drawsFit ((firstMember (V := V) J Js).rounds.map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take
        (firstMember (V := V) J Js).rounds.length) = true := by
  subst hp
  have hk := planOk_head_O h hO
  have hl : (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length ≤
      (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).oracles.length := by
    have hs := shaped_len b (planOk_shaped h.laid.planOk b
      (by rw [hcut]; exact List.mem_append_right _ List.mem_cons_self))
    rw [hr, hor] at hs
    exact Nat.le_of_eq hs.symm
  have hz : b.rounds = (laidOf J.p).map (·.1) := by
    rw [hr, ← zip_laid J.p hk, List.map_fst_zip hl]
  have hsplit : b.rounds = ((laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1) ++
      ((laidOf J.p).drop (firstLen J.p.nums.stages)).map (·.1) := by
    rw [hz, ← List.map_append, List.take_append_drop]
  have h4 := draws_front pre t b hcut _ _ hsplit ρ hρ
  rw [List.length_map] at h4
  exact h4

include h hO hp hfr in
/-- What the part shows is something, at any challenges of the declared form. -/
theorem some_at_O (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (m : ProofFile.Honest.Mid W X) (ds : List Fmt.Drawn)
    (hd : drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true)
    (asks : List (List (List ℕ))) (c : (firstMember J Js : Member V W X Pb).part.Coins) :
    (σ.shows φ (firstMember J Js) c m ds asks).isSome = true := by
  have T := firstPubOwn_at h hO Js J hp hfr hJ ho
  have hlen0 := drawsFit_length _ _ hd
  subst hp
  have hst : J.p.nums.stages = piOFull.nums.stages := congrArg (·.stages) (nums_head_O h hO)
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  have hlen : ds.length = firstLen J.p.nums.stages := by
    rw [hlen0, List.length_map]
    show ((laidOf J.p).take (firstLen J.p.nums.stages)).length = _
    rw [List.length_take]
    exact Nat.min_eq_left T.enough
  rw [shows_first φ σ J Js s t rest m (byNo ds) ds
    ⟨hst.trans hlit, T.enough, (formPub_of_B _ s t rest (hst.trans hlit) T.form).sorts, T.tables,
      hlen, fun n hn => (List.getD_eq_getElem _ _ hn).symm⟩ c asks]
  rfl

include h hO hp hfr in
/-- **`MeetsAt` at any challenges of the declared form and any positions within the bound.** -/
theorem meets_at_O (hJ : Js.p = pO) (ho : Js.own = true) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X)
    (ds : List Fmt.Drawn)
    (hd : drawsFit ((firstMember (V := V) J Js).rounds.map (·.1)) ds = true)
    (asks : List (List (List ℕ)))
    (hb : testBud Js (firstMember (V := V) J Js).number ds asks) :
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
      (bareFront chain m) ds asks :=
  meetsAt_of_exact (exact_at_O h hO Js J hp hfr hJ ho φ σ chain firstTree) ca m
    (bareFront chain m) ds asks (testOn_first φ J Js ca m (bareFront chain m))
    (seen_bareFront chain m) hd hb
    (holds_of_quiet (bareFront chain m) chain firstTree _ ds (quiet_head_O (V := V) h hO Js J hp))
    (stop_first (V := V) J Js (φ.sees m.st.input) m.loc ds)
    (some_at_O h hO Js J hp hfr hJ ho φ σ m ds hd asks)

include h hO hp hfr in
/-- **`MeetsAt` at the positions that the description's declared rounds read and at the list's own
stretch of challenges, at every due list.** -/
theorem meets_due_O (hJ : Js.p = pO) (ho : Js.own = true) (fs : List (Fall St))
    (σ : Side St ProofFile.Cl V W X Pb) (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder J Js fs = some σ)
    (pre t : List (Block St ProofFile.Cl)) (n : ℕ)
    (hcut : (P5J.F0T o Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length +
      ((σ.row.take (firstMember (V := V) J Js).number).map fun x => x.1.moves.length).sum)
    (ρ : Draws) (hρ : ρ.due (P5J.F0T o Zp Np cF) = true) (φ : Face V W Pb) (chain firstTree : ℕ)
    (ca : CsAll (firstMember (V := V) J Js).part.carries) (m : ProofFile.Honest.Mid W X) :
    MeetsAt φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js) ca m
      (bareFront chain m) ((ρ.shared.drop n).take (firstMember (V := V) J Js).rounds.length)
      (asksFrom (treeAsks (P5J.F0T o Zp Np cF) ρ 1)
        ((firstMember (V := V) J Js).rounds.map (·.2.length))
        (((rowsOfChain (P5J.F0T o Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  have hb := bud_first_O h hO Js J hp hJ fs σ hσ pre t n hcut hn ρ hρ
  have hr : σ.block.rounds = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds ∧
      σ.block.oracles = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles := by
    obtain ⟨b, hf, _, hr, hor⟩ := find_gomega h hO
    have hσ' := hσ
    unfold testSide Side.seated at hσ'
    rw [hp, hf] at hσ'
    obtain rfl := Option.some.inj hσ'
    exact ⟨hr, hor⟩
  have hn' : n = (pre.flatMap (·.rounds)).length := hn
  have hd := draws_stretch_O (V := V) h hO Js J hp σ.block pre t hcut hr.1 hr.2 ρ hρ
  rw [← hn'] at hd
  exact meets_at_O h hO Js J hp hfr hJ ho φ σ chain firstTree ca m _ hd _ hb

end Due

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.length_eraseDups
#print axioms ProofFile.Honest.K12.Light.different_le
#print axioms ProofFile.Honest.K12.Light.ownTold
#print axioms ProofFile.Honest.K12.Light.dealt_flat
#print axioms ProofFile.Honest.K12.Light.roots_OFull
#print axioms ProofFile.Honest.K12.Light.first_told
#print axioms ProofFile.Honest.K12.Light.p12At_cases
#print axioms ProofFile.Honest.K12.Light.open_OFull
#print axioms ProofFile.Honest.K12.Light.cnts_OFull
#print axioms ProofFile.Honest.K12.Light.counts_thin
#print axioms ProofFile.Honest.K12.Light.front_count
#print axioms ProofFile.Honest.K12.Light.drawsFit_cut
#print axioms ProofFile.Honest.K12.Light.draws_front
#print axioms ProofFile.Honest.K12.Light.oracles_head_O
#print axioms ProofFile.Honest.K12.Light.cut_at_descN
#print axioms ProofFile.Honest.K12.Light.cut_head_O
#print axioms ProofFile.Honest.K12.Light.asks_head_O
#print axioms ProofFile.Honest.K12.Light.cnts_head_O
#print axioms ProofFile.Honest.K12.Light.bud_first_O
#print axioms ProofFile.Honest.K12.Light.draws_stretch_O
#print axioms ProofFile.Honest.K12.Light.some_at_O
#print axioms ProofFile.Honest.K12.Light.meets_at_O
#print axioms ProofFile.Honest.K12.Light.meets_due_O
