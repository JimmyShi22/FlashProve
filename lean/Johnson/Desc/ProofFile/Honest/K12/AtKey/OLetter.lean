-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OLetter.lean: the new trees of every member of the filled key thread (`TR`, see
OStep.lean's head), at any letter; and so the letter `SaidField TR BaseNil` is carried over every member. A rule for a
file asks this at `SaidField` (`fromThreads_field`) or at `SaidWalk` (`fromThreads_walk`): the `treesNext_` laws serve both.

  `fresh_nil_of_no_trees`    a member that states no tree has no new source
  `member_counts`            the eight's trees, by the kernel
  `treesNext_no_trees`       members 0, 1, 3, 4, 6, 7, 8, 11: no new tree
  `treesNext_in_eight`       members 1 to 8, by `asks_key`
  `treesNext_at_nine`, `treesNext_at_ten`   the two tests
  `saidNext_every_member`    the letter over every member

The premises, with who pays them. hsource, scope: `key_sourced` with `later_sourced`. hK₀: `full_made`. hsend: `send_keyOf`.
hsp: the key prover in scope; inside `saidNext_every_member` it follows from hlin. F, hlin, hN: those of `asks_key`.
hno: no part of the thread's halves stops: `no_stop_at_key` (K12/AtKey/UStep.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `treesNext_in_eight`, `treesNext_at_nine`, `treesNext_at_ten`,
  `saidNext_every_member`, `saidNext_at_ten` bear this label; the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
  Their ground: the thread's pair is a premise of `TreesNext` and `SaidNext`; F ties the input to the coins.
- That a stand is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OField
import E2E.KeyAsksKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source Claim sharedTests keyAsProof)
open Desc.K14 (St blocksOr)
open Desc.K14.Honest (Eight FlatOf flatOf_carried)
open ProofFile.Honest
open ProofFile.Honest.K14 (Plan2 WitLens FiveFields k14_asks)
open AtPublicFiles.AtFiles (KeySourced flat₂)
open AtPublicFiles.AtFiles.Full (QK PF omega_full par_sourced)
open AtPublicFiles.KeySharedThread (parKey randKey sentKey lettersKey plan_key)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.HalvesAreJobs (pU pO trees_nine_at place_omega)
open AtPublicFiles.KeyLay (withTestsOnUAndOmega)
open AtPublicFiles.TableFilled (TR ttF arm_U trees_ten_real)
open AtPublicFiles.TreesAtTenKey (block_ten)
open AtPublicFiles.KeyDoorNine (seat_nine)
open AtPublicFiles.KeyAsksKey (asks_key)
open AtPublicFiles.Stops (NoStop chainStopAt_none)

/-- The eight's trees, by the kernel. -/
theorem member_counts :
    (blocksOr QK).map (fun b => (b.oracles.flatMap id).length) = [0, 1, 0, 0, 2, 0, 0, 0] := by
  decide +kernel

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A member that states no tree has no new source.** -/
theorem fresh_nil_of_no_trees (T : Thread Bk S Cl V W X Pb) {b : ℕ} {blk : Block S Cl}
    (hblk : T.bs[b]? = some blk) (h : blk.oracles.flatMap id = []) : T.fresh b = [] := by
  have e : treesTo T.bs (b + 1) = treesTo T.bs b := by
    unfold treesTo
    rw [List.take_add_one, List.flatMap_append, hblk]
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [h]
    simp
  have eh : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [e]
  unfold Thread.fresh
  rw [eh, List.filter_eq_nil_iff]
  intro σ hσ
  simp [hσ]

end

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)
  (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)

/-- The letter at the filled thread. -/
abbrev letterAt : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop :=
  SaidField (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) BaseNil

/-- The last member is the chain's end. -/
theorem end_member :
    (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[11]? =
      some (H2K.JointK.keySharedEnd Xs.chains PF) := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w
  have hl : ((H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]) ++
      [H2K.JointK.keyOmega (PF.O.getD PF.U)]).length = 11 := by
    unfold H2K.JointK.keySharedPre
    rw [List.length_append, List.length_append, List.length_cons, List.length_map,
      AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : flat₂ Xs.chains PF = ((H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]) ++
      [H2K.JointK.keyOmega (PF.O.getD PF.U)]) ++ H2K.JointK.keySharedEnd Xs.chains PF :: [] := by
    have h0 : flat₂ Xs.chains PF = (H2K.JointK.keySharedPre Xs.chains PF ++ [H2K.JointK.keyGu PF]) ++
        H2K.JointK.keyOmega (PF.O.getD PF.U) :: [H2K.JointK.keySharedEnd Xs.chains PF] :=
      H2K.JointK.keyShared_cut_omega _ _ _ omega_full
    rw [h0]
    simp
  rw [hO.bs]
  show (flat₂ Xs.chains PF)[11]? = _
  rw [hc]
  exact AtPublicFiles.KeyDoorNine.get_at _ _ _ 11 hl

/-- **Members 0, 1, 3, 4, 6, 7, 8 and 11 have no new tree.** -/
theorem treesNext_no_trees (e : parKey Xs PF = QK) {b : ℕ} (hb : b ∈ [0, 1, 3, 4, 6, 7, 8, 11]) :
    TreesNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said b := by
  have F := flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs PF) B.b1 B.b2 B.b3 B.b4 B.b5
    B.b6 B.b7 B.b8 (sharedTests PF) VerifiableInference.Desc.K12.Seat.last B.made
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, hxs, l0, l1, -, l3, l4, -, l6, l7, l8⟩ := F
  have hbs : (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := hxs
  have hc : [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8].map
      (fun b => (b.oracles.flatMap id).length) = [0, 1, 0, 0, 2, 0, 0, 0] := by
    rw [← AtPublicFiles.AtFiles.Full.blocksOr_eight B, e]
    exact member_counts
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hc
  obtain ⟨c1, -, c3, c4, -, c6, c7, c8⟩ := hc
  have at_front : ∀ {n : ℕ} {x : Block _ _}, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[n]? =
      some x → x.oracles.flatMap id = [] →
      TreesNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said n := fun h1 h2 =>
    treesNext_of_fresh_nil _ (fresh_nil_of_no_trees _ h1 h2)
  have hmem : b = 0 ∨ b = 1 ∨ b = 3 ∨ b = 4 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 11 := by
    simpa using hb
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact at_front (x := x0) (by rw [hbs]; rfl) (by rw [l0.oracles]; rfl)
  · exact at_front (x := x1) (by rw [hbs]; rfl)
      (by rw [l1.oracles]; exact List.eq_nil_of_length_eq_zero c1)
  · exact at_front (x := x3) (by rw [hbs]; rfl)
      (by rw [l3.oracles]; exact List.eq_nil_of_length_eq_zero c3)
  · exact at_front (x := x4) (by rw [hbs]; rfl)
      (by rw [l4.oracles]; exact List.eq_nil_of_length_eq_zero c4)
  · exact at_front (x := x6) (by rw [hbs]; rfl)
      (by rw [l6.oracles]; exact List.eq_nil_of_length_eq_zero c6)
  · exact at_front (x := x7) (by rw [hbs]; rfl)
      (by rw [l7.oracles]; exact List.eq_nil_of_length_eq_zero c7)
  · exact at_front (x := x8) (by rw [hbs]; rfl)
      (by rw [l8.oracles]; exact List.eq_nil_of_length_eq_zero c8)
  · exact at_front (end_member K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) rfl

include hK₀ in
/-- **At a member of the eight the new trees are the thread's tables**: at the two sendings this is what they
send. -/
theorem treesNext_in_eight {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = ProofFile.Honest.K14.planData (parKey Xs PF))
    (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant)
    (hno : NoStop (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hs) {b : ℕ} (h1 : 1 ≤ b)
    (h8 : b ≤ 8) : TreesNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said b := by
  have hap : [ProofFile.Honest.K14.place 1, ProofFile.Honest.K14.sendPlace 2, ProofFile.Honest.K14.place 4,
      ProofFile.Honest.K14.sendPlace 5, ProofFile.Honest.K14.place 7, ProofFile.Honest.K14.place 8,
      (withTestsOnUAndOmega K₁ pU pO).onU.place, (withTestsOnUAndOmega K₁ pU pO).onOmega.place].Nodup := by
    have pa : (withTestsOnUAndOmega K₁ pU pO).onU.place = AtPublicFiles.KeyBook.foldedTestPlace := AtPublicFiles.KeyPlaysAt.place_on
    have pb : (withTestsOnUAndOmega K₁ pU pO).onOmega.place = AtPublicFiles.KeyBook.omegaTestPlace := place_omega
    rw [pa, pb]
    decide
  obtain ⟨layO, h⟩ := asks_key Xs Nr PF K₀ (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ tk (ttF K₀ Xs K₁ B own₀) rest
    Kp Vd w hsource scope hK₀ F hlin hsend hap hN
  exact treesNext_of_playsS _ (playsS_of _ _ (k14_asks h (fun _ _ _ => none) b h1 h8).1)
    fun blk _ m ds => chainStopAt_none _ hno [blk] _ _

/-- **At member 9 the new trees are the test's.** -/
theorem treesNext_at_nine (e : parKey Xs PF = QK) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    TreesNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 9 := by
  intro blk hblk k s m E ds y cols hA _ hd hM
  have h9 : (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[9]? = some (H2K.JointK.keyGu PF) :=
    (seat_nine Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
      (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w B).1
  obtain rfl : blk = H2K.JointK.keyGu PF := Option.some.inj (hblk.symm.trans h9)
  exact trees_nine_at Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w e
    B hsend hsp own₀ (fun _ hτ => arm_U K₀ Xs K₁ B own₀ hτ) k s m E ds y cols hA hd hM

/-- **At member 10 the new trees are the test's.** -/
theorem treesNext_at_ten (e : parKey Xs PF = QK) (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    TreesNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 := by
  intro blk hblk k s m E ds y cols hA _ hd hM
  have h10 : (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).bs[10]? =
      some (H2K.JointK.keyOmega (PF.O.getD PF.U)) :=
    block_ten Xs Nr K₁ ℓ Nm Mg₀ K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀) rest Kp Vd w B
  obtain rfl : blk = H2K.JointK.keyOmega (PF.O.getD PF.U) := Option.some.inj (hblk.symm.trans h10)
  exact trees_ten_real K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hsend hsp k s m E ds y cols hA hd hM

include hK₀ in
/-- **The letter over every member.** -/
theorem saidNext_every_member {Z : VerifierAndGoals.PublicFiles} (hsource : KeySourced Z Xs Nr PF)
    (scope : VerifierAndGoals.InScope Z = true)
    (F : FiveFields (parKey Xs PF)
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w).valid
      (lettersKey Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
        (tbKey (parKey Xs PF) K₁.weights (randKey K₁) tk (ttF K₀ Xs K₁ B own₀)) rest Kp Vd w).stored
      K₁.weights (randKey K₁))
    (hlin : K₁.lin = ProofFile.Honest.K14.planData (parKey Xs PF))
    (hsend : K₁.send = ⟨parKey Xs PF, 0⟩)
    (hN : Function.Injective Nm.tenant)
    (hno : NoStop (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).hs) (b : ℕ) :
    SaidNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
      (letterAt K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) b := by
  have e : parKey Xs PF = QK := par_sourced hsource scope
  have hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).planOk = true := hsource.named.plan
  obtain ⟨layO, hQ⟩ := plan_key hsource scope
  have hsp : K₁.lin.S.sharedSplitNeeded = true := by
    rw [hlin]
    exact hQ.facts.two
  intro blk hblk
  have hj := lt_of_member _ hblk
  rw [members_of_thread K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀] at hj
  refine saidNext_at_member K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hp hj ?_ blk hblk
  have hall : b = 9 ∨ b = 10 ∨ (1 ≤ b ∧ b ≤ 8) ∨ b = 0 ∨ b = 11 := by omega
  rcases hall with rfl | rfl | ⟨h1, h8⟩ | rfl | rfl
  · exact treesNext_at_nine K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ e hsend hsp
  · exact treesNext_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ e hsend hsp
  · exact treesNext_in_eight K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ hsource scope F hlin hsend
      hN hno h1 h8
  · exact treesNext_no_trees K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ e (by simp)
  · exact treesNext_no_trees K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ e (by simp)

include hK₀ in
/-- **The letter over member 10**, with the thread's readers, from the law on its new trees. -/
theorem saidNext_at_ten (e : parKey Xs PF = QK)
    (hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).planOk = true)
    (hsend : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) :
    SaidNext (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀)
      (letterAt K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) 10 :=
  saidNext_at_member K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hp (by omega)
    (treesNext_at_ten K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ _ e hsend hsp)

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.member_counts
#print axioms ProofFile.Honest.K12.AtKey.fresh_nil_of_no_trees
#print axioms ProofFile.Honest.K12.AtKey.end_member
#print axioms ProofFile.Honest.K12.AtKey.treesNext_no_trees
#print axioms ProofFile.Honest.K12.AtKey.treesNext_in_eight
#print axioms ProofFile.Honest.K12.AtKey.treesNext_at_nine
#print axioms ProofFile.Honest.K12.AtKey.treesNext_at_ten
#print axioms ProofFile.Honest.K12.AtKey.saidNext_every_member
#print axioms ProofFile.Honest.K12.AtKey.saidNext_at_ten
