-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/TreesAtTenKey.lean

trees_of_thr_ten (K12/TreesAtTen.lean) CALLED AT MEMBER 10 OF THE KEY's SHARED THREAD, at the table tbKey
with a letter tt, at the parts with the two halves, as TreesAtNine.lean and HalvesAreJobs.lean do at 9.

  trees_own_moved   trees_of_thr_ten without hrs and hst: they follow from Moved, hhalf and two stages
  count_O           the test on G_omega declares four trees. By the kernel
  trees_ten_sign    hT AT MEMBER 10, TO THE SIGN: OWN 7 TO 10, THE OTHER FOUR OF THE EIGHT
  trees_ten_at      the same with the field as a spare premise, for PlaysAtTen.lean

PREMISES OF trees_ten_sign, and who pays each.
- e, B: par_sourced, plan_key in the goals' scope. hs, hsp: as trees_nine_at.
- own₀: any value of X₀.
- h7, htt: THE ARMS: own 7 is ownTbl, own 8 to 10 are testTbl, at n₀ = 43 and the constant yes. Premises;
  equations of functions, with no k, m, w, h in them. ownTbl's terms are at
  K12/OwnTbl.lean's head.
THE FIELD is no premise of this law: Moved holds a play that returned, and at the field none a guarded
step's does not (opened_of_play). It is Plays that cannot stand bare at 10: Plays asks a return at the field
none, so it is false wherever playable; what a letter must give is PlaysS's hop (PlaysAtTen.lean).

HAD IN THE PROOF, NOT PREMISES: hblk by the chain's cut. hfresh by text. hR: rows_heard_KO. hk, two stages,
hcount: hk_O, len_O, count_O, pO_full. hpl: place_go. hhalf: find_O. htable's and hfixed's counts:
trees_key_O, rounds_key_O, sendings_count; hfixed: fixed_own, fixed_key_O.

Limits.
- A conditional: that Thr stands at 10 and that Moved is had: not said here.
- plays_of_playsOn can take trees_ten_sign as its hT by the sign; no PlaysOn from A := Thr is to be had here.
- The thread's table is tbKey (E2E/KeyTreesKey.lean). No filling of tt is typed here.
- At parKey by e. NOT IN FRONT OF A LAW OVER COINS: the laws it calls bear that label.
- Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.HalvesAreJobs
import E2E.KeyFixedLinesO
import Johnson.Desc.ProofFile.Honest.K12.TreesAtTen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.TreesAtTenKey
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (flat₂)
open AtPublicFiles.AtFiles.Full (QK PF omega_full)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyTblTrial (sendings_count)
open AtPublicFiles.KeyTreesKey (treesOf5)
open AtPublicFiles.KeyFixedLines (trees_key_O rounds_key_O fixed_key_O fixed_own)
open AtPublicFiles.KeyLay (rows_heard_KO hk_O len_O withTestsOnUAndOmega wtOf rdOf)
open AtPublicFiles.TreesAtNine (TN)
open AtPublicFiles.HalvesAreJobs (pU pO pO_full JO place_go find_O)
open H2K.Member (piKOFull)
open H2K.JointK (keyGu keyOmega keySharedPre keySharedEnd keyShared_cut_omega)

/-- **trees_of_thr_ten without hrs and hst.** -/
theorem trees_own_moved {S Cl W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl Empty W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh = none) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (h2 : 2 ≤ J.p.nums.stages.length)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J).needsField)
    (hcount : (blk.oracles.flatMap id).length = J.p.nums.stages.length)
    (own₀ : X)
    (htable₀ : T.table (.own (treesTo T.bs b)) =
      ownTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true))
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + (τ + 1))) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed₀ : T.fixed (.own (treesTo T.bs b)) = T.front + roundsTo T.bs b + 1)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + (τ + 1))) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E →
      drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
      T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT hd hMv σ hσ
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, -⟩, -⟩ := hMv'
  obtain ⟨ho, hr⟩ := ProofFile.Honest.Small.member_lengths hhalf hl
  rw [needsField_rounds] at hr
  obtain ⟨s, t, rest, hst⟩ : ∃ a b r, J.p.nums.stages = a :: b :: r := by
    cases hh : J.p.nums.stages with
    | nil =>
      rw [hh] at h2
      simp only [List.length_nil] at h2
      omega
    | cons a u =>
      cases u with
      | nil =>
        rw [hh] at h2
        simp only [List.length_cons, List.length_nil] at h2
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hzl := ProofFile.Honest.Small.zip_length ho hr
  have l1 : (firstPart J : Part Empty W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part Empty W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part Empty W X).moves.length +
      ((restPart J : Part Empty W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  exact trees_of_thr_ten T hblk J hfresh hR hk s t rest hst hpl hhalf hrs hcount own₀ htable₀ htable
    hfixed₀ hfixed k st m E ds y cols hT hd hMv σ hσ

/-- The test on G_omega declares four trees. By the kernel. -/
theorem count_O : ((keyOmega (PF.O.getD PF.U)).oracles.flatMap id).length = 4 := by
  decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **Member 10 is the test on G_omega, at the thread's own bs.** -/
theorem block_ten (B : Eight (parKey Xs PF)) :
    (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).bs[10]? =
      some (keyOmega (PF.O.getD PF.U)) := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀
    (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w
  have hp : (keySharedPre Xs.chains PF ++ [keyGu PF]).length = 10 := by
    unfold keySharedPre
    rw [List.length_append, List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : flat₂ Xs.chains PF = (keySharedPre Xs.chains PF ++ [keyGu PF]) ++
      keyOmega (PF.O.getD PF.U) :: [keySharedEnd Xs.chains PF] :=
    keyShared_cut_omega _ _ _ omega_full
  rw [hO.bs]
  show (flat₂ Xs.chains PF)[10]? = _
  rw [hc]
  exact AtPublicFiles.KeyDoorNine.get_at _ _ _ 10 hp

/-- **hT AT MEMBER 10, to the sign: the new trees, own 7 to 10.** -/
theorem trees_ten_sign (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (h7 : tt 7 = ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true))
    (htt : ∀ τ, τ < 3 → tt (8 + τ) = testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) τ) :
    ∀ k s m E ds y cols,
      Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 10 k s m E →
      drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds = true →
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Moved
        (keyOmega (PF.O.getD PF.U)) k m E ds y cols →
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Trees
        ((TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).fresh 10) k y.2
        (E.add y.1) := by
  have hc3 := sendings_count
  rw [← e] at hc3
  have hp : (JO Xs K₁ B).p = piKOFull := AtPublicFiles.HalvesAreJobs.pO_full
  have hlen : (JO Xs K₁ B).p.nums.stages.length = 4 := by
    rw [hp]
    exact len_O
  have e7 := trees_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt)
    rest Kp Vd w e B
  have e43 := rounds_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt)
    rest Kp Vd w e B
  have h0 : (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).front = 0 := rfl
  have hhalf : ((TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hs.find? fun g =>
      g.place == (keyOmega (PF.O.getD PF.U)).place) =
      some (proverSideOfProximityTest (JO Xs K₁ B) : Placed Empty (Common W₀ Rc TableKey) X₀).needsField :=
    find_O Xs K₁ B hs hsp
  refine trees_own_moved _ (block_ten Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w B) (JO Xs K₁ B) rfl
    (rows_heard_KO ⟨parKey Xs PF, 0⟩ pU pO [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8]
      (wtOf K₁) (rdOf K₁))
    (by rw [hp]; exact hk_O) (by omega) (place_go Xs K₁ B) hhalf ?_ own₀ ?_ ?_ ?_ ?_
  · rw [count_O, hlen]
  · rw [e7, e43, h0, Nat.zero_add]
    show (if 7 < treesU (parKey Xs PF) then _ else
      if 7 < treesU (parKey Xs PF) + treesOf5 (parKey Xs PF) then _ else tt 7) = _
    rw [if_neg (by omega), if_neg (by omega)]
    exact h7
  · intro τ hτ
    rw [hlen] at hτ
    have hτ3 : τ < 3 := by omega
    rw [e7, e43, h0, Nat.zero_add]
    show (if 7 + (τ + 1) < treesU (parKey Xs PF) then _ else
      if 7 + (τ + 1) < treesU (parKey Xs PF) + treesOf5 (parKey Xs PF) then _ else
        tt (7 + (τ + 1))) = _
    rw [if_neg (by omega), if_neg (by omega), show 7 + (τ + 1) = 8 + τ by omega]
    exact htt τ hτ3
  · rw [e7, e43, h0, Nat.zero_add]
    exact fixed_own Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp
      Vd w e
  · intro τ hτ
    rw [hlen] at hτ
    have hτ3 : τ < 3 := by omega
    rw [e7, e43, h0, Nat.zero_add, hp, show 7 + (τ + 1) = 8 + τ by omega]
    exact fixed_key_O Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest
      Kp Vd w e hτ3

/-- The same with the field as a premise, spare: the form that PlaysAtTen.lean calls. -/
theorem trees_ten_at (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hs : K₁.send = ⟨parKey Xs PF, 0⟩) (hsp : K₁.lin.S.sharedSplitNeeded = true) (own₀ : X₀)
    (h7 : tt 7 = ownTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true))
    (htt : ∀ τ, τ < 3 → tt (8 + τ) = testTbl 1 (JO Xs K₁ B) own₀ 43 (fun _ _ _ => true) τ) :
    ∀ k s m E ds y cols,
      Thr (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 10 k s m E →
      m.opened.isSome = true →
      drawsFit (keyOmega (PF.O.getD PF.U)).rounds ds = true →
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Moved
        (keyOmega (PF.O.getD PF.U)) k m E ds y cols →
      (TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Trees
        ((TN Xs Nr (withTestsOnUAndOmega K₁ pU pO) ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).fresh 10) k y.2
        (E.add y.1) :=
  fun k s m E ds y cols hT _ hd hMv =>
    trees_ten_sign Xs Nr K₁ ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hs hsp own₀ h7 htt k s m E ds y
      cols hT hd hMv

end

end AtPublicFiles.TreesAtTenKey

end

#print axioms AtPublicFiles.TreesAtTenKey.trees_own_moved
#print axioms AtPublicFiles.TreesAtTenKey.count_O
#print axioms AtPublicFiles.TreesAtTenKey.block_ten
#print axioms AtPublicFiles.TreesAtTenKey.trees_ten_sign
#print axioms AtPublicFiles.TreesAtTenKey.trees_ten_at
