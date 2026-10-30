-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/TreesAtNine.lean

hT AT MEMBER 9 OF THE KEY's SHARED THREAD, AS LEAN's OWN WORD. `trees_of_thr` (K12/TreesOfThr.lean) called
at `threadKey`, at the table `tbKey` with a letter tt, and handed to `plays_of_playsOn` as its argument.

  `trees_of_moved`   `trees_of_thr` without hrs and hst: both follow from `Moved`, hhalf and hcount
  `JN`               the job: `jobNine`, at the written places, at any key's parts K'
  `trees_nine`       hT at member 9: the statement of the binder of `plays_of_playsOn`, at this thread
  `plays_nine`       `Plays` at 9 from `PlaysOn` and Thr → A: the law takes `trees_nine` as its hT

PREMISES OF `trees_nine`, and who pays each.
- e : parKey Xs PF = QK, B : Eight …: `par_sourced`, `plan_key` in the goals' scope (as `not_plays_at`).
- hsp: `hQ.facts.two`, there. hOp: the place of the pair at G_omega: by the parts.
- hU : K.onU = proverSideOfProximityTest J: A PREMISE ON THE PARTS: met by `not_plays_at`'s `Kx`, with the guard nowhere:
  this half is the plain one, as proverSideOfTestOnU is.
- own₀: any value of X₀: `K.ownShared₀` is at hand.
- htt: THE ARM: at own 3 to 6 the letter is `testTbl` at n₀ = 8 and the constant yes. Here a premise;
  its text stands at the filling. It is an equation of functions, with no k, m, w, h in it.

HAD IN THE PROOF, NOT PREMISES: hblk, SeatOf: `seat_nine`. hfresh: by text. hR: `rows_heard_KU`, by the
text of `sentKey` and `sentOf`. hk, hcount: `hk_U`, `len_U`, `tests_count`, `place_full`. htable's counts:
`trees_key`, `rounds_key`, `sendings_count`. hfixed: `fixed_key`. hhalf: `find_of_nodup`, `keyProver_shared`.

Limits.
- MEMBER 9 ALONE: OWN 3 TO 6, FOUR OF THE EIGHT TREES. At member 10 three premises of `trees_of_thr` are
  false: hfresh, hhalf, and htable at own 7.
- A conditional: that Thr stands is not said here, and Moved is a premise of `trees_nine`. That Moved
  is had wherever Thr stands and `Plays`' other premises hold is `plays_at_nine` (PlaysAtNine.lean).
- `plays_nine` takes `PlaysOn` as a hypothesis and is called by nobody: `plays_at_nine` pays `PlaysOn` and
  calls `plays_of_playsOn` itself. It stands as the word that `trees_nine` types as hT.
- The thread's table is `tbKey` (E2E/KeyTreesKey.lean). No filling of tt is typed here.
- At QK by e, not at AK.
- Nothing on completeness, on soundness or on what is hidden.

NOT IN FRONT OF A LAW OVER COINS: `trees_nine`, `plays_nine` bear this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: the thread from Thr and
`Moved` as premises, `Plays` as an end. None: the bar is flat. -/
import E2E.KeyFixedLines
import E2E.KeyPlaysAt
import E2E.CongruenceAtKey
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr
import Johnson.Desc.ProofFile.Honest.Thread.FileRow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.TreesAtNine
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyDoorNine (jobNine seat_nine)
open AtPublicFiles.KeyTreesKey (tbKey)
open AtPublicFiles.KeyTblTrial (sendings_count tests_count)
open AtPublicFiles.KeyTreesKey (treesOf5)
open AtPublicFiles.KeyFixedLines (trees_key rounds_key fixed_key)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeyLay (rows_heard_KU hk_U len_U)
open H2K.Member (piKUFull)

/-- **`trees_of_thr` without hrs and hst**: under `Moved`, hhalf and hcount they follow. -/
theorem trees_of_moved {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh.isNone = false) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J))
    (hcount : (blk.oracles.flatMap id).length + 1 = J.p.nums.stages.length)
    (own₀ : X)
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + τ)) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + τ)) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT hd hMv σ hσ
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, -⟩, -⟩ := hMv'
  obtain ⟨ho, hr⟩ := ProofFile.Honest.Small.member_lengths hhalf hl
  obtain ⟨i, hi, -⟩ := K14.fresh_mem_own T hblk hσ
  have hi' : i + 1 < J.p.nums.stages.length := by omega
  obtain ⟨s, t, rest, hst⟩ : ∃ a b r, J.p.nums.stages = a :: b :: r := by
    cases hh : J.p.nums.stages with
    | nil =>
      rw [hh] at hi'
      simp only [List.length_nil] at hi'
      omega
    | cons a u =>
      cases u with
      | nil =>
        rw [hh] at hi'
        simp only [List.length_cons, List.length_nil] at hi'
        omega
      | cons b r => exact ⟨a, b, r, rfl⟩
  have hzl := ProofFile.Honest.Small.zip_length ho hr
  have l1 : (firstPart J : Part V W X).moves.length = firstLen J.p.nums.stages := by
    rw [first_moves]
    exact (List.length_map _).trans List.length_range
  have l2 : (restPart J : Part V W X).moves.length = restLen J.p.nums.stages := by
    rw [rest_moves J s t rest hst]
    exact (List.length_map _).trans List.length_range
  have hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages := by
    refine hzl.trans ?_
    show (firstPart J : Part V W X).moves.length + ((restPart J : Part V W X).moves.length + 0) = _
    rw [l1, l2, Nat.add_zero]
  exact trees_of_thr T hblk J hfresh hR hk s t rest hst hpl hhalf hrs hcount own₀ htable hfixed k st
    m E ds y cols hT hd hMv σ hσ

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk X' Wk' P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk) (K' : KeyParts W₀ Rc X₀ X' Wk')
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- The job: `jobNine` at the written places. -/
abbrev JN (B : Eight (parKey Xs PF)) : TestJob (Common W₀ Rc TableKey) X₀ :=
  jobNine (X₀ := X₀) Xs PF K' B

/-- The thread, at the trial's table. -/
abbrev TN : Thread Bk (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).S₂
    (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).Cl Empty (Common W₀ Rc TableKey) X₀ TableKey :=
  threadKey Xs Nr PF K ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w

/-- **hT at member 9 of the key's shared thread.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem trees_nine (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfProximityTest (JN Xs K' B)) (hOp : K.onOmega.place = omegaTestPlace) (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) =
      testTbl 1 (JN Xs K' B) own₀ 8 (fun _ _ _ => true) τ) :
    ∀ k s m E ds y cols, Thr (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9 k s m E →
      drawsFit (H2K.JointK.keyGu PF).rounds ds = true →
      (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Moved (H2K.JointK.keyGu PF) k m E ds y cols →
      (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).Trees
        ((TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).fresh 9) k y.2 (E.add y.1) := by
  have hs := sendings_count
  rw [← e] at hs
  have hblk := (seat_nine Xs Nr PF K ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w B).1
  have hseat := (seat_nine Xs Nr PF K' ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w B).2
  have hp : (JN Xs K' B).p = piKUFull := place_full
  have hlen : (JN Xs K' B).p.nums.stages.length = 5 := by
    rw [hp]
    exact len_U
  have e3 := trees_key Xs Nr K ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w e B
  have e8 := rounds_key Xs Nr K ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w e B
  have h0 : (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).front = 0 := rfl
  have pU : K.onU.place = foldedTestPlace := by
    rw [hU]
    exact AtPublicFiles.KeyPlaysAt.place_on
  have hnd : ((keyProver K).shared.map (·.place)).Nodup := by
    rw [keyProver_shared _ hsp, pU, hOp]
    decide
  have hfind : ((keyProver K).shared.find? fun g => g.place == K.onU.place) = some K.onU :=
    AtPublicFiles.KeyPlaysAt.find_of_nodup (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place)
      (g := K.onU) (keyProver K).shared (List.mem_append_right _ List.mem_cons_self) hnd
  have hgp : (H2K.JointK.keyGu PF).place = K.onU.place := by
    rw [hU]
    exact hseat.place
  have hhalf : ((TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hs.find? fun g =>
      g.place == (H2K.JointK.keyGu PF).place) = some (proverSideOfProximityTest (JN Xs K' B)) := by
    show ((keyProver K).shared.find? fun g => g.place == (H2K.JointK.keyGu PF).place) = _
    rw [hgp, hfind, hU]
  refine trees_of_moved _ hblk (JN Xs K' B) rfl
    (rows_heard_KU ⟨parKey Xs PF, 0⟩ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U)
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] (keyProver K').storedWords
      (fun c => K'.weights c.w₀) (fun c => AtPublicFiles.KeySharedThread.randKey K' c.rc))
    (by rw [hp]; exact hk_U) hseat.place hhalf ?_ own₀ ?_ ?_
  · rw [tests_count.1, hlen]
  · intro τ hτ
    rw [hlen] at hτ
    have hτ4 : τ < 4 := by omega
    rw [e3, e8, h0, Nat.zero_add]
    show (if 3 + τ < treesU (parKey Xs PF) then _ else
      if 3 + τ < treesU (parKey Xs PF) + treesOf5 (parKey Xs PF) then _ else tt (3 + τ)) = _
    rw [if_neg (by omega), if_neg (by omega)]
    exact htt τ hτ4
  · intro τ hτ
    rw [hlen] at hτ
    have hτ4 : τ < 4 := by omega
    rw [e3, e8, h0, Nat.zero_add, hp]
    exact fixed_key Xs Nr K ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w e hτ4

/-- **`Plays` at 9 from `PlaysOn`: the law takes `trees_nine` as its hT.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem plays_nine (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF))
    (hsp : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU = proverSideOfProximityTest (JN Xs K' B)) (hOp : K.onOmega.place = omegaTestPlace) (own₀ : X₀)
    (htt : ∀ τ, τ < 4 → tt (3 + τ) =
      testTbl 1 (JN Xs K' B) own₀ 8 (fun _ _ _ => true) τ)
    {A B' : Coins Bk → (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr PF).S₂ →
      Mid (Common W₀ Rc TableKey) X₀ → Env → Prop}
    (h : PlaysOn (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).φ Bk
      (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).chain
      (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).ft
      (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w).hs (H2K.JointK.keyGu PF) A B')
    (hA : ∀ k s m E, Thr (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9 k s m E → A k s m E) :
    Plays (TN Xs Nr K ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w) 9 :=
  plays_of_playsOn _
    (seat_nine Xs Nr PF K ℓ Nm Mg₀ (tbKey (parKey Xs PF) wts rnd tk tt) rest Kp Vd w B).1 h hA
    (trees_nine Xs Nr K K' ℓ Nm Mg₀ wts rnd tk tt rest Kp Vd w e B hsp hU hOp own₀ htt)

end

end AtPublicFiles.TreesAtNine

#print axioms AtPublicFiles.TreesAtNine.trees_of_moved
#print axioms AtPublicFiles.TreesAtNine.JN
#print axioms AtPublicFiles.TreesAtNine.TN
#print axioms AtPublicFiles.TreesAtNine.trees_nine
#print axioms AtPublicFiles.TreesAtNine.plays_nine
