-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStateSide18.lean:
WHAT THE LIBRARY's TIES ASK OF THE FIRST CHAIN's STATE FROM BORDER 18 ON, BESIDE `ASide` (its `E18`,
Johnson/Top/Fire/Code/KeyASideAll.lean: the row "Eval" is the claim's; the last group's open rows
lie on their own tables; the first mask of the test on W lies in W's tree): FROM A THREAD, in scope.
By calls. On the verifier's state alone. NOTHING IS SHOWN OF ANY PROVER.

THE LIBRARY HAS IT ALONG ITS OWN HISTORY (`e18_at_end`). Its proof goes one step back and calls a
step that is proved of the sub-protocol number 17 as it is (`astep17E_scope`,
Johnson/Top/Fire/Code/RowAStepsE.lean), then that the seal hands the state on. Here the same two are
folded along `Reach`, with the nineteen steps of E2E/KeyStateSide.lean.

  (`Side18 X k s`, E2E/KeySideDef.lean: `ASideH` at the library's seats, and from border 18 on
      `E18`)
  **`steps18`**: the nineteen steps of that invariant, in scope
  `side18_reach_scope`, **`side18_sourced`**: at every state that `Reach` reaches
  **`side18_thr`**, **`side18_behind`**: at the border where the first chain's thread stands; behind
      the step of each of the nineteen

Limits. The samples at the open pins are not in it. At the library's own seats. The first chain
alone. The thread is `laid₁` (E2E/KeyRest.lean): with any halves and any tables. It is true also
where the thread holds at nothing. SINCE THE THREADS' CLAUSE ON THE STATE IS LAID AS THIS VERY SIDE
(E2E/KeyRest.lean), THE STATEMENT "at the border where the thread stands" CONCLUDES A CONJUNCT OF
ITS OWN PREMISE. Its proof reads the thread's clause on the verifier's fold alone: stated at that
clause, where it can pay something: E2E/KeyMade.lean. The statements "behind the step" are not
touched by this.

-/
import E2E.KeyStateSide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread

section
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows23 (Fk oneAt atSix)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made}

/-- **The nineteen steps of that invariant.** -/
theorem steps18 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hZ : VerifierAndGoals.InScope Zp = true)
    (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (hft : N.nums.firstTree = 0) :
    ∀ j, j < 19 → ∀ b, (Fk X N P).first.blocksInOrder[j]? = some b →
      StepInv b (Side18 X j) (Side18 X (j + 1)) := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces
    (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
      (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  have h5s := five_in_scope hZ hP hm hX hp
  obtain ⟨pub1⟩ := public11_full (oneAt X) pieces (g11 X) h5s.2.1 h5s.2.2.2.2 (plan11_of hp)
  have hst : 1 ≤ (oneAt X).ranges.stages.length := by
    rw [h5s.2.1, Johnson.RunOne.KeyLetters.stages_full]
    decide
  have S := steps₁ X N P atSix x₀ x₁ (H₀ X) (H₁ X) hl (public10_in_scope hZ hP hm hX hp c₁ k₁ q₁)
    pub1 hst rfl rfl bw hw (gaps_in_scope X N P c₁ k₁ q₁ hZ hP hm hX hp hft)
  intro j hj b hb s s' rs gs hf hy hA
  refine ⟨S j hj b hb s s' rs gs hf hy hA.1, fun h18 => ?_⟩
  have hj' : j = 17 ∨ j = 18 := by omega
  rcases hj' with rfl | rfl
  · exact (astep17E_scope X N P c₁ k₁ q₁ hZ hP hm hX hp b (q₁ ▸ hb) s s' rs gs hf hy hA.1.1).2
  · obtain ⟨asks, ha⟩ := dec_seal (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b hb
    rw [ha] at hy
    have e : s' = s := end_same asks s s' hy
    rw [e]
    exact hA.2 (Nat.le_refl 18)

theorem side18_reach_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hft : N.nums.firstTree = 0)
    (ft k : Nat) (a : Xi × FirstState) (hk : k ≤ 19)
    (h : Reach ft (Fk X N P).first.blocksInOrder (Fk X N P).start₁ k a) : Side18 X k a.2 :=
  inv_of_reach (Side18 X) 19
    (fun z => ⟨aSide_reach_scope X N P c₁ k₁ q₁ hZ hP hm hX hp hft ft 0 (z, (Fk X N P).start₁ z)
      (Nat.zero_le _) (Reach.zero z), fun e => absurd e (by decide)⟩)
    (steps18 X N P c₁ k₁ q₁ hZ hP hm hX hp hft) h hk

/-- **In scope, at what the key file's description is made of.** -/
theorem side18_sourced {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (ft k : Nat) (a : Xi × FirstState) (hk : k ≤ 19)
    (h : Reach ft (Fk X N P).first.blocksInOrder (Fk X N P).start₁ k a) : Side18 X k a.2 := by
  obtain ⟨X₀, m, h0, hm, hX, hN, -⟩ := hs.source
  exact side18_reach_scope X N P _ _ rfl scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm
    hX hs.named.plan (firstTree_of_rangesNumbers hN) ft k a hk h

end

section
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile.Honest
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **At the border where the thread stands.** -/
theorem side18_thr (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b ≤ 19) {k : Coins Bk}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E) : Side18 Xs b s :=
  side18_sourced Xs N Pl hs scope 0 b (m.st.input.x, s) hb
    (reach_thr Xs N Pl L w₀ rc x (by rw [(lengths scope hs.named).1]; exact hb) hT)

/-- **BEHIND THE STEP**, at every one of the nineteen. -/
theorem side18_behind (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b < 19)
    {blk : Block FirstState VerifiableInference.Desc.Key.Claim}
    (hblk : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk) {k : Coins Bk}
    {s s' : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Unit) X'} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E)
    (hS : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s') :
    Side18 Xs (b + 1) s' :=
  side18_sourced Xs N Pl hs scope 0 (b + 1) (m.st.input.x, s') hb
    (Reach.succ (reach_thr Xs N Pl L w₀ rc x
      (by rw [(lengths scope hs.named).1]; exact Nat.le_of_lt hb) hT) hblk
      (stepYes_of_step hS.2))

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.steps18
#print axioms AtPublicFiles.KeyThread.side18_reach_scope
#print axioms AtPublicFiles.KeyThread.side18_sourced
#print axioms AtPublicFiles.KeyThread.side18_thr
#print axioms AtPublicFiles.KeyThread.side18_behind
