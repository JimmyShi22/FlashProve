-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStateSide.lean: THE STATE's SIDE OF THE LIBRARY's PROMISE AT EVERY BORDER OF THE KEY FILE's
FIRST CHAIN, FROM A THREAD: at the border where a thread stands, and BEHIND THE STEP OF ANY OF THE
NINETEEN SUB-PROTOCOLS, those of a kind among them. By calls. On the verifier's state alone. NOTHING
IS SHOWN OF ANY PROVER.

THE LIBRARY HAS THIS ALONG ITS OWN HISTORY (`aSide_of_hist`,
Johnson/Top/Fire/Code/KeyASideAtFk.lean; in scope `aSide_at_all`, KeyASideAll.lean): along
sub-protocols that ask besides that every word shown is below the prime. A thread
(Johnson/Desc/ProofFile/Honest/Thread/Thr.lean) gives the history along the sub-protocols AS THEY
ARE (`Reach`, Johnson/Top/H0/Walk/Reach.lean; `thr_reach_of`, Honest/Thread/ReachBack.lean), and
from that the library's cannot be had. BUT THE LIBRARY's NINETEEN STEPS (`StepInv`,
Johnson/Top/Fire/Code/ReachedInv.lean) ARE PROVED OF THE SUB-PROTOCOLS AS THEY ARE: here the same
nineteen are folded along `Reach`.

  `stepInv_yes`: GENERAL: a step of the library's form, at an accepting step (`StepYes`)
  **`inv_of_reach`**: GENERAL: such steps, folded along `Reach`: the like of the library's
      `reached_held_inv`
  **`steps₁`**: THE NINETEEN, GATHERED: a list of calls: `stepFk0`, `stepFk1`, `aStep2` and its
      like, the seven fields of `Gaps`: as they stand inside the proof of `aSide_of_hist`
  `aSide_of_reach`: so `ASideH` at every state that `Reach` reaches, under the premises of
      `aSide_of_hist`
  `aSide_reach_scope`, **`aSide_sourced`**: IN SCOPE, with no premise on a step: by the calls of
      `aSide_at_all`'s proof
  **`aSide_thr`**: at the border where the first chain's thread stands
  **`aSide_behind`**: BEHIND THE STEP of the sub-protocol number b, for every b below nineteen

Limits.
- `ASideH` is the library's Bool on the state, that the book places the pinned messages, that the
  statement is in order, one tie on a mask, and at two borders what the layer wants of what was
  heard. IT IS NOT THE WHOLE CLAUSE ON THE STATE OF THE FIRST CHAIN's THREAD (E2E/KeyRest.lean):
  what the library's ties ask from border 18 on, and "the stored table's OOD sample is there", are
  not in it.
- At the library's own seats (`atSix`), not at a letter.
- The first chain alone.
- THE THREAD IS `laid₁`: the key file's first thread WITH ANY HALVES AND ANY TABLES. At the thread
  without halves the step of a sub-protocol of a kind is nobody's step.
- SINCE THE THREADS' CLAUSE ON THE STATE IS LAID AS THIS VERY SIDE (E2E/KeyRest.lean), THE STATEMENT
  "at the border where the thread stands" CONCLUDES A CONJUNCT OF ITS OWN PREMISE. Its proof reads
  the thread's clause on the verifier's fold alone: stated at that clause, where it can pay
  something: E2E/KeyMade.lean. The statements "behind the step" are not touched by this.
- It is true also where the thread holds at nothing.

-/
import E2E.KeyRest
import E2E.KeyKeepsAt
import E2E.KeyPublic
import E2E.KeyThreadFits
import Johnson.Top.Fire.Code.KeyASideAll
import Johnson.Top.H0.Walk.ReachInv
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread

/-! ## 1 The fold, general -/

section
open VerifiableInference.Desc (Block)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD (StepInv)
variable {P S Cl : Type}

/-- A step of the library's form, at an accepting step. -/
theorem stepInv_yes {ft : Nat} {b : Block S Cl} {A B : S → Prop} (h : StepInv b A B) {s s' : S}
    (hy : StepYes ft b s s') (ha : A s) : B s' := by
  obtain ⟨R, c, -, e⟩ := hy
  have q := (VerifiableInference.Desc.Sound.step_ok_iff ft b s s' R c c.length).1 e
  exact h s s' R _ q.1 q.2.2.2 ha

/-- **Such steps, folded along `Reach`.** -/
theorem inv_of_reach {ft : Nat} {bs : List (Block S Cl)} {start : P → S} (I : Nat → S → Prop)
    (K : Nat) (h0 : ∀ z, I 0 (start z))
    (hs : ∀ k, k < K → ∀ b, bs[k]? = some b → StepInv b (I k) (I (k + 1))) {k : Nat} {a : P × S}
    (h : Reach ft bs start k a) : k ≤ K → I k a.2 :=
  Reach.inv (Inv := fun k a => k ≤ K → I k a.2) (fun z _ => h0 z)
    (fun k _ _ _ b _ hb hy ih hk =>
      stepInv_yes (hs k (Nat.lt_of_succ_le hk) b hb) hy (ih (Nat.le_of_succ_le hk))) h

end

/-! ## 2 The nineteen -/

section
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
  VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup Xi)
open Johnson.RunOne.KeyRows1 Johnson.RunOne.KeyRows23
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (at_ : Where) (x₀ x₁ : Lookup)

/-- **The nineteen steps, gathered.** -/
theorem steps₁ (H₀ H₁ : FirstState → Prop) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (P10 : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)))
    (P11 : Public11 (oneAt X) pieces (g11 X)) (hst : 1 ≤ (oneAt X).ranges.stages.length)
    (hat0 : at_ 0 = (0, 0)) (hat1 : at_ 1 = (1, 0))
    (bw : Block FirstState VerifiableInference.Desc.Key.Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (G : Gaps X N P at_ H₀ H₁) :
    ∀ j, j < 19 → ∀ b, (Fk X N P).first.blocksInOrder[j]? = some b →
      StepInv b (ASideH (oneAt X) at_ H₀ H₁ j) (ASideH (oneAt X) at_ H₀ H₁ (j + 1)) := by
  intro j hj b hb
  match j, hj with
  | 0, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 0 (by decide) (by decide) b
      (stepFk0 X N P at_ P10 hat0 b hb)
  | 1, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 1 (by decide) (by decide) b
      (stepFk1 X N P at_ P11 hst hat1 b hb)
  | 2, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 2 (by decide) (by decide) b
      (aStep2 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 3, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 3 (by decide) (by decide) b
      (aStep3 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 4, _ =>
    exact fun s s' rs gs hf hy hA => ⟨(G.g4 b hb s s' rs gs hf hy hA.1).1,
      fun _ => (G.g4 b hb s s' rs gs hf hy hA.1).2, fun e => absurd e (by decide)⟩
  | 5, _ =>
    exact fun s s' rs gs hf hy hA => ⟨G.g5 b hb s s' rs gs hf hy ⟨hA.1, hA.2.1 rfl⟩,
      fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
  | 6, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 6 (by decide) (by decide) b
      (aStep6 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 7, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 7 (by decide) (by decide) b
      (aStep7 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 8, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 8 (by decide) (by decide) b
      (aStep8 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 9, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 9 (by decide) (by decide) b
      (aStep9 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 10, _ =>
    exact fun s s' rs gs hf hy hA => ⟨(G.g10 b hb s s' rs gs hf hy hA.1).1,
      fun e => absurd e (by decide), fun _ => (G.g10 b hb s s' rs gs hf hy hA.1).2⟩
  | 11, _ =>
    exact fun s s' rs gs hf hy hA => ⟨G.g11 b hb s s' rs gs hf hy ⟨hA.1, hA.2.2 rfl⟩,
      fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
  | 12, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 12 (by decide) (by decide) b
      (aStep12 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 13, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 13 (by decide) (by decide) b
      (aStep13 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 14, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 14 (by decide) (by decide) b
      (aStep14 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl b hb)
  | 15, _ => exact plainStep (oneAt X) at_ H₀ H₁ 15 (by decide) (by decide) b (G.g15 b hb)
  | 16, _ => exact plainStep (oneAt X) at_ H₀ H₁ 16 (by decide) (by decide) b (G.g16 b hb)
  | 17, _ => exact plainStep (oneAt X) at_ H₀ H₁ 17 (by decide) (by decide) b (G.g17 b hb)
  | 18, _ =>
    exact plainStep (oneAt X) at_ H₀ H₁ 18 (by decide) (by decide) b
      (aStep18 (oneAt X) at_ X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b hb)
  | n + 19, h19 => exact absurd h19 (by omega)

/-- **At every state that `Reach` reaches**, under the premises of the library's law. -/
theorem aSide_of_reach (H₀ H₁ : FirstState → Prop) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hm : (oneAt X).ranges.messageId = 1)
    (P10 : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)))
    (P11 : Public11 (oneAt X) pieces (g11 X)) (hst : 1 ≤ (oneAt X).ranges.stages.length)
    (hat0 : at_ 0 = (0, 0)) (hat1 : at_ 1 = (1, 0))
    (bw : Block FirstState VerifiableInference.Desc.Key.Claim)
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (G : Gaps X N P at_ H₀ H₁) (ft k : Nat) (a : Xi × FirstState) (hk : k ≤ 19)
    (h : Reach ft (Fk X N P).first.blocksInOrder (Fk X N P).start₁ k a) :
    ASideH (oneAt X) at_ H₀ H₁ k a.2 :=
  inv_of_reach (ASideH (oneAt X) at_ H₀ H₁) 19
    (fun z => ⟨aSide0_fk X N P at_ (by rw [hl]; rfl) hm z, fun e => absurd e (by decide),
      fun e => absurd e (by decide)⟩)
    (steps₁ X N P at_ x₀ x₁ H₀ H₁ hl P10 P11 hst hat0 hat1 bw hw G) h hk

end

/-! ## 3 In scope -/

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

/-- By the calls of the proof of the library's `aSide_at_all`. -/
theorem aSide_reach_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m)
    (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true) (hft : N.nums.firstTree = 0)
    (ft k : Nat) (a : Xi × FirstState) (hk : k ≤ 19)
    (h : Reach ft (Fk X N P).first.blocksInOrder (Fk X N P).start₁ k a) :
    ASideH (oneAt X) atSix (H₀ X) (H₁ X) k a.2 := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces
    (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
      (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  have h5s := five_in_scope hZ hP hm hX hp
  obtain ⟨pub1⟩ := public11_full (oneAt X) pieces (g11 X) h5s.2.1 h5s.2.2.2.2 (plan11_of hp)
  have hid : (oneAt X).ranges.messageId = 1 := by rw [h5s.2.1]; exact id_full
  have hst : 1 ≤ (oneAt X).ranges.stages.length := by
    rw [h5s.2.1, Johnson.RunOne.KeyLetters.stages_full]
    decide
  exact aSide_of_reach X N P atSix x₀ x₁ (H₀ X) (H₁ X) hl hid
    (public10_in_scope hZ hP hm hX hp c₁ k₁ q₁) pub1 hst rfl rfl bw hw
    (gaps_in_scope X N P c₁ k₁ q₁ hZ hP hm hX hp hft) ft k a hk h

/-- **In scope, at what the key file's description is made of.** -/
theorem aSide_sourced {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (ft k : Nat) (a : Xi × FirstState) (hk : k ≤ 19)
    (h : Reach ft (Fk X N P).first.blocksInOrder (Fk X N P).start₁ k a) :
    ASideH (oneAt X) atSix (H₀ X) (H₁ X) k a.2 := by
  obtain ⟨X₀, m, h0, hm, hX, hN, -⟩ := hs.source
  exact aSide_reach_scope X N P _ _ rfl scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX
    hs.named.plan (firstTree_of_rangesNumbers hN) ft k a hk h

end

/-! ## 4 From the thread -/

section
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows23 (atSix)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD (ASideH)
open ProofFile.Honest
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- The thread gives the history along the sub-protocols as they are. -/
theorem reach_thr {b : Nat} (hb : b ≤ (D Xs N Pl).first.blocksInOrder.length) {k : Coins Bk}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E) :
    Reach 0 (D Xs N Pl).first.blocksInOrder (D Xs N Pl).start₁ b (m.st.input.x, s) :=
  thr_reach_of (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) (D Xs N Pl).start₁ m.st.input.x hb
    (fun _ h => h) hT

/-- **At the border where the thread stands.** -/
theorem aSide_thr (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b ≤ 19) {k : Coins Bk}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E) :
    ASideH (one₀ Xs) atSix (H₀ Xs) (H₁ Xs) b s :=
  aSide_sourced Xs N Pl hs scope 0 b (m.st.input.x, s) hb
    (reach_thr Xs N Pl L w₀ rc x (by rw [(lengths scope hs.named).1]; exact hb) hT)

/-- **BEHIND THE STEP**, at every one of the nineteen. -/
theorem aSide_behind (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b < 19)
    {blk : Block FirstState VerifiableInference.Desc.Key.Claim}
    (hblk : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk) {k : Coins Bk}
    {s s' : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Unit) X'} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E)
    (hS : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s') :
    ASideH (one₀ Xs) atSix (H₀ Xs) (H₁ Xs) (b + 1) s' :=
  aSide_sourced Xs N Pl hs scope 0 (b + 1) (m.st.input.x, s') hb
    (Reach.succ (reach_thr Xs N Pl L w₀ rc x
      (by rw [(lengths scope hs.named).1]; exact Nat.le_of_lt hb) hT) hblk
      (stepYes_of_step hS.2))

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.stepInv_yes
#print axioms AtPublicFiles.KeyThread.inv_of_reach
#print axioms AtPublicFiles.KeyThread.steps₁
#print axioms AtPublicFiles.KeyThread.aSide_of_reach
#print axioms AtPublicFiles.KeyThread.aSide_reach_scope
#print axioms AtPublicFiles.KeyThread.aSide_sourced
#print axioms AtPublicFiles.KeyThread.reach_thr
#print axioms AtPublicFiles.KeyThread.aSide_thr
#print axioms AtPublicFiles.KeyThread.aSide_behind
