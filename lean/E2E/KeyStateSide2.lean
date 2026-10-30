-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyStateSide2.lean: THE STATE's SIDE OF THE LIBRARY's PROMISE AT EVERY BORDER OF THE KEY FILE's
SHARED CHAIN (`Tests₂`, Johnson/RunOne/KeyOn2Parts.lean, at the library's own letters: `T₂`,
Johnson/Top/Fire/Code/KeyASide2AtFk.lean), FROM A THREAD, in scope: at the border where the shared
chain's thread stands, and BEHIND THE STEP OF ANY OF ITS TWELVE SUB-PROTOCOLS. By calls. On the
verifier's states alone. NOTHING IS SHOWN OF ANY PROVER. THAT HEAP READS TWO STATES: the shared
chain's own, and the first chain's last, which the library's sub-protocols are handed and OUR SHARED
THREAD IS NOT. So it is said here AT EVERY GOOD STATE OF THE FIRST CHAIN: one at which the first
chain's side holds at its last border (`Side18 X 19`, E2E/KeyStateSide18.lean). The library's twelve
steps (`StepInvP`, Johnson/Top/Fire/Code/ReachedInvPair.lean) hold "at every handed half", and are
proved of the sub-protocols as they are: they are folded here along `Reach`, as the first chain's
are in E2E/KeyStateSide.lean. The library has the like along its own history (`aSide₂_at_all`,
Johnson/Top/Fire/Code/KeyASide2All.lean).

  **`invP_of_reach`**: GENERAL: steps that read what is handed too, folded along `Reach`: the like
      of the library's `reached_held_invP`
  **`steps₂`**: THE TWELVE, GATHERED, in scope: a list of calls: `g0_paid`, `gap₂_1`, `gap₂_3`,
      `gap₂_4`, `gap₂_6`, `gap₂_7`, `gap₂_8`, the two fields of `two₂_made`, `g9_scope`,
      `g10_scope`, `g11_paid`
  `start₂_good`: the start: the library's `tests₂_start` at a good state, by the calls of the proof
      of its `s0_made`
  `t₂_reach_scope`, **`t₂_sourced`**: at every state that `Reach` reaches
  `OverShared`, `Begun₂`: what is asked of a thread: its list, the number of its first own tree, and
      that it begins where the description starts the chain
  **`t₂_thr`**, **`t₂_behind`**: from any such thread

Limits.
- ONE PREMISE ON THE INSTANCE: the key fits the shape's index (`KeyFits`). It is a test with code on
  the key alone, and a clause of the description's own test on the instance; that payer is not
  typed.
- THAT A GOOD STATE OF THE FIRST CHAIN EXISTS IS NOT SHOWN: where there is none these statements say
  nothing. The first chain's thread at its last border gives one (`side18_thr`).
- The oracles' side of the promise is not in it; nor the samples at the open pins.
- At the library's own seats and numbers (`atSix`, `off₂N`).
- The thread is any thread over the shared chain: `laid₂` (E2E/KeyRest.lean) is one, with any halves
  and any tables.
- AT `laid₂`, WHOSE CLAUSE ON THE STATE IS LAID AS THIS VERY SIDE (E2E/KeyRest.lean), THE STATEMENT
  "at the border where the thread stands" CONCLUDES A CONJUNCT OF ITS OWN PREMISE. Its proof reads
  the thread's clause on the verifier's fold alone: stated at that clause, where it can pay
  something: E2E/KeyMade.lean. The statements "behind the step" are not touched by this.
- `t₂_behind` FOLDS FROM THE START AND SO ASKS THAT THE KEY FITS; the leaner form, one step from the
  clause in front, asks nothing of the instance: `side₂_step`, E2E/KeyMade.lean.
- It is true also where the thread holds at nothing.

-/
import E2E.KeyStateSide18
import Johnson.Top.Fire.Code.KeyASide2All

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread

/-! ## 1 The fold, general -/

section
open VerifiableInference.Desc (Block)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD (StepInvP)
variable {P S Cl : Type}

/-- **Steps that read what is handed too, folded along `Reach`.** -/
theorem invP_of_reach {ft : Nat} {bs : List (Block S Cl)} {start : P → S} (I : Nat → P × S → Prop)
    (K : Nat) (h0 : ∀ z, I 0 (z, start z))
    (hs : ∀ k, k < K → ∀ b, bs[k]? = some b → StepInvP b (I k) (I (k + 1))) {k : Nat} {a : P × S}
    (h : Reach ft bs start k a) : k ≤ K → I k a :=
  Reach.inv (Inv := fun k a => k ≤ K → I k a) (fun z _ => h0 z)
    (fun k z s s' b _ hb hy ih hk => by
      obtain ⟨R, c, -, e⟩ := hy
      have q := (VerifiableInference.Desc.Sound.step_ok_iff ft b s s' R c c.length).1 e
      exact hs k (Nat.lt_of_succ_le hk) b hb z s s' R _ q.1 q.2.2.2 (ih (Nat.le_of_succ_le hk))) h

end

/-! ## 2 The twelve, and the start, in scope -/

section
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.StepSide2 (g9_scope g10_scope)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made}

/-- **The twelve steps, gathered.** -/
theorem steps₂ (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀)
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) :
    ∀ j, j < 12 → ∀ b, (Fk X N P).shared.blocksInOrder[j]? = some b →
      StepInvP b (T₂ X atSix off₂N j) (T₂ X atSix off₂N (j + 1)) := by
  intro j hj b hb
  match j, hj with
  | 0, _ => exact g0_paid X N P atSix off₂N b hb
  | 1, _ => exact gap₂_1 atSix off₂N hZ hP hm hX hp b hb
  | 2, _ => exact (two₂_made X N P hZ hP hm hX hp).g2 b hb
  | 3, _ => exact gap₂_3 atSix off₂N hp b hb
  | 4, _ => exact gap₂_4 atSix off₂N hp b hb
  | 5, _ => exact (two₂_made X N P hZ hP hm hX hp).g5 b hb
  | 6, _ => exact gap₂_6 atSix off₂N hZ hP hm hX hp b hb
  | 7, _ => exact gap₂_7 atSix off₂N hp b hb
  | 8, _ => exact gap₂_8 atSix off₂N hZ hP hm hX hp b hb
  | 9, _ => exact g9_scope X N P atSix off₂N hZ hP hm hX hL hp b hb
  | 10, _ => exact g10_scope X N P atSix off₂N hZ hP hm hX hL hp b hb
  | 11, _ =>
    exact g11_paid X N P atSix off₂N (lengths_in_scope hZ hP hm hX hp hw).2.1 b hb
  | n + 12, h12 => exact absurd h12 (by omega)

/-- **The start, at a good state of the first chain.** -/
theorem start₂_good (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀)
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (Fk X N P).planOk = true) (x : Xi) (e₁ : FirstState) (hg : Side18 X 19 e₁)
    (hfit : x.key.fits (shapeAt X).fold.index = true) :
    T₂ X atSix off₂N 0 ((x, e₁), (Fk X N P).start₂ x) := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  have E := hg.2 (by decide)
  have hfo := fileOk_of_planOk' _ hp
  obtain ⟨e1, e2⟩ := pubsOf_k m X hX
  exact tests₂_start X N P atSix off₂N (form_of_fileOk X N P hfo) (lin_of_fileOk X N P hfo)
    (codes_of_front X N P (by rw [e2, e1]) (front_of_planOk X N P hp) hfo) x₀ x₁ hl x e₁ hg.1.1
    E.1 E.2.2 hfit

theorem t₂_reach_scope (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀)
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
    (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true) (e₁ : FirstState)
    (hg : Side18 X 19 e₁) (ft k : Nat) (a : Xi × St₂) (hk : k ≤ 12)
    (h : Reach ft (Fk X N P).shared.blocksInOrder (Fk X N P).start₂ k a)
    (hfit : a.1.key.fits (shapeAt X).fold.index = true) :
    T₂ X atSix off₂N k ((a.1, e₁), a.2) :=
  invP_of_reach
    (fun k (a : Xi × St₂) => a.1.key.fits (shapeAt X).fold.index = true →
      T₂ X atSix off₂N k ((a.1, e₁), a.2)) 12
    (fun z hf => start₂_good X N P hZ hP hm hX hp z e₁ hg hf)
    (fun j hj b hb z s s' rs gs hf hy hA hfz =>
      steps₂ X N P hZ hP hm hX hL hp hw j hj b hb (z, e₁) s s' rs gs hf hy (hA hfz)) h hk hfit

/-- **In scope, at what the key file's description is made of.** -/
theorem t₂_sourced {Z : VerifierAndGoals.PublicFiles} (hs : AtPublicFiles.AtFiles.KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) (e₁ : FirstState) (hg : Side18 X 19 e₁) (ft k : Nat)
    (a : Xi × St₂) (hk : k ≤ 12) (h : Reach ft (Fk X N P).shared.blocksInOrder (Fk X N P).start₂ k a)
    (hfit : a.1.key.fits (shapeAt X).fold.index = true) :
    T₂ X atSix off₂N k ((a.1, e₁), a.2) := by
  obtain ⟨X₀, m, h0, hm, hX, -, hL⟩ := hs.source
  exact t₂_reach_scope X N P scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hL
    hs.named.plan hs.named.wanted e₁ hg ft k a hk h hfit

end

/-! ## 3 From the thread -/

section
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows23 (St₂ atSix shapeAt)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open LPFD (T₂ off₂N)
open ProofFile.Honest
variable {Bk : ProverCoinCounts} {V W Xh Pb : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (x : Xi) {Z : VerifierAndGoals.PublicFiles}

/-- **A thread over the shared chain**: its list is the description's, and the number in the label
of its first own tree is 0. -/
structure OverShared (T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb) : Prop where
  bs : T.bs = (D Xs N Pl).shared.blocksInOrder
  ft : T.ft = 0

/-- It begins where the description starts the chain at x, at every valid input. -/
def Begun₂ (T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb) : Prop :=
  ∀ k w h s₀, T.valid w → T.begun k w h s₀ → s₀ = (D Xs N Pl).start₂ x

variable {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}

/-- The shared chain's thread gives the history along the sub-protocols as they are. -/
theorem reach_thr₂ (hO : OverShared Xs N Pl T) (hB : Begun₂ Xs N Pl x T) {b : Nat}
    (hb : b ≤ (D Xs N Pl).shared.blocksInOrder.length) {k : Coins Bk} {s : St₂} {m : Mid W Xh} {E : Env}
    (hT : Thr T b k s m E) :
    Reach 0 (D Xs N Pl).shared.blocksInOrder (D Xs N Pl).start₂ b (x, s) := by
  have h := thr_reach_of T (D Xs N Pl).start₂ x (by rw [hO.bs]; exact hb)
    (fun s₀ hs₀ => hB k _ _ s₀ hT.2.2.2.2.2.2 hs₀) hT
  rw [hO.ft, hO.bs] at h
  exact h

/-- **At the border where the thread stands**, at every good state of the first chain. -/
theorem t₂_thr (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) (hO : OverShared Xs N Pl T) (hB : Begun₂ Xs N Pl x T) {b : Nat}
    (hb : b ≤ 12) {k : Coins Bk} {s : St₂} {m : Mid W Xh} {E : Env} (hT : Thr T b k s m E) :
    ∀ e₁ : FirstState, Side18 Xs 19 e₁ → T₂ Xs atSix off₂N b ((x, e₁), s) := fun e₁ hg =>
  t₂_sourced Xs N Pl hs scope e₁ hg 0 b (x, s) hb
    (reach_thr₂ Xs N Pl x hO hB (by rw [(lengths scope hs.named).2.1]; exact hb) hT) hfit

/-- **BEHIND THE STEP**, at every one of the twelve. -/
theorem t₂_behind (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) (hO : OverShared Xs N Pl T) (hB : Begun₂ Xs N Pl x T) {b : Nat}
    (hb : b < 12) {blk : Block St₂ (D Xs N Pl).Cl} (hblk : T.bs[b]? = some blk) {k : Coins Bk}
    {s s' : St₂} {m : Mid W Xh} {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W Xh}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hT : Thr T b k s m E)
    (hS : T.Stepped blk k s m E ds y cols s') :
    ∀ e₁ : FirstState, Side18 Xs 19 e₁ → T₂ Xs atSix off₂N (b + 1) ((x, e₁), s') := fun e₁ hg => by
  have hy := stepYes_of_step hS.2
  rw [hO.ft] at hy
  rw [hO.bs] at hblk
  exact t₂_sourced Xs N Pl hs scope e₁ hg 0 (b + 1) (x, s') hb
    (Reach.succ (reach_thr₂ Xs N Pl x hO hB
      (by rw [(lengths scope hs.named).2.1]; exact Nat.le_of_lt hb) hT) hblk hy) hfit

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.invP_of_reach
#print axioms AtPublicFiles.KeyThread.steps₂
#print axioms AtPublicFiles.KeyThread.start₂_good
#print axioms AtPublicFiles.KeyThread.t₂_reach_scope
#print axioms AtPublicFiles.KeyThread.t₂_sourced
#print axioms AtPublicFiles.KeyThread.reach_thr₂
#print axioms AtPublicFiles.KeyThread.t₂_thr
#print axioms AtPublicFiles.KeyThread.t₂_behind
