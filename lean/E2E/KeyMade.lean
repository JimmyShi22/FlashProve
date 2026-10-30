-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMade.lean: THE CLAUSE ON THE STATE OF THE KEY FILE's FIRST TWO THREADS (E2E/KeyRest.lean),
FROM THE THREAD's CLAUSE ON THE VERIFIER's OWN FOLD ALONE (`Thread.Made`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean): so it can be paid WHERE IT IS OWED: at a chain's
start, and wherever a thread is to be shown to stand. And ONE STEP of the shared chain's clause,
which asks nothing of the instance. In scope. By calls. On the verifier's states alone. NOTHING IS
SHOWN OF ANY PROVER.

WHY. A thread at a border holds its clause on the state among its own conjuncts: a statement that
draws that clause from the WHOLE thread concludes what it assumes (so `aSide_thr`, `side18_thr`,
and `t₂_thr` at `laid₂`, of E2E/KeyStateSide.lean, KeyStateSide18.lean, KeyStateSide2.lean). Their
proofs read the fold's clause alone: here they are stated at it.

  `reach_made₁`, `reach_made₂`: the fold's clause gives the history along the sub-protocols as they
      are: `reach_of_made` (Johnson/Desc/ProofFile/Honest/Thread/MadeLaw.lean)
  **`side18_made`**: the first chain: `Side18 Xs b s`, b ≤ 19
  **`side₂_made`**: the shared chain: `Side₂ Xs b x.key s`, b ≤ 12, where the key fits, at any
      thread over that chain
  `overShared_laid₂`: `laid₂` is such a thread
  **`form_made₁`**, **`form_made₂`**: so the threads' whole clause `Form`, where besides the stored
      table's OOD sample is there (and, at the shared chain, the input is the family's)
  **`side₂_step`**: ONE STEP: `Side₂ Xs b key s` and an accepting step of the sub-protocol number b
      give `Side₂ Xs (b + 1) key s'`: one of the library's twelve steps (`steps₂`), at every good
      state of the first chain: NO FOLD FROM THE START, AND NOTHING ON THE KEY

Limits.
- "The key fits" (`KeyFits`) is a premise of `side₂_made` and `form_made₂`: it is what the shared
  chain's START asks. It is a clause of the description's own test on the instance. The library has
  a payer where the letter that reads the carried OOD sample is its own (`fits_of_recBack`,
  Johnson/Top/Fire/Code/KeyAt32Letters.lean): not called here.
- "The OOD sample is there" is a premise on a letter.
- The last chain is not treated.
- It is true also where nothing is folded.

-/
import E2E.KeyStateSide2
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open Johnson.RunOne.KeyRows23 (St₂)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile.Honest

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

theorem reach_made₁ {b : Nat} (hb : b ≤ (D Xs N Pl).first.blocksInOrder.length) {k : Coins Bk}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hM : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Made b k s m E) :
    Reach 0 (D Xs N Pl).first.blocksInOrder (D Xs N Pl).start₁ b (m.st.input.x, s) :=
  reach_of_made (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) (D Xs N Pl).start₁ m.st.input.x hb
    (fun _ h => h) hM

theorem overShared_laid₂ : OverShared Xs N Pl (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂) := ⟨rfl, rfl⟩

theorem reach_made₂ {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hO : OverShared Xs N Pl T) {b : Nat} (hb : b ≤ (D Xs N Pl).shared.blocksInOrder.length) {k : Coins Bk}
    {s : St₂} {m : Mid W Xh} {E : Env}
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = (D Xs N Pl).start₂ x)
    (hM : T.Made b k s m E) :
    Reach 0 (D Xs N Pl).shared.blocksInOrder (D Xs N Pl).start₂ b (x, s) := by
  have h := reach_of_made T (D Xs N Pl).start₂ x (by rw [hO.bs]; exact hb) h0 hM
  rw [hO.ft, hO.bs] at h
  exact h

/-- **The first chain's side, from the fold's clause.** -/
theorem side18_made (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b ≤ 19) {k : Coins Bk} {s : FirstState}
    {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hM : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Made b k s m E) : Side18 Xs b s :=
  side18_sourced Xs N Pl hs scope 0 b (m.st.input.x, s) hb
    (reach_made₁ Xs N Pl L w₀ rc x (by rw [(lengths scope hs.named).1]; exact hb) hM)

/-- **The shared chain's side, from the fold's clause.** -/
theorem side₂_made {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) (hO : OverShared Xs N Pl T) {b : Nat} (hb : b ≤ 12) {k : Coins Bk}
    {s : St₂} {m : Mid W Xh} {E : Env}
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = (D Xs N Pl).start₂ x)
    (hM : T.Made b k s m E) : Side₂ Xs b x.key s := fun e₁ hg =>
  t₂_sourced Xs N Pl hs scope e₁ hg 0 b (x, s) hb
    (reach_made₂ Xs N Pl x hO (by rw [(lengths scope hs.named).2.1]; exact hb) h0 hM) hfit

/-- **The first thread's whole clause on the state.** -/
theorem form_made₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b ≤ 19) {k : Coins Bk} {s : FirstState}
    {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hM : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Made b k s m E)
    (hr : ∃ r, L.base.recOf m.st.input.x = some r) :
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Form b k s m :=
  have h := side18_made Xs N Pl L w₀ rc x hs scope hb hM
  ⟨h.1.1.1, h, hr⟩

/-- **The shared thread's.** -/
theorem form_made₂ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) {b : Nat} (hb : b ≤ 12) {k : Coins Bk} {s : St₂}
    {m : Mid (Common W₀ Rc OnBytes.TableKey) X'} {E : Env}
    (hM : (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂).Made b k s m E) (hk : m.st.input.key = x.key)
    (hr : ∃ r, L.base.recOf x = some r) : (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂).Form b k s m := by
  refine ⟨rfl, ?_, ?_⟩
  · show Side₂ Xs b m.st.input.key s
    rw [hk]
    exact side₂_made Xs N Pl x hs scope hfit (overShared_laid₂ Xs N Pl L w₀ rc x) hb
      (fun _ h => h) hM
  · show ∃ r, L.base.recOf ⟨m.st.input.key⟩ = some r
    rw [hk]
    exact hr

end

section
variable (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) {Z : VerifierAndGoals.PublicFiles}

/-- **ONE STEP of the shared chain's clause.** -/
theorem side₂_step (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b < 12) {blk : Block St₂ (D Xs N Pl).Cl}
    (hblk : (D Xs N Pl).shared.blocksInOrder[b]? = some blk) {ft : Nat} {s s' : St₂}
    (hy : StepYes ft blk s s') {key : OnBytes.TableKey} (h : Side₂ Xs b key s) :
    Side₂ Xs (b + 1) key s' := by
  intro e₁ hg
  obtain ⟨X₀, m, h0, hm, hX, -, hL⟩ := hs.source
  obtain ⟨R, c, -, e⟩ := hy
  have q := (VerifiableInference.Desc.Sound.step_ok_iff ft blk s s' R c c.length).1 e
  exact steps₂ Xs N Pl scope (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hL
    hs.named.plan hs.named.wanted b hb blk hblk (⟨key⟩, e₁) s s' R _ q.1 q.2.2.2 (h e₁ hg)

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.reach_made₁
#print axioms AtPublicFiles.KeyThread.overShared_laid₂
#print axioms AtPublicFiles.KeyThread.reach_made₂
#print axioms AtPublicFiles.KeyThread.side18_made
#print axioms AtPublicFiles.KeyThread.side₂_made
#print axioms AtPublicFiles.KeyThread.form_made₁
#print axioms AtPublicFiles.KeyThread.form_made₂
#print axioms AtPublicFiles.KeyThread.side₂_step
