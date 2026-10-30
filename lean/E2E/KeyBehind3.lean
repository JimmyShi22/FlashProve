-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyBehind3.lean: BEHIND THE YES OF A SUB-PROTOCOL OF THE KEY FILE's LAST CHAIN THE THREAD's
CLAUSE ON THE STATE HOLDS AT THE NEXT BORDER: AT ALL FOUR, the two of a kind among them, in scope;
the whole debt `Behind` (Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) at the two of no kind
(number 1: the test on the taken trees' sources; number 3: the chain's end); AND THE CLAUSE AT THE
CHAIN's START, from the two earlier threads at their last borders and the start's yes. At the
threads with any halves and any tables (`laid₁`, `laid₃`, E2E/KeyRest.lean), and any thread over
the shared chain that begins at the description's start. By calls. On the verifier's states alone. NOTHING IS SHOWN OF ANY PROVER.

  **`seat_behind`**: GENERAL in the thread: behind a run of the frame's play, a thread reads what it
      is handed as in front: the input is the same, and so are the challenges in front of the chain
  **`form_behind₃`**: `(laid₃ …).Form (b + 1)` behind the step of the sub-protocol number b, b < 4:
      from the clause in front by ONE of the library's four steps (`side₃_step`, E2E/KeySide3.lean)
  **`behind₃`**: `Behind (laid₃ …) b` at b = 1, 3: with `keeps_filled₃` (E2E/KeyKeepsAt.lean)
  **`side₃_of_threads`**: THE START: from the first thread at border 19 at e₁, any thread over the
      shared chain that begins at the description's start, at border 12 at e₂, and the yes of the last chain's start at them, in scope,
      where the key fits: `Side₃` at border 0 at ((x,
      e₁, e₂), s₃): `door_of_threads` (E2E/KeySideCash.lean) and `side₃_start`

`seat_behind` is a step inside the proof of the threads' own `thr_next`
(Johnson/Desc/ProofFile/Honest/Thread/PaysLaw.lean), said by itself.

Limits.
- AT A SUB-PROTOCOL OF A KIND `Behind` asks besides what its step keeps, which is a letter there.
- `side₃_of_threads` speaks at (x, e₁, e₂), and the last thread is handed the values of the letter
  `ends`.

- It is true also where a thread holds at nothing.

-/
import E2E.KeySide3
import E2E.KeySideCash
import E2E.KeyKeepsAt
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces)
open Johnson.RunOne.KeyRows23 (St₂ St₃)
open ProofFile.Honest

/-! ## 1 What a thread is handed, behind a run of play -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

theorem seat_behind {b : Nat} {k : Coins Bk} {m : Mid W X} {ss : List (Step W X)}
    {ds : List Fmt.Drawn} {back : List Fmt.RoundView} {y : List Played × Mid W X} (hF : T.Fit b m)
    (hy : play ss ds back m = .ok y) (s' : S) : T.seat k y.2 s' = T.seat k m s' := by
  unfold Thread.seat
  rw [(play_mid _ _ _ _ _ hy).1, play_heard _ _ _ _ _ hy,
    List.take_append_of_le_length (by rw [T.heard_length hF]; exact Nat.le_add_right _ _)]

end

/-! ## 2 At the last thread -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' X₀' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₃ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₃ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **The clause on the state, behind each of the four.** -/
theorem form_behind₃ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b < 4) {blk : Block St₃ Claim}
    (hblk : (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃).bs[b]? = some blk) {k : Coins Bk} {s s' : St₃}
    {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Unit) X'} {cols : List OpenedColumn}
    (hT : Thr (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃) b k s m E)
    (hS : (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃).Stepped blk k s m E ds y cols s') :
    (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃).Form (b + 1) k s' y.2 := by
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have hseat := seat_behind (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃) (k := k) hT.2.1 hy s'
  have hside : Side₃ Xs Pl b ((laid₃ Xs N Pl L w₀ rc x hs₃ tb₃).seat k m s) := hT.2.2.1.2
  have hnext : Side₃ Xs Pl (b + 1) ((laid₃ Xs N Pl L w₀ rc x hs₃ tb₃).seat k m s') :=
    side₃_step Xs N Pl hs scope hb hblk (stepYes_of_step hS.2) hside
  unfold Thread.Form
  rw [hseat]
  exact ⟨hnext.1.shape, hnext⟩

/-- **THE WHOLE DEBT, at the two of no kind.** -/
theorem behind₃ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ∀ b ∈ [1, 3], Behind (laid₃ Xs N Pl L w₀ rc x hs₃ tb₃) b := by
  intro b hb blk hblk k s m E ds y cols s' hT _ hS
  have hb4 : b < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  exact ⟨form_behind₃ Xs N Pl L w₀ rc x hs scope hb4 hblk hT hS, trivial,
    keeps_filled₃ Xs N Pl L w₀ rc x b hb blk hblk s s' (stepYes_of_step hS.2)⟩

/-- **THE START**, from the two earlier threads at their last borders. -/
theorem side₃_of_threads {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hfit : KeyFits Xs x) {k₁ k₂ : Coins Bk} {e₁ : FirstState} {e₂ : St₂}
    {m₁ : Mid (Local W₀ Rc Xi Unit) X'} {m₂ : Mid W Xh}
    {E₁ E₂ : Env} (h₁ : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) 19 k₁ e₁ m₁ E₁)
    (hO : OverShared Xs N Pl T) (hB : Begun₂ Xs N Pl x T) (h₂ : Thr T 12 k₂ e₂ m₂ E₂) {s₃ : St₃}
    (hst : (D Xs N Pl).start₃ x e₁ e₂ = .ok s₃) : Side₃ Xs Pl 0 ((x, e₁, e₂), s₃) :=
  side₃_start Xs N Pl x e₁ e₂ s₃ hst
    (door_of_threads Xs N Pl L w₀ rc x hs scope hfit h₁ hO hB h₂).1

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.seat_behind
#print axioms AtPublicFiles.KeyThread.form_behind₃
#print axioms AtPublicFiles.KeyThread.behind₃
#print axioms AtPublicFiles.KeyThread.side₃_of_threads
