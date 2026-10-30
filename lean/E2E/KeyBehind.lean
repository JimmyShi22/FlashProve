-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyBehind.lean: BEHIND THE YES OF A SUB-PROTOCOL OF THE KEY FILE's FIRST AND SHARED CHAIN: THE
THREAD's CLAUSE ON THE STATE HOLDS AT THE NEXT BORDER: AT ALL NINETEEN AND ALL TWELVE, those of a
kind among them, in scope; and the whole debt `Behind`
(Johnson/Desc/ProofFile/Honest/Thread/Pays.lean) at the fourteen of these that belong to no kind. By
calls. On the verifier's states alone. NOTHING IS SHOWN OF ANY PROVER.

  **`form_behind₁`**: `(laid₁ …).Form (b + 1)` behind the step of the sub-protocol number b, b < 19:
      by `side18_behind` (E2E/KeyStateSide18.lean)
  **`form_behind₂`**: the like at the shared chain, b < 12: from the clause in front by ONE of the
      library's steps (`side₂_step`, E2E/KeyMade.lean)
  **`behind₁`**: `Behind (laid₁ …) b` at b = 2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18: with
      `keeps_stepped₁` (E2E/KeyKeepsAt.lean)
  `QuietEnds₂`: what a thread over the shared chain has to bring at that chain's front and end
  **`behind₂`**: `Behind T b` at b = 0, 11, at any such thread
  `behind_laid₂`: `Behind (laid₂ …) b` at b = 0, 11
  `seat₁_laid`, `seat₂_laid`, `seat₃_laid`, `table_laid₁`, `table_laid₂`, `table_laid₃`: LEAN's WORD
      THAT A SEATED THREAD, AND ONE WHOSE TABLES ARE LAID ANEW, IS SUCH A TERM: by unfolding

ALL OF IT FOR ALL HALVES AND ALL TABLES (`laid₁`, `laid₂`, E2E/KeyRest.lean): the proofs read
neither. At the threads WITHOUT halves the step of a sub-protocol of a kind is nobody's step, and a
statement there would hold for nothing.

Limits.
- AT A SUB-PROTOCOL OF A KIND `Behind` asks besides what its step keeps, which is a letter there: so
  the whole debt is paid at none of these; the clause on the state is.
- THE CLAUSE ON THE STATE IS WHAT E2E/KeyRest.lean LAYS: at the shared chain it speaks at every good
  state of the first chain, and of everything where there is none.
- NOTHING IS ASKED OF THE INSTANCE: that the key fits the shape's index is owed where the shared
  chain's clause is first laid: at its start (E2E/KeyMade.lean).
- The last chain is not treated.
- It is true also where the thread holds at nothing.

-/
import E2E.KeyMade
import E2E.KeyLaid

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces)
open Johnson.RunOne.KeyRows23 (St₂)
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

/-- **The first chain: the clause on the state, behind each of the nineteen.** -/
theorem form_behind₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b < 19) {blk : Block FirstState Claim}
    (hblk : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk) {k : Coins Bk}
    {s s' : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Unit) X'} {cols : List OpenedColumn}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E)
    (hS : (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s') :
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Form (b + 1) k s' y.2 := by
  have hside := side18_behind Xs N Pl L w₀ rc x hs scope hb hblk hT hS
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have hi : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hy).1
  obtain ⟨-, -, r, hr⟩ := hT.2.2.1
  refine ⟨hside.1.1.1, hside, r, ?_⟩
  show L.base.recOf y.2.st.input.x = some r
  rw [hi]
  exact hr

/-- **The shared chain: the clause on the state, behind each of the twelve.** -/
theorem form_behind₂ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    {b : Nat} (hb : b < 12) {blk : Block St₂ (D Xs N Pl).Cl}
    (hblk : (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂).bs[b]? = some blk) {k : Coins Bk}
    {s s' : St₂} {m : Mid (Common W₀ Rc OnBytes.TableKey) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Common W₀ Rc OnBytes.TableKey) X'} {cols : List OpenedColumn}
    (hT : Thr (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂) b k s m E)
    (hS : (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂).Stepped blk k s m E ds y cols s') :
    (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂).Form (b + 1) k s' y.2 := by
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have hi : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hy).1
  obtain ⟨-, hside, r, hr⟩ := hT.2.2.1
  have hside' : Side₂ Xs b m.st.input.key s := hside
  have hr' : L.base.recOf ⟨m.st.input.key⟩ = some r := hr
  refine ⟨rfl, ?_, r, ?_⟩
  · show Side₂ Xs (b + 1) y.2.st.input.key s'
    rw [hi]
    exact side₂_step Xs N Pl hs scope hb hblk (stepYes_of_step hS.2) hside'
  · show L.base.recOf ⟨y.2.st.input.key⟩ = some r
    rw [hi]
    exact hr'

end

section
open VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23 (Fk oneAt)
open LPFD (hl_in_scope hw_in_scope)
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {hs₂ : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X')}
  {tb₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **THE WHOLE DEBT, at the first chain's twelve of no kind.** -/
theorem behind₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ∀ b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18],
      Behind (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b := by
  intro b hb blk hblk k s m E ds y cols s' hT _ hS
  obtain ⟨X₀, mm, h0, hm, hX, -, -⟩ := hs.source
  have hP := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope scope hP hm hX hs.named.plan
  obtain ⟨bw, hw⟩ := hw_in_scope scope hP hm hX hs.named.plan pieces
    (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))
    (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
      (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1)))
  have hb19 : b < 19 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  exact ⟨form_behind₁ Xs N Pl L w₀ rc x hs scope hb19 hblk hT hS, trivial,
    keeps_stepped₁ Xs N Pl L w₀ rc x hl hw b hb blk hblk k s m E ds y cols s' hS⟩

/-- **What a thread over the shared chain has to bring at that chain's front and end**, where the
state stays as it is: its form goes on to the next border, whatever is played; so do its riders;
and its letter `keeps` holds of a state and itself. -/
structure QuietEnds₂ {S Cl V W Xh Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W Xh Pb) : Prop where
  form : ∀ b ∈ [0, 11], ∀ k s (m m' : Mid W Xh), T.Form b k s m → T.Form (b + 1) k s m'
  rides : ∀ b ∈ [0, 11], ∀ w s, T.rides b w s → T.rides (b + 1) w s
  keeps : ∀ b ∈ [0, 11], ∀ s, T.keeps b s s

/-- The whole debt at the front and end of `laid₂`. -/
theorem behind_laid₂ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ∀ b ∈ [0, 11], Behind (laid₂ Xs N Pl L w₀ rc x hs₂ tb₂) b := by
  intro b hb blk hblk k s m E ds y cols s' hT _ hS
  have hb12 : b < 12 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  have hy := stepYes_of_step hS.2
  have hblk' : (D Xs N Pl).shared.blocksInOrder[b]? = some blk := hblk
  have e : s' = s := same_ends₂ Xs N Pl (lengths scope hs.named).2.1 _ b hb blk hblk' s s' hy
  refine ⟨form_behind₂ Xs N Pl L w₀ rc x hs scope hb12 hblk hT hS, trivial, ?_⟩
  subst e
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl <;> rfl

/-- **THE WHOLE DEBT, at the shared chain's front and end.** -/
theorem behind₂ {V W Xh Pb : Type} {T : Thread Bk (D Xs N Pl).S₂ (D Xs N Pl).Cl V W Xh Pb}
    (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hO : OverShared Xs N Pl T) (hQ : QuietEnds₂ T) : ∀ b ∈ [0, 11], Behind T b := by
  intro b hb blk hblk k s m E ds y cols s' hT _ hS
  have hy := stepYes_of_step hS.2
  have hblk' := hblk
  rw [hO.bs] at hblk'
  have e : s' = s := same_ends₂ Xs N Pl (lengths scope hs.named).2.1 _ b hb blk hblk' s s' hy
  subst e
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hp⟩, -⟩ := hM
  have hi : y.2.st.input = m.st.input := (play_mid _ _ _ _ _ hp).1
  refine ⟨hQ.form b hb k _ _ _ hT.2.2.1, ?_, hQ.keeps b hb _⟩
  rw [hi]
  exact hQ.rides b hb _ _ hT.2.2.2.2.2.1

end

/-! ## A seated thread is such a term -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X₀' X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (H : Prover W₀ Rc Xi OnBytes.TableKey Unit X₀' X')

theorem seat₁_laid (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table) :
    AtPublicFiles.KeyLink.seat₁ (D Xs N Pl) H (laid₁ Xs N Pl L w₀ rc x hs tb) =
      laid₁ Xs N Pl L w₀ rc x H.first tb := rfl

theorem seat₂_laid (hs : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀'))
    (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table) :
    AtPublicFiles.KeyLink.seat₂ (D Xs N Pl) H (laid₂ Xs N Pl L w₀ rc x hs tb) =
      laid₂ Xs N Pl L w₀ rc x H.shared tb := rfl

theorem seat₃_laid (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table) :
    AtPublicFiles.KeyLink.seat₃ (D Xs N Pl) H (laid₃ Xs N Pl L w₀ rc x hs tb) =
      laid₃ Xs N Pl L w₀ rc x H.second tb := rfl

theorem table_laid₁ (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (tb tb' : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table) :
    { laid₁ Xs N Pl L w₀ rc x hs tb with table := tb' } = laid₁ Xs N Pl L w₀ rc x hs tb' := rfl

theorem table_laid₂ (hs : List (Placed Empty (Common W₀ Rc OnBytes.TableKey) X₀'))
    (tb tb' : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table) :
    { laid₂ Xs N Pl L w₀ rc x hs tb with table := tb' } = laid₂ Xs N Pl L w₀ rc x hs tb' := rfl

theorem table_laid₃ (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (tb tb' : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table) :
    { laid₃ Xs N Pl L w₀ rc x hs tb with table := tb' } = laid₃ Xs N Pl L w₀ rc x hs tb' := rfl

/-- The threads without halves are the case of no halves and the structure's tables. -/
theorem filled_laid₁ : filled₁ (X' := X') Xs N Pl L w₀ rc x = laid₁ Xs N Pl L w₀ rc x [] L.table₁ :=
  rfl

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.seat₁_laid
#print axioms AtPublicFiles.KeyThread.seat₂_laid
#print axioms AtPublicFiles.KeyThread.seat₃_laid
#print axioms AtPublicFiles.KeyThread.table_laid₁
#print axioms AtPublicFiles.KeyThread.table_laid₂
#print axioms AtPublicFiles.KeyThread.behind_laid₂
#print axioms AtPublicFiles.KeyThread.table_laid₃
#print axioms AtPublicFiles.KeyThread.filled_laid₁
#print axioms AtPublicFiles.KeyThread.form_behind₁
#print axioms AtPublicFiles.KeyThread.form_behind₂
#print axioms AtPublicFiles.KeyThread.behind₁
#print axioms AtPublicFiles.KeyThread.behind₂
