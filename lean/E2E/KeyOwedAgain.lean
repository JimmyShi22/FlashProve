-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyOwedAgain.lean: OF THE DEBT `Exchange` (Johnson/Desc/ProofFile/Honest/Thread/Pays.lean: the
items that a sub-protocol's row owes hold behind it) AT THREE SUB-PROTOCOLS OF NO KIND OF THE KEY
FILE's FIRST CHAIN (the two lookups' layers, numbers 5 and 11; the laying of the lookups' rows,
number 14): THE HALF THAT THE EQUATION ON THE STATE PAYS. A row of the table that READS an item and
leaves it open owes it again when the table is read forward. Such an item is open in front, so the
thread holds its sentence there; the step's equation carries the sentence across. WHAT THE ROW MAKES
ANEW IS NOT TREATED. On sentences and states. NOTHING IS SHOWN OF ANY PROVER.

  **`owed_again`**: GENERAL in the thread: an item that is open in front, whose sentence goes from
      the state and the oracles in front to those behind at every witness, holds behind the step, at
      every continuation of the challenges
  `again`, `anew`: the two halves of what the three rows owe · `owes_split`: the rows owe just
      these; what is owed again is open in front and plain: BY EVALUATION
  **`items_again₁`**: the first half holds behind the step: in scope, under the one premise on the
      reading (`ReadsL`)
  **`exchange_of_anew₁`**: so `Exchange` at these three is owed for the second half alone

By `fwd_eq₁` (E2E/KeyRides.lean), `keeps_stepped₁` (E2E/KeyKeepsAt.lean), `seat_behind`
(E2E/KeyBehind3.lean), `play_mid`, `play_heard` (Johnson/Desc/ProofFile/Honest/Law/Along.lean,
Thread/PaysLaw.lean). The general lemma is a step inside the proof of the threads' own `thr_next`
(Thread/PaysLaw.lean), said of an item that is owed.

Limits.
- WHAT IS LEFT: at a layer the lookup's rows and its claims on keys; at number 14 the rows on the
  ranges' group: that these hold at the honest witness is content, and is not treated.
- `owes_split` is an evaluation of OUR table's rows: it shows no row right.
- It is true also where the thread holds at nothing.

-/
import E2E.KeyRides
import E2E.KeyBehind3
import E2E.KeyStateSide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows1 (ReadsL)
open Johnson.RunOne.KeyRows23 (atSix)
open ProofFile.Honest

/-! ## 1 General in the thread -/

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **An item that is open in front and carried across holds behind.** -/
theorem owed_again {b : Nat} {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hA : Thr T b k s m E) (hS : T.Stepped blk k s m E ds y cols s') (O : List T.ι)
    (hO : ∀ i ∈ O, i ∈ T.opened b)
    (hc : ∀ i ∈ O, ∀ v, T.means m.st.input i (T.seat k m s) (T.strs E) v →
      T.means m.st.input i (T.seat k m s') (T.strs (E.add y.1)) v) :
    T.Items O k s' y.2 (E.add y.1) := by
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  intro ds' i hi
  have h0 := hA.2.2.2.1 (ds ++ ds') i (hO i hi)
  have h1 := hc i hi _ h0
  rw [seat_behind T hA.2.1 hy s', (play_mid _ _ _ _ _ hy).1, play_heard _ _ _ _ _ hy,
    List.append_assoc]
  exact h1

end

/-! ## 2 The three rows -/

/-- What the row number b reads and leaves: owed again. -/
def again : Nat → List KItem
  | 5 | 11 => [.pinT, .pin 0, .pin 1]
  | 14 => [.pin 1]
  | _ => []

/-- What it makes anew. -/
def anew : Nat → List KItem
  | 5 => [.rows 0, .kclaims 0]
  | 11 => [.rows 1, .kclaims 1]
  | 14 => [.grows]
  | _ => []

theorem owes_split : ∀ b ∈ [5, 11, 14],
    (∀ i ∈ (rowsFirst b).owes, i ∈ anew b ∨ i ∈ again b) ∧
      ∀ i ∈ again b, i ∈ fwdOpen (start₁ 2) rowsFirst b ∧ plain i = true ∧ i ≠ .grows := by
  decide

/-! ## 3 At the thread -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {Z : VerifierAndGoals.PublicFiles}

/-- **What is owed again holds behind the step.** -/
theorem items_again₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hG : ReadsL L.base.h₁) : ∀ b ∈ [5, 11, 14], ∀ blk,
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk → ∀ k s m E ds y cols s',
    Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E →
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s' →
    (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Items (again b) k s' y.2 (E.add y.1) := by
  intro b hb blk hblk k s m E ds y cols s' hT hS
  have hb' : b ∈ [2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 18] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
    rcases hb with rfl | rfl | rfl <;> simp
  obtain ⟨X₀, mm, h0, hm, hX, -, -⟩ := hs.source
  have hP := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  obtain ⟨x₀, x₁, hl⟩ := LPFD.hl_in_scope scope hP hm hX hs.named.plan
  obtain ⟨bw, hw⟩ := LPFD.hw_in_scope scope hP hm hX hs.named.plan pieces
    (rootsBefore Xs.Y.D.1 (batchRound Xs.Y.D.1))
    (groupsTold Xs.Y.told.1 (rootsBefore Xs.Y.D.1 (lastSendRound Xs.Y.D.1))
      (rootsAt Xs.Y.D.1 (lastSendRound Xs.Y.D.1)))
  have hk := keeps_stepped₁ Xs N Pl L w₀ rc x hl hw b hb' blk hblk k s m E ds y cols s' hS
  have hsp := (owes_split b hb).2
  refine owed_again (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) hT hS (again b) (fun i hi => (hsp i hi).1)
    (fun i hi v hu => ?_)
  exact fwd_eq₁ (D Xs N Pl) L.base.h₁ atSix L.meetsT (one₀ Xs) L.R hG L.kind₁ b hb' i
    (hsp i hi).2.1 (fun _ => (hsp i hi).2.2) _ s s' _ _ v hk hu

/-- **So the exchange at these three is owed for what the row makes anew alone.** -/
theorem exchange_of_anew₁ (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hG : ReadsL L.base.h₁) : ∀ b ∈ [5, 11, 14],
    (∀ blk, (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[b]? = some blk → ∀ k s m E ds y cols s',
      Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b k s m E → drawsFit blk.rounds ds = true →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s' →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Items (anew b) k s' y.2 (E.add y.1)) →
    Exchange (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) b := by
  intro b hb hnew blk hblk k s m E ds y cols s' hT hd hS ds' i hi
  rcases (owes_split b hb).1 i hi with h | h
  · exact hnew blk hblk k s m E ds y cols s' hT hd hS ds' i h
  · exact items_again₁ Xs N Pl L w₀ rc x hs scope hG b hb blk hblk k s m E ds y cols s' hT hS
      ds' i h

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.owed_again
#print axioms AtPublicFiles.KeyThread.owes_split
#print axioms AtPublicFiles.KeyThread.items_again₁
#print axioms AtPublicFiles.KeyThread.exchange_of_anew₁
