-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrWalk.lean: K8's DRAW AND K1's LATER SENDING: an accepting decision is `KeepsTr`.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.ProofFile.Honest.K9.TrAre
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.First.K8.LawFunsStay
import Johnson.Desc.Sound.FoldSteps
import Johnson.Desc.Sound.HearsOnce
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-! ## 2 Three kinds' shares -/

/-- **K8: the approximate range proof's draw.** -/
theorem k8_stepsT {Cl : Type} (p : First.K8.Par) :
    (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).Steps (KeepsTr) := by
  intro s rs gs s' h
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s s' rs gs h
  obtain ⟨tl, _, hm⟩ := (First.K8.decide_atS_iff p s s' r gs).1 h
  rw [hm.2.2.2.2.2.2.2.2]
  exact keeps_sameT (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])

theorem rootTaken_tr (F : Fork) (t w : ℕ) :
    tr (F.rootTaken t w) = tr F := tr_taken F t w

theorem commitOne_tr {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F') :
    tr F' = tr F := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_tr _ _ _)
    | cases h

theorem commitAll_tr {L : LinkCtx} : ∀ (ts : List ℕ) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → tr F' = tr F
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_tr ts F₁ F' h).trans (commitOne_tr h1)

theorem commitBehind_tr {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) :
    lnk L' = lnk L ∧ tr F' = tr F := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact ⟨rfl, commitAll_tr ts F F₁ h1⟩
    · cases h

theorem commitStep_tr {W : Type} {send : L3.Send W} {ts : List ℕ} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') :
    lnk s'.L = lnk s.L ∧ tr s'.F = tr s.F := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_tr (L' := y.1) (F' := y.2) h2

theorem commitOwn_tr {Cl : Type} {P : K1.Par} {link moment : ℕ} {arrays : Option (List ℕ)}
    {x y : K1.Owing (L3.St (_root_.Desc.Plain.DState Unit))} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (K1.commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    lnk y.held.L = lnk x.held.L ∧ tr y.held.F = tr x.held.F := by
  simp only [K1.commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (K1.laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_tr h1
  · cases h

/-- **K1: a segment's later sending.** -/
theorem k1_stepsT {Cl : Type} (P : K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.commitAtS (Cl := Cl) P link moment arrays).Steps (KeepsTr) := by
  intro s rs gs s' h
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (K1.commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := K1.owedOf s, held := { L := L, F := F, tl := tl, w := K1.stateOf s () } } rs
        gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      obtain ⟨e1, e2⟩ := commitOwn_tr h1
      rw [← h]
      exact keeps_putsT hL hF (u := K1.laid s y.held.w) hL hF e1 e2
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k8_stepsT
#print axioms VerifiableInference.Desc.LinkJoin.rootTaken_tr
#print axioms VerifiableInference.Desc.LinkJoin.commitOne_tr
#print axioms VerifiableInference.Desc.LinkJoin.commitAll_tr
#print axioms VerifiableInference.Desc.LinkJoin.commitBehind_tr
#print axioms VerifiableInference.Desc.LinkJoin.commitStep_tr
#print axioms VerifiableInference.Desc.LinkJoin.commitOwn_tr
#print axioms VerifiableInference.Desc.LinkJoin.k1_stepsT
