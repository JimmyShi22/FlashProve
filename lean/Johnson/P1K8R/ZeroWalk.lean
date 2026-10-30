-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroWalk.lean: "EVERY VIRTUAL ROW OF EVERY ARRAY OF AN OPEN LEDGER BEGINS AT COLUMN 0"
(`KeepsZero`, Johnson/P1K8R/ZeroFrame.lean) PASSES THREE KINDS' ACCEPTING DECISIONS: A SUB-PROTOCOL
WITHOUT A ROUND THAT LEAVES THE LEDGER, THE APPROXIMATE RANGE PROOF's DRAW (K8), A SEGMENT's LATER
SENDING (K1). MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksWalk.lean (its
part 2, "Three kinds' shares", and keeps_puts), WITH THE ROWS' FIRST COLUMNS (`l0s`) IN THE PLACE OF
THE ARRAYS' LOOKS AND WITHOUT THE LINK's NUMBER. Lemmas; none of the library's goals. No prover
stands in them; nothing on completeness, soundness or hiding.

  `kz_puts`   a writing of a link's context and of a ledger with the same first columns (there:
      keeps_puts)
  `quiet_kz`, `k8_kz`, **`k1_kz`**   the three kinds' decisions step in `KeepsZero` (there:
      quiet_steps, k8_steps, k1_steps)
  `rootTaken_l0s`, `commitOne_l0s`, `commitAll_l0s`   K1's routines leave the first columns (there:
      the same names with "looks")
  `commitBehind_l0s`, `commitStep_l0s`, `commitOwn_l0s`   the like
What is new against that file: nothing is argued anew. `rootTaken_l0s` holds as there: marking an
array as committed writes its field root alone.
Limits. THE DECISIONS ALONE. The other kinds' shares are not here.

-/
import Johnson.P1K8R.ZeroFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- A writing of a link's context and of a ledger with the same first columns. u: any state with
s's two readings. -/
theorem kz_puts {s u : S} {L0 L : LinkCtx} {F0 F : Fork} (hF : s.fork? = some F0)
    (uL : u.link? = some L0) (uF : u.fork? = some F0)
    (ef : F.trees.map l0s = F0.trees.map l0s) : KeepsZero s ((u.putLink L).putFork F) := by
  obtain ⟨-, r2⟩ := reads_puts u L0 F0 uL uF L F
  refine kz_of_cases fun G' hG => Or.inr ⟨F0, hF, ?_⟩
  rw [← Option.some.inj (r2.symm.trans hG), ef]

/-- A sub-protocol without a round whose function leaves the ledger. -/
theorem quiet_kz {Cl : Type} (n : String) (chain : ℕ) (link : Option ℕ)
    (piece : ℕ) (f : S → Except String S)
    (hf : ∀ s s', f s = .ok s' → s'.fork? = s.fork?) :
    (roundlessBlock (Cl := Cl) n chain link piece f).Steps KeepsZero :=
  fun s _ _ s' h => kz_same (hf s s' h)

/-- **K8: the approximate range proof's draw.** -/
theorem k8_kz {Cl : Type} (p : First.K8.Par) :
    (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).Steps KeepsZero := by
  intro s rs gs s' h
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s s' rs gs h
  obtain ⟨tl, _, hm⟩ := (First.K8.decide_atS_iff p s s' r gs).1 h
  rw [hm.2.2.2.2.2.2.2.2]
  exact kz_same (First.K8.putTl_fork _ _)

theorem rootTaken_l0s (F : Fork) (t w : ℕ) :
    (F.rootTaken t w).trees.map l0s = F.trees.map l0s :=
  map_modify_same l0s (fun X => { X with root := some w }) (fun _ => rfl) F.trees t

theorem commitOne_l0s {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F') :
    F'.trees.map l0s = F.trees.map l0s := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_l0s _ _ _)
    | cases h

theorem commitAll_l0s {L : LinkCtx} : ∀ (ts : List ℕ) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → F'.trees.map l0s = F.trees.map l0s
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
      exact (commitAll_l0s ts F₁ F' h).trans (commitOne_l0s h1)

theorem commitBehind_l0s {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) :
    L'.link = L.link ∧ F'.trees.map l0s = F.trees.map l0s := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact ⟨rfl, commitAll_l0s ts F F₁ h1⟩
    · cases h

theorem commitStep_l0s {W : Type} {send : L3.Send W} {ts : List ℕ} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') :
    s'.L.link = s.L.link ∧ s'.F.trees.map l0s = s.F.trees.map l0s := by
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
        exact commitBehind_l0s (L' := y.1) (F' := y.2) h2

theorem commitOwn_l0s {Cl : Type} {P : K1.Par} {link moment : ℕ} {arrays : Option (List ℕ)}
    {x y : K1.Owing (L3.St (_root_.Desc.Plain.DState Unit))} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (K1.commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    y.held.L.link = x.held.L.link ∧ y.held.F.trees.map l0s = x.held.F.trees.map l0s := by
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
        exact commitStep_l0s h1
  · cases h

/-- **K1: a segment's later sending.** -/
theorem k1_kz {Cl : Type} (P : K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.commitAtS (Cl := Cl) P link moment arrays).Steps KeepsZero := by
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
      obtain ⟨e1, e2⟩ := commitOwn_l0s h1
      rw [← h]
      exact kz_puts hF (u := K1.laid s y.held.w) hL hF e2
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kz_puts
#print axioms VerifiableInference.Desc.LinkJoin.quiet_kz
#print axioms VerifiableInference.Desc.LinkJoin.k8_kz
#print axioms VerifiableInference.Desc.LinkJoin.rootTaken_l0s
#print axioms VerifiableInference.Desc.LinkJoin.commitOne_l0s
#print axioms VerifiableInference.Desc.LinkJoin.commitAll_l0s
#print axioms VerifiableInference.Desc.LinkJoin.commitBehind_l0s
#print axioms VerifiableInference.Desc.LinkJoin.commitStep_l0s
#print axioms VerifiableInference.Desc.LinkJoin.commitOwn_l0s
#print axioms VerifiableInference.Desc.LinkJoin.k1_kz
