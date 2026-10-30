-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/PutsMore.lean: The kind "lookup" (K3): WHAT A YES OF ONE OF ITS THREE RUNS OF
CLAIMS ("objects", "planes", "join") LEAVES, WITH NO PREMISE ON THE LEDGER's SIZES: a ledger F was
open; behind the run the state is s.putFork G; and G has F's next slot, number of slots,
coefficients of the one equation (LS) and planned number of claims. AND WHAT FOLLOWS IN THE LETTERS
OF THE KIND "batching" (K9): KeepsDoor, good9, numOf; and, from PutsCore
(Johnson/Top/H/Keep/RunsPutFork.lean), "a ledger with its sizes stays open". Statements and proofs.

OBJECT: objectsRun, K3.planesRun, K3.joinRun at a seat with AtS2; Fork.hide, Fork.hideRun,
  Fork.paid.
Used by Johnson/Desc/First/Link/Law/SortK3Join.lean and Johnson/Desc/First/Link/Law/SortK3More.lean.
LETTERS: seat, lm, readers, keys; run: any run with PutsMore | PutsCore; u.
Compiled with the whole library.

Main names:
  Frame4 F G: G.next = F.next, G.ns = F.ns, G.LS = F.LS, G.planClaimsF = F.planClaimsF.
  Frame4.trans, frame4_paid, frame4_hide, frame4_hideSteps, frame4_hideRun.
  PutsMore run. objects_more, planes_more, join_more.
  funs_putFork4: S.putFork leaves S.funs?.
  keepsDoor_of_more, good9_of_more, numOf_of_more: from PutsMore.
  sizedOpen_of_core, sizedLSOpen_of_core: from PutsCore: in the unfolded text of
    HasFork (Johnson/Desc/First/Link/Law/SizedRides.lean).

Limits. On the three bare runs. That the run which a link states at an entry IS the bare run is
another file's. Nothing on what the claims are worth.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsPutFork
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.First.Batch.Law.MovesDoor
import Johnson.Desc.First.Batch.Law.RowsRide
import Johnson.Desc.First.Batch.Law.FitsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat Readers planesRun joinRun)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (KeepsDoor good9 numOf)

/-- Four fields of the ledger are the same. -/
def Frame4 (F G : Fork) : Prop :=
  G.next = F.next ∧ G.ns = F.ns ∧ G.LS = F.LS ∧ G.planClaimsF = F.planClaimsF

theorem Frame4.refl (F : Fork) : Frame4 F F := ⟨rfl, rfl, rfl, rfl⟩

theorem Frame4.trans {F G H : Fork} (a : Frame4 F G) (b : Frame4 G H) : Frame4 F H :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.trans a.2.2.2⟩

theorem frame4_paid (F : Fork) (i : ℕ) : Frame4 F (F.paid i) := ⟨rfl, rfl, rfl, rfl⟩

theorem frame4_hide {F G : Fork} {j : ℕ} {y factor : E} (h : F.hide j y factor = some G) :
    Frame4 F G := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp at h

theorem frame4_hideSteps (factor : E) : ∀ (l : List E) (first : ℕ) (A : Fork) (x : ℕ × Fork),
    l.foldlM (Fork.hideStep factor) (first, A) = some x → Frame4 A x.2
  | [], first, A, x, h => by
    have hx : (first, A) = x := by simpa using h
    subst hx
    exact Frame4.refl A
  | y :: l, first, A, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, A) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : A.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        exact (frame4_hide hh).trans (frame4_hideSteps factor l _ _ _ h2)

theorem frame4_hideRun {F G : Fork} {first : ℕ} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : Frame4 F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact frame4_hideSteps factor _ _ _ _ hx
  · simp at h

/-- **Every yes of the run: a ledger was open; the state behind is s.putFork G; four fields of G are
F's.** No premise on the sizes. -/
def PutsMore (run : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n s cl s', run n s = .ok (cl, s') →
    ∃ F G : Fork, s.fork? = some F ∧ s' = s.putFork G ∧ Frame4 F G

section
variable (seat : Seat S Claim) (hA : AtS2 seat)
include hA

theorem objects_more : PutsMore (objectsRun seat) := by
  intro n s cl s' h
  obtain ⟨F, g, e1, _, rfl⟩ := objects_cut seat h
  exact ⟨F, _, (hA.fork s).symm.trans e1, hA.mark s _, frame4_paid F _⟩

theorem planes_more (lm : ℕ) (readers : Readers S) : PutsMore (planesRun seat lm readers) := by
  intro n s cl s' h
  obtain ⟨F, g, e1, e2⟩ := planes_heard seat lm readers h
  obtain ⟨G, hG, rfl⟩ := planes_fills seat lm readers e1 e2 h
  exact ⟨F, _, (hA.fork s).symm.trans e1, hA.mark s _, (frame4_hideRun hG).trans (frame4_paid G _)⟩

theorem join_more (keys : S → Option (Array Aff)) : PutsMore (joinRun seat keys) := by
  intro n s cl s' h
  obtain ⟨F, g, e1, e2⟩ := join_heard seat keys h
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys e1 e2 h
  exact ⟨F, _, (hA.fork s).symm.trans e1, hA.mark s _, frame4_paid F _⟩

end

/-- S.putFork leaves the tables. (The same sentence, putFork_funs, stands in
Johnson/Desc/First/K8/LawCondK1.lean: typed again here, three lines, so
that this file stands on few files.) -/
theorem funs_putFork4 (s : S) (G : Fork) : (s.putFork G).funs? = s.funs? := by
  cases hh : s.here with
  | between => simp [S.funs?, S.putFork, hh]
  | fin _ => simp [S.funs?, S.putFork, hh]
  | mem _ => simp [S.funs?, S.putFork, hh]
  | lay a => simp [S.funs?, S.putFork, hh]
  | att a => simp [S.funs?, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.funs?, S.putFork, hh, ho]
    | true => simp [S.funs?, S.putFork, hh, ho]

section
variable {run : ℕ → S → Except String (List Claim × S)}

/-- **All that the door reads beside the ledger stays.** -/
theorem keepsDoor_of_more (h : PutsMore run) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor atS e e₁ := by
  intro n e c e₁ hr a ha
  obtain ⟨F, G, hF, rfl, fr⟩ := h n e c e₁ hr
  obtain rfl : a.F = F := Option.some.inj ((fork_of_atS ha).symm.trans hF)
  obtain ⟨a₁, h1, L⟩ := atS_putFork e a G ha fr.1
  exact ⟨a₁, h1, by rw [L.L], by rw [L.d]⟩

/-- **good9 stays.** -/
theorem good9_of_more (h : PutsMore run) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → good9 e → good9 e₁ := by
  rintro n e c e₁ hr ⟨a, ha, hh, hz⟩
  obtain ⟨F, G, hF, rfl, fr⟩ := h n e c e₁ hr
  obtain rfl : a.F = F := Option.some.inj ((fork_of_atS ha).symm.trans hF)
  obtain ⟨a₁, h1, L⟩ := atS_putFork e a G ha fr.1
  exact ⟨a₁, h1, by rw [L.L]; exact hh, by rw [L.F, fr.2.2.1, fr.2.1]; exact hz⟩

/-- **The numbers stay.** -/
theorem numOf_of_more (h : PutsMore run) (u : HTailF2) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → numOf u e₁ = numOf u e := by
  intro n e c e₁ hr
  obtain ⟨F, G, hF, rfl, fr⟩ := h n e c e₁ hr
  unfold numOf
  rw [pf_tl, funs_putFork4, fork_putFork e F G hF, hF]
  show (_, _, some G.planClaimsF) = (_, _, some F.planClaimsF)
  rw [fr.2.2.2]

/-- **A ledger with its sizes stays open.** -/
theorem sizedOpen_of_core (h : PutsCore run) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → (∃ G, e.fork? = some G ∧ Sized G) →
      ∃ G, e₁.fork? = some G ∧ Sized G := by
  rintro n e c e₁ hr ⟨F, hF, hS⟩
  obtain ⟨G, rfl, _, _, hG⟩ := h n e c e₁ F hF hS hr
  exact ⟨G, fork_putFork e F G hF, hG⟩

/-- The like with "one coefficient for each slot". -/
theorem sizedLSOpen_of_core (h : PutsCore run) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → (∃ G, e.fork? = some G ∧ Sized G ∧ G.LS.size = G.ns) →
      ∃ G, e₁.fork? = some G ∧ Sized G ∧ G.LS.size = G.ns := by
  rintro n e c e₁ hr ⟨F, hF, hS, hL⟩
  obtain ⟨G, rfl, e1, e2, hG⟩ := h n e c e₁ F hF hS hr
  exact ⟨G, fork_putFork e F G hF, hG, by rw [e1, e2]; exact hL⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.Frame4.refl
#print axioms VerifiableInference.OnPublicFiles.Frame4.trans
#print axioms VerifiableInference.OnPublicFiles.frame4_paid
#print axioms VerifiableInference.OnPublicFiles.frame4_hide
#print axioms VerifiableInference.OnPublicFiles.frame4_hideSteps
#print axioms VerifiableInference.OnPublicFiles.frame4_hideRun
#print axioms VerifiableInference.OnPublicFiles.objects_more
#print axioms VerifiableInference.OnPublicFiles.planes_more
#print axioms VerifiableInference.OnPublicFiles.join_more
#print axioms VerifiableInference.OnPublicFiles.funs_putFork4
#print axioms VerifiableInference.OnPublicFiles.keepsDoor_of_more
#print axioms VerifiableInference.OnPublicFiles.good9_of_more
#print axioms VerifiableInference.OnPublicFiles.numOf_of_more
#print axioms VerifiableInference.OnPublicFiles.sizedOpen_of_core
#print axioms VerifiableInference.OnPublicFiles.sizedLSOpen_of_core
