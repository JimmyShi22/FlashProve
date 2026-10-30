-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/PutsKap.lean: The kind "lookup" (K3): A YES OF ONE OF ITS THREE RUNS OF CLAIMS
("objects", "planes", "join") LEAVES, OF THE OPEN LEDGER, THE MAP OF HANDED-OUT WEIGHTS, THE PLAN's
NUMBER OF CLAIMS AND THE COUNT OF CLAIMS. The sister of Johnson/Top/H/Keep/PutsMore.lean at three
other fields; no premise on the ledger's sizes. Statements and proofs.

OBJECT: objectsRun, K3.planesRun, K3.joinRun at a seat with AtS2; Fork.hide, Fork.hideRun,
  Fork.paid.
Used by Johnson/Desc/First/Link/Law/SortK3Join.lean,
  Johnson/Desc/First/Link/Law/SortK3ObjectsKap.lean and
  Johnson/Desc/First/Link/Law/SortK3PlanesKap.lean.
LETTERS: seat, lm, readers, keys; run: any run with PutsKap.
Compiled with the whole library.

Main names:
  FrameKap F G: G.kapMapF = F.kapMapF, G.planClaimsF = F.planClaimsF, G.nClaim = F.nClaim.
  FrameKap.trans, frameKap_paid, frameKap_hide, frameKap_hideSteps, frameKap_hideRun.
  PutsKap run. objects_kap, planes_kap, join_kap.
  kapOf_of_puts: THE END: in the unfolded text of kapOf (KapRuns.lean):
    s.fork?.map fun F => (F.kapMapF, F.planClaimsF, F.nClaim).

Limits. On the three bare runs. That the run which a link states at an entry IS the bare run is
another file's.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsPutFork
import Johnson.Top.H.Keep.K3Inv
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat Readers planesRun joinRun)

/-- Three fields of the ledger are the same. -/
def FrameKap (F G : Fork) : Prop :=
  G.kapMapF = F.kapMapF ∧ G.planClaimsF = F.planClaimsF ∧ G.nClaim = F.nClaim

theorem FrameKap.refl (F : Fork) : FrameKap F F := ⟨rfl, rfl, rfl⟩

theorem FrameKap.trans {F G H : Fork} (a : FrameKap F G) (b : FrameKap G H) : FrameKap F H :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.trans a.2.2⟩

theorem frameKap_paid (F : Fork) (i : ℕ) : FrameKap F (F.paid i) := ⟨rfl, rfl, rfl⟩

theorem frameKap_hide {F G : Fork} {j : ℕ} {y factor : E} (h : F.hide j y factor = some G) :
    FrameKap F G := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, rfl⟩
  · simp at h

theorem frameKap_hideSteps (factor : E) : ∀ (l : List E) (first : ℕ) (A : Fork) (x : ℕ × Fork),
    l.foldlM (Fork.hideStep factor) (first, A) = some x → FrameKap A x.2
  | [], first, A, x, h => by
    have hx : (first, A) = x := by simpa using h
    subst hx
    exact FrameKap.refl A
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
        exact (frameKap_hide hh).trans (frameKap_hideSteps factor l _ _ _ h2)

theorem frameKap_hideRun {F G : Fork} {first : ℕ} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : FrameKap F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact frameKap_hideSteps factor _ _ _ _ hx
  · simp at h

/-- **Every yes of the run: a ledger was open; the state behind is s.putFork G; three fields of G
are F's.** No premise on the sizes. -/
def PutsKap (run : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n s cl s', run n s = .ok (cl, s') →
    ∃ F G : Fork, s.fork? = some F ∧ s' = s.putFork G ∧ FrameKap F G

section
variable (seat : Seat S Claim) (hA : AtS2 seat)
include hA

theorem objects_kap : PutsKap (objectsRun seat) := by
  intro n s cl s' h
  obtain ⟨F, g, e1, _, rfl⟩ := objects_cut seat h
  exact ⟨F, _, (hA.fork s).symm.trans e1, hA.mark s _, frameKap_paid F _⟩

theorem planes_kap (lm : ℕ) (readers : Readers S) : PutsKap (planesRun seat lm readers) := by
  intro n s cl s' h
  obtain ⟨F, g, e1, e2⟩ := planes_heard seat lm readers h
  obtain ⟨G, hG, rfl⟩ := planes_fills seat lm readers e1 e2 h
  exact ⟨F, _, (hA.fork s).symm.trans e1, hA.mark s _,
    (frameKap_hideRun hG).trans (frameKap_paid G _)⟩

theorem join_kap (keys : S → Option (Array Aff)) : PutsKap (joinRun seat keys) := by
  intro n s cl s' h
  obtain ⟨F, g, e1, e2⟩ := join_heard seat keys h
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys e1 e2 h
  exact ⟨F, _, (hA.fork s).symm.trans e1, hA.mark s _, frameKap_paid F _⟩

end

/-- **THE END**: the three numbers of the open ledger stay. -/
theorem kapOf_of_puts {run : ℕ → S → Except String (List Claim × S)} (h : PutsKap run) :
    ∀ n e c e₁, run n e = .ok (c, e₁) →
      (e₁.fork?.map fun F => (F.kapMapF, F.planClaimsF, F.nClaim)) =
        e.fork?.map fun F => (F.kapMapF, F.planClaimsF, F.nClaim) := by
  intro n e c e₁ hr
  obtain ⟨F, G, hF, rfl, fr⟩ := h n e c e₁ hr
  rw [fork_putFork e F G hF, hF]
  show some (G.kapMapF, G.planClaimsF, G.nClaim) = some (F.kapMapF, F.planClaimsF, F.nClaim)
  rw [fr.1, fr.2.1, fr.2.2]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.FrameKap.refl
#print axioms VerifiableInference.OnPublicFiles.FrameKap.trans
#print axioms VerifiableInference.OnPublicFiles.frameKap_paid
#print axioms VerifiableInference.OnPublicFiles.frameKap_hide
#print axioms VerifiableInference.OnPublicFiles.frameKap_hideSteps
#print axioms VerifiableInference.OnPublicFiles.frameKap_hideRun
#print axioms VerifiableInference.OnPublicFiles.objects_kap
#print axioms VerifiableInference.OnPublicFiles.planes_kap
#print axioms VerifiableInference.OnPublicFiles.join_kap
#print axioms VerifiableInference.OnPublicFiles.kapOf_of_puts
