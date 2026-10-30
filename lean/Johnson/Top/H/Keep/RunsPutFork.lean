-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/RunsPutFork.lean: The kind "lookup" (K3): A YES OF ONE OF ITS THREE RUNS OF
CLAIMS ("objects", "planes", "join") TURNS THE CARRIED RECORD BY putFork ALONE: behind it the
record is s.putFork G for a ledger G. Statements and proofs.

OBJECT: objectsRun (Johnson/Top/H/K3RunsLaw.lean), K3.planesRun, K3.joinRun
  (Johnson/Desc/First/Look/K3Runs.lean), at a seat that lays its marks by putFork.
Used by Johnson/Desc/First/Look/K03StatesRaw.lean, Johnson/Top/H/Keep/PutsMore.lean,
  Johnson/Desc/First/Link/Law/SortK3Join.lean and 4 more.
LETTERS: seat (with AtS2: Johnson/Top/H/Keep/RunsAtS.lean), lm, readers, keys, n, s free.
Compiled with the whole library.

Main names:
  Puts run: every yes of the run leaves s.putFork G for some G.
  objects_puts, planes_puts, join_puts.
  PutsCore run: besides, from an open ledger F that has its sizes: G.LS = F.LS, G.ns = F.ns, and G
    has its sizes. objects_core, planes_core, join_core.

Limits. On the three runs alone. The HEARING at the digits' seat writes the smallness test's record
besides (the seat's field put): that is no run. The run "guests" leaves the record as it is
(guests_same, Johnson/Top/H/Keep/K3Block.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsAtS
import Johnson.Top.H.Keep.PadLS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat Readers planesRun joinRun)

/-- Every yes of the run leaves the record with another ledger, and nothing else turned. -/
def Puts (run : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n s cl s', run n s = .ok (cl, s') → ∃ G : Fork, s' = s.putFork G

variable (seat : Seat S Claim) (hA : AtS2 seat)
include hA

theorem objects_puts : Puts (objectsRun seat) := by
  intro n s cl s' h
  obtain ⟨F, g, _, _, rfl⟩ := objects_cut seat h
  exact ⟨_, hA.mark s _⟩

theorem planes_puts (lm : ℕ) (readers : Readers S) : Puts (planesRun seat lm readers) := by
  intro n s cl s' h
  have h0 := h
  unfold planesRun at h0
  rw [named_bind] at h0
  obtain ⟨F, e1, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨g, e2, _⟩ := h0
  obtain ⟨_, _, G, _, _, _, _, rfl⟩ := planesRun_cut seat lm readers e1 e2 h
  exact ⟨_, hA.mark s _⟩

theorem join_puts (keys : S → Option (Array Aff)) : Puts (joinRun seat keys) := by
  intro n s cl s' h
  have h0 := h
  unfold joinRun at h0
  rw [named_bind] at h0
  obtain ⟨F, e1, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨g, e2, _⟩ := h0
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys e1 e2 h
  exact ⟨_, hA.mark s _⟩

/-- The like with what the new ledger keeps: from an open ledger F that has its sizes: the
coefficients of the one equation (LS), the number of slots, and the sizes. -/
def PutsCore (run : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n s cl s' F, s.fork? = some F → Sized F → run n s = .ok (cl, s') →
    ∃ G : Fork, s' = s.putFork G ∧ G.LS = F.LS ∧ G.ns = F.ns ∧ Sized G

theorem objects_core : PutsCore (objectsRun seat) := by
  intro n s cl s' F hF hS h
  obtain ⟨F1, g, e1, _, rfl⟩ := objects_cut seat h
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans ((hA.fork s).symm.trans e1))
  exact ⟨_, hA.mark s _, rfl, rfl, paid_sized _ hS⟩

theorem planes_core (lm : ℕ) (readers : Readers S) : PutsCore (planesRun seat lm readers) := by
  intro n s cl s' F hF hS h
  obtain ⟨F1, g, e1, e2⟩ := planes_heard seat lm readers h
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans ((hA.fork s).symm.trans e1))
  obtain ⟨G, hG, rfl⟩ := planes_fills seat lm readers e1 e2 h
  obtain ⟨hs, hz, _, _⟩ := OnBytes.PscRun.hideRun_ok F G _ _ _ hS hG
  have a1 := _root_.Fo.Tp.same_LS hs
  have a2 := _root_.Fo.Tp.same_ns hs
  exact ⟨_, hA.mark s _, a1, a2, paid_sized _ hz⟩

theorem join_core (keys : S → Option (Array Aff)) : PutsCore (joinRun seat keys) := by
  intro n s cl s' F hF hS h
  obtain ⟨F1, g, e1, e2⟩ := join_heard seat keys h
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans ((hA.fork s).symm.trans e1))
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys e1 e2 h
  exact ⟨_, hA.mark s _, rfl, rfl, paid_sized _ hS⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_puts
#print axioms VerifiableInference.OnPublicFiles.planes_puts
#print axioms VerifiableInference.OnPublicFiles.join_puts
#print axioms VerifiableInference.OnPublicFiles.objects_core
#print axioms VerifiableInference.OnPublicFiles.planes_core
#print axioms VerifiableInference.OnPublicFiles.join_core
