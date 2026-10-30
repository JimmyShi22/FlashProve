-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/K3Inv.lean: The kind "lookup" (K3): ITS PROMISE ON THE RECORD for the
law "a stretch of slots that is owed stays owed along a walk of steps" (StepKeepsUnder,
Johnson/Desc/Part/LedgerKeeps.lean), AND THAT LAW OF K3's THREE RUNS OF CLAIMS AND, AT ITS OWN
STRETCH, OF ITS decide. Definitions, statements and proofs.

Why a promise. The run "planes" fills the slots of the leaves' sumcheck's hiding polynomial late, at
an address that it reads off the record: g.leaves.first, g what was heard. Over ALL records such a
run keeps no stretch. Under a promise that pins the address it does.

K3 meets the law in two roles.
(A) Its steps stand beside ANOTHER's stretch of n slots from a on. The promise K3InvA: the open
    ledger has its sizes; whatever lookup has been heard at this seat, its leaves' stretch lies
    apart from the stretch that is watched.
(B) Its OWN stretch, from g.leaves.first on. The promise K3InvB g: what was heard is still this g;
    the open ledger has its sizes. The stretch's own writer, "planes", is left out of the walk.

Main names:
  lvLen g: the number of slots that "planes" fills: the length of the leaves' sumcheck's walk: a
    function of what was heard. (That it is 1 + 2 d + 5 behind a hearing: not here.)
  K3Apart, K3InvA, K3InvB: the promises. runStep run: a run of claims as a step, in the form of
    LedgerKeeps.lean's stepsOf.
  objects_keepsA, join_keepsA, planes_keepsA: role (A), at every seat whose functions fit.
  objects_keepsB, join_keepsB: role (B). decide_keepsB: under K3InvB the kind's decide refuses (it
    asks that nothing is heard yet): so its step is empty and need not be left out.
  planes_fills: what "planes" does to the marks: it writes within its own stretch.

Limits. Role (A) of decide (it writes above the next slot, and hands K3Apart on) and the walk's
start in role (B) are other files'. That another kind's step leaves "heard" and the sizes is that
kind's. At a promise that no record meets all is free. A run that always refuses has these laws
emptily.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LedgerKeeps
import Johnson.Desc.Part.LedgerKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers)
open VerifiableInference.Desc.Part (StepKeepsUnder decides)

variable {S Cl : Type}

/-! ## The promises -/

/-- The number of slots that "planes" fills. -/
def lvLen (g : Forest.Heard) : ℕ := g.leaves.walk.1.length

/-- Whatever lookup has been heard, its leaves' stretch lies apart from the n slots from a on. -/
def K3Apart (heard : S → Option Forest.Heard) (a n : ℕ) (s : S) : Prop :=
  ∀ g, heard s = some g → g.leaves.first + lvLen g ≤ a ∨ a + n ≤ g.leaves.first

/-- **Role (A).** -/
def K3InvA (fork : S → Option Fork) (heard : S → Option Forest.Heard) (a n : ℕ) (s : S) : Prop :=
  (∀ F, fork s = some F → Sized F) ∧ K3Apart heard a n s

/-- **Role (B).** -/
def K3InvB (fork : S → Option Fork) (heard : S → Option Forest.Heard) (g : Forest.Heard) (s : S) :
    Prop :=
  heard s = some g ∧ ∀ F, fork s = some F → Sized F

/-- A run of claims as a step: at any number, whatever claims it hands out. -/
def runStep (run : ℕ → S → Except String (List Cl × S)) : S → S → Prop :=
  fun s s' => ∃ i l, run i s = .ok (l, s')

/-! ## A mark on a debt turns no slot -/

theorem owed_paid {F : Fork} {a n : ℕ} (h : SlotsOwed F a n) (i : ℕ) : SlotsOwed (F.paid i) a n :=
  ⟨h.1, h.2⟩

/-- What a step that lays a ledger G by the seat's "mark" hands on, in both roles. -/
theorem mark_keeps (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) {s : S}
    {F G : Fork} (hF : seat.fork s = some F) (hS : Sized F) (hL : Later F G) :
    seat.fork (seat.mark s G) = some G ∧ seat.heard (seat.mark s G) = seat.heard s ∧
      ∀ H, seat.fork (seat.mark s G) = some H → Sized H := by
  refine ⟨hs.markFork s F G hF, hs.markHeard s F G hF, fun H hH => ?_⟩
  obtain rfl : G = H := Option.some.inj ((hs.markFork s F G hF).symm.trans hH)
  exact hL.sized hS

/-! ## What a yes of each run is made of -/

theorem objects_cut (seat : Seat S Cl) {i : ℕ} {s s' : S} {l : List Cl}
    (h : objectsRun seat i s = .ok (l, s')) :
    ∃ F g, seat.fork s = some F ∧ seat.heard s = some g ∧
      s' = seat.mark s (F.paid g.owedObjects) := by
  unfold objectsRun at h
  rw [named_bind] at h
  obtain ⟨F, e1, h⟩ := h
  rw [named_bind] at h
  obtain ⟨g, e2, h⟩ := h
  exact ⟨F, g, e1, e2, (congrArg Prod.snd (Except.ok.inj h)).symm⟩

theorem join_heard (seat : Seat S Cl) (keys : S → Option (Array Aff)) {i : ℕ} {s s' : S}
    {l : List Cl} (h : joinRun seat keys i s = .ok (l, s')) :
    ∃ F g, seat.fork s = some F ∧ seat.heard s = some g := by
  unfold joinRun at h
  rw [named_bind] at h
  obtain ⟨F, e1, h⟩ := h
  rw [named_bind] at h
  obtain ⟨g, e2, -⟩ := h
  exact ⟨F, g, e1, e2⟩

theorem planes_heard (seat : Seat S Cl) (lm : ℕ) (readers : Readers S) {i : ℕ} {s s' : S}
    {l : List Cl} (h : planesRun seat lm readers i s = .ok (l, s')) :
    ∃ F g, seat.fork s = some F ∧ seat.heard s = some g := by
  unfold planesRun at h
  rw [named_bind] at h
  obtain ⟨F, e1, h⟩ := h
  rw [named_bind] at h
  obtain ⟨g, e2, -⟩ := h
  exact ⟨F, g, e1, e2⟩

/-- **What "planes" does to the ledger**: a run of lvLen g values under the slots from
g.leaves.first on, then a mark on a debt. -/
theorem planes_fills (seat : Seat S Cl) (lm : ℕ) (readers : Readers S) {i : ℕ} {s s' : S}
    {l : List Cl} {F : Fork} {g : Forest.Heard} (hf : seat.fork s = some F)
    (hg : seat.heard s = some g) (h : planesRun seat lm readers i s = .ok (l, s')) :
    ∃ G, F.hideRun g.leaves.first (Array.replicate (lvLen g) zeroE) (subE zeroE oneE) = some G ∧
      s' = seat.mark s (G.paid g.owedPlanes) := by
  obtain ⟨r, rows, G, u, _, h1, _, rfl⟩ := planesRun_cut seat lm readers hf hg h
  obtain ⟨_, row, p', h2, _⟩ := Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, hG, -, -⟩ := Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  exact ⟨G, hG, rfl⟩

/-! ## Role (A) -/

section
variable (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (a n : ℕ)
include hs

theorem paid_keepsA {s : S} {F : Fork} (i : ℕ) (hI : K3InvA seat.fork seat.heard a n s)
    (hF : seat.fork s = some F) (ho : SlotsOwed F a n) :
    K3InvA seat.fork seat.heard a n (seat.mark s (F.paid i)) ∧
      ∃ F', seat.fork (seat.mark s (F.paid i)) = some F' ∧ Later F F' ∧ SlotsOwed F' a n := by
  obtain ⟨m1, m2, m3⟩ := mark_keeps seat form hs hF (hI.1 F hF) (paid_later F i)
  exact ⟨⟨m3, fun g hg => hI.2 g (m2 ▸ hg)⟩, _, m1, paid_later F i, owed_paid ho i⟩

theorem objects_keepsA :
    StepKeepsUnder (K3InvA seat.fork seat.heard a n) seat.fork a n (runStep (objectsRun seat)) := by
  rintro s s' F hI ⟨i, l, h⟩ hF ho
  obtain ⟨F1, g, e1, -, rfl⟩ := objects_cut seat h
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  exact paid_keepsA seat form hs a n _ hI hF ho

theorem join_keepsA (keys : S → Option (Array Aff)) :
    StepKeepsUnder (K3InvA seat.fork seat.heard a n) seat.fork a n
      (runStep (joinRun seat keys)) := by
  rintro s s' F hI ⟨i, l, h⟩ hF ho
  obtain ⟨F1, g, e1, e2⟩ := join_heard seat keys h
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys hF e2 h
  exact paid_keepsA seat form hs a n _ hI hF ho

/-- **"planes" beside another's stretch.** -/
theorem planes_keepsA (lm : ℕ) (readers : Readers S) :
    StepKeepsUnder (K3InvA seat.fork seat.heard a n) seat.fork a n
      (runStep (planesRun seat lm readers)) := by
  rintro s s' F hI ⟨i, l, h⟩ hF ho
  obtain ⟨F1, g, -, e2⟩ := planes_heard seat lm readers h
  obtain ⟨G, hG, rfl⟩ := planes_fills seat lm readers hF e2 h
  have hS : Sized F := hI.1 F hF
  have hw : WritesWithin F G g.leaves.first (lvLen g) := by
    have := hideRun_writesWithin hS hG
    rwa [Array.size_replicate] at this
  have hL : Later F (G.paid g.owedPlanes) := (hideRun_keeps hG).trans (paid_later G _)
  obtain ⟨m1, m2, m3⟩ := mark_keeps seat form hs hF hS hL
  exact ⟨⟨m3, fun g' hg' => hI.2 g' (m2 ▸ hg')⟩, _, m1, hL,
    owed_paid (owed_of_writesWithin ho hw ((hI.2 g e2).symm)) _⟩

end

/-! ## Role (B) -/

section
variable (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (g : Forest.Heard)
  (a n : ℕ)
include hs

theorem paid_keepsB {s : S} {F : Fork} (i : ℕ) (hI : K3InvB seat.fork seat.heard g s)
    (hF : seat.fork s = some F) (ho : SlotsOwed F a n) :
    K3InvB seat.fork seat.heard g (seat.mark s (F.paid i)) ∧
      ∃ F', seat.fork (seat.mark s (F.paid i)) = some F' ∧ Later F F' ∧ SlotsOwed F' a n := by
  obtain ⟨m1, m2, m3⟩ := mark_keeps seat form hs hF (hI.2 F hF) (paid_later F i)
  exact ⟨⟨m2.trans hI.1, m3⟩, _, m1, paid_later F i, owed_paid ho i⟩

theorem objects_keepsB :
    StepKeepsUnder (K3InvB seat.fork seat.heard g) seat.fork a n (runStep (objectsRun seat)) := by
  rintro s s' F hI ⟨i, l, h⟩ hF ho
  obtain ⟨F1, g1, e1, -, rfl⟩ := objects_cut seat h
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  exact paid_keepsB seat form hs g a n _ hI hF ho

theorem join_keepsB (keys : S → Option (Array Aff)) :
    StepKeepsUnder (K3InvB seat.fork seat.heard g) seat.fork a n
      (runStep (joinRun seat keys)) := by
  rintro s s' F hI ⟨i, l, h⟩ hF ho
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys hF hI.1 h
  exact paid_keepsB seat form hs g a n _ hI hF ho

end

/-- **Under K3InvB the kind's decide refuses**: so its step is empty. -/
theorem decide_keepsB (seat : Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (g : Forest.Heard)
    (a n : ℕ) :
    StepKeepsUnder (K3InvB seat.fork seat.heard g) seat.fork a n
      (decides (Desc.K3.block seat piece laid before p guests)) := by
  rintro s s' F hI ⟨rs, gs, h⟩ - -
  obtain ⟨_, _, _, hn, _, _⟩ := decide_ok seat piece laid before p guests s s' rs gs h
  rw [hI.1] at hn
  cases hn

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_keepsA
#print axioms VerifiableInference.OnPublicFiles.join_keepsA
#print axioms VerifiableInference.OnPublicFiles.planes_keepsA
#print axioms VerifiableInference.OnPublicFiles.objects_keepsB
#print axioms VerifiableInference.OnPublicFiles.join_keepsB
#print axioms VerifiableInference.OnPublicFiles.decide_keepsB
