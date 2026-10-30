-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/GrowsHear.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing on what lies under a slot. That the hearing returns: a
premise everywhere. That the ledger in front has its sizes (Sized) and is free above its next slot:
premises of the tops. WORDS. "The ledger": the verifier's table of hidden scalars
(OnBytes.Model.Fork): ns slots; next: the slot of the next scalar that is sent; a slot is "filled"
once a hidden scalar is put under it.
LETTERS. No "there is".
OBJECT. The hearings of the output head's own rounds (Desc/Kinds/: hide, sendThenBatch, heardBy,
sumcheck, level, Norm.hear, FinalNorm.hear, hear), as functions on the ledger.
USER. The public item "every slot from the ledger's next free number on is free" behind the output
head's block (Law/GrowsAt.lean).
WHAT IT IS. WHEREVER A HEARING OF THE OUTPUT HEAD RETURNS, IT HAS FILLED NO SLOT AT OR ABOVE THE
NEXT SLOT OF THE LEDGER THAT IT RETURNS. The hearings write the ledger by Fork.hideRun alone, three
times: hide (the run ends at the new next slot) · the masked sumcheck's hearing (its end values: the
same) · the laying of the hiding polynomial's coefficients (under the sumcheck's own slots, which
lie below). Grows F G G is later than F (OnBytes/Tie/Pv/Psc/PscLater.lean), and whatever is filled
in G at or above G's next slot was filled in F.
  Grows.refl, Grows.trans, Grows.free   the last: free above is handed on.
  grows_run         one run of Fork.hideRun that ends at or below the new next slot. KeepsG x
                    wherever x returns from a ledger with its sizes, the ledger grows.
  keepsG_…          the hearings, one by one, in the order and by the steps of Law/KeepsHear.lean.
  keepsG_hear       the head's whole hearing.
  hear_free         so: free above in front gives free above behind.
NEAREST RELATIVES: Law/KeepsHear.lean: Keeps, keeps_… (the first half of Grows alone) · Desc/Part/
MaskedSumFree.lean: hear_room, hearRow_room
  (free above across the part's hearing UNDER A PREMISE OF
ROOM, next + n <= ns: the honest prover's side; here nothing is known but that the hearing returned)
· Desc/First/Look/K3KeepsFree.lean, K3CallsKeeps.lean (the like for the lookup's blocks).
A search (statements that name free above, FreeIn, Fresh or a slot's mark at
next, over the table's files, the output head's files, the seats' files and the lookups' and
attention's, in versions other than these: 731 files): none for these hearings.

-/
import Mathlib
import OnBytes.Tie.Pv.Psc.PscRoom
import Johnson.Desc.Part.MaskedSumLedger
import Johnson.Desc.Kinds.Law.KeepsHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Later Sized FreeAbove hideRun_ok hideRun_keeps)

/-- G is later than F, and whatever is filled in G at or above G's next slot was filled in F. -/
def Grows (F G : Fork) : Prop :=
  Later F G ∧ ∀ j, G.next ≤ j → OnBytes.PscRun.Filled G j → OnBytes.PscRun.Filled F j

theorem Grows.refl (F : Fork) : Grows F F := ⟨Later.refl F, fun _ _ h => h⟩

theorem Grows.trans {F G H : Fork} (a : Grows F G) (b : Grows G H) : Grows F H :=
  ⟨a.1.trans b.1, fun j hj h => a.2 j (Nat.le_trans b.1.next hj) (b.2 j hj h)⟩

/-- **Free above is handed on.** -/
theorem Grows.free {F G : Fork} (a : Grows F G) (h : FreeAbove F) : FreeAbove G :=
  fun j hj hG => h j (Nat.le_trans a.1.next hj) (a.2 j hj hG)

/-- One run that ends at or below the new next slot. -/
theorem grows_run {F G : Fork} {n first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (hn : F.next ≤ n) (hle : first + v.size ≤ n)
    (h : ({ F with next := n } : Fork).hideRun first v factor = some G) :
    Grows F G ∧ G.next = n := by
  obtain ⟨a1, _, _, a4⟩ := hideRun_ok _ G first v factor (show Sized { F with next := n } from hF) h
  have hnx : G.next = n := congrArg Fork.next a1
  refine ⟨⟨(later_next F n hn).trans (hideRun_keeps h), fun j hj hG => ?_⟩, hnx⟩
  rw [hnx] at hj
  exact (a4 j (Or.inr (Nat.le_trans hle hj))).2.2.1 hG

/-- Wherever the hearing returns from a ledger with its sizes, the ledger grows. -/
def KeepsG {α : Type} (x : Hear α) : Prop :=
  ∀ F rs a G left, Sized F → x F rs = some (a, G, left) → Grows F G

theorem keepsG_bind {α β : Type} {x : Hear α} {f : α → Hear β} (hx : KeepsG x)
    (hf : ∀ a, KeepsG (f a)) : KeepsG (x >>= f) := by
  intro F rs b G left hF h
  obtain ⟨a, G1, l1, h1, h2⟩ := bind_some h
  have g1 := hx _ _ _ _ _ hF h1
  exact g1.trans (hf a _ _ _ _ _ (g1.1.sized hF) h2)

theorem keepsG_pure {α : Type} (a : α) : KeepsG (pure a : Hear α) := by
  intro F rs b G left _ h
  obtain ⟨_, rfl, _⟩ := pure_some h
  exact Grows.refl _

theorem keepsG_need {α : Type} (x : Option α) : KeepsG (Hear.need x) := by
  intro F rs b G left _ h
  obtain ⟨_, rfl, _⟩ := need_some h
  exact Grows.refl _

theorem keepsG_round (n k : Nat) : KeepsG (Hear.round n k) := by
  intro F rs b G left _ h
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some v =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.1]; exact Grows.refl _

theorem keepsG_hide (v : List E) : KeepsG (hide v) := by
  intro F rs b G left hF h
  unfold hide at h
  cases hr : ({ F with next := F.next + v.length } : Fork).hideRun F.next v.toArray
      OnBytes.oneE with
  | none => rw [hr] at h; cases h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2.1]
    exact (grows_run hF (Nat.le_add_right _ _) (by simp) hr).1

theorem keepsG_drawPoint (n : Nat) : KeepsG (drawPoint n) :=
  keepsG_bind (keepsG_round 0 n) fun _ => keepsG_pure _

theorem keepsG_sendThenBatch (n rows : Nat) : KeepsG (sendThenBatch n rows) := by
  unfold sendThenBatch
  refine keepsG_bind (keepsG_round n 1) fun x => ?_
  obtain ⟨v, g⟩ := x
  exact keepsG_bind (keepsG_hide v) fun _ => keepsG_bind (keepsG_need _) fun _ => keepsG_pure _

/-- The part's hearing of a sumcheck. -/
theorem keepsG_heardBy (lead : Nat) (C : Array Hid → Form) (z : Point) (ends : Nat) :
    KeepsG (heardBy lead C z ends) := by
  intro F0 t b F1 left hF h
  unfold heardBy at h
  obtain ⟨rs, Fx, l0, h1, k1⟩ := bind_some h
  have hFx : F0 = Fx := by
    unfold Hear.stretch at h1
    split at h1
    · cases h1
    · simp only [Option.some.injEq, Prod.mk.injEq] at h1
      exact h1.2.1
  subst hFx
  obtain ⟨ld, Fy, l1, h2, k2⟩ := bind_some k1
  obtain ⟨_, rfl, rfl⟩ := need_some h2
  obtain ⟨c', Fa, l2, h3, k3⟩ := bind_some k2
  have L1 : Grows F0 Fa := keepsG_hide ld _ _ _ _ _ hF h3
  have hFa : Sized Fa := L1.1.sized hF
  obtain ⟨Fl, Fz, l3, h4, k4⟩ := bind_some k3
  obtain ⟨rfl, rfl, rfl⟩ := ledger_some h4
  obtain ⟨hG, Fw, l4, h5, k5⟩ := bind_some k4
  obtain ⟨e5, rfl, rfl⟩ := need_some h5
  obtain ⟨hd, G⟩ := hG
  dsimp only at k5
  obtain ⟨_, Tt, R, _, _, _, hrun2⟩ := Part.MaskedSum.hear_spec e5
  obtain ⟨L2, hnG⟩ := grows_run hFa (by omega) (by simp) hrun2
  obtain ⟨q1, _, q3⟩ := Part.MaskedSum.heard_lenK e5
  obtain ⟨Fr, Fv, l5, h6, k6⟩ := bind_some k5
  obtain ⟨e6, rfl, rfl⟩ := need_some h6
  have L3 : Grows G Fr :=
    (grows_run (n := G.next) (L2.1.sized hFa) (Nat.le_refl _)
      (by rw [Array.size_replicate, q1, q3, hnG]; omega) e6).1
  obtain ⟨u, Fu, l6, h7, k7⟩ := bind_some k6
  obtain ⟨rfl, rfl⟩ := lay_some h7
  obtain ⟨es, Ft, l7, h8, k8⟩ := bind_some k7
  obtain ⟨rfl, rfl, _⟩ := hiddenFrom_some h8
  obtain ⟨_, rfl, _⟩ := pure_some k8
  exact (L1.trans L2).trans L3

theorem keepsG_sumcheck (z : Point) (ends : Nat) : KeepsG (sumcheck z ends) := by
  unfold sumcheck
  refine keepsG_bind (keepsG_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  exact keepsG_pure _

theorem keepsG_level (z : Point) (start : Form) : KeepsG (level z start) := by
  unfold level
  refine keepsG_bind (keepsG_heardBy _ _ _ _) fun x => ?_
  obtain ⟨c, s⟩ := x
  refine keepsG_bind (keepsG_round 0 1) fun y => ?_
  obtain ⟨a, g⟩ := y
  exact keepsG_bind (keepsG_need _) fun _ => keepsG_pure _

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

theorem keepsG_normRest (pV : Point) : KeepsG (Norm.hearRest pV) := by
  unfold Norm.hearRest
  refine keepsG_bind (keepsG_sendThenBatch _ _) fun x => ?_
  obtain ⟨W, gam⟩ := x
  refine keepsG_bind ?_ fun rhoI => ?_
  · exact keepsG_pure _
  refine keepsG_bind (keepsG_level _ _) fun sq => ?_
  refine keepsG_bind (keepsG_sendThenBatch _ _) fun y => ?_
  obtain ⟨P, om⟩ := y
  exact keepsG_bind (keepsG_sumcheck _ _) fun _ => keepsG_pure _

theorem keepsG_norm : KeepsG Norm.hear :=
  keepsG_bind (keepsG_drawPoint _) fun pV => keepsG_normRest pV

theorem keepsG_final : KeepsG FinalNorm.hear :=
  keepsG_bind (keepsG_sumcheck _ _) fun _ => keepsG_pure _

/-- **The head's whole hearing.** -/
theorem keepsG_hear : KeepsG hear :=
  keepsG_bind keepsG_norm fun _ => keepsG_bind keepsG_final fun _ =>
    keepsG_bind (keepsG_sumcheck _ _) fun _ => keepsG_pure _

/-- **FREE ABOVE IN FRONT GIVES FREE ABOVE BEHIND**; the number of slots and the sizes stay. -/
theorem hear_free {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hF : Sized F)
    (hf : FreeAbove F) (h : hear F rs = some (H, G, left)) :
    FreeAbove G ∧ G.ns = F.ns ∧ Sized G :=
  have g := keepsG_hear _ _ _ _ _ hF h
  ⟨g.free hf, g.1.ns, g.1.sized hF⟩

end Classes

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.keepsG_hear
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hear_free
