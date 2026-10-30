-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/LateLow.lean: The kind "lookup" (K3): THE LATE SLOTS OF ITS THREE RUNS, AS A
LINK's READER ANSWERS THEM: "objects" and "join": none; "planes": the window of the sumcheck over
the leaves: so that each lies below whatever the window ends below: the premise hlow of
k3_formsIn_fwd (Johnson/Top/H/Keep/FormsPassK3.lean) at these three. And: NO KEPT ROW NAMES THE
SLOT OF THE MERGE's END VALUE where that slot is free: the premise hmerge of objects_formsIn and
objects_formsInT (Johnson/Top/H/Keep/FormsInObjects.lean, FormsInTObjects.lean). Statements and
proofs.

OBJECT: K9.readersOfLink H l at a run that the link states as the lookup's own run; K9.lateOf;
  K9.mergeOf.
Used by Johnson/P5J/K03OwnItLayAt.lean, Johnson/Top/H/Keep/FormsPassOurs.lean,
  Johnson/Top/H/Keep/FormsPassRun.lean and 2 more.
LETTERS: H, l, b, seat, keys | lm, readers, s, R, n free.
Compiled with the whole library.

Main names:
  link_reader: where the name is not "K8.equations" and the link's second hole is silent, a link's
    reader's answer is the run's own reader's.
  objects_low, join_low: R.late = []. planes_low: every late slot lies below n, where the window
    ends at or below n.
  merge_of_free: the kept rows against the merge's slot.

Limits. hfind: THE RUN THAT THE LINK STATES UNDER THE NAME IS THE LOOKUP's RUN ITSELF (an equation
of functions): other files have it at the description's own links. hs (the second hole is silent),
hA (the seat's ledger is the state's, its mark is putFork), Sized at "planes": premises. hfree (the
merge's slot is free in the ledger): NOT K3's FILES' TO SHOW: the merging kind's.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassK3
import Johnson.Top.H.Keep.FormsInObjects
import Johnson.Top.H.Keep.K3Late
import Johnson.Top.H.Keep.K3Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat planesRun joinRun)
open VerifiableInference.Desc.K9 (Read readerOf readersOfLink statesOfLink LinkHoles lateOf mergeOf)
open _root_.Fo.Tp (NamedAll)

/-- A link's reader's answer is the run's own reader's. -/
theorem link_reader {H : LinkHoles} {l : Link S Claim} {b : ℕ} {name : String} {s : S} {R : Read}
    (hn : (name == "K8.equations") = false) (hs : H.silent b name s = none)
    (h : (readersOfLink H l).forms b name s = some R) :
    readerOf (statesOfLink l) b name s = some R := by
  have h' : (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := h
  rw [hn] at h'
  cases hr : readerOf (statesOfLink l) b name s with
  | none =>
    simp only [hr] at h'
    have h2 : H.silent b name s = some R := h'
    rw [hs] at h2
    exact nomatch h2
  | some R0 =>
    simp only [hr] at h'
    exact h'

section
variable (H : LinkHoles) (l : Link S Claim) (b : ℕ) (seat : Seat S Claim) (hA : AtS2 seat)
include hA

/-- **"objects" fills nothing late.** -/
theorem objects_low {s : S} {R : Read} (hs : H.silent b "objects" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "objects") = some (nm, r) →
      r = objectsRun seat)
    (h : (readersOfLink H l).forms b "objects" s = some R) : R.late = [] := by
  obtain ⟨nm, run, cl, t, F, G, hf, hr, hF, hG, _, rfl⟩ :=
    reader_test (link_reader (by decide) hs h)
  rw [hfind nm run hf] at hr
  obtain ⟨F2, g, e1, _, rfl⟩ := objects_cut seat hr
  obtain rfl : F = F2 := Option.some.inj (hF.symm.trans ((hA.fork s).symm.trans e1))
  rw [hA.mark, fork_putFork s F _ hF] at hG
  obtain rfl := Option.some.inj hG
  exact lateOf_same F (F.paid g.owedObjects) rfl

/-- **"join" fills nothing late.** -/
theorem join_low (keys : S → Option (Array Aff)) {s : S} {R : Read}
    (hs : H.silent b "join" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun seat keys)
    (h : (readersOfLink H l).forms b "join" s = some R) : R.late = [] := by
  obtain ⟨nm, run, cl, t, F, G, hf, hr, hF, hG, _, rfl⟩ :=
    reader_test (link_reader (by decide) hs h)
  rw [hfind nm run hf] at hr
  obtain ⟨F2, g, e1, e2⟩ := join_heard seat keys hr
  obtain rfl : F = F2 := Option.some.inj (hF.symm.trans ((hA.fork s).symm.trans e1))
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys e1 e2 hr
  rw [hA.mark, fork_putFork s F _ hF] at hG
  obtain rfl := Option.some.inj hG
  exact lateOf_same F (F.paid g.owedJoin) rfl

/-- **The late slots of "planes" lie in the window.** -/
theorem planes_low (lm : ℕ) (readers : Desc.K3.Readers S) {s : S} {R : Read} {n : ℕ}
    (hs : H.silent b "planes" s = none)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun seat lm readers)
    (hS : ∀ F, s.fork? = some F → Sized F)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ n)
    (h : (readersOfLink H l).forms b "planes" s = some R) : ∀ x ∈ R.late, x.1 < n := by
  obtain ⟨nm, run, cl, t, F, G, hf, hr, hF, hG, _, rfl⟩ :=
    reader_test (link_reader (by decide) hs h)
  rw [hfind nm run hf] at hr
  obtain ⟨F2, g, e1, e2⟩ := planes_heard seat lm readers hr
  obtain rfl : F = F2 := Option.some.inj (hF.symm.trans ((hA.fork s).symm.trans e1))
  obtain ⟨Gp, ep, lp⟩ := planes_late seat lm readers e1 (hS F hF) e2 hr
  rw [ep, hA.mark, fork_putFork s F _ hF] at hG
  obtain rfl := Option.some.inj hG
  intro x hx
  have hx' : x ∈ lateG F Gp := hx
  rw [lp] at hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx'
  exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (List.mem_range.1 hi) _) (hwin g e2)

end

/-- **No kept row names the slot of the merge's end value, where that slot is free.** -/
theorem merge_of_free {s : S} {F : Fork} {rows : Array Aff} (hN : NamedAll F rows)
    (hfree : ∀ j, mergeOf s = some j → ¬ Filled F j) :
    ∀ f ∈ rows.toList, ∀ x ∈ f.slots.toList, mergeOf s ≠ some x.1 :=
  fun f hf x hx e => hfree x.1 e ((hN f hf).2 x hx).2

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objects_low
#print axioms VerifiableInference.OnPublicFiles.join_low
#print axioms VerifiableInference.OnPublicFiles.planes_low
#print axioms VerifiableInference.OnPublicFiles.merge_of_free
