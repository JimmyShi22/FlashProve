-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LeavesFree.lean: behind the lookup's hearing the slots of the
leaves' sumcheck are still free, and so the three claims on the planes are made at the hearing's own
ledger, and at every later one that has not filled these slots. Theorems; for every face.

Terms. Honest/K3/GLOSSARY.md ("claim", "hearing", "hidden value", "leaves", "ledger", "slot").

What is shown.
  `leaves_walk`: where `messagesV` returns from a ledger whose arrays have their size: a slot of the
    leaves' own is filled behind the hearing just if it was filled in front of it.
  `leaves_free`: so, where the ledger in front was free from its count of slots on, as far as the
    lookup's hidden values reach, the leaves' own slots are free behind the hearing.
  `hearV_next`: behind the hearing the count of slots stands behind all of the lookup's hidden
    values.
  `leaves_owed`, `planesV_of_owed`: the same in the library's own word `SlotsOwed`
    (OnBytes/Tie/Pv/Psc/PscRoom.lean), which its theorems carry over later steps.
  `planesV_behind`: `planesV` returns at the hearing's own ledger, with three claims.
  `leavesFreeOf`: the last clause of the statement `LookHeard` (Honest/K3/Law/Statements.lean), from
    its invariant in front of the first stage and the hearing's return.
  `planesBehind`: under the same hypotheses `planesV` returns at the hearing's own ledger.

Hypotheses that remain. The hearing has returned (`hh`; in `leaves_walk` `h`: `messagesV`); the
first ledger's arrays have their size (`hS`); the first ledger is free from its count of slots on,
as far as the lookup reaches (`hfree`: in `leaves_free`, `leaves_owed`, `planesV_behind`).
  `hroom`: (in `planesV_of_owed`, `planesV_behind`) the first ledger has room for the lookup's
    slots.
  `hS'`, `hL`, `ho`: (in `planesV_of_owed`) the later ledger's arrays have their size; it is `Later`
    than the hearing's; the leaves' own slots are owed at it.
  `hinv`: (in `leavesFreeOf`, `planesBehind`) the invariant in front of the first stage.

How the proof goes. In front of the leaves' sumcheck no text changes a mark at or above the count of
slots that it leaves (Honest/K3/Law/Tidy.lean). The leaves' own hearing, which has no end value,
changes no mark below the slots of end values (the part's `hear_fills`). The round of samples leaves
the ledger as it is. The bits' sumcheck changes no mark below the count in front of it (the part's
`whole_writesAbove`).

Users. This file is imported by Honest/K3/Law/Seated.lean, Honest/K3/Law/Thread/Group11.lean
[not in this library], Honest/K3/Law/Thread/LeavesOpen.lean [not in this library],
Honest/K3/Law/Thread/LookAsksOf.lean [not in this library] and Honest/K3/Parts/Packs.lean.

Limits. "If the hearing returned". Between the hearing and the run of claims that makes the three
claims other sub-protocols write into the same ledger: that they spare the leaves' own slots is not
shown here: Honest/K3/Law/PlanesReturn.lean assumes it at the later ledger. Nothing is said on what
the claims are worth.
Instances: Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.PlanesReturn
import Johnson.Desc.ProofFile.Honest.K3.Law.Tidy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV messagesV planesV leafVars bitsCall)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)

/-- **A slot of the leaves' own is filled behind the hearing just if it was filled in front of it.**
n₀: the count of slots in front of the leaves' sumcheck.
Conditional on the return of `messagesV` and on the first ledger's arrays having their size. -/
theorem leaves_walk (f : LFace) {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (h : messagesV f F rs = some (g, G, rest)) :
    ∃ n₀, n₀ + (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1) = F.next + f.slots ∧
      G.next = F.next + f.slots ∧
      ∀ j, n₀ ≤ j → j < n₀ + (1 + f.mu + 2 * f.d) → (Filled G j ↔ Filled F j) := by
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨_, qG, _⟩ := pure_spec h
  have P13 : Reach F F13 :=
    Tidy.step e13 hS <| Tidy.step e12 hS <| Tidy.step e11 hS <| Tidy.step e10 hS <|
    Tidy.step e9 hS <| Tidy.step e8 hS <| Tidy.step e7 hS <| Tidy.step e6 hS <|
    Tidy.step e5 hS <| Tidy.step e4 hS <| Tidy.step e3 hS <| Tidy.step e2 hS <|
    Tidy.step e1 hS (Reach.refl F)
  have S13 := P13.later.sized hS
  have hh := openV_hear e14
  have n14 := MaskedSum.hear_next S13 hh
  have S14 := (MaskedSum.hear_keeps hh).sized S13
  have q15 := drawsV_same e15
  obtain ⟨_, _, _, s15⟩ := drawsV_spec e15
  have hw := sumV_whole e16
  obtain ⟨e, Gm, sh, he, hb, _, hr⟩ := MaskedSum.whole_parts hw
  have S15 : Sized F15 := q15 ▸ S14
  have nm := MaskedSum.hear_next S15 hb
  have n16 := MaskedSum.row_next ((MaskedSum.hear_keeps hb).sized S15) hr
  have wa := MaskedSum.whole_writesAbove S15 hw
  obtain ⟨a17, q17⟩ := slot_spec e17
  obtain ⟨b18, q18⟩ := must_spec e18
  obtain ⟨a1, _⟩ := slot_spec e1
  simp only [Bool.and_eq_true, beq_iff_eq] at b18
  have o14 : ownSlots ({ lead := 0, vs := leafVars f table.point, ends := none } : Call).all =
      1 + f.mu + 2 * f.d := own_leafVars f _
  have n14' : F14.next = F13.next + (1 + f.mu + 2 * f.d) := by
    rw [n14, o14]
    rfl
  have nm' : Gm.next = F15.next + (1 + 2 * (f.mu + f.d) + 2) + 1 := by
    rw [nm, own_bits]
    have : ze.reverse.toList.length = f.mu + f.d := by simp [s15]
    rw [this]
    rfl
  refine ⟨F13.next, ?_, ?_, fun j a b => ?_⟩
  · rw [q15] at nm'
    have b := b18.1
    omega
  · rw [qG, q18, q17, ← a17, b18.1, a1]
  · rw [qG, q18, q17]
    have s1 : Filled F16 j ↔ Filled F15 j := wa.2 j (by rw [q15, n14']; exact b)
    have s2 : Filled F14 j ↔ Filled F13 j :=
      MaskedSum.hear_fills S13 hh j (Or.inl (by rw [o14]; exact b))
    rw [q15] at s1
    exact s1.trans (s2.trans (P13.low j a))

/-- **Behind the hearing the leaves' own slots are free**, where the ledger in front was free from
its count of slots on as far as the lookup's hidden values reach. Conditional on the return of
`hearV` and on `Sized` in front. Instances, and an alteration that shows the hypothesis on free
slots at work: Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by evaluation). -/
theorem leaves_free (f : LFace) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hfree : ∀ j, F.next ≤ j → j < F.next + f.slots → ¬ Filled F j)
    (hh : hearV f F x = some (g, G)) :
    ∀ j, F.next + firstSlot f .leaves ≤ j →
      j < F.next + firstSlot f .leaves + Stage.own f .leaves → ¬ Filled G j := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have hp := two_le_planes_of_ok f hok
  obtain ⟨n₀, hn, _, hw⟩ := leaves_walk f hS hm
  have h0 : n₀ = F.next + firstSlot f .leaves := by
    have h := firstSlot_leaves f hp
    rw [slots_leaves, slots_bits] at h
    omega
  have hown : Stage.own f .leaves = 1 + f.mu + 2 * f.d := slots_leaves f
  intro j a b hf
  rw [hown] at b
  exact hfree j (by omega) (by omega) ((hw j (by omega) (by omega)).1 hf)

/-- Behind the hearing the count of slots stands behind all of the lookup's hidden values.
Conditional on the return of `hearV` and on `Sized` in front. -/
theorem hearV_next (f : LFace) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hh : hearV f F x = some (g, G)) : G.next = F.next + f.slots := by
  obtain ⟨_, _, h, _⟩ := leaves_walk f hS (hearV_messages hh).2
  exact h

/-- **The same in the library's own word for a stretch of slots that a later row will fill**
(`SlotsOwed`, OnBytes/Tie/Pv/Psc/PscRoom.lean): the leaves' own slots lie below the count of slots
and are free. The library's theorems carry that word over every step that writes above the count or
within a stretch apart (`owed_of_spares`, `owed_along`, same file; for the masked sumcheck's texts
`whole_spares`, `hear_spares`, `row_spares`, Johnson/Desc/Part/MaskedSumFree.lean). Conditional on
the return of `hearV`, on `Sized` in front and on the first ledger being free as far as the lookup
reaches. Instances: Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by evaluation). -/
theorem leaves_owed (f : LFace) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hfree : ∀ j, F.next ≤ j → j < F.next + f.slots → ¬ Filled F j)
    (hh : hearV f F x = some (g, G)) :
    OnBytes.PscRun.SlotsOwed G (F.next + firstSlot f .leaves) (Stage.own f .leaves) := by
  refine ⟨?_, leaves_free f hS hfree hh⟩
  have h := firstSlot_leaves f (two_le_planes_of_ok f (hearV_messages hh).1)
  have hown : Stage.own f .leaves = Stage.slots f .leaves := rfl
  rw [hearV_next f hS hh, hown]
  omega

/-- `planesV` returns at every ledger with arrays of the right size and the first ledger's room at
which the leaves' own slots are owed in that sense. Conditional on the return of `hearV`, on `Sized`
in front, on F' being `Later` than the hearing's own ledger, and on these slots being owed at F'. -/
theorem planesV_of_owed (f : LFace) {F G F' : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hroom : F.next + f.slots ≤ F.ns) (hh : hearV f F x = some (g, G)) (hS' : Sized F')
    (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot f .leaves) (Stage.own f .leaves)) :
    ∃ cl G', planesV f g F' = some (cl, G') ∧ cl.length = 3 :=
  planesV_returns f hS hroom hh hS' hL ho.2

/-- **The three claims on the planes are made at the hearing's own ledger.** Conditional on the
return of `hearV`, on `Sized` and room in front, and on the first ledger being free as far as the
lookup reaches. `planesV` is seated at no place of a proof file (Honest/K3/Law/SeatedAll.lean has
the seated run). Instances: Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by
evaluation). -/
theorem planesV_behind (f : LFace) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hroom : F.next + f.slots ≤ F.ns)
    (hfree : ∀ j, F.next ≤ j → j < F.next + f.slots → ¬ Filled F j)
    (hh : hearV f F x = some (g, G)) : ∃ cl G', planesV f g G = some (cl, G') ∧ cl.length = 3 :=
  planesV_returns f hS hroom hh ((hearV_later hh).sized hS) (Later.refl G)
    (leaves_free f hS hfree hh)

/-- The last clause of the statement `LookHeard`, from its invariant in front of the first stage.
Conditional on the return of `hearV`. -/
theorem leavesFreeOf {W : Type} (R : Course W) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV}
    (hinv : Inv R 0 F) (hh : hearV R.f F x = some (g, G)) :
    ∀ j, R.first + firstSlot R.f .leaves ≤ j →
      j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j := by
  have hnext : F.next = R.first := by
    have := hinv.next
    simpa [slotsIn] using this
  have h := leaves_free R.f hinv.sized (by rw [hnext]; exact fun j a b => hinv.free j (hnext ▸ a) b)
    hh
  rw [hnext] at h
  exact h

/-- Under the same hypotheses the three claims are made at the hearing's own ledger.
Conditional on the return of `hearV`. -/
theorem planesBehind {W : Type} (R : Course W) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV}
    (hinv : Inv R 0 F) (hh : hearV R.f F x = some (g, G)) :
    ∃ cl G', planesV R.f g G = some (cl, G') ∧ cl.length = 3 := by
  have hnext : F.next = R.first := by
    have := hinv.next
    simpa [slotsIn] using this
  exact planesV_behind R.f hinv.sized (by rw [hnext]; exact hinv.room)
    (by rw [hnext]; exact fun j a b => hinv.free j (hnext ▸ a) b) hh

#print axioms ProofFile.Honest.K3.Law.leaves_walk
#print axioms ProofFile.Honest.K3.Law.leaves_free
#print axioms ProofFile.Honest.K3.Law.hearV_next
#print axioms ProofFile.Honest.K3.Law.leaves_owed
#print axioms ProofFile.Honest.K3.Law.planesV_of_owed
#print axioms ProofFile.Honest.K3.Law.planesV_behind
#print axioms ProofFile.Honest.K3.Law.leavesFreeOf
#print axioms ProofFile.Honest.K3.Law.planesBehind

end ProofFile.Honest.K3.Law
