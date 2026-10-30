-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/PlanesReturn.lean: the three claims on the planes are made, at
every later ledger at which the slots of the leaves' sumcheck are still free: the statement
`PlanesReturn` of Honest/K3/Law/Statements.lean, proved. Theorems.

Terms. Honest/K3/GLOSSARY.md ("claim", "count, bits, planes", "hidden value", "leaves", "ledger",
"slot").

What is shown.
  `own_leafVars`, `own_bits`: how many slots of its own a leaves' and a bits' sumcheck takes, at any
    points.
  `firstSlot_leaves`: the hidden values in front of the leaves' sumcheck, its own and the bits' are
    all of the lookup's.
  `leaves_heard`: where `messagesV` returns: the structure of the leaves' sumcheck that it returns
    was made by the part's own `hear`, at a ledger that is later than the first one and whose count
    of slots is given.
  `leaves_first`: that count is the first ledger's plus `firstSlot f .leaves`.
  `planesV_returns`: so `planesV` returns, with three claims; for every face; no course is named.
  `planesReturn`: the statement as it is written in Statements.lean.

Hypotheses that remain, in `planesV_returns`.
  `hh`: the hearing has returned: that it returns is another statement's.
  `hfree`: the leaves' own slots are still free at the later ledger.
  `hS`, `hroom`, `hS'`, `hL`: both ledgers' arrays have their size; the first has room for the
    lookup's slots; the second is `Later` than the hearing's.
  The statement `PlanesReturn` has, in the place of `hS` and `hroom`, `Inv R 0 F`; its `Fit R` and
    `R.rounds = some x` are not used by the proof of `planesReturn`.
  In the steps: `h`, `hp`: two planes at least; `h`: (in `leaves_heard`) `messagesV` returns; `hn`:
    (in `leaves_first`) the count behind; `h`, `hs`: (in two helpers on lists) s is no member of the
    front.

How the proof goes. The count is not found by counting through the tie, the parts' step and the
trees. `messagesV` itself tests at its end that the count of slots stands at the first count plus
`Face.slots`; behind the leaves' sumcheck stand a round of samples, which leaves the ledger as it
is, and the bits' sumcheck, whose slots are counted by the part's own theorems
(Johnson/Desc/Part/MaskedSumFree.lean). So the count in front of the leaves' sumcheck is computed
backward, and `slots_stages` (Honest/K3/RowLaw.lean) says what is left.

Users. This file is imported by Honest/K3/Law/LeavesFree.lean and Honest/K3/Shape/Closed.lean.

Limits. Nothing is said on what the claims are worth. `planesV` is the text of the sub-protocol of
Johnson/Desc/First/Look/Via/Rounds.lean itself, which is seated at no place of a proof file: for the
seated run see Honest/K3/Law/SeatedAll.lean.
Instances: Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.Law.GoesOn
import Johnson.Desc.ProofFile.Honest.K3.RowCut
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw
import Johnson.Desc.Part.MaskedSumFree
import Johnson.Desc.Part.MaskedSumReady

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

/-! ## Counts -/

theorem sum_map_const {α : Type} (l : List α) (c : Nat) : (l.map fun _ => c).sum = l.length * c :=
    by
  rw [map_const_replicate, sum_replicate_const]

/-- The leaves' sumcheck takes 1 + mu + 2 d slots of its own, at any point. -/
theorem own_leafVars (f : LFace) (z : Array E) : ownSlots (leafVars f z) = 1 + f.mu + 2 * f.d := by
  simp only [ownSlots_eq, leafVars, List.map_map, Function.comp_def, Var.d, sum_leaf]
  omega

/-- The bits' sumcheck takes 1 + 2 n + 2 slots of its own, at any point of n coordinates. -/
theorem own_bits (zs : List E) : ownSlots (bitsCall zs).all = 1 + 2 * zs.length + 2 := by
  simp only [bitsCall, Call.all, ownSlots_eq, List.map_append, List.map_map, Function.comp_def,
    Var.d, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, sum_map_const]
  omega

theorem idxOf_split {α : Type} [DecidableEq α] (pre post : List α) (s : α) (h : s ∉ pre) :
    (pre ++ s :: post).idxOf s = pre.length := by
  induction pre with
  | nil => simp
  | cons a l ih =>
    have hne : a ≠ s := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, List.idxOf_cons_ne _ hne,
      ih (fun hm => h (List.mem_cons_of_mem _ hm)), List.length_cons]

theorem sum_take_idxOf (g : Stage → Nat) (pre post : List Stage) (s : Stage) (hs : s ∉ pre) :
    (((pre ++ s :: post).take ((pre ++ s :: post).idxOf s)).map g).sum + g s + (post.map g).sum =
      ((pre ++ s :: post).map g).sum := by
  rw [idxOf_split pre post s hs, List.take_left', List.map_append, List.sum_append, List.map_cons,
    List.sum_cons]
  · omega
  · rfl

/-- The hidden values in front of the leaves' sumcheck, its own and the bits' are all
of the lookup's. -/
theorem firstSlot_leaves (f : LFace) (h : 2 ≤ f.planes) :
    firstSlot f .leaves + Stage.slots f .leaves + Stage.slots f .bits = f.slots := by
  have h1 := sum_take_idxOf (Stage.slots f) _ [Stage.zero, Stage.bits] Stage.leaves
    (fun hm => front_closed f _ hm rfl)
  have hz : (([Stage.zero, Stage.bits] : List Stage).map (Stage.slots f)).sum =
      Stage.slots f .bits := by
    show 0 + (Stage.slots f .bits + 0) = _
    omega
  rw [hz] at h1
  rw [← slots_stages f h]
  exact h1

/-! ## The structure of the leaves' sumcheck -/

/-- **Where the lookup's rounds were heard, the leaves' structure was made by the part's own
hearing**, at a ledger F₀ that is later than the first one; and F₀'s count of slots, the leaves' own
slots and the bits' slots make up the first count and the verifier's count of the lookup's hidden
values. Conditional on the return of `messagesV` and on the first ledger's arrays
having their size. C, z, F₀ and rs₀ are bound by "∃" and held by what functions return at them
alone: some values: not said to be the step's own. -/
theorem leaves_heard (f : LFace) {F G : Fork} {rs rest : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (h : messagesV f F rs = some (g, G, rest)) :
    ∃ (C : Aff) (z : Array E) (F₀ G₀ : Fork) (rs₀ : List Fmt.RoundView),
      MaskedSum.hear C { lead := 0, vs := leafVars f z, ends := none } F₀ rs₀ =
        some (g.leaves, G₀) ∧
      Later F F₀ ∧
      F₀.next + (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1) = F.next + f.slots := by
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
  obtain ⟨hg, _, _⟩ := pure_spec h
  have L13 : Later F F13 :=
    (GoesOn.later e1).trans <| (GoesOn.later e2).trans <| (GoesOn.later e3).trans <|
    (GoesOn.later e4).trans <| (GoesOn.later e5).trans <| (GoesOn.later e6).trans <|
    (GoesOn.later e7).trans <| (GoesOn.later e8).trans <| (GoesOn.later e9).trans <|
    (GoesOn.later e10).trans <| (GoesOn.later e11).trans <| (GoesOn.later e12).trans
      (GoesOn.later e13)
  have S13 := L13.sized hS
  have hh := openV_hear e14
  have n14 := MaskedSum.hear_next S13 hh
  have S14 := (MaskedSum.hear_keeps hh).sized S13
  have q15 := drawsV_same e15
  obtain ⟨_, _, _, s15⟩ := drawsV_spec e15
  obtain ⟨e, Gm, sh, he, hb, _, hr⟩ := MaskedSum.whole_parts (sumV_whole e16)
  have S15 : Sized F15 := q15 ▸ S14
  have nm := MaskedSum.hear_next S15 hb
  have n16 := MaskedSum.row_next ((MaskedSum.hear_keeps hb).sized S15) hr
  obtain ⟨a17, _⟩ := slot_spec e17
  obtain ⟨b18, _⟩ := must_spec e18
  obtain ⟨a1, _⟩ := slot_spec e1
  simp only [Bool.and_eq_true, beq_iff_eq] at b18
  have n14' : F14.next = F13.next + (1 + f.mu + 2 * f.d) := by
    rw [n14]
    show F13.next + ownSlots (leafVars f table.point) + 0 = _
    rw [own_leafVars]
    rfl
  have nm' : Gm.next = F15.next + (1 + 2 * (f.mu + f.d) + 2) + 1 := by
    rw [nm, own_bits]
    have : ze.reverse.toList.length = f.mu + f.d := by simp [s15]
    rw [this]
    rfl
  rw [q15] at nm'
  subst hg
  refine ⟨_, _, F13, F14, _, hh, L13, ?_⟩
  have b := b18.1
  omega

/-- That ledger's count of slots is the first one's plus the hidden values in front
of the leaves'. -/
theorem leaves_first (f : LFace) (hp : 2 ≤ f.planes) {F F₀ : Fork}
    (hn : F₀.next + (1 + f.mu + 2 * f.d) + (1 + 2 * (f.mu + f.d) + 2 + 1) = F.next + f.slots) :
    F₀.next = F.next + firstSlot f .leaves := by
  have h := firstSlot_leaves f hp
  rw [slots_leaves, slots_bits] at h
  omega

/-- **The three claims on the planes are made**: where the hearing returned from a ledger F with
arrays of the right size and room for the lookup, at every later ledger F' with such arrays at which
the leaves' own slots are free.
Conditional on the return of `hearV` and on the leaves' own slots being free at F'. `planesV` is the
text of the sub-protocol of Johnson/Desc/First/Look/Via/Rounds.lean itself, which is seated at no
place of a proof file: for the seated run see Honest/K3/Law/SeatedAll.lean.
Instances: Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by evaluation). -/
theorem planesV_returns (f : LFace) {F G F' : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hroom : F.next + f.slots ≤ F.ns) (hh : hearV f F x = some (g, G)) (hS' : Sized F')
    (hL : Later G F')
    (hfree : ∀ j, F.next + firstSlot f .leaves ≤ j →
      j < F.next + firstSlot f .leaves + Stage.own f .leaves → ¬ Filled F' j) :
    ∃ cl G', planesV f g F' = some (cl, G') ∧ cl.length = 3 := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have hp := two_le_planes_of_ok f hok
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, hn⟩ := leaves_heard f hS hm
  have hF0 := leaves_first f hp hn
  have hown : Stage.own f .leaves = 1 + f.mu + 2 * f.d := slots_leaves f
  have hall : ownSlots ({ lead := 0, vs := leafVars f z, ends := none } : Call).all =
      1 + f.mu + 2 * f.d := own_leafVars f z
  have hns : F'.ns = F.ns := hL.ns.trans (hearV_later hh).ns
  have hr := MaskedSum.row_returns_later h0 hS' (by rw [hall, hns]; omega)
    (fun j a b => hfree j (by omega) (by rw [hall] at b; omega)) oneE {}
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hr
  exact ⟨_, _, by unfold planesV; rw [hy]; rfl, rfl⟩

/-- The statement as Honest/K3/Law/Statements.lean writes it. Conditional on what the statement
itself assumes: the return of `hearV` and the leaves' own slots free at the later ledger. Instances:
Honest/K3/Law/LeavesFreeGuards.lean [not in this library] (by evaluation). -/
theorem planesReturn : PlanesReturn := by
  intro W R F G F' x g hfit hinv _ hh hS' hL hfree
  have hnext : F.next = R.first := by
    have := hinv.next
    simpa [slotsIn] using this
  refine planesV_returns R.f hinv.sized (by rw [hnext]; exact hinv.room) hh hS' hL ?_
  rw [hnext]
  exact hfree

#print axioms ProofFile.Honest.K3.Law.sum_map_const
#print axioms ProofFile.Honest.K3.Law.own_leafVars
#print axioms ProofFile.Honest.K3.Law.own_bits
#print axioms ProofFile.Honest.K3.Law.idxOf_split
#print axioms ProofFile.Honest.K3.Law.sum_take_idxOf
#print axioms ProofFile.Honest.K3.Law.firstSlot_leaves
#print axioms ProofFile.Honest.K3.Law.leaves_heard
#print axioms ProofFile.Honest.K3.Law.leaves_first
#print axioms ProofFile.Honest.K3.Law.planesV_returns
#print axioms ProofFile.Honest.K3.Law.planesReturn

end ProofFile.Honest.K3.Law
