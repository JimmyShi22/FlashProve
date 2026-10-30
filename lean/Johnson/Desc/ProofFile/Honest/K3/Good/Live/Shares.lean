-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Shares.lean: the kind "lookup" (K3): two lists of claims
that are made of what a lookup heard alone, with no run of claims in the statement: the heard rows
as plain claims, and the first four claims of the smallness test's equations: under the condition of
Honest/K3/Good/Live/Clause.lean the first is live on the window of "objects" and the second on the
windows of "planes" and "join"; neither names a slot outside the lookup's own stretch. Theorems.

Terms. Honest/K3/GLOSSARY.md ("window", "run (of claims): objects, guests, planes, join", "slot").
In this file: `plainOf l` makes of each form the claim `{ form := f }`
(Johnson/Desc/K8/Honest/FallLayers.lean); `four8 tl g` is the list of four claims of
Johnson/Desc/First/Batch/Law/K8Four.lean; "live" and "does not name" are `liveAt` and `unnamedAt`
(Johnson/Desc/K9/Honest/SlotsLive.lean). g is what the lookup heard, p the place's public
parameters, h its shape; a window counts from p.first. `InWin` is a definition of this file; the
library bears that short name in other senses (for one: Johnson/Road/K4/Slots/RunsSpare.lean). `Run`
(Honest/K3/GoodDraws.lean) has three values: the run "guests" has no window.

What is shown.
  `rows_live`: `plainOf g.rows.toList` is live on each slot of the window of "objects".
  `rows_unnamed`: it names no slot outside the lookup's own stretch.
  `four8_live`: `four8 tl g` is live on each slot of the windows of "planes" and "join", at every
    tl.
  `four8_unnamed`: it names no slot outside the lookup's own stretch, at every tl.
A remark, stated by no theorem of this file: with `window_iff` (Honest/K3/Good/Live/Windows.lean)
the two lists together are live on the whole stretch.
  `InWin p h r j`: slot j is in the window of the run r, counted from p.first.
  `pay_live`, `pay_unnamed`, `pay_live8`, `pay_unnamed8`: the four above, in the form "for every g
    that the optional value o holds": o is what a state holds as heard by the lookup, and meets the
    condition.

Hypotheses that remain. `hp`: the place's parameters make the shape h. `J`: g meets the condition
(in the two on "names no slot" at any test T). `hj`: j is in the window; or `Outside p h j`. No
hypothesis on any calling kind: the forms of `four8` are a constant less g.cEnd, the row form of the
leaves' sumcheck with nothing kept, the form on g.sBit, and a constant; what the four claims read of
arrays is in their runs of entries, which the two tests do not read. In the four `pay_…`: `J` is
said of the optional value o, and g is whatever o holds.

Related. The library spells the four claims out, one by one: `four8_zero`
(Johnson/Desc/K8/Honest/DigitsLiveOf.lean); `four8_one`, `four8_two`, `four8_three`
(Johnson/Desc/K8/Honest/PlanesLiveOf.lean).

How the proof goes. `cEnd_sc`, `planes_sc`, `outside_clear` (Honest/K3/Good/Live/Forms.lean).

Users. Honest/K3/Good/Live/SharesCover.lean, Honest/K3/Good/Live/SharesGuards.lean
[not in this library] and Honest/K9/GoodAttEight.lean import this file.

Limits. That a state holds such a g, that tl is the smallness test's structure at that state, and
that a run's list of claims begins with `four8 tl g` (the library's `take_four`, K8Four.lean) are
not said here. Whether g was heard by the lookup on the digits or by another is not asked: the
statements hold of any g that meets the condition. No instance of the hypotheses together is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Forms
import Johnson.Desc.K8.Honest.FallLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes (oneE)
open OnBytes.Model (Aff HTailF2)
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.K9H (liveAt unnamedAt)
open VerifiableInference.Desc.K9L (four8)
open VerifiableInference.Desc.First.K8.Honest (plainOf)
open ProofFile.Honest.K3.Law.Exchange (toHeard_parts)

/-! ## The heard rows -/

/-- **The heard rows, as plain claims, are live on the window of "objects".** Conditional on the
hypotheses that the head of this file lists. -/
theorem rows_live {p : P} {h : Shape} (hp : p.shape = some h) {g : Heard}
    (J : Clause p (some g)) {j : ℕ} (hj : j ∈ windowOf (faceOf h) .objects) :
    liveAt (plainOf g.rows.toList) (p.first + j) = true := by
  obtain ⟨H, F, G, rs, gv, eH, hd, hn, hh, hto, hcd, hgd⟩ := clause_open hp J
  obtain rfl : g = H := Option.some.inj eH
  obtain ⟨_, _, _, _, hrows, _⟩ := toHeard_parts hto
  obtain ⟨a, ha, hne⟩ := gives_pure hd hcd hh .objects (goodRun_of _ _ hgd .objects) hj
  have ha' : a ∈ g.rows.toList := by rw [hrows]; exact ha
  rw [hn] at hne
  exact live_of_form (cl := { form := a }) (List.mem_map.2 ⟨a, ha', rfl⟩) rfl hne

/-- **They name no slot outside the lookup's own stretch.** Conditional on the hypotheses that the
head of this file lists. -/
theorem rows_unnamed {T : LFace → List Fmt.Drawn → Bool} {p : P} {h : Shape}
    (hp : p.shape = some h) {g : Heard} (J : ClauseBy T p (some g)) {j : ℕ}
    (hj : Outside p h j) : unnamedAt (plainOf g.rows.toList) j = true := by
  refine unnamed_of_forms fun cl hcl => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hcl
  exact (outside_clear hp J hj).1 a ha

/-! ## The first four claims of the smallness test's equations -/

/-- **They are live on the windows of "planes" and "join".** Conditional on the hypotheses that the
head of this file lists. -/
theorem four8_live (tl : HTailF2) {p : P} {h : Shape} (hp : p.shape = some h) {g : Heard}
    (J : Clause p (some g)) {j : ℕ}
    (hj : j ∈ windowOf (faceOf h) .planes ∨ j ∈ windowOf (faceOf h) .join) :
    liveAt (four8 tl g) (p.first + j) = true := by
  rcases hj with hj | hj
  · rcases planes_sc hp J hj with h1 | h1
    · exact live_of_form (l := four8 tl g)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) rfl (h1 {} (sc_empty _))
    · refine live_of_form (l := four8 tl g)
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl ?_
      show sc (Aff.slot g.sBit) (p.first + j) ≠ 0
      rw [h1, sc_slot, if_pos rfl]
      exact one_ne_zero
  · refine live_of_form (l := four8 tl g) (List.mem_cons_self ..) rfl ?_
    show sc (Aff.ofConst _ - g.cEnd) (p.first + j) ≠ 0
    rw [sc_sub, sc_ofConst, zero_sub]
    exact neg_ne_zero.2 (cEnd_sc hp J hj)

/-- **They name no slot outside the lookup's own stretch.** Conditional on the hypotheses that the
head of this file lists. -/
theorem four8_unnamed {T : LFace → List Fmt.Drawn → Bool} (tl : HTailF2) {p : P} {h : Shape}
    (hp : p.shape = some h) {g : Heard} (J : ClauseBy T p (some g)) {j : ℕ}
    (hj : Outside p h j) : unnamedAt (four8 tl g) j = true := by
  obtain ⟨_, c2, c3, c4⟩ := outside_clear hp J hj
  refine unnamed_of_forms fun cl hcl => ?_
  unfold four8 at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl
  · exact clear_sub (clear_ofConst _ _) c2
  · exact c3 _ _ (clear_empty _)
  · exact clear_slot c4
  · exact clear_ofConst _ _

/-! ## The same, at an optional value that meets the condition -/

/-- Slot j is in the window of the run r, counted from the place's first slot. -/
def InWin (p : P) (h : Shape) (r : Run) (j : Nat) : Prop :=
  ∃ j' ∈ windowOf (faceOf h) r, j = p.first + j'

/-- `rows_live`, for every g that the optional value o holds. -/
theorem pay_live {p : P} {h : Shape} (hp : p.shape = some h) {o : Option Heard} (J : Clause p o) :
    ∀ g, o = some g → ∀ j, InWin p h .objects j → liveAt (plainOf g.rows.toList) j = true := by
  rintro g rfl j ⟨j', hj', rfl⟩
  exact rows_live hp J hj'

/-- `rows_unnamed`, for every g that the optional value o holds. -/
theorem pay_unnamed {T : LFace → List Fmt.Drawn → Bool} {p : P} {h : Shape}
    (hp : p.shape = some h) {o : Option Heard} (J : ClauseBy T p o) :
    ∀ g, o = some g → ∀ j, Outside p h j → unnamedAt (plainOf g.rows.toList) j = true := by
  rintro g rfl j hj
  exact rows_unnamed hp J hj

/-- `four8_live`, for every g that the optional value o holds. -/
theorem pay_live8 (tl : HTailF2) {p : P} {h : Shape} (hp : p.shape = some h) {o : Option Heard}
    (J : Clause p o) :
    ∀ g, o = some g → ∀ j, InWin p h .planes j ∨ InWin p h .join j →
      liveAt (four8 tl g) j = true := by
  rintro g rfl j (⟨j', hj', rfl⟩ | ⟨j', hj', rfl⟩)
  · exact four8_live tl hp J (.inl hj')
  · exact four8_live tl hp J (.inr hj')

/-- `four8_unnamed`, for every g that the optional value o holds. -/
theorem pay_unnamed8 {T : LFace → List Fmt.Drawn → Bool} (tl : HTailF2) {p : P} {h : Shape}
    (hp : p.shape = some h) {o : Option Heard} (J : ClauseBy T p o) :
    ∀ g, o = some g → ∀ j, Outside p h j → unnamedAt (four8 tl g) j = true := by
  rintro g rfl j hj
  exact four8_unnamed tl hp J hj

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.rows_live
#print axioms ProofFile.Honest.K3.Good.Live.rows_unnamed
#print axioms ProofFile.Honest.K3.Good.Live.four8_live
#print axioms ProofFile.Honest.K3.Good.Live.four8_unnamed
#print axioms ProofFile.Honest.K3.Good.Live.pay_live
#print axioms ProofFile.Honest.K3.Good.Live.pay_unnamed
#print axioms ProofFile.Honest.K3.Good.Live.pay_live8
#print axioms ProofFile.Honest.K3.Good.Live.pay_unnamed8
