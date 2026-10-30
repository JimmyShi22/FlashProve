-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/StillRun.lean: THE BATCHING KIND's PREMISE ON A RUN OF CLAIMS, PAID ONCE
FOR EVERY RUN THAT LEAVES THE CARRIED RECORD AS IT IS AND RETURNS PLAIN CLAIMS WHOSE FORMS ARE READ
OFF WHAT WAS FIXED BEFORE THE DRAW.
Theorems, under named premises on the letters that all kinds share. A tool for the kinds' files.
The forms are read off ALL of q, the snapshot's ledger among it, at a state that goes
on from q, not off φ alone: φ must be blind to the ledger: so a run
whose readers look at the live ledger (attention's) could not meet that.

Why. Every run of a link's order owes `RunOk` (Johnson/Desc/First/Link/Law/LinkJoinRuns.lean:
`hrun`). The runs that lay hiding coefficients behind the draw have payers of their own (K4Run.lean,
K11Run.lean beside this file). The other runs write nothing. For such a run the whole debt is: its
claims' values at a later state are functions of what was fixed before the draw and of the data.

What is said.
  `Still φ Ok run fs`: the run's shape: `hands`: a yes hands the record back as it is; `forms`: at a
    state that goes on from q its claims are the plain claims of the forms `fs q`. `valsStill`,
    `lenStill`: their values in the world that the snapshot's ledger names
    (Johnson/Desc/First/Link/Law/K4Values.lean: `refWorld`, no window), and their number. Where q
    has no snapshot the two part (no value; the forms' number): never met at a yes.
  `still_plainOk`, `still_runOk`: **`PlainOk` and `RunOk` of such a run**, under hOk: every slot
    that a form names is filled in the snapshot; hFu: at a full state that goes on from q the
    entries of virtual rows that the forms name are `ent q y`. `still_door`: the door's duty: the
    record is the same.

HOW STRONG `forms` IS. The claims hang on the state alone: so at all q from which one state goes on
`fs q` must be one list, and all states that go on from one q and say yes must return one list.
Whatever the run's readers look at must therefore be fixed by q: φ's share, and of the ledger only
what is filled in the snapshot. So `forms` is payable only if `Ok q` says that every slot UNDER
WHICH A READER LOOKS is filled in the snapshot: another set than the slots that the forms NAME, of
which hOk speaks. `fs` takes no number: the forms may not hang on the number of claims in front.

Limits. AN IMPLICATION: that a run of the protocol is `Still`, and hOk and hFu, are its kind's
to show. A run that never says yes at a state that goes on from some q is `Still` for
nothing, and its `RunOk` is idle. It covers no claim with a run of entries (`eqFirst`). No member
here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Batch.Law.PlainRuns
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.First.Batch.Law.MovesDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.StillRun
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Values (refWorld values_ref)

variable {α K : Type}

/-- The run's shape: a yes hands the record back as it is; and at a state that goes on from q its
claims are the plain claims of forms that are read off q: off φ AND OFF THE SNAPSHOT (its ledger
among it: a reader that looks at the live ledger through what was shown before the draw is met by
what the snapshot shows). -/
structure Still (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (run : ℕ → S → Except String (List Claim × S))
    (fs : α × Option Pub9 → Option (List Aff)) : Prop where
  hands : ∀ n e c e₁, run n e = .ok (c, e₁) → e₁ = e
  forms : ∀ q n e c e₁, Fx9 φ Ok q e → run n e = .ok (c, e₁) →
    ∃ l, fs q = some l ∧ c = l.map fun f => ({ form := f } : Claim)

/-- The number of the run's claims. -/
def lenStill (fs : α × Option Pub9 → Option (List Aff)) (q : α × Option Pub9) : ℕ :=
  ((fs q).getD []).length

variable [Field K] (ρ : Reading K)

/-- The values of the run's claims. -/
def valsStill (fs : α × Option Pub9 → Option (List Aff))
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (q : α × Option Pub9) (y : Bound K) : List K :=
  match q.2 with
  | some u => ((fs q).getD []).map fun f => f.value ρ (refWorld ρ u.F [] (ent q y) y)
  | none => []

/-- **PlainOk OF A RUN THAT LEAVES THE RECORD AS IT IS.** -/
theorem still_plainOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (run : ℕ → S → Except String (List Claim × S)) (fs : α × Option Pub9 → Option (List Aff))
    (hrun : Still φ Ok run fs)
    (hOk : ∀ q l u, Ok q → fs q = some l → q.2 = some u →
      ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fs q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    PlainOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (valsStill ρ fs ent) (lenStill fs) := by
  intro q front e a c e₁ hf hg ha _ hr
  obtain rfl := hrun.hands front e c e₁ hr
  obtain ⟨l, hq, rfl⟩ := hrun.forms q front e₁ c e₁ hf hr
  have hf0 := hf
  obtain ⟨hok, _, u, b0, hu, hb0, gu⟩ := hf
  obtain rfl : a = b0 := Option.some.inj (ha.symm.trans hb0)
  have hmore : more9 φ e₁ e₁ := ⟨rfl, fun a' ha' => ⟨a', ha', goesOn_refl a'⟩⟩
  refine ⟨a, ha, rfl, rfl, hg, hmore, hf0, by simp [lenStill, hq], fun cl hcl => ?_,
    fun t b y ht hfull hb => ?_⟩
  · obtain ⟨f, _, rfl⟩ := List.mem_map.1 hcl
    rfl
  · obtain ⟨b', hb', gb⟩ := ht.2.1.2 a ha
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    have hfx : Fx9 φ Ok q t := fx_of_more φ Ok q _ t hf0 ht.2.1
    simp only [valsStill, hu, hq, Option.getD_some]
    exact values_ref ρ l b.L u.F b.F [] (ent q y) y (gu.1.trans gb.1)
      (fun _ h => absurd h List.not_mem_nil)
      (fun f hf' x hx => Or.inr (hOk q l u hok hq hu f hf' x hx))
      (fun f hf' x hx => hFu q l t b y hfx hfull hb hq f hf' x hx)

/-- **RunOk OF SUCH A RUN.** -/
theorem still_runOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (run : ℕ → S → Except String (List Claim × S)) (fs : α × Option Pub9 → Option (List Aff))
    (hrun : Still φ Ok run fs)
    (hOk : ∀ q l u, Ok q → fs q = some l → q.2 = some u →
      ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled u.F x.1)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K)
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fs q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (plainTm (valsStill ρ fs ent)) (lenStill fs) :=
  runOk_of_plain ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run _ _ (part_of_more φ)
    (still_plainOk ρ φ Ok Fu run fs hrun hOk ent hFu)

omit [Field K] in
/-- The door's duty: the record is the same. -/
theorem still_door (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (run : ℕ → S → Except String (List Claim × S)) (fs : α × Option Pub9 → Option (List Aff))
    (hrun : Still φ Ok run fs) (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (h : run n e = .ok (c, e₁)) : KeepsDoor atS e e₁ := by
  obtain rfl := hrun.hands n e c e₁ h
  exact fun a ha => ⟨a, ha, rfl, rfl⟩

end VerifiableInference.Desc.StillRun

#print axioms VerifiableInference.Desc.StillRun.still_plainOk
#print axioms VerifiableInference.Desc.StillRun.still_runOk
#print axioms VerifiableInference.Desc.StillRun.still_door
