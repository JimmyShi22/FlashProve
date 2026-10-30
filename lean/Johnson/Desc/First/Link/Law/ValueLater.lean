-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/ValueLater.lean: THE VALUE OF A PLAIN CLAIM, READ AT A LATER LEDGER, IS
ITS VALUE AT THE LEDGER AT WHICH ITS SLOTS WERE FILLED. Theorems: tools for whoever pays «fixed
before the draw» at a run of plain claims.

Why. The batching kind's law asks of a run of claims that the claims' values, read at ANY later full
state, are functions of what was fixed before the draw and of the prover's data
(Johnson/Desc/LinkLaw19.lean: `RunGoesOn`; the batching kind's own `RunOk`). A claim's value reads
the ledger at the slots that its form names (shown value and factor) and the arrays' frame at the
entries that it names. What lies under a filled slot stays (`OnBytes.PscRun.Later`). So the value
can be read at the ledger in front.

What is said.
  `value_on`: a form's value is the same in two worlds that agree at the slots and the entries that
    the form names.
  `slot_later`: under a slot that is filled in G, the hidden value at a later ledger B is that at G.
    `slot_laid`: under a slot that holds (shown 0, factor −1) it is the mask row's entry: the
    data's.
  `value_later`: **a form all of whose slots are filled in G has at every later ledger B the value
    that it has at G, if the two worlds agree at the entries that it names.** `claim_plain`: a claim
    without runs has its form's value. `values_later`: the like of a list of forms as plain claims.
  `entry_same`: two frames that agree at the array t (its number of rows) and at the virtual row r
    (its weights), under one table of names, give the same entry.

Limits. Tools. Which slots a kind's forms name, that the hearing or the run itself has filled them,
and that the virtual rows that its entries name have their weights at a full state, is each kind's.
Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.Measure
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ValueLater
open OnBytes OnBytes.Model
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc.K9L (claimValue worldAt entryAt Bound)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A form's value is the same in two worlds that agree at what the form names. -/
theorem value_on (f : Aff) (W W' : World K)
    (hs : ∀ x ∈ f.slots.toList, W'.slot x.1 = W.slot x.1)
    (he : ∀ x ∈ f.ents.toList, W'.entry x.tree x.row x.idx = W.entry x.tree x.row x.idx) :
    f.value ρ W' = f.value ρ W := by
  unfold Aff.value
  rw [List.map_congr_left fun x hx => show Ent.value ρ W' x = Ent.value ρ W x by
      unfold Ent.value
      rw [he x hx],
    List.map_congr_left fun x hx => show slotValue ρ W' x = slotValue ρ W x by
      unfold slotValue
      rw [hs x hx]]

/-- Under a filled slot the hidden value stays. -/
theorem slot_later (L L' : LinkCtx) (G B : Fork) (y : Bound K) (h : Later G B) (j : ℕ)
    (hj : Filled G j) : (worldAt ρ L' B y).slot j = (worldAt ρ L G y).slot j := by
  obtain ⟨_, h1, h2⟩ := h.keep j hj
  show ρ.val (B.vp.getD j zeroE) - ρ.val (B.mf.getD j zeroE) * y.mask j =
    ρ.val (G.vp.getD j zeroE) - ρ.val (G.mf.getD j zeroE) * y.mask j
  rw [h1, h2]

/-- Under a slot that holds (shown 0, factor -1) the hidden value is the mask row's entry. -/
theorem slot_laid (L : LinkCtx) (G : Fork) (y : Bound K) (j : ℕ) (h1 : G.vp.getD j zeroE = zeroE)
    (h2 : G.mf.getD j zeroE = subE zeroE oneE) : (worldAt ρ L G y).slot j = y.mask j := by
  show ρ.val (G.vp.getD j zeroE) - ρ.val (G.mf.getD j zeroE) * y.mask j = _
  rw [h1, h2, ρ.sub, ρ.zero, ρ.one]
  ring

/-- **THE VALUE AT A LATER LEDGER.** -/
theorem value_later (f : Aff) (L L' : LinkCtx) (G B : Fork) (y : Bound K) (h : Later G B)
    (hs : ∀ x ∈ f.slots.toList, Filled G x.1)
    (he : ∀ x ∈ f.ents.toList, (worldAt ρ L' B y).entry x.tree x.row x.idx =
      (worldAt ρ L G y).entry x.tree x.row x.idx) :
    f.value ρ (worldAt ρ L' B y) = f.value ρ (worldAt ρ L G y) :=
  value_on ρ f _ _ (fun x hx => slot_later ρ L L' G B y h x.1 (hs x hx)) he

/-- A claim without runs has its form's value. -/
theorem claim_plain (W : World K) (f : Aff) : claimValue ρ W { form := f } = f.value ρ W := by
  simp [claimValue]

/-- The like of a list of forms, as plain claims. -/
theorem values_later (fs : List Aff) (L L' : LinkCtx) (G B : Fork) (y : Bound K) (h : Later G B)
    (hs : ∀ f ∈ fs, ∀ x ∈ f.slots.toList, Filled G x.1)
    (he : ∀ f ∈ fs, ∀ x ∈ f.ents.toList, (worldAt ρ L' B y).entry x.tree x.row x.idx =
      (worldAt ρ L G y).entry x.tree x.row x.idx) :
    (fs.map fun f => ({ form := f } : Claim)).map (claimValue ρ (worldAt ρ L' B y)) =
      fs.map fun f => f.value ρ (worldAt ρ L G y) := by
  rw [List.map_map]
  refine List.map_congr_left fun f hf => ?_
  show claimValue ρ _ { form := f } = _
  rw [claim_plain, value_later ρ f L L' G B y h (hs f hf) (he f hf)]

/-- Two frames that agree at an array's number of rows and at a virtual row's weights give the same
entry, under one table of names. -/
theorem entry_same (arrayOf : Array (ℕ × String)) (fr fr' : Array (HTree × Array (HRow × ℕ)))
    (y : Bound K) (t r i : ℕ) (h1 : (fr'.getD t default).1.R = (fr.getD t default).1.R)
    (h2 : ((fr'.getD t default).2.getD r default).1.coef =
      ((fr.getD t default).2.getD r default).1.coef) :
    entryAt ρ arrayOf fr' y t r i = entryAt ρ arrayOf fr y t r i := by
  unfold entryAt
  rw [h1, h2]

end VerifiableInference.Desc.ValueLater

#print axioms VerifiableInference.Desc.ValueLater.value_on
#print axioms VerifiableInference.Desc.ValueLater.slot_later
#print axioms VerifiableInference.Desc.ValueLater.slot_laid
#print axioms VerifiableInference.Desc.ValueLater.value_later
#print axioms VerifiableInference.Desc.ValueLater.claim_plain
#print axioms VerifiableInference.Desc.ValueLater.values_later
#print axioms VerifiableInference.Desc.ValueLater.entry_same
