-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/CanAllPlan.lean: the kind "lookup" (K3): the first
hypothesis of the marks' bounds (`CanAll`, Honest/K3/Good/MarkShare.lean) at data that bear the
PLAN's entries, work bits and all; and what `CanAll` gives round by round. Conditional. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), sample and kit. In this file: f
is a lookup's face, C a kit, es the plan's entries at the lookup, dsb the data of the rounds of the
lookup's member.

What is shown.
  `canAll_of_plan`: `CanAll`, at a kit that meets the three clauses of the frame's `drawsFit_typed`
    (Honest/Law/Due.lean), at data that bear the plan's entries and the kinds
    of their names.
  `no_pad`: under `CanAll`: at every message of the kit, at every round of the verifier's list, a
    sampled value stands and has just as many elements as the round draws.

Why `canAll_of_plan` stands beside `canAll_of_kit` (Honest/K3/Good/MarkKit.lean). That theorem asks
that the data bear the verifier's entries, whose work bits are 0. A description's data bear the
plan's entries, which are the verifier's but for the work bits. The frame's test on samples reads no
work bit (`drawsWork`, Honest/K3/Law/Steps.lean).

Hypotheses that remain.
  `hC`: the three clauses on the kit. The frame's `kit_two` (Honest/Law/KitTwo.lean) has them at the
    kit at the release's field; it is not called here.
  `hes`: the plan's entries pass the verifier's test. `hk`: the data bear them, round for round.
  `hc`, `h`: (in `no_pad`) `CanAll`; en is the verifier's entry at the number n.

Imported: Honest/K3/Good/MarkShare.lean and, beneath it, Honest/Law/Due.lean.

Users. Honest/K3/Good/H3/Fence.lean [not in this library] and Member.lean.

Limits. Implications. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkShare
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Entries
import Johnson.Desc.ProofFile.Honest.K3.Law.Steps
import Johnson.Desc.ProofFile.Honest.K3.Law.CutOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc (fieldPrimeWord)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-- CONDITIONAL on three clauses on the kit: whatever the kit's messages show is such as the
lookup's rounds can sample, at data that bear THE PLAN's entries (work bits and all). -/
theorem canAll_of_plan (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (f : LFace) (es : List Fmt.Entry)
    (hes : entriesFit f es = true) (dsb : List RDT)
    (hk : List.Forall₂ KindFits dsb (es.map Law.declOf)) : CanAll C f dsb := fun ρ => by
  have h1 := drawsFit_typed C hC dsb (es.map Law.declOf) hk (fun z hz => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
    exact (entriesV_tame f _ (fit_mem f es hes e he)).2.1) ρ
  rw [Law.drawsWork f es _ hes] at h1
  exact h1

/-- **No default is read.** CONDITIONAL on CanAll: at every message of the kit, at every round of
the verifier's list, a drawn value stands and has just as many elements as the round draws. -/
theorem no_pad (C : CK) (f : LFace) (dsb : List RDT) (hc : CanAll C f dsb)
    (ρ : Iop.Rho (uLT C dsb)) (n : Nat) (en : Fmt.Entry) (h : (entriesV f)[n]? = some en) :
    ∃ R, (drawnT C dsb ρ)[n]? = some R ∧ R.elems.length = en.drawE := by
  have h0 : drawsFit ((entriesV f).map Law.declOf) (drawnT C dsb ρ) = true := hc ρ
  have hl := congrArg List.length (Law.drawsFit_counts _ _ h0)
  rw [List.length_map, List.length_map] at hl
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.1 h
  have hn' : n < (drawnT C dsb ρ).length := by
    rw [hl]
    exact hn
  exact ⟨_, List.getElem?_eq_getElem hn',
    Law.cut_fit_at _ _ n en _ h0 h (List.getElem?_eq_getElem hn')⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.canAll_of_plan
#print axioms ProofFile.Honest.K3.Good.no_pad
