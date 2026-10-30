-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/ReadItems.lean: Given.read returns the further items of a chain's parameter bytes
as they were spelled, with no bound on the number of all bytes.

OnBytes/Params/ReadBackLaws.lean (Given.read_items) says it of parameter bytes that are fewer than
2^64 in all. OnBytes/Tie/SameChains.lean takes that bound from a yes of the checks; the planner's
yes alone is not known to give it. Here the bound is asked of each item alone. Of the plan it is
asked that the entries' names fit and that none is the name of the configuration's item. Then, where
the reader returns at all, the plan has fewer than 2^64 entries (read_short,
OnBytes/Params/Fit/ReadPrefix.lean). The plan with every number modulo 2^64 spells the same bytes
and fits the format's words (OnBytes/Params/Fit/ReadNorm.lean). So the library's theorem that
reading undoes spelling (Fmt.params_back) applies.

Main theorems.
 - paramsRead_fit: what the library's reader returns: the reduced plan, the digest, the items.
 - **Given.read_items_fit**: the items in what Given.read returns are the items that were spelled.

What is asked: each entry's name fits (Fmt.nameFit) and is not "configuration"; the digest has 32
bytes; each item's name fits and its value has fewer than 2^64 bytes; the reader returns. Nothing if
the reader refuses. Nothing on soundness. For proofs only; the program does not import this file.


-/
import OnBytes.Params.Fit.ReadPrefix

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- What the library's reader returns on the parameter bytes: the reduced plan, the digest, the
items; if the entries' names fit, the plan has fewer than 2^64 entries, the digest has 32 bytes, and
each item's name fits and its value has fewer than 2^64 bytes. -/
theorem paramsRead_fit {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    (hn : ∀ e ∈ P.entries, nameFit e.name = true) (hl : P.entries.length < 2 ^ 64)
    (h32 : cfg.size = 32) (ho : ∀ y ∈ others, nameFit y.1 = true ∧ y.2.size < 2 ^ 64) :
    paramsRead (paramsBytes P cfg others) = some ⟨normP P, cfg, others⟩ := by
  have hf : (⟨normP P, cfg, others⟩ : Fmt.Params).fit = true := by
    unfold Fmt.Params.fit
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨fit_normP hn hl, beq_iff_eq.2 h32⟩, List.all_eq_true.2 fun y hy => ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨(ho y hy).1, decide_eq_true (ho y hy).2⟩
  rw [← paramsBytes_norm]
  exact params_back ⟨normP P, cfg, others⟩ hf

/-- **The items as read back are the items that were spelled.** -/
theorem Given.read_items_fit {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hn : ∀ e ∈ P.entries, nameFit e.name = true)
    (hc : ∀ e ∈ P.entries, e.name ≠ configName) (h32 : cfg.size = 32)
    (ho : ∀ y ∈ others, nameFit y.1 = true ∧ y.2.size < 2 ^ 64)
    (h : Given.read (paramsBytes P cfg others) = some g) : g.items = others := by
  have hp := paramsRead_fit hn (read_short hn hc h) h32 ho
  unfold Given.read at h
  rw [paramsReadT_eq, hp] at h
  simp only [Option.bind_some] at h
  split at h
  · cases h
    rfl
  · cases h

end OnBytes.Params

#print axioms OnBytes.Params.paramsRead_fit
#print axioms OnBytes.Params.Given.read_items_fit
