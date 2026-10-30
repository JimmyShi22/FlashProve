-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/NothingSpent.lean: at the empty list of entries the equation of the field fresh
holds for any two functions of the coins, because the runs at the empty list have one value only.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves. A general lemma of probability, for every number of coins d. No sender, no
oracle message and no location of a coin is in it.
  nothingSpent  Spec.nothingSpent: for any functions sh and kn of the coins and every list L of
                entries with L = [], over uniform coins c the tuple (cutAll c L, sh c, kn c) has the
                distribution of (some r, sh c, kn c), where r is sampled uniformly from the runs of
                L, independently of c. The statement and its proof are both in this file.
  fresh_none    The same with [] written in place of L. A tool for nothingSpent; it counts as
                nothing toward any goal of the release.

How it fits. rowsFresh_of_core (Johnson/SendSim/At/JoinRows.lean) uses nothingSpent for the first
case of SpenderClear, an address that spends nothing of the owner. So it serves rowsFresh
(Johnson/SendSim/At/RowsFresh.lean); Johnson/SendSim/At/SpendersAloneProofs.lean uses it too. The
proof rests on map_snd_unif (Prob/Count.lean).
-/
import Prob.Count
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest Prob

/-- For any functions sh and kn of the coins and every list L of entries that is empty: over uniform
coins c, the tuple (cutAll c L, sh c, kn c) has the distribution of (some r, sh c, kn c) with r
uniform on the runs of L and independent of c. Statement only; proved as nothingSpent below. -/
def Spec.nothingSpent : Prop :=
  ∀ (d : Due) (β γ : Type) (sh : Cs d → β) (kn : Cs d → γ) (L : List Ahead), L = [] →
    (unif (Cs d)).map (fun c => (cutAll c L, sh c, kn c)) =
      (unif (CsAll (L.map Ahead.named) × Cs d)).map fun a => (some a.1, sh a.2, kn a.2)

/-- Spec.nothingSpent with the empty list written out. A tool for nothingSpent; it counts as nothing
toward any goal of the release. -/
theorem fresh_none {d : Due} {β γ : Type} (sh : Cs d → β) (kn : Cs d → γ) :
    (unif (Cs d)).map (fun c => (cutAll c [], sh c, kn c)) =
      (unif (CsAll (([] : List Ahead).map Ahead.named) × Cs d)).map fun a =>
        (some a.1, sh a.2, kn a.2) := by
  have e : (fun a : CsAll (([] : List Ahead).map Ahead.named) × Cs d =>
      ((some a.1 : Option (CsAll (([] : List Ahead).map Ahead.named))), sh a.2, kn a.2)) =
      (fun c => (cutAll c [], sh c, kn c)) ∘ Prod.snd := by
    funext a
    rfl
  rw [e, ← PMF.map_comp, map_snd_unif]

/-- Proof of Spec.nothingSpent, from fresh_none. -/
theorem nothingSpent : Spec.nothingSpent := by
  intro d β γ sh kn L h
  subst h
  exact fresh_none sh kn

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.nothingSpent
