-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/WriteAll.lean: for entries that are within the number of coins and share no
number, the runs that cutAll cuts off uniform coins are uniform and independent of cutAll at any
entries that share no number with them.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves. General lemmas, for every number of coins d and all lists of entries. No
sender, no oracle message and no location of a coin is in them. An entry is within d if its run ends
within d in both fields.
  runs_apart     Let every entry of es be within d, let no two entries of es share a number
                 (ApartAll), and let es and ks share no number in either field. Then, over uniform
                 coins c, the pair (cutAll c es, cutAll c ks) has the distribution in which the
                 first component is replaced by fresh uniform runs, independent of the second. A
                 statement on distributions of coins alone: nothing that a sender discloses is in
                 it, and it counts as nothing toward any goal of the release.
  lens_runs      Under the first two premises, reading the runs (runsOf) and overwriting them
                 (writeAll) satisfy the library's three equations of a lens (Prob.Lens.OK): what is
                 written is read back; writing what is read changes nothing; the last writing
                 counts.
  cutAll_writeAll   Under the same two premises, cutAll of writeAll c es v at es is v.

How it fits. coinsFresh (Johnson/SendSim/At/CoinsFresh.lean) and coinsFreshWide
(Johnson/SendSim/At/FreshWideProofs.lean) call runs_apart. They are the case of the field fresh in
which the job does not fit its place, on the way to sendFreshAtWide
(Johnson/SendSim/Seat/HandedWideProofs.lean). The proofs rest on the lemmas on writeRun and
cutAll_tells (Johnson/SendSim/At/Runs.lean) and on Prob.Lens.map_set (Prob/LensLaw.lean).

The other names.
  writeAll, runsOf   coins with all runs of a list of entries overwritten; the runs read off the
                 coins (a default value where cutAll returns none).
  ce_writeAll, cf_writeAll   at a number that is not a number of any entry, writeAll leaves the coin
                             unchanged.
  cs_eq_of_coins   two values of the coins with the same coin at every number are equal.
  eq_of_cut_off  two values with the same cutAll that agree at all other numbers are equal, if the
                 entries are within d.
  cutAll_runsOf  if the entries are within d, cutAll c es is some (runsOf es c).
-/
import Prob.LensLaw
import Johnson.SendSim.At.Runs

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob

variable {d : Due}

/-- The coins c with the runs of all entries of es overwritten by the runs v, the last entry first.
-/
def writeAll (c : Cs d) : (es : List Ahead) → CsAll (es.map Ahead.named) → Cs d
  | [], _ => c
  | e :: es, v =>
    writeRun (writeAll c es (show Cs e.count × CsAll (es.map Ahead.named) from v).2) e.start
      e.count (show Cs e.count × CsAll (es.map Ahead.named) from v).1

/-- The runs that cutAll cuts off c at the entries es, or a default value where cutAll returns none.
-/
def runsOf (es : List Ahead) (c : Cs d) : CsAll (es.map Ahead.named) := (cutAll c es).getD default

/-- At a number of the extension field that is not a number of es, writeAll leaves the coin
unchanged. -/
theorem ce_writeAll (c : Cs d) : ∀ (es : List Ahead) (v : CsAll (es.map Ahead.named)) (N : ℕ),
    N ∉ eAll es → ce (writeAll c es v) N = ce c N
  | [], _, _, _ => rfl
  | e :: es, v, N, h => by
    have h' : N ∉ eOf e ∪ eAll es := h
    rw [Finset.mem_union, not_or] at h'
    show ce (writeRun _ _ _ _) N = _
    rw [ce_writeRun _ _ _ _ N fun hh => h'.1 (Finset.mem_Ico.2 hh)]
    exact ce_writeAll c es _ N h'.2

/-- The same for the base field. -/
theorem cf_writeAll (c : Cs d) : ∀ (es : List Ahead) (v : CsAll (es.map Ahead.named)) (N : ℕ),
    N ∉ fAll es → cf (writeAll c es v) N = cf c N
  | [], _, _, _ => rfl
  | e :: es, v, N, h => by
    have h' : N ∉ fOf e ∪ fAll es := h
    rw [Finset.mem_union, not_or] at h'
    show cf (writeRun _ _ _ _) N = _
    rw [cf_writeRun _ _ _ _ N fun hh => h'.1 (Finset.mem_Ico.2 hh)]
    exact cf_writeAll c es _ N h'.2

/-- If every entry of es is within d and no two of them share a number (ApartAll), cutAll of
writeAll c es v at es is some v. -/
theorem cutAll_writeAll (c : Cs d) : ∀ es : List Ahead,
    (∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) → ApartAll es →
    ∀ v : CsAll (es.map Ahead.named), cutAll (writeAll c es v) es = some v
  | [], _, _, _ => rfl
  | e :: es, hW, hA, v => by
    obtain ⟨v1, v2⟩ : Cs e.count × CsAll (es.map Ahead.named) := v
    have hA' := List.pairwise_cons.1 hA
    have h0 := cutAll_writeAll c es (fun e' he' => hW e' (List.mem_cons_of_mem _ he')) hA'.2 v2
    show ((writeRun (writeAll c es v2) e.start e.count v1).cut e.start e.count).bind
      (fun x => (cutAll (writeRun (writeAll c es v2) e.start e.count v1) es).map fun y => (x, y)) =
      some (v1, v2)
    rw [cut_writeRun _ _ _ _ (hW e List.mem_cons_self),
      cutAll_congr (writeRun (writeAll c es v2) e.start e.count v1) (writeAll c es v2) es
        (fun i hi => cf_writeRun _ _ _ _ i (not_mem_of_apart_f e es hA'.1 i hi))
        (fun i hi => ce_writeRun _ _ _ _ i (not_mem_of_apart_e e es hA'.1 i hi)), h0]
    rfl

/-- Two values of the coins with the same coin at every number, in both fields, are equal. -/
theorem cs_eq_of_coins (c c' : Cs d) (hf : ∀ N, cf c N = cf c' N) (he : ∀ N, ce c N = ce c' N) :
    c = c' := by
  refine cs_ext _ _ (funext fun i => ?_) (funext fun i => ?_)
  · have := hf i.1
    unfold cf at this
    rwa [dif_pos i.2, dif_pos i.2] at this
  · have := he i.1
    unfold ce at this
    rwa [dif_pos i.2, dif_pos i.2] at this

/-- If every entry of es is within d, two values of the coins with the same cutAll at es that agree
at every number that is not a number of es are equal. -/
theorem eq_of_cut_off (c c' : Cs d) (es : List Ahead)
    (hW : ∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e)
    (h : cutAll c es = cutAll c' es) (hf : ∀ N, N ∉ fAll es → cf c N = cf c' N)
    (he : ∀ N, N ∉ eAll es → ce c N = ce c' N) : c = c' := by
  obtain ⟨tf, te⟩ := cutAll_tells c c' es hW h
  refine cs_eq_of_coins c c' (fun N => ?_) fun N => ?_
  · by_cases hN : N ∈ fAll es
    · exact tf N hN
    · exact hf N hN
  · by_cases hN : N ∈ eAll es
    · exact te N hN
    · exact he N hN

/-- If every entry of es is within d, cutAll c es is some (runsOf es c). -/
theorem cutAll_runsOf (c : Cs d) (es : List Ahead)
    (hW : ∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) :
    cutAll c es = some (runsOf es c) := by
  obtain ⟨v, hv⟩ := cutAll_some c es hW
  unfold runsOf
  rw [hv]
  rfl

/-- If every entry of es is within d and no two of them share a number (ApartAll), runsOf and
writeAll satisfy the three equations of the library's Prob.Lens.OK. -/
theorem lens_runs (es : List Ahead)
    (hW : ∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e)
    (hA : ApartAll es) :
    Lens.OK (runsOf (d := d) es) fun v c => writeAll c es v where
  tst_set := fun v c => by
    unfold runsOf
    rw [cutAll_writeAll c es hW hA v]
    rfl
  set_tst := fun c => eq_of_cut_off _ _ es hW
    (by rw [cutAll_writeAll c es hW hA, cutAll_runsOf c es hW])
    (fun N hN => cf_writeAll c es _ N hN) fun N hN => ce_writeAll c es _ N hN
  set_set := fun v v' c => eq_of_cut_off _ _ es hW
    (by rw [cutAll_writeAll _ es hW hA, cutAll_writeAll _ es hW hA])
    (fun N hN => by rw [cf_writeAll _ es _ N hN, cf_writeAll _ es _ N hN, cf_writeAll _ es _ N hN])
    fun N hN => by rw [ce_writeAll _ es _ N hN, ce_writeAll _ es _ N hN, ce_writeAll _ es _ N hN]

/-- If every entry of es is within d, no two of them share a number (ApartAll), and es and ks share
no number in either field, then over uniform coins c the pair (cutAll c es, cutAll c ks) has the
distribution of (fresh uniform runs, cutAll c ks), the two independent. A lemma on coins alone, used
as a tool; it counts as nothing toward any goal of the release. -/
theorem runs_apart (es ks : List Ahead)
    (hW : ∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e)
    (hA : ApartAll es) (hE : Disjoint (eAll es) (eAll ks)) (hF : Disjoint (fAll es) (fAll ks)) :
    (unif (Cs d)).map (fun c => (cutAll c es, cutAll c ks)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun a => (some a.1, cutAll a.2 ks) := by
  rw [← Lens.map_set (lens_runs (d := d) es hW hA), PMF.map_comp]
  refine congrArg (fun f => (unif (CsAll (es.map Ahead.named) × Cs d)).map f) (funext fun a => ?_)
  show (cutAll (writeAll a.2 es a.1) es, cutAll (writeAll a.2 es a.1) ks) = _
  rw [cutAll_writeAll a.2 es hW hA a.1, cutAll_congr (writeAll a.2 es a.1) a.2 ks
    (fun i hi => cf_writeAll a.2 es a.1 i fun h => Finset.disjoint_left.1 hF h hi)
    fun i hi => ce_writeAll a.2 es a.1 i fun h => Finset.disjoint_left.1 hE h hi]

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.lens_runs
#print axioms OnBytes.SendSim.At.runs_apart
