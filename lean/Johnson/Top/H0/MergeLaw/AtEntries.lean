-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/AtEntries.lean: what the merge's law asks of its written rounds (`MergeDs`,
Johnson/Top/H0/MergeLaw/Maps.lean) follows from the block's own entries. Theorems with their proofs.

The law's written rounds were letters under `MergeDs`. Here one equation takes its place: the
rounds'
entries, in order, are `mergeEntries` (Johnson/Desc/First/Fork/MergeKind.lean), the list of which
the
block's declared rounds are made; and each round's kind is that of its entry's name.

Main names:
  `sd_of_entry`: the library's `sendsDraws_of` (OnBytes/Slice/RoundsOf.lean) at a written round.
  `entries_of`: the equation on the entries, round by round.
  `mergeDs_of_entries`: from the equation on the entries, and "no round is of the kind sealed or
    seeds": `MergeDs`, and one round for each column bit.
  `split_of_entries`: a list of written rounds with these entries has the merge's form: two rounds,
    a list, two rounds.
  `kinds_of_names`: the premise on kinds, out of `Fmt.kindOf` at the five names.
  `mergeDs_of_list`: all in one.

Limits. That a plan's stretch at the merge's place has these entries is not shown here. Of a written
round the entry and the kind alone are read: nothing on its items, trees or openings. Nothing on
soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Maps
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (RoundName)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)

/-- A written round whose entry is e, of a kind that is neither "sealed" nor "seeds". -/
theorem sd_of_entry (d : RDT) (e : Fmt.Entry) (he : d.entry = e) (hk : d.kind ≠ .sealed)
    (hs : d.kind ≠ .seeds) (ht : e.trits = 0) (hz : e.drawNZ ≤ e.drawE) (hl : e.logN ≤ 64) :
    SendsDraws (toRD d) (nS d.items) e.drawE e.poss e.logN := by
  subst he
  exact sendsDraws_of (r := { entry := d.entry, kind := d.kind, items := d.items })
    ⟨rfl, rfl, rfl⟩ ht hk hs hz hl

/-- The equation on the entries, round by round. -/
theorem entries_of (k n work : ℕ) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (he : (dZ :: d0 :: (ds ++ [dY, dV])).map (·.entry) = mergeEntries k n work) :
    dZ.entry = { name := RoundName.batSigma.name, work := work, drawE := 1, rows := n } ∧
      d0.entry = { name := RoundName.pscEpsilon.name, work := work, msg := 24, drawE := 1 } ∧
      (∀ d ∈ ds, d.entry =
        { name := RoundName.pscRound.name, work := work, msg := 48, drawE := 1 }) ∧
      dY.entry =
        { name := RoundName.pscY.name, work := work, msg := 24, drawE := 1, drawNZ := 1 } ∧
      dV.entry = { name := RoundName.pscValues.name, msg := 24 } ∧ ds.length = k := by
  unfold mergeEntries at he
  simp only [List.map_cons, List.map_append, List.map_nil, List.cons.injEq] at he
  obtain ⟨eZ, e0, e3⟩ := he
  have hlen : ds.length = k := by
    have := congrArg List.length e3
    simp only [List.length_append, List.length_map, List.length_replicate, List.length_cons,
      List.length_nil] at this
    omega
  obtain ⟨e4, e5⟩ := List.append_inj e3 (by simp [hlen])
  simp only [List.cons.injEq, and_true] at e5
  obtain ⟨eY, eV⟩ := e5
  exact ⟨eZ, e0, fun d hd => (List.eq_replicate_iff.1 e4).2 _ (List.mem_map_of_mem hd), eY, eV,
    hlen⟩

/-- **What is asked of the written rounds follows from the block's own entries.** -/
theorem mergeDs_of_entries (k n work : ℕ) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (he : (dZ :: d0 :: (ds ++ [dY, dV])).map (·.entry) = mergeEntries k n work)
    (hkind : ∀ d ∈ dZ :: d0 :: (ds ++ [dY, dV]), d.kind ≠ .sealed ∧ d.kind ≠ .seeds) :
    MergeDs dZ d0 ds dY dV ∧ ds.length = k := by
  obtain ⟨eZ, e0, eR, eY, eV, hlen⟩ := entries_of k n work he
  have kZ := hkind dZ (by simp)
  have k0 := hkind d0 (by simp)
  have kY := hkind dY (by simp)
  have kV := hkind dV (by simp)
  refine ⟨⟨⟨_, _, sd_of_entry dZ _ eZ kZ.1 kZ.2 rfl (Nat.zero_le _) (Nat.zero_le _)⟩,
    ⟨_, _, sd_of_entry d0 _ e0 k0.1 k0.2 rfl (Nat.zero_le _) (Nat.zero_le _)⟩,
    fun d hd => ⟨_, _, sd_of_entry d _ (eR d hd) (hkind d (by simp [hd])).1
      (hkind d (by simp [hd])).2 rfl (Nat.zero_le _) (Nat.zero_le _)⟩,
    ?_, ?_, ?_, ?_, ?_,
    ⟨_, _, sd_of_entry dV _ eV kV.1 kV.2 rfl (Nat.zero_le _) (Nat.zero_le _)⟩⟩, hlen⟩
  · exact (sd_of_entry dY _ eY kY.1 kY.2 rfl (Nat.le_refl _) (Nat.zero_le _)).plain
  · exact (sd_of_entry dY _ eY kY.1 kY.2 rfl (Nat.le_refl _) (Nat.zero_le _)).els
  · exact (sd_of_entry dY _ eY kY.1 kY.2 rfl (Nat.le_refl _) (Nat.zero_le _)).poss
  · rw [eY]
    simp [Fmt.dsOf, Fmt.dsElems, kY.2, IsNZ]
  · rw [eY]
    exact Nat.zero_le _

/-- A list of written rounds with the merge's entries has the merge's form. -/
theorem split_of_entries (k n work : ℕ) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries k n work) :
    ∃ dZ d0 ds dY dV, L = dZ :: d0 :: (ds ++ [dY, dV]) := by
  have hl : L.length = k + 4 := by
    have := congrArg List.length he
    simpa [mergeEntries] using this
  match L, hl with
  | dZ :: d0 :: M, hl =>
    have hM : M.length = k + 2 := by simpa using hl
    refine ⟨dZ, d0, M.take k, M[k]'(by omega), M[k + 1]'(by omega), ?_⟩
    congr 2
    apply List.ext_getElem
    · simp [hM]
    · intro i h1 h2
      by_cases hi : i < k
      · simp [hi, hM]
      · have : i = k ∨ i = k + 1 := by omega
        rcases this with rfl | rfl <;> simp [hM]

/-- Where each round's kind is that of its entry's name, as the format has it (`Fmt.kindOf`), no
round with one of the merge's entries is of the kind "sealed" or "seeds". -/
theorem kinds_of_names (k n work : ℕ) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries k n work)
    (hk : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∀ d ∈ L, d.kind ≠ .sealed ∧ d.kind ≠ .seeds := by
  intro d hd
  have key : ∀ (nm : String) (K : Fmt.Kind), Fmt.kindOf nm = some K → d.entry.name = nm →
      K ≠ .sealed → K ≠ .seeds → d.kind ≠ .sealed ∧ d.kind ≠ .seeds := by
    intro nm K h1 h2 h3 h4
    have h5 := hk d hd
    rw [h2, h1] at h5
    have h6 : K = d.kind := Option.some.inj h5
    subst h6
    exact ⟨h3, h4⟩
  have hm : d.entry ∈ mergeEntries k n work := he ▸ List.mem_map_of_mem hd
  unfold mergeEntries at hm
  simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | ⟨_, h⟩ | h | h
  · exact key RoundName.batSigma.name .elems (by decide) (by rw [h]) (by decide) (by decide)
  · exact key RoundName.pscEpsilon.name .join (by decide) (by rw [h]) (by decide) (by decide)
  · exact key RoundName.pscRound.name .elems (by decide) (by rw [h]) (by decide) (by decide)
  · exact key RoundName.pscY.name .elems (by decide) (by rw [h]) (by decide) (by decide)
  · exact key RoundName.pscValues.name .nothing (by decide) (by rw [h]) (by decide) (by decide)

/-- **All in one**: a list of written rounds that has the merge's entries, each round of the kind of
its entry's name, has the merge's form, meets `MergeDs`, and has one round for each column bit. -/
theorem mergeDs_of_list (k n work : ℕ) (L : List RDT)
    (he : L.map (·.entry) = mergeEntries k n work)
    (hk : ∀ d ∈ L, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ dZ d0 ds dY dV, L = dZ :: d0 :: (ds ++ [dY, dV]) ∧ MergeDs dZ d0 ds dY dV ∧
      ds.length = k := by
  obtain ⟨dZ, d0, ds, dY, dV, rfl⟩ := split_of_entries k n work L he
  exact ⟨dZ, d0, ds, dY, dV, rfl,
    mergeDs_of_entries k n work he (kinds_of_names k n work _ he hk)⟩

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.mergeDs_of_list
#print axioms VerifiableInference.Desc.First.MergeLaw.mergeDs_of_entries
#print axioms VerifiableInference.Desc.First.MergeLaw.split_of_entries
