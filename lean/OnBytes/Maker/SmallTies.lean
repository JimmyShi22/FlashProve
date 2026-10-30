-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/SmallTies.lean: three small hypotheses of OnBytes/Maker/AcceptOfYes.lean, from what
the strict reader gives (OnBytes/Maker/ReadFacts.lean, ReadSpecs.lean) and from the laws on keys
(OnBytes/Maker/LinkRecordLaws.lean).

Main theorems.
  `vals_nil`: a message that is read whole as no item holds no value.
  `sealedLast_viewX`: the strict reader's view of a chain ends in a sealing round (`SealedLast`,
    OnBytes/Maker/Decide3Laws.lean), if the chain's last round as read holds no value and has drawn
    no element, no position and no matrix entry.
  `drawRound_bare`, `sealedLast_read` (with the test `bareSeal`, OnBytes/Maker/ViewTests.lean): the
    same of a chain that the program's reader has read, from a test on the description's last round.
  `t₁_roots`: a first chain that was read under a description made from the rounds R₁ has as many
    roots as the plain data made of R₁ count.
  `keyRec_recOfKey`: a key with the item 0 whose sizes fit the shape, none of whose factors is the
    program's 0, and whose words are all below the prime is the key written of the record that is
    read off it.

What is not claimed. That a key which the program makes passes these tests. Nothing on soundness.


-/
import OnBytes.Maker.Decide3Laws
import OnBytes.Maker.ReadSpecs
import OnBytes.Maker.LinkRecordLaws
import OnBytes.Maker.TypingViews
import OnBytes.Tie.StoredView

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Slice

/-- A message that is read whole as no item holds no value. -/
theorem vals_nil (f : Fmt.Fld) (msg : ByteArray) (l : List Fmt.ItemValue)
    (h : Fmt.whole (Fmt.readItems f []) msg = some l) : l = [] := by
  unfold Fmt.whole at h
  simp only [Fmt.readItems] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- **The strict reader's view ends in a sealing round.** -/
theorem sealedLast_viewX (S : Fmt.SpecX) (o : Fmt.ChainOut) (ros : List Fmt.RoundOut)
    (last : Fmt.RoundOut) (ho : o.rounds.toList = ros ++ [last]) (hv : last.vals = [])
    (he : last.drawn.elems = []) (hp : last.drawn.poss = []) (ht : last.drawn.trits = []) :
    SealedLast (Fmt.viewX S o) := by
  refine ⟨ros.map fun r => ⟨Fmt.noRoots r.vals, r.drawn⟩, last.drawn.digest, ?_⟩
  show (o.rounds.toList.map fun r => (⟨Fmt.noRoots r.vals, r.drawn⟩ : Fmt.RoundView)) = _
  rw [ho, List.map_append, List.map_singleton, hv]
  have e : last.drawn = ⟨[], [], [], last.drawn.digest⟩ := by
    rw [← he, ← hp, ← ht]
  rw [e]
  rfl

/-- A round of the kind "sealed" whose entry asks for no position, element or matrix entry draws
nothing but a digest. -/
theorem drawRound_bare (f : Fmt.Fld) (e : Fmt.Entry) (row : Fmt.Row) (h1 : e.poss = 0)
    (h2 : e.drawE = 0) (h3 : e.drawNZ = 0) (h4 : e.trits = 0) :
    ∃ d, Fmt.drawRound f e .sealed row = ⟨[], [], [], d⟩ := by
  unfold Fmt.drawRound Fmt.drawRoundD Fmt.drawPoss Fmt.drawElems Fmt.drawPlainNZ Fmt.drawTrits
  rw [h1, h2, h3, h4]
  exact ⟨_, rfl⟩

/-- **A chain that the program's reader has read under a description whose last round passes
`bareSeal`**: its view ends in a sealing round. -/
theorem sealedLast_read (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (x : Fmt.Round × List Fmt.Stored) (hx : (S.base.rounds.zip S.stored).getLast? = some x)
    (hb : bareSeal x.1 = true) : SealedLast (Fmt.viewX S o) := by
  obtain ⟨-, H⟩ := readChain_read S seen b i o j e
  obtain ⟨last, -, e2, hm⟩ := split_last _ _ H.length_eq x hx
  have F : RoundRead S.base.plan x last := OnBytes.Tie.forall₂_zip H (x, last) hm
  unfold bareSeal at hb
  simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hb
  obtain ⟨⟨⟨⟨⟨k, hi⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hb
  have hv : last.vals = [] := vals_nil S.base.plan.field last.msg last.vals (hi ▸ F.vals)
  obtain ⟨row, hd⟩ := F.drawn
  rw [k] at hd
  obtain ⟨d, hd'⟩ := drawRound_bare S.base.plan.field x.1.entry row h1 h2 h3 h4
  rw [hd'] at hd
  exact sealedLast_viewX S o _ last e2 hv (by rw [hd]) (by rw [hd]) (by rw [hd])

/-- **The first chain's roots are as many as the data count.** -/
theorem t₁_roots {g : Params.Given} {label : ℕ} {st : ByteArray} {rand : Fmt.Rand}
    {R₁ : Params.Rounds} {ft : ℕ} {S : Fmt.SpecX}
    (hS : Params.describeWith g label st rand R₁ ft = some S) (seen : Fmt.Seen) (b : ByteArray)
    (i : ℕ) (c : ChainRead) (e : readChain S seen b i = some (c.out, c.next))
    (R₂ R₃ : Params.Rounds) : (Three.Whole.of R₁ R₂ R₃).t₁ = c.roots.length :=
  (readChain_roots hS seen b i c e).symm

/-- **A key with the item 0 is written of the record that is read off it**, under the tests of
`key_back`. -/
theorem keyRec_recOfKey (sh : Params.IndexShape) (key : TableKey) (h0 : key.item = 0)
    (hf : key.fits sh = true) (hz : (key.seeds.all fun x => !isZeroE x.beta) = true)
    (hr : ∀ a ∈ key.record, okE a = true)
    (hs : ∀ x ∈ key.seeds, okE x.beta = true ∧ ∀ a ∈ x.z, okE a = true) :
    keyRec (recOfKey sh key) = key := by
  have e := key_back sh key hf hz hr hs
  rw [h0] at e
  exact e.symm

end OnBytes.Maker
