-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/RoundsMake.lean: what the shared chain's three drawing blocks declare of their
rounds, by their make; and that a written round with such an entry sends and draws as the library's
maps of written rounds ask (SendsDraws).

  rounds_of_blocks   the first, the fourth and the seventh block declare one round each, whose entry
                     is the page's own: "LIN point" draws kCol elements, "LOC" draws the shape's
                     number of columns as positions below 2 ^ logN, "LIN zeta" draws kRow elements;
                     none draws anything else.
  sendsDraws_entry   a written round that is neither a sealing nor one of seeds, whose entry draws
                     no matrix entry and no more elements other than 0 than elements, and has logN
                     at most 64, sends and draws what its entry says.
  point_sendsDraws, loc_sendsDraws, zeta_sendsDraws   a written round that has the declared entry of
                     that block.

What is not claimed. PREMISES: the written round has the declared entry; its kind is neither a
sealing nor one of seeds; at "LOC": the code's logN is at most 64. That a file's written rounds are
those that its blocks declare is shown where the description is compiled.

-/
import Johnson.Desc.K14.Law.LocRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block)

/-- The entry of the page's round number i. -/
def entryAt (P : P14) (i : Nat) : Fmt.Entry := (entries P).getD i default

/-- **What the three drawing blocks declare.** -/
theorem rounds_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    b1.rounds.map (·.entry) = [entryAt P 0] ∧ b4.rounds.map (·.entry) = [entryAt P 1] ∧
      b7.rounds.map (·.entry) = [entryAt P 2] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold entryAt entries rounds whys
    split <;> rfl

/-- The three entries' numbers. -/
theorem entry_point (P : P14) : (entryAt P 0).drawE = P.S.kCol ∧ (entryAt P 0).poss = 0 ∧
    (entryAt P 0).trits = 0 ∧ (entryAt P 0).drawNZ = 0 ∧ (entryAt P 0).logN = 0 := by
  unfold entryAt entries rounds whys
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

@[inherit_doc entry_point]
theorem entry_loc (P : P14) : (entryAt P 1).drawE = 0 ∧ (entryAt P 1).poss = P.S.fold.columns ∧
    (entryAt P 1).trits = 0 ∧ (entryAt P 1).drawNZ = 0 ∧
    (entryAt P 1).logN = P.S.fold.index.code.logN := by
  unfold entryAt entries rounds whys
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

@[inherit_doc entry_point]
theorem entry_zeta (P : P14) : (entryAt P 2).drawE = P.S.kRow ∧ (entryAt P 2).poss = 0 ∧
    (entryAt P 2).trits = 0 ∧ (entryAt P 2).drawNZ = 0 ∧ (entryAt P 2).logN = 0 := by
  unfold entryAt entries rounds whys
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **A written round sends and draws what its entry says.** -/
theorem sendsDraws_entry (d : RDT) (ht : d.entry.trits = 0) (hk : d.kind ≠ .sealed)
    (hs : d.kind ≠ .seeds) (hz : d.entry.drawNZ ≤ d.entry.drawE) (hl : d.entry.logN ≤ 64) :
    SendsDraws (toRD d) (nS d.items) d.entry.drawE d.entry.poss d.entry.logN :=
  sendsDraws_of (r := ⟨d.entry, d.kind, d.items, []⟩) ⟨rfl, rfl, rfl⟩ ht hk hs hz hl

/-- A written round with the declared entry of "LIN point". -/
theorem point_sendsDraws (P : P14) (d : RDT) (he : d.entry = entryAt P 0)
    (hk : d.kind ≠ .sealed) (hs : d.kind ≠ .seeds) :
    SendsDraws (toRD d) (nS d.items) P.S.kCol 0 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := entry_point P
  have := sendsDraws_entry d (by rw [he, h3]) hk hs (by rw [he, h4]; exact Nat.zero_le _)
    (by rw [he, h5]; exact Nat.zero_le _)
  rwa [he, h1, h2, h5] at this

/-- A written round with the declared entry of "LOC". -/
theorem loc_sendsDraws (P : P14) (d : RDT) (he : d.entry = entryAt P 1)
    (hk : d.kind ≠ .sealed) (hs : d.kind ≠ .seeds) (hl : P.S.fold.index.code.logN ≤ 64) :
    SendsDraws (toRD d) (nS d.items) 0 P.S.fold.columns P.S.fold.index.code.logN := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := entry_loc P
  have := sendsDraws_entry d (by rw [he, h3]) hk hs (by rw [he, h4]; exact Nat.zero_le _)
    (by rw [he, h5]; exact hl)
  rwa [he, h1, h2, h5] at this

/-- A written round with the declared entry of "LIN zeta". -/
theorem zeta_sendsDraws (P : P14) (d : RDT) (he : d.entry = entryAt P 2)
    (hk : d.kind ≠ .sealed) (hs : d.kind ≠ .seeds) :
    SendsDraws (toRD d) (nS d.items) P.S.kRow 0 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := entry_zeta P
  have := sendsDraws_entry d (by rw [he, h3]) hk hs (by rw [he, h4]; exact Nat.zero_le _)
    (by rw [he, h5]; exact Nat.zero_le _)
  rwa [he, h1, h2, h5] at this

end Desc.K14.Law
