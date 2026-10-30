-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SeedOfRows.lean: THE SENDINGS' INVARIANT
`K1.SeedIs` (Johnson/Desc/K1/Law/SeedIs.lean: the statement holds the message, marked as sampled,
                    with just kind K1's one sample row at an out-of-domain seed and answer) OUT OF
                    THE CODE SWITCH's FILES' TWO INVARIANTS ON THE MESSAGES' STORED SAMPLE ROWS
                    (`K2.RowsInv K2.QGoodS`, Johnson/Top/H0/K2Hands/SampleChain.lean;
                    `K2.AnsweredStored`, AnsweredStored.lean), THE MARK, AND `K1.Tie` OF THE SHAPE.
                    On a statement; kind-free; no walk. Theorems. A law file; no running text
                    imports it.
  `raw_zero_reads_zero`   THE NEGATIVE CONTROL: the raw triple (p, 0, 0), p the prime as a word, has
                    not all words 0 and reads as 0 in the field: so "the factor's raw words are not
                    all 0", which is all that the sending's decision and the test on the rounds ask,
                    does not give a unit: the canonical form is spent in earnest.
  `one_row`           an array of one entry.
  `seedIs_of_rows`    St.codes = cs · St.oracles[o]? = some x · x.shape = s · x.sampled = true ·
K1.Tie cs s · RowsInv QGoodS St · AnsweredStored St ⊢ ∃ ρ y, K1.SeedIs cs s St o ρ y. CALLED:
form_eq (Johnson/Desc/K1/Law/FormEq.lean: the kind's sample row is the program's row with the
answer as its target) · cube_bits · v_bitsZ · OnBytes.Slice.isZeroE_iff.

Limits. The two invariants and the mark are premises here. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.SampleChain
import Johnson.Top.H0.K2Hands.AnsweredStored
import Johnson.Desc.K1.Law.FormEq
import Johnson.Desc.K1.Law.SeedIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc.First (K2.RowsInv K2.QGoodS K2.AnsweredStored)

/-- **The negative control.** -/
theorem raw_zero_reads_zero :
    isZeroE (E.ofTriple (pW, 0, 0)) = false ∧ readE (E.ofTriple (pW, 0, 0)) = 0 := by
  refine ⟨by decide, ?_⟩
  have h : toF pW = 0 := by
    unfold toF
    exact (ZMod.natCast_eq_zero_iff _ _).2 (by decide)
  rw [readE_ofTriple]
  apply Code.Cubic.ext
  · exact h
  · exact toF_zero
  · exact toF_zero

theorem one_row {α : Type} {a : Array α} {r : α} (h1 : a.size = 1) (h0 : a[0]? = some r) :
    a = #[r] := by
  apply Array.ext
  · simpa using h1
  · intro i hi _
    obtain rfl : i = 0 := by omega
    have := (Array.getElem?_eq_some_iff.1 h0).2
    simpa using this

/-- **The sendings' invariant, out of the two on the stored rows, the mark and the tie.** -/
theorem seedIs_of_rows {cs : Codes} {s : OracleShape} {St : Statement} {o : ℕ} {x : OnBytes.Oracle}
    (hc : St.codes = cs) (hx : St.oracles[o]? = some x) (hs : x.shape = s)
    (hm : x.sampled = true) (hT : K1.Tie cs s) (hG : K2.RowsInv K2.QGoodS St)
    (hA : K2.AnsweredStored St) : ∃ ρ y, K1.SeedIs cs s St o ρ y := by
  have h1 : x.shape.answers = 1 := by rw [hs]; exact hT.one
  have hn : x.sampleRows.size ≠ 0 := hA o x hx (by rw [h1]; decide)
  obtain ⟨seeds, ⟨hsz, hrow⟩, hgood⟩ := hG o x hx hn
  rw [hc, hs] at hrow hgood
  rw [h1] at hsz
  obtain ⟨seed, row, t, hseed, hform, hr0⟩ := hrow 0 (by rw [hT.one]; decide)
  obtain ⟨hlong, hz, hok⟩ := hgood seed (List.mem_of_getElem? hseed)
  have hne : readE seed.beta ≠ 0 := fun h0 => by
    rw [(isZeroE_iff seed.beta hok).2 h0] at hz
    cases hz
  obtain ⟨row', hrow', erow⟩ := Option.map_eq_some_iff.1
    (K1.form_eq cs s o seed.z seed.beta 0 t hT.lengths hT.shape hT.fits)
  obtain rfl : row' = row := Option.some.inj (hrow'.symm.trans hform)
  refine ⟨(fun u => readL seed.z u.val, Units.mk0 (readE seed.beta) hne), readE t, hc, x, seed.z,
    seed.beta, t, hx, hs, hm, ?_, ⟨?_, fun _ => rfl, rfl⟩, rfl⟩
  · rw [← erow]
    exact one_row hsz hr0
  · rw [K1.cube_bits, K1.v_bitsZ] at hlong
    exact hlong

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.raw_zero_reads_zero
#print axioms VerifiableInference.Desc.LinkJoin.seedIs_of_rows
