-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsFits.lean

From "every key is in its table" to the conditions "Fits" of Johnson/HonestTrace/Counts.lean, at
the chosen rows "hitsOf".

Main theorem:
* "fits_hitsOf": let FoNums.ok h hold; for every call c below h.NC let every place of the key
  vector Kv c hold the value of a row below 2^(k_c) of the table T c (Cb.Lkp.InTable), and let every
  padding place hold the value of the call's padding row; let the public numbers count the padding
  places (PubFits h pad). Then Fits h T Kv (hitsOf h T Kv pad).

Limits. T, Kv and pad are arbitrary arguments: no table, key vector or padding place of a sub-proof
of the protocol occurs. The four premises are assumed, not proved, and no theorem of this file says
that they can hold together. "Every key is in its table" is one of two things that are assumed of
the key vectors: the other is that a padding place holds the value of the call's padding row. E is
a field with decidable equality because Cb.Lkp.InTable is typed over a field and firstRow compares
values; no operation of the field is used.

Not claimed: that the premises hold of any sub-proof; that the C++ prover chooses these rows;
any equation of the lookup argument.

-/
import Johnson.HonestTrace.Counts
import Cb.Gen.LkpAlg

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model

/-- Under FoNums.ok h: if for every call c below h.NC every place of Kv c holds the value of a row
below 2^(k_c) of T c, every padding place of call c holds the value of the call's padding row, and
PubFits h pad holds, then Fits h T Kv (hitsOf h T Kv pad) holds. -/
theorem fits_hitsOf {E : Type} [Field E] [DecidableEq E] (h : Forest.Shape) (T Kv : ℕ → ℕ → E)
    (pad : ℕ → ℕ → Bool) (hok : FoNums.ok h = true)
    (hin : ∀ c < h.NC, Cb.Lkp.InTable (FoNums.nOf h c) (FoNums.kOf h c) (Kv c) (T c))
    (hpad : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, pad c i = true →
      Kv c i = T c (FoNums.t0Of h c))
    (hpub : PubFits h pad) :
    Fits h T Kv (hitsOf h T Kv pad) := by
  refine ⟨?_, ?_, ?_, hpub⟩
  · intro c hc i hi
    show (if pad c i = true then FoNums.t0Of h c
      else firstRow (T c) (FoNums.kOf h c) (Kv c i)) < _
    split_ifs with hp
    · exact t0Of_lt hok hc
    · exact (firstRow_spec _ _ _ (hin c hc i hi)).1
  · intro c hc i hi
    show Kv c i = T c (if pad c i = true then FoNums.t0Of h c
      else firstRow (T c) (FoNums.kOf h c) (Kv c i))
    split_ifs with hp
    · exact hpad c hc i hi hp
    · exact (firstRow_spec _ _ _ (hin c hc i hi)).2.1
  · intro c _ i _ hp
    exact if_pos hp

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.fits_hitsOf
