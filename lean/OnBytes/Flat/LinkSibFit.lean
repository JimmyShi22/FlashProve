-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkSibFit.lean: the instance that a converter's value gives
(`xOfAskedC`, OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) is the instance made of two records
(`recX`, OnBytes/Flat/LinkSib.lean): of the records that are read off that value.

Main names:
  `trAns_anT`: a list of the program's field elements, as many as a table has answers, each with
    words below the prime: read as typed answers and written back as triples of words, it is the
    list of their triples.
  `recsOf`: the two records read off a converter's value: each table's seeds, and its answers as
    they are read in the field.
  `recX_recsOf`: the instance made of them is `xOfAskedC` of the value.

Hypotheses of `recX_recsOf`: each table has 2 ^ v * s answers, each with words below the prime.

Limits: values alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.LinkSib
import OnBytes.TypedOracleCompiler.Slice.EntryConv
import OnBytes.Slice.KeyOfRecBack

set_option autoImplicit false

noncomputable section

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice OnBytes.Tie

section
variable (v lg s : ℕ)

/-- Read as typed answers and written back, a list of lawful answers of the right length is the list
of their triples. -/
theorem trAns_anT (l : List E) (hlen : l.length = 2 ^ v * s) (hok : ∀ a ∈ l, okE a = true) :
    trAns (anT v s (l.map E.triple)) = l.map E.triple := by
  refine List.ext_getElem (by rw [trAns, List.length_ofFn, List.length_map, hlen]) ?_
  intro n h1 h2
  have hn : n < 2 ^ v * s := by rwa [trAns, List.length_ofFn] at h1
  have hs : 0 < s := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hn; cases hn
  have hq : n / s < 2 ^ v := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hn)
  have hl : n < l.length := by rw [hlen]; exact hn
  unfold trAns anT
  rw [List.getElem_ofFn]
  show ofE (toE ((l.map E.triple).getD (Sz.rowNo (vtx v (n / s)) * s + n % s) (0, 0, 0))) = _
  rw [ProxRun.rowNo_vtx v _ hq, Nat.div_add_mod' n s,
    List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map]
  exact congrArg E.triple (writeE_readE l[n] (hok _ (List.getElem_mem hl)))

/-- The two records read off a converter's value. -/
def recsOf (a : AskedE) : RecP NZ v lg s × RecP NZ v lg s :=
  ((seedOfC lg s a.l0, anT v s (a.first.answers.map E.triple)),
    (seedOfC lg s a.l1, anT v s (a.further.answers.map E.triple)))

/-- The instance made of them is the converter's. -/
theorem recX_recsOf (a : AskedE) (h0 : a.first.answers.length = 2 ^ v * s)
    (h1 : a.further.answers.length = 2 ^ v * s) (k0 : ∀ e ∈ a.first.answers, okE e = true)
    (k1 : ∀ e ∈ a.further.answers, okE e = true) :
    recX (recsOf v lg s a) = xOfAskedC lg s a := by
  unfold recX recsOf xOfAskedC
  simp only [trAns_anT v s _ h0 k0, trAns_anT v s _ h1 k1]

end

end OnBytes.Flat
