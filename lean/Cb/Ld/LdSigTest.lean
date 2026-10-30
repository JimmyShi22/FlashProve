-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSigTest.lean: proof of `Spec.sig_two` (Cb/Ld/LdSig.lean): the relaxation by decoding with a
sample, at a small code, at a radius not below half the distance.

A guard against empty statements.

`Spec.sig_two` states: there are a field, an oracle message o (`OMsg`: code `o.C`, sample map `o.Z`,
radius `o.e`, order `o.rank`), a number d, a word f, a seed ρ and two messages m ≠ m' with
`o.C.Laws`, `o.C.Dist d`, o.e < d and `o.Z.OK`, such that m and m' are in the list of f
(`OMsg.InList`), ρ has no collision (`OMsg.Clash`), and the decoder returns m at the answers of m,
and m' at those of m'.
The terms are those of Cb/Ld/LdSig.lean. The decoder (`OMsg.dec`) returns the message of the nearest
codeword, the first in the order, among the pairs whose message has the answers; it returns none if
that one is beyond the radius.

The oracle message. The code of Cb/Ld/LdRelToy.lean (Reed-Solomon over the field with 101 elements,
five points, one message symbol, one symbol of randomness, distance 4), one row, plain format,
radius 2. The sample map "all": one seed, and the answers are all entries of the message; so no two
different messages ever have the same answers (its number is 0).

The word of Cb/Ld/LdRelToy.lean has two messages in its list.

Notation:
  `K`: the field (`ZMod 101`, Cb/Ld/LdRelToy.lean);
  `toyLd R`: the toy: rows R under `C5`, read as they stand; here R = `Unit`: one row
    (Cb/Ld/LdRelToy.lean);
  `allZ`: the sample map whose answers are all entries: the head's "all";
  `toyO`: `OMsg.plain (toyLd Unit) (allZ ..) 2 fun _ => 0`: by the binders of `OMsg.plain`
    (Cb/Ld/LdSig.lean): the code, the sample map, the radius e = 2, the order `rank` = `fun _ => 0`.

Limits: no parameter of a protocol. The sample map "all" hides nothing and is as long as the
message: it is there for the test alone.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigProofs
import Cb.Ld.LdRelToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
namespace LdToy
open Iop Prob Hiop Cb.Ood

open Classical in
/-- the sample map whose answers are all entries -/
@[reducible] def allZ (E J : Type) [Field E] [Fintype J] : Sample E J :=
  { D := Unit, S := J, mat := fun _ s j => if s = j then 1 else 0, err := 0 }

theorem allZ_val (E J : Type) [Field E] [Fintype J] (u : J → E) : (allZ E J).val () u = u := by
  classical
  funext s
  simp [Sample.val]

theorem allZ_ok (E J : Type) [Field E] [Fintype J] : (allZ E J).OK := by
  intro v hv
  refine le_of_eq (cnt_false fun ρ h => hv ?_)
  cases ρ
  rw [allZ_val] at h
  exact h

/-- the oracle message of the test -/
@[reducible] def toyO : OMsg K :=
  OMsg.plain (toyLd Unit) (allZ K (toyLd Unit).J) 2 fun _ => 0

end LdToy

open LdToy Cb.Ood in
theorem sig_two : Spec.sig_two := by
  obtain ⟨f, w, w', hne, hw, hw'⟩ := ld_toy_two
  have hc : ¬ toyO.Clash f () := by
    rintro ⟨u, u', _, _, hn, h⟩
    rw [allZ_val, allZ_val] at h
    exact hn h
  refine ⟨K, inferInstance, toyO, 4, f, (), w.1, w'.1, (ld_toy Unit).1, (ld_toy Unit).2.1,
    by norm_num, allZ_ok K _, hne, ⟨w.2, hw⟩, ⟨w'.2, hw'⟩, hc, ?_, ?_⟩
  · exact (sig_dec_good K toyO f () hc _ w.1).2 ⟨⟨w.2, hw⟩, rfl⟩
  · exact (sig_dec_good K toyO f () hc _ w'.1).2 ⟨⟨w'.2, hw'⟩, rfl⟩

end Cb
