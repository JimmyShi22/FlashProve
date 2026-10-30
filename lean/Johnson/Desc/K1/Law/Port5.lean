-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port5.lean: what the kind's sample row pins, in the library's own terms: at a
shape with one answer, a message of the library's code is a candidate of a word at the sample (in
the word's list, with the answer) just if it is in the list and its tables meet the kind's sample
row; and where the seed is no collision of the word's list, at most one message of the list meets
the row.

Main names: cand_iff, unique_port.

What is not claimed. One answer a message. That a seed is no collision is a premise: the number of
the seeds that are is the library's (its lists and its evading samples, under the test on numbers of
Johnson/Pack/Check.lean). Which word was sent, and that a message is in its list, is not said.
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Port4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood

/-- **A candidate of the library's decoder with a sample is a member of the list whose tables meet
the kind's sample row.** -/
theorem cand_iff (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (h : Tie S.codes x.shape) (e : Nat) (f : (portOmZ S.codes x.shape e).Str) (z : List E)
    (β y : E) (ρ : (Fin (bitsZ S.codes x.shape) → GE) × GEˣ)
    (r : ReadsOne S.codes x.shape z β ρ) (w : Means.Words GE)
    (msg : (portCode S.codes x.shape).J → GE) (hw : w o = tabOf S.codes x.shape msg) :
    (portOmZ S.codes x.shape e).Cand f (ρ, fun _ => readE y) msg ↔
      (portOmZ S.codes x.shape e).InList f msg ∧
        Means.Says rdE S (sampleRow (Msg.of S.codes x.shape) o z β 0 y) w := by
  rw [says_port S o x hx h z β y ρ r w msg hw]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, congrFun b ()⟩
  · rintro ⟨a, b⟩
    exact ⟨a, funext fun _ => b⟩

/-- **Where the seed is no collision of the word's list, at most one message of the list meets the
kind's sample row.** -/
theorem unique_port (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (h : Tie S.codes x.shape) (e : Nat) (f : (portOmZ S.codes x.shape e).Str) (z : List E)
    (β y : E) (ρ : (Fin (bitsZ S.codes x.shape) → GE) × GEˣ)
    (r : ReadsOne S.codes x.shape z β ρ) (hno : ¬ (portOmZ S.codes x.shape e).Clash f ρ)
    (w w' : Means.Words GE) (msg msg' : (portCode S.codes x.shape).J → GE)
    (hw : w o = tabOf S.codes x.shape msg) (hw' : w' o = tabOf S.codes x.shape msg')
    (hl : (portOmZ S.codes x.shape e).InList f msg)
    (hl' : (portOmZ S.codes x.shape e).InList f msg')
    (hs : Means.Says rdE S (sampleRow (Msg.of S.codes x.shape) o z β 0 y) w)
    (hs' : Means.Says rdE S (sampleRow (Msg.of S.codes x.shape) o z β 0 y) w') : msg = msg' := by
  by_contra hne
  have a := (says_port S o x hx h z β y ρ r w msg hw).1 hs
  have b := (says_port S o x hx h z β y ρ r w' msg' hw').1 hs'
  exact hno ⟨msg, msg', hl, hl', hne, funext fun _ => a.trans b.symm⟩

end VerifiableInference.Desc.K1
