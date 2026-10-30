-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfThird.lean: the two hypotheses on lists of the oracle messages that the sub-protocol for
the claim that the encoded index is well-formed sends, met within the unique-decoding radius.
This is weights-formedness: the case of the oracle messages
of the preamble at 3 e < d (the list clause on the encoded index, inside `Cf.OK Lc`,
stays a hypothesis: see Limits).

Statements (in `Cb.Spec`) and proofs.
Of the named conditions of Cb/Ld/LdWfFull.lean (`G.OK`) two speak of lists of the oracle messages
that the preamble sends: `list`: every word of the oracle message a has at most L a messages within
its radius; `evades`: two different messages of one list have the same answers at few seeds.
If the radius of each oracle message is below half its distance as read (`LdCode.Dist`: counted on
the transformed codewords, in long positions) (in particular: within a third), both follow, at
L a = 1, from laws and distances alone.

A parameter list is what is asked of one sub-protocol, in two parts: a record of all items but
round-by-round knowledge soundness (`PreListR`, Hiop/RecSubs.lean), and that item, which is a
definition of its own (`PreKnowR`, Hiop/RecSubs.lean). `Spec.ldWfThird` concludes both, under the
hypotheses of its statement (`PreKnowR`: on the statements without a collision, `conf.free`).

The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
`C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native words
to long words, are linear over E; the encoder sends only the zero message with zero randomness to
zero; and, for every long position x, any two native words that agree at the native positions
`C.src x` have the same long symbol at x. Here `Laws` is a premise of `Spec.ldWfThird_list`,
`Spec.ldWfThird_ok` and `Spec.ldWfThird`.

Main names:
  `Spec.ldWfThird_list`: an oracle message with the laws of its code, distance d as read and 2 e < d
    has lists of at most one message (Cb/Ld/LdRelJohnson.lean: `ld_list_unique`, `ld_msgs_list`).
  `Spec.ldWfThird_evades`: lists of at most one message: "evades" holds, whatever the sample map:
    there are no two different messages in a list.
  `Spec.ldWfThird_err`: and the sending's error is 0: with lists of one message no seed has a
    collision.
  `Spec.ldWfThird_ok`: so: at L a = 1, with the laws of the codes, distances dS a and 3 e a < dS a
    (used: 2 e a < dS a), the conditions `G.OK` hold as soon as they hold given the two clauses. The
    plain form of this, and the one to cite: Cb/Ld/LdWfEndThird.lean (`Z.Third p dS`, a record of
    conditions; `ldWfEnd3_ok`).
  `Spec.ldWfThird`: the two items of the object (`PreListR`, `PreKnowR`) in that case, if p is the
    characteristic of E (`CharP E p`).
No hypothesis on lists or on agreement is left among the conditions on the preamble's own oracle
messages. No verifier of the preamble tests a word: agreement is not asked here at all; the test
that follows asks it.

Limits: this file says nothing on the list clause inside `Cf.OK Lc`: it is the configuration's. It
is on the encoded index at its radius of decoding. Cb/Obj/LdObjectConfMore.lean: `ldCm_list_unique`
gives `Cf.ListOK 1` from 2 eM below the distance, and `ldCm_list_F` the clause.
The sample is still drawn and answered: with lists of one message it decides nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfFull
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

namespace Spec
section
variable (E : Type) [Field E] [Fintype E]

def ldWfThird_list : Prop :=
  ∀ (o : OMsg E) (d : ℕ), o.C.Laws → o.C.Dist d → 2 * o.e < d → o.ListLE 1

def ldWfThird_evades : Prop := ∀ o : OMsg E, o.ListLE 1 → o.Evades

def ldWfThird_err : Prop := ∀ (S : Sig E) (Sd : S.Seeds), ldSendFamErr S Sd (fun _ => 1) = 0

end
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The conditions, within a third. (not all hypotheses are named here: see the statement below) -/
def ldWfThird_ok : Prop :=
  ∀ (G : LdWfF F E) (Y : G.B.MaskLay) (p Lc : ℕ) (dS : G.W.P.S.O → ℕ), (∀ a, G.L a = 1) →
    (∀ a, (G.W.P.S.om a).C.Laws) → (∀ a, (G.W.P.S.om a).C.Dist (dS a)) →
    (∀ a, 3 * (G.W.P.S.om a).e < dS a) →
    ((∀ a, (G.W.P.S.om a).ListLE (G.L a)) → (∀ a, (G.W.P.S.om a).Evades) → G.OK Y p Lc) →
    G.OK Y p Lc

/-- The two items of the object, within a third. (not all hypotheses are named here: see the
statement below) -/
def ldWfThird : Prop :=
  ∀ (p : ℕ) [CharP E p] (G : LdWfF F E) (Y : G.B.MaskLay) (Lc : ℕ) (dS : G.W.P.S.O → ℕ),
    (∀ a, G.L a = 1) → (∀ a, (G.W.P.S.om a).C.Laws) → (∀ a, (G.W.P.S.om a).C.Dist (dS a)) →
    (∀ a, 3 * (G.W.P.S.om a).e < dS a) →
    ((∀ a, (G.W.P.S.om a).ListLE (G.L a)) → (∀ a, (G.W.P.S.om a).Evades) → G.OK Y p Lc) →
    PreListR G.W.O.left G.B.wf G.B.hWf id id G.W.Cf.conf.Rwf G.B.nums ∧
    PreKnowR G.W.O.left G.B.wf G.W.Cf.conf.free G.W.Cf.conf.RwfR (fun _ _ _ => ()) G.B.nums.err

end
end Spec

section
variable {E : Type} [Field E] [Fintype E]

theorem ldWfThird_list : Spec.ldWfThird_list E := fun o d hL hd h2 f =>
  ld_msgs_list E o.P o.C o.e 1 (ld_list_unique E o.P o.C d o.e hL hd h2) (o.upW f)

omit [Fintype E] in
theorem ldWfThird_evades : Spec.ldWfThird_evades E := by
  classical
  intro o h f m m' hm hm' hne
  have h2 := h f {m, m'} fun u hu => by
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact hm
    · rw [Finset.mem_singleton.1 hu]
      exact hm'
  rw [Finset.card_pair hne] at h2
  exact absurd h2 (by norm_num)

omit [Field E] [Fintype E] in
theorem ldWfThird_err : Spec.ldWfThird_err E := fun S Sd => Finset.sum_eq_zero fun a _ => by
  show Sd.mult a * (Nat.choose 1 2 * (S.om a).Z.err) = 0
  rw [Nat.choose_eq_zero_of_lt (by norm_num), Nat.zero_mul, Nat.mul_zero]

end

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldWfThird_ok : Spec.ldWfThird_ok F E := by
  intro G Y p Lc dS hL1 hLaws hD h3 h
  have hl : ∀ a, (G.W.P.S.om a).ListLE 1 := fun a =>
    ldWfThird_list (G.W.P.S.om a) (dS a) (hLaws a) (hD a) (by have := h3 a; omega)
  exact h (fun a => by rw [hL1 a]; exact hl a) fun a => ldWfThird_evades (G.W.P.S.om a) (hl a)

theorem ldWfThird : Spec.ldWfThird F E := fun p _ G Y Lc dS hL1 hLaws hD h3 h =>
  ldWfFull p G Y Lc (ldWfThird_ok G Y p Lc dS hL1 hLaws hD h3 h)

end
end Cb
