-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseForms.lean: linear algebra for linear claims: a claim on some coordinates of some
encoded messages (a row of a protocol), written as a linear form on all coordinates of the messages
of a group of oracles.

In standard terms: a linear form with a state, `sl : Slf E St J`, is a coefficient vector indexed by
J that depends on a state st; the claim (t, st) holds of a vector m if ∑ j, sl st j · m j = t
(`Slf.Holds`).

Definitions, statements and proofs. No protocol.

Why: a protocol states its last rows on vectors that are somewhere inside the messages of its oracle
messages ("u k is the entry l k of the message of G_u"). A test on a group (Cb/Ld/LdBatSig.lean)
needs linear forms with a state (`Slf`, Cb/Ld/LdRel.lean) on all coordinates of the message of the
group's complex.

Main names:
  `Slf.push φ a`: coefficients a st i, named by i : I, on the entries φ i of a vector with
    coordinates J: the form on J whose coefficient at j is the sum of the a st i with φ i = j. φ
    need not be injective. `Spec.ldForm_push`: its value at m is ∑ i, a st i · m (φ i).
  `Slf.sub s₁ s₂`; `Spec.ldForm_sub`: the value of a difference is the difference of the values.
  `G.onMem o h sl`: a form on the message of the member o of the group G, as a form on the message
    of the complex: zeros on the other members (`Slf.atMem`, Cb/Ld/LdBatSig.lean).
    `Spec.ldForm_onMem`: its value at the group's message of a tuple of messages is the form's value
    at the member's message.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatSigProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood

/-- Coefficients on some entries of a vector, as a form on all its coordinates. -/
def Slf.push {E St I J : Type} [AddCommMonoid E] [Fintype I] [DecidableEq J]
    (φ : I → J) (a : St → I → E) : Slf E St J :=
  fun st j => ∑ i, if φ i = j then a st i else 0

/-- the difference of two forms with one state -/
def Slf.sub {E St J : Type} [Sub E] (s₁ s₂ : Slf E St J) : Slf E St J := fun st j =>
  s₁ st j - s₂ st j

/-- A form on the message of one member, as a form on the message of the group's complex: zeros on
the other members. -/
def Grp.onMem {E : Type} [Zero E] {S : Sig E} (G : Grp S) {St : Type} (o : S.O)
    (h : G.mem o) (sl : Slf E St (S.om o).C.J) : Slf E St G.C.J :=
  Slf.atMem (Jf := fun a : G.A => (S.om a.1).C.J) ⟨o, h⟩ sl

namespace Spec

def ldForm_push : Prop :=
  ∀ (E St I J : Type) [Field E] [Fintype I] [Fintype J] [DecidableEq J] (φ : I → J)
      (a : St → I → E) (st : St) (m : J → E),
    (Slf.push φ a).val st m = ∑ i, a st i * m (φ i)

def ldForm_sub : Prop :=
  ∀ (E St J : Type) [Field E] [Fintype J] (s₁ s₂ : Slf E St J) (st : St) (m : J → E),
    (s₁.sub s₂).val st m = s₁.val st m - s₂.val st m

def ldForm_onMem : Prop :=
  ∀ (E St : Type) [Field E] (S : Sig E) (G : Grp S) (o : S.O) (h : G.mem o)
      (sl : Slf E St (S.om o).C.J) (st : St) (m : S.Msg),
    (G.onMem o h sl).val st (G.msg m) = sl.val st (m o)

end Spec

theorem ldForm_push : Spec.ldForm_push := by
  intro E St I J _ _ _ _ φ a st m
  unfold Slf.val Slf.push
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (φ i)]
  · rw [if_pos rfl]
  · intro j _ hj
    rw [if_neg (Ne.symm hj), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem ldForm_sub : Spec.ldForm_sub := by
  intro E St J _ _ s₁ s₂ st m
  unfold Slf.val Slf.sub
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => sub_mul _ _ _

theorem ldForm_onMem : Spec.ldForm_onMem := by
  intro E St _ S G o h sl st m
  exact ldBat_atMem E St G.A (fun a : G.A => (S.om a.1).C.J) ⟨o, h⟩ sl st (G.msg m)

end Cb
