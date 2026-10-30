-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerLaws.lean

The laws of the relations' side `ledgerSide s pol` (Policy/Rel/LedgerSide.lean), in the forms of
premises of the protocol's files.

The statements are in `Policy.Spec`. Each follows from the statements of
Policy/Rel/LedgerRelLaws.lean on the relation pair, read at p = 2^64 - 2^32 + 1 in the fields of the
side. All are for a lawful table s of scales and a policy with `PolCond` (C, θ < 2^40, cap < 2^16).

* `ledgerSide_ok`: `RelSide.OK` (Cm/GlRefWfRel.lean).
* `ledger_language`, `ledger_witness`: the two directions between the relaxed relation and
  `IsTrueUnder s pol`.
* `ledger_duty`: the last premise of `ldPartCf_model` and `ldPartCf_langs` (Cb/Part/LdPartCf.lean).
* `ledger_narrow`, `ledger_keeps`: where there is a relaxed witness there is a strict one, and the
  honest trace is a relaxed one.

Limits: the statements are on a relation, not on a protocol. No theorem of this file applies them to
those premises. What the heads of Policy/Rel/True.lean and Policy/Rel/LedgerRelLaws.lean list as not
said is not said here either.
-/
import Policy.Rel.LedgerSide
import Policy.Rel.LedgerRelLaws

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.Spec

open Inst.Model Inst.Model.All

/-! Each statement is for a lawful table s of scales and a policy pol with `PolCond`. -/

/-- strict ⊆ relaxed; if there is a strict witness, the honest trace is one -/
def ledgerSide_ok : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol → (ledgerSide s pol).OK

/-- a relaxed witness shows that the request is true under the policy -/
def ledger_language : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol →
    ∀ i x w, (ledgerSide s pol).Rno i x w → IsTrueUnder s pol i x

/-- at a request that is true under the policy the honest trace is a relaxed witness -/
def ledger_witness : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol →
    ∀ i x, IsTrueUnder s pol i x → (ledgerSide s pol).Rno i x ((ledgerSide s pol).trace i x)

/-- a relaxed witness makes the honest trace a strict witness -/
def ledger_duty : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol →
    ∀ i x c, (ledgerSide s pol).Rno i x c →
      (ledgerSide s pol).Ryes i x ((ledgerSide s pol).trace i x)

/-- where there is a relaxed witness there is a strict one -/
def ledger_narrow : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol →
    ∀ i x c, (ledgerSide s pol).Rno i x c → ∃ c', (ledgerSide s pol).Ryes i x c'

/-- a relaxed witness makes the honest trace a relaxed witness -/
def ledger_keeps : Prop :=
  ∀ s : Cm.Scales, s.Lawful → ∀ pol : AcceptancePolicy, PolCond pol →
    ∀ i x c, (ledgerSide s pol).Rno i x c →
      (ledgerSide s pol).Rno i x ((ledgerSide s pol).trace i x)

end Policy.Spec

namespace Policy

open Inst.Model Inst.Model.All

theorem ledger_language : Spec.ledger_language := fun _ hs _ hpol i x w h =>
  ledger_forces Cb.Gl.p Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x w h

theorem ledger_duty : Spec.ledger_duty := fun s hs pol hpol i x c h =>
  (ledger_trace_iff Cb.Gl.p Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x).2
    (ledger_language s hs pol hpol i x c h)

theorem ledger_witness : Spec.ledger_witness := fun _ hs _ hpol i x h =>
  ledger_sub Cb.Gl.p _ i x _
    ((ledger_trace_iff Cb.Gl.p Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x).2 h)

theorem ledgerSide_ok : Spec.ledgerSide_ok := fun _ hs _ hpol =>
  { sub := fun i x w h => ledger_sub Cb.Gl.p _ i x w h
    admits := fun i x w h =>
      ledger_admits Cb.Gl.p Code.pGold_prime ledger_gl_big _ (tableOK_ppOf hs hpol) i x w h }

theorem ledger_narrow : Spec.ledger_narrow := fun s hs pol hpol i x c h =>
  ⟨_, ledger_duty s hs pol hpol i x c h⟩

theorem ledger_keeps : Spec.ledger_keeps := fun s hs pol hpol i x c h =>
  ledger_witness s hs pol hpol i x (ledger_language s hs pol hpol i x c h)

end Policy
