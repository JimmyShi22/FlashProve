-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfMasksBatt.lean: book-keeping on what a block reads of the prover's witness.
A block that reads entries of (matrix of the index, named entries of the messages): its reading as a
function of the wide reading; the batching of tensor rows is such a block.

Definitions, statements (in `Cb.Spec`) and proofs.
Cb/Ld/LdWfMasks.lean derives the two hypotheses on masks of Cb/Ld/LdWf.lean from conditions `Y.OK`
and `B.D.Nn.Hides (P.S.budT B.t)` (`Spec.ldWfM_hyp`). Two clauses of `Y.OK` (`rd`, `com`) say, for
each masked block: the block's own reading of the witness is a function g of the wide reading (the
entries in Rd of all messages; the further witness), and g commutes with the overwriting of the
block's masks.
At `B.DmB` (`Spec.ldWfMB_kc`) and at `K.dm` (Cb/Ld/LdWfMasksLkp.lean: `Spec.ldWfML_kc`,
`Spec.ldWfML_put`, under its two premises), the masked blocks read the same kind of thing: the
entries, in a set RdJ of their own, of the tuple `P.msg (U, m)`: the matrix of the prover's index
message U beside the named entries `P.ent m` of the messages; their masks are at named entries.

Main names:
  `P.EntAt nAt`: a condition on places: the named entries (`P.ent m n`, n : `P.N`) are entries of
    the messages, at different places nAt n.
  `wfCutJ RdJ w`: the reading of such a block: the entries in RdJ of `P.msg` (the prover's index
    message, the messages); all others 0.
  `wfG RdJ nAt`: g: the same, computed from (entries, further witness).
  `Spec.ldWfMB_rdG`: under `P.EntAt nAt`: `wfCutJ RdJ w = wfG RdJ nAt (wfWide Rd w)`, if every named
    entry in RdJ lies in Rd.
  `Spec.ldWfMB_comG`: under `P.EntAt nAt`: `wfG` commutes with the overwriting of named entries at
    different places atN i that lie in RdJ: on the wide side at nAt (atN i), on the block's side at
    the named entry atN i.
  The batching (its letters, the parameters of its item "masked messages", are a fixed term,
  `B.DmB`, Cb/Ld/LdWf.lean). `Spec.ldWfMB_kc`: `B.DmB.kc w = wfCutJ B.Rd w`, by definition.
  `Spec.ldWfMB_rd`, `Spec.ldWfMB_com`: under the hypotheses of their statements, the two conditions
  for it; places: nAt (`P.wAt` i); a mask value is the vector of its entries. Used: the batching's
  own condition `OwnOK`.

Limits: this file says nothing on the lookups' letters (`B.Dm`, Cb/Ld/LdWf.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfMasks
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample}

/-- The named entries are entries of the messages, at different places. -/
structure LdWfP.EntAt (P : LdWfP E C) (nAt : P.N → P.S.Ent) : Prop where
  ent : ∀ m n, P.ent m n = P.S.ents m (nAt n)
  inj : Function.Injective nAt

open Classical in
/-- the reading of a block: the entries in RdJ -/
def wfCutJ {P : LdWfP E C} (RdJ : P.bt.J → Prop) (w : P.W) : P.bt.J → E := fun j =>
  if RdJ j then P.msg (w.2.1.1.1, P.S.msgs w.1) j else 0

open Classical in
/-- the same, from the wide reading -/
def wfG {P : LdWfP E C} (RdJ : P.bt.J → Prop)
    (nAt : P.N → P.S.Ent) (k : (P.S.Ent → E) × P.Wp) : P.bt.J → E :=
  fun j => if RdJ j then Sum.elim (P.mat k.2.1.1.1) (fun n => k.1 (nAt n)) j else 0

namespace Spec
variable (E)

def ldWfMB_rdG : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (RdJ : P.bt.J → Prop) (nAt : P.N → P.S.Ent) (Rd : P.S.Ent → Prop),
    P.EntAt nAt → (∀ n, RdJ (Sum.inr n) → Rd (nAt n)) →
    ∀ w, wfCutJ RdJ w = wfG RdJ nAt (wfWide Rd w)

def ldWfMB_comG : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (RdJ : P.bt.J → Prop) (nAt : P.N → P.S.Ent)
      (I : Type) (atN : I → P.N),
    P.EntAt nAt → Function.Injective atN → (∀ i, RdJ (Sum.inr (atN i))) →
    ∀ (v : I → E) (k : (P.S.Ent → E) × P.Wp),
      wfG RdJ nAt (Function.extend (fun i => nAt (atN i)) v k.1, k.2) =
        Function.extend (fun i => (Sum.inr (atN i) : P.bt.J)) v (wfG RdJ nAt k)

def ldWfMB_kc : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (w : P.W), B.DmB.kc w = wfCutJ B.Rd w

def ldWfMB_rd : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (nAt : P.N → P.S.Ent) (Rd : P.S.Ent → Prop),
    P.EntAt nAt → (∀ n, B.Rd (Sum.inr n) → Rd (nAt n)) →
    ∀ w, B.DmB.kc w = wfG B.Rd nAt (wfWide Rd w)

def ldWfMB_com : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk) (nAt : P.N → P.S.Ent), P.EntAt nAt → P.bt.OwnOK B.Rd →
    ∀ (M : B.DmB.Mk) (k : (P.S.Ent → E) × P.Wp),
      wfG B.Rd nAt (wfPut (fun i => nAt (P.wAt i)) (fun M' : B.DmB.Mk => M') M k) =
        B.DmB.put M (wfG B.Rd nAt k)

end Spec

theorem ldWfMB_rdG : Spec.ldWfMB_rdG E := by
  classical
  intro C P RdJ nAt Rd hE hR w
  funext j
  unfold wfG wfCutJ
  by_cases hj : RdJ j
  · rw [if_pos hj, if_pos hj]
    cases j with
    | inl a => rfl
    | inr n =>
        show P.ent (P.S.msgs w.1) n = cutTo Rd (P.S.ents (P.S.msgs w.1)) (nAt n)
        unfold cutTo
        rw [if_pos (hR n hj), hE.ent]
  · rw [if_neg hj, if_neg hj]

theorem ldWfMB_comG : Spec.ldWfMB_comG E := by
  classical
  intro C P RdJ nAt I atN hE hI hO v k
  have hinj : Function.Injective fun i => nAt (atN i) := fun i i' h => hI (hE.inj h)
  have hinjJ : Function.Injective fun i => (Sum.inr (atN i) : P.bt.J) := fun i i' h =>
    hI (Sum.inr.inj h)
  funext j
  by_cases hx : ∃ i, (Sum.inr (atN i) : P.bt.J) = j
  · obtain ⟨i, rfl⟩ := hx
    rw [hinjJ.extend_apply]
    unfold wfG
    rw [if_pos (hO i)]
    show Function.extend (fun i => nAt (atN i)) v k.1 (nAt (atN i)) = v i
    exact hinj.extend_apply v k.1 i
  · rw [Function.extend_apply' _ _ _ hx]
    unfold wfG
    by_cases hj : RdJ j
    · rw [if_pos hj, if_pos hj]
      cases j with
      | inl a => rfl
      | inr n =>
          show Function.extend (fun i => nAt (atN i)) v k.1 (nAt n) = k.1 (nAt n)
          exact Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hx ⟨i, congrArg Sum.inr (hE.inj hi)⟩
    · rw [if_neg hj, if_neg hj]

theorem ldWfMB_kc : Spec.ldWfMB_kc E := fun _ _ _ _ => rfl

theorem ldWfMB_rd : Spec.ldWfMB_rd E := fun C P B nAt Rd hE hR w =>
  ldWfMB_rdG C P B.Rd nAt Rd hE hR w

theorem ldWfMB_com : Spec.ldWfMB_com E := fun C P B nAt hE hO M k =>
  ldWfMB_comG C P B.Rd nAt _ P.wAt hE (fun _ _ h => hO.inj (congrArg Sum.inr h)) hO.own M k

end Cb
