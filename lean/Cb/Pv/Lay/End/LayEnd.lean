-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayEnd.lean: the ledger of the verifier's claims in a layers' sub-proof, part by part,
and what the chain of the sub-proof's own rounds owes at its end, from shares.

The link of a sub-proof asks that the pull-back of the ledger of the verifier's claims to the early
entries (Cb/Sub/Late.lean) gives what the chain of the sub-proof's own rounds claims at its end
(Ch.Last). This file has the frame of that statement for a layers' sub-proof, at letters.

Main definitions.
 - LayCl: the ledger in eleven parts, in the order in which the parts are meant to be added: the
   lookup's own claims; the three claims behind the sums of squares; the batch of the row products;
   the norms' rows; the shown values of the terms; the gated products; the selectors' sums; the
   planes; the embedding; the three claims of the batched sumcheck; the merge's row.
 - LayCl.all: the parts one after the other.
 - Shares: five premises, each of which says what some of the parts pay: the claim Dn of the first
   statement; the clauses of the norms' two stretches; those of the terms and of the batched
   sumcheck; those of the two gated products; those of the weights' round and the merge. Ok: what
   may be asked of a last statement and the messages beside the ledger.
Main theorems: holds_all (the pull-back of the whole holds if and only if that of each part does);
last_of_shares.

Limits: a frame. No part of the ledger and no share is given here. Ok is a letter: at an Ok that
never holds, last_of_shares says nothing. Ok must bear what no ledger pays: that an output carries
the state of its claim, the pending row, and that a drawn coefficient is not 0. That the order is a
program's is not said. The smallness test's own claims are not among the parts.


-/
import Cb.Sub.Late
import Cb.Pv.Lay.End.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End

open TWhole Cb.Sub Cb.Pv.Lay

variable {E : Type} [Field E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]

/-- The pull-back of a ledger laid behind another holds if and only if both pull-backs hold. -/
theorem pull_append (a : J₂ → Aff E J₁) (L₁ L₂ : Ledger E (J₁ ⊕ J₂)) (m : J₁ → E) :
    Ledger.Holds (pullL a (L₁ ++ L₂)) m ↔
      Ledger.Holds (pullL a L₁) m ∧ Ledger.Holds (pullL a L₂) m := by
  unfold pullL
  rw [List.map_append]
  exact holds_append _ _ m

/-- The ledger of a layers' sub-proof, part by part. -/
structure LayCl (E J : Type) where
  look : Ledger E J
  sq : Ledger E J
  bat : Ledger E J
  led : Ledger E J
  terms : Ledger E J
  gated : Ledger E J
  hot : Ledger E J
  planes : Ledger E J
  emb : Ledger E J
  stack : Ledger E J
  merge : Ledger E J

/-- The parts one after the other. -/
def LayCl.all {J : Type} (c : LayCl E J) : Ledger E J :=
  c.look ++ (c.sq ++ (c.bat ++ (c.led ++ (c.terms ++ (c.gated ++ (c.hot ++ (c.planes ++
    (c.emb ++ (c.stack ++ c.merge)))))))))

/-- The pull-back of the whole holds if and only if that of each part does. -/
theorem holds_all (a : J₂ → Aff E J₁) (c : LayCl E (J₁ ⊕ J₂)) (m : J₁ → E) :
    Ledger.Holds (pullL a c.all) m ↔
      Ledger.Holds (pullL a c.look) m ∧ Ledger.Holds (pullL a c.sq) m ∧
      Ledger.Holds (pullL a c.bat) m ∧ Ledger.Holds (pullL a c.led) m ∧
      Ledger.Holds (pullL a c.terms) m ∧ Ledger.Holds (pullL a c.gated) m ∧
      Ledger.Holds (pullL a c.hot) m ∧ Ledger.Holds (pullL a c.planes) m ∧
      Ledger.Holds (pullL a c.emb) m ∧ Ledger.Holds (pullL a c.stack) m ∧
      Ledger.Holds (pullL a c.merge) m := by
  unfold LayCl.all
  simp only [pull_append]

variable [Fintype E] {M X : Type}

/-- What the parts of the ledger pay, group of clauses by group. -/
structure Shares (T : LayTail E M X) (Dn : X → M → Prop) (msg₁ : M → J₁ → E)
    (a : T.s7.Nx → J₂ → Aff E J₁) (cl : T.s7.Nx → LayCl E (J₁ ⊕ J₂))
    (Ok : T.s7.Nx → M → Prop) : Prop where
  dn : ∀ e m, Ok e m → Ledger.Holds (pullL (a e) (cl e).look) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).hot) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).planes) (msg₁ m) → Dn (T.xL e) m
  norms : ∀ e m, Ok e m → Ledger.Holds (pullL (a e) (cl e).sq) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).bat) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).led) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).hot) (msg₁ m) →
    T.lL (T.xL e) (T.b1 e).1.1.1.1.2 m ∧ T.s1.Lc (T.b1 e).1.1 (T.b1 e).1.2 m ∧ T.ow1 (T.b1 e) m ∧
      T.lP (T.xP e) (T.b2 e).1.1.1.2 m ∧ T.s2.Lc (T.b2 e).1.1 (T.b2 e).1.2 m ∧ T.ow2 (T.b2 e) m
  terms : ∀ e m, Ok e m → Ledger.Holds (pullL (a e) (cl e).terms) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).stack) (msg₁ m) →
    T.s3.Lc (T.b3 e).1.1 (T.b3 e).1.2 m ∧ T.ow3 (T.b3 e) m ∧
      T.s4.Lc (T.b4 e).1.1 (T.b4 e).1.2 m ∧ T.ow4 (T.b4 e) m
  gated : ∀ e m, Ok e m → Ledger.Holds (pullL (a e) (cl e).gated) (msg₁ m) →
    T.s5.Lc (T.b5 e).1.1 (T.b5 e).1.2 m ∧ T.ow5 (T.b5 e) m ∧
      T.s6.Lc (T.b6 e).1.1 (T.b6 e).1.2 m ∧ T.ow6 (T.b6 e) m
  weights : ∀ e m, Ok e m → Ledger.Holds (pullL (a e) (cl e).emb) (msg₁ m) →
    Ledger.Holds (pullL (a e) (cl e).merge) (msg₁ m) →
    T.lW (T.xW e) (T.y7 e).1.2 m ∧ T.s7.Lc (T.y7 e) e.1.2 m ∧ T.s7.Out e m

/-- What the chain claims at its end, from the pull-back of the whole ledger and the shares. -/
theorem last_of_shares {T : LayTail E M X} {Dn : X → M → Prop} {msg₁ : M → J₁ → E}
    {a : T.s7.Nx → J₂ → Aff E J₁} {cl : T.s7.Nx → LayCl E (J₁ ⊕ J₂)} {Ok : T.s7.Nx → M → Prop}
    (S : Shares T Dn msg₁ a cl Ok) (e : T.s7.Nx) (m : M) (hOk : Ok e m)
    (h : Ledger.Holds (pullL (a e) (cl e).all) (msg₁ m)) : T.ch.Last Dn e m := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := (holds_all (a e) (cl e) (msg₁ m)).1 h
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := S.norms e m hOk k2 k3 k4 k7
  obtain ⟨t1, t2, t3, t4⟩ := S.terms e m hOk k5 k10
  obtain ⟨g1, g2, g3, g4⟩ := S.gated e m hOk k6
  obtain ⟨w1, w2, w3⟩ := S.weights e m hOk k9 k11
  exact (T.last_iff Dn e m).2 ⟨S.dn e m hOk k1 k7 k8, n1, n2, n3, n4, n5, n6, t1, t2, t3, t4, g1,
    g2, g3, g4, w1, w2, w3⟩

end Cb.Pv.Lay.End
