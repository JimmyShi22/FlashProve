-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndInto.lean: for toys: from the stage after a closing to the last three moves of
a request: what the closing leaves is written as the rows that stay open; the pending tensor rows
are made.

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. Its last moves, the final batching, make the claims on the
encoded index that are still pending into one. This file, for small examples, leads from the end of
a segment's closing to these last moves.
Definitions, statements and proofs (an assembly).
It uses Cb/Obj/LdObjectReqEnd.lean (`R : LdORE F E Kc`), Cb/Obj/LdObjectReqEndAt.lean (`R.reqOf`:
the request with given first sendings, segments, and any list "tail" that ends at `R.X.src`, then
`R.lastP`) and Cb/Ld/LdTenSay.lean (`X.sayT`: the stand-in, in a toy, for the ends of sumchecks at
maps of the index).

Main names:
  `R.pre Xa Φ A₁`: the stage after a closing: over `R.S`: a predicate Φ on (an explicit part Xa, the
    messages), beside a base joint A₁ on (`R.St`, the index, messages, prover encoded index, ghost).
    This is the form of `LdLocD.tgt` (Cb/Req1/LdSegKit.lean; Φ := what is claimed after the
    locations).
  `R.stepP1 .. rows`: a step without rounds to `R.X.p1`: the explicit part x of Φ becomes the
    explicit part "rows x" of the rows that stay open.
  `R.Into Xa Φ A₁ rows`: what is asked: Φ x m says exactly that the rows hold (for a closing:
    Cb/Req1/LdSegAfterRows.lean); the exact relation of A₁ gives "the index is the encoding of the
    prover encoded index with this record"; its condition excludes a collision; the cores agree;
    back: on its condition, if the statement decodes the index with its record, the relaxed relation
    of A₁ holds. (So A₁ claims nothing more than that in the relaxed world: a trivial model.)
  `R.tailP ..` := the step ; `X.sayT`: from `R.pre ..` to `R.X.src`.
  `Spec.ldOREI_tail`: `R.Into`, `X.SayOK κ` ⇒ `tailP.Hyp`; its kinds; `tailP.Zk base` from: the
    say-block's own entries are fresh at `R.pre ..`.
  `Spec.ldOREI_carry`: a fact that is fresh at `R.pre ..` is fresh after the step.

Limits: this file does not say that the batching's own entries are fresh after tailP. This file
gives no instance of `R.Into`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndSay
import Cb.Obj.LdObjectReqEndAt
import Cb.Req1.LdSegFrontTabZk
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdORE
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] (R : LdORE F E Kc)
variable (Xa : Type) (Φ : Xa → R.S.Msg → Prop)
  (A₁ : Rels Kc R.St R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G)))

/-- The stage after a closing. -/
@[reducible] def pre : LdStage E Kc :=
  ⟨R.S, Xa × R.St, R.Cf.conf.E0, R.Cf.conf.PIdx × R.G, claimRels Φ A₁⟩

variable (rows : Xa → R.X.Xr)

/-- The step. -/
def stepP1 : LdMv (R.pre Xa Φ A₁) R.X.p1 :=
  ldStepF R.S (claimRels Φ A₁) R.X.p1.A fun x => (rows x.1, x.2)

/-- What is asked. -/
structure Into : Prop where
  rows : ∀ x m, Φ x m ↔ R.X.RowsOK (rows x) m
  fw   : ∀ st y w, A₁.rel st y w → R.Cf.conf.Enc (R.rc st) y w.2.1
  on   : ∀ st y, A₁.on (st, y) → ¬ R.Cf.conf.coll y (R.rc st).1
  core : ∀ w, R.coreZ w = A₁.core w
  bw   : ∀ st y w, A₁.on (st, y) → (∃ U, R.Cf.conf.dcd y (R.rc st) = some U) → A₁.relR (st, y) w

/-- The step; the values are said; the rows come out. -/
def tailP : LdProg (R.pre Xa Φ A₁) R.X.src :=
  ((LdProg.nil _).snoc (R.stepP1 Xa Φ A₁ rows)).app R.X.sayT

end LdORE

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOREI_step : Prop :=
  ∀ (R : LdORE F E Kc) (Xa : Type) (Φ : Xa → R.S.Msg → Prop)
      (A₁ : Rels Kc R.St R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G))) (rows : Xa → R.X.Xr),
    R.Into Xa Φ A₁ rows → (R.stepP1 Xa Φ A₁ rows).Hyp

def ldOREI_carry : Prop :=
  ∀ (R : LdORE F E Kc) (Xa : Type) (Φ : Xa → R.S.Msg → Prop)
      (A₁ : Rels Kc R.St R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G))) (rows : Xa → R.X.Xr)
      (base : MaskFact (R.pre Xa Φ A₁).J.W → Prop) (f : MaskFact (R.pre Xa Φ A₁).J.W),
    base f → (R.stepP1 Xa Φ A₁ rows).After base f

/-- The tail. -/
def ldOREI_tail : Prop :=
  ∀ (R : LdORE F E Kc) (Xa : Type) (Φ : Xa → R.S.Msg → Prop)
      (A₁ : Rels Kc R.St R.Cf.conf.E0 (R.S.Msg × (R.Cf.conf.PIdx × R.G)))
      (rows : Xa → R.X.Xr) (κ : R.X.Q → R.X.Nm),
    R.Into Xa Φ A₁ rows → R.X.SayOK κ →
    (R.tailP Xa Φ A₁ rows).Hyp ∧
    ((R.tailP Xa Φ A₁ rows).All fun t => t = .sub ∨ t = .step) ∧
    ∀ base : MaskFact (R.pre Xa Φ A₁).J.W → Prop,
      base (R.X.sayMask κ).fact → (R.tailP Xa Φ A₁ rows).Zk base

end
end Spec

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOREI_step : Spec.ldOREI_step F E Kc := by
  intro R Xa Φ A₁ rows h
  refine ldStepF_hyp R.S (claimRels Φ A₁) R.X.p1.A _ ?_ ?_ ?_ ?_
  · rintro x y w ⟨hΦ, hA⟩
    exact ⟨h.fw x.2 y w hA, (h.rows x.1 w.1).1 hΦ, trivial⟩
  · intro x y hx
    exact ⟨h.on x.2 y hx, trivial⟩
  · intro w
    exact h.core w
  · rintro x y w hx ⟨U, hU, hr, -⟩
    exact ⟨(h.rows x.1 w.1).2 hr, h.bw x.2 y w hx ⟨U, hU⟩⟩

theorem ldOREI_carry : Spec.ldOREI_carry F E Kc := fun R _ Φ A₁ rows base f hb =>
  ldStepF_carry R.S (claimRels Φ A₁) R.X.p1.A (fun x => (rows x.1, x.2)) base f hb

theorem ldOREI_tail : Spec.ldOREI_tail F E Kc := by
  intro R Xa Φ A₁ rows κ hI hS
  obtain ⟨s1, s2, s3⟩ := ldTenSay_prog E Kc R.X κ hS
  refine ⟨?_, ?_, fun base hb => ?_⟩
  · unfold LdORE.tailP
    rw [ldProg_app_hyp, LdProg.hyp_snoc]
    exact ⟨⟨LdProg.hyp_nilK _, ldOREI_step F E Kc R Xa Φ A₁ rows hI⟩, s1⟩
  · unfold LdORE.tailP
    rw [ldProg_app_all, LdProg.all_snoc]
    exact ⟨⟨LdProg.all_nilK _ _, Or.inr rfl⟩, s3⟩
  · unfold LdORE.tailP
    rw [ldProg_app_zk, LdProg.zk_snoc, LdProg.after_snoc, LdProg.after_nil]
    exact ⟨⟨(LdProg.zk_nil _ _).2 trivial, ldStepF_zk _ _ _ _ _⟩,
      s2 _ (ldOREI_carry F E Kc R Xa Φ A₁ rows base _ hb)⟩

end
end Cb
