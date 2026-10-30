-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBattVKeep.lean: the pending row that is left after the batching with a value shown reads, of
all oracle messages, the holder of the inner entry alone (under the hypotheses of its statements).

Book-keeping for composition. After a batching step of an interactive oracle proof one linear claim
that reads the encoded index stays open. This file states what stays open over a subset of the
prover's oracle messages, the kept ones, in the form that the next part of the protocol takes.
Definitions, statements and proofs. For any data of the batching (`LdTenVD`, Cb/Ld/LdBattVSeg.lean).
What is left beside the rows (`X.left`, Cb/Ld/LdBattVSeg.lean): the index is decoded; what else was
claimed (A0); the pending row. That row reads the matrix of the index and the inner entry (at
`X.cAt`; its holder: the member `X.cAt.1`; told in the head of Cb/Ld/LdBattV.lean).

Main names (kp is a set of members):
  `X.leftK kp A0k`: what is left, as a joint on the kept messages; A0k: "what else was claimed" on
    the kept messages.
  `X.KeepOK kp A0k`: the conditions: the inner entry lies in a kept member; A0 is A0k of the kept
    messages (relation, relaxed relation, condition, core).
  `Spec.ldBattVSeg_tk_pend`: the inner entry in a kept member ⇒ the pending row says the same of all
    messages and of (the kept ones, 0 elsewhere).
  `Spec.ldBattVSeg_tk_ends`: `X.KeepOK kp A0k` ⇒ `X.Ends X.Mid id` (what is left on the kept
    messages, read off all messages).

Why: a closing carries "what else is claimed" as a joint on the oracle messages that are kept at its
bridge. The batching's list of moves ends with "what is left is written as Az" (`X.Ends`,
Cb/Ld/LdBattVSeg.lean: what is left goes over into Az: fields `fw`, `bw`, `on`, `core`), for any Az
on all messages. Here Az is made in the form that a closing needs, and `X.Ends` is shown.
The difference to the first form: there every entry that the batching reads (its own masks, the
incoming masks) has to lie in a kept member, because the one row that is left reads them all (the
first form and that row: the head of Cb/Ld/LdBatt.lean, "Output"). Here the hiding coefficients and
the incoming masks may lie in members of the closing's group: the row that reads them is closed with
the segment. `X.Own` (Cb/Ld/LdBattVSeg.lean) is not needed.

Limits: this file does not say which members a protocol keeps.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBattVSegProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

namespace LdTenVD
variable {E Kc : Type} [Field E] [Fintype E] (X : LdTenVD E Kc)
  (kp : X.S.O → Prop) [DecidablePred kp]

/-- messages of all members from the kept ones; 0 elsewhere -/
def back (mk : (X.S.sub kp).Msg) : X.S.Msg := fun o => if h : kp o then mk ⟨o, h⟩ else fun _ => 0

theorem back_res (m : X.S.Msg) (o : X.S.O) (h : kp o) :
    X.back kp (X.S.res (T := OMsg.Msg) kp m) o = m o := dif_pos h

/-- What is left, on the kept messages. -/
def leftK (A0k : Rels Kc X.St X.C.E0 ((X.C.Msg × (X.S.sub kp).Msg) × X.Wp)) :
    Rels Kc X.Mid X.C.E0 ((X.S.sub kp).Msg × (X.C.PIdx × X.Wp)) :=
  idxAt X.C (fun z => X.rc (X.stOf z).2) ⟨fun z y w =>
      A0k.rel (X.stOf z).2 y w ∧ X.PendOK z (w.1.1, X.back kp w.1.2),
    fun a w => A0k.relR ((X.stOf a.1).2, a.2) w ∧ X.PendOK a.1 (w.1.1, X.back kp w.1.2),
    fun a => A0k.on ((X.stOf a.1).2, a.2),
    A0k.core⟩

/-- The conditions. -/
structure KeepOK (A0k : Rels Kc X.St X.C.E0 ((X.C.Msg × (X.S.sub kp).Msg) × X.Wp)) : Prop where
  c    : kp X.cAt.1
  rel  : ∀ st y U m wp,
    X.A0.rel st y ((U, m), wp) ↔ A0k.rel st y ((U, X.S.res (T := OMsg.Msg) kp m), wp)
  relR : ∀ a U m wp, X.A0.relR a ((U, m), wp) ↔ A0k.relR a ((U, X.S.res (T := OMsg.Msg) kp m), wp)
  on   : ∀ a, X.A0.on a ↔ A0k.on a
  core : ∀ U m wp, A0k.core ((U, X.S.res (T := OMsg.Msg) kp m), wp) = X.A0.core ((U, m), wp)

end LdTenVD

namespace Spec

def ldBattVSeg_tk_pend : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (kp : X.S.O → Prop) [DecidablePred kp],
    kp X.cAt.1 →
    ∀ (z : X.Mid) (U : X.C.Msg) (m : X.S.Msg),
      X.PendOK z (U, X.back kp (X.S.res (T := OMsg.Msg) kp m)) ↔ X.PendOK z (U, m)

def ldBattVSeg_tk_ends : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (X : LdTenVD E Kc) (kp : X.S.O → Prop) [DecidablePred kp]
      (A0k : Rels Kc X.St X.C.E0 ((X.C.Msg × (X.S.sub kp).Msg) × X.Wp)),
    X.KeepOK kp A0k → X.Ends X.Mid id (onMsgRels (X.S.res (T := OMsg.Msg) kp) (X.leftK kp A0k))

end Spec

theorem ldBattVSeg_tk_pend : Spec.ldBattVSeg_tk_pend := by
  intro E Kc _ _ X kp _ hc z U m
  refine battV_rowB_reads E X.bt z _ _ (fun _ => rfl) ?_
  show X.back kp (X.S.res (T := OMsg.Msg) kp m) X.cAt.1 X.cAt.2 = m X.cAt.1 X.cAt.2
  rw [X.back_res kp m X.cAt.1 hc]

theorem ldBattVSeg_tk_ends : Spec.ldBattVSeg_tk_ends := by
  intro E Kc _ _ X kp _ A0k h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z y w h1
    exact ⟨h1.1, (h.rel _ _ _ _ _).1 h1.2.1, (ldBattVSeg_tk_pend E Kc X kp h.c z _ _).2 h1.2.2⟩
  · intro z y w _ _ hz
    obtain ⟨U, hU, h2, h3⟩ := hz
    exact ⟨U, hU, (h.relR _ _ _ _).2 h2, (ldBattVSeg_tk_pend E Kc X kp h.c z _ _).1 h3⟩
  · intro z y h1
    exact ⟨h1.1, (h.on _).1 h1.2⟩
  · intro w
    exact h.core _ _ _

end Cb
