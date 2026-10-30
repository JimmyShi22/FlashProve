-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDKitSame.lean: the own condition of a step without rounds (`LdPend.StepD`,
Cb/Ld/LdLayDKit.lean) does not depend on how the arriving block's own entries and values are
written.

Two auxiliary lemmas, for whoever builds an instance of the records that use `LdPend.StepD`
(Cb/Ld/LdLayD.lean: `LdReqRefLayD`). A block is a pending block (`LdPend`, Cb/Ld/LdMia.lean): a set
"own" of entries of oracle messages with values at them, and a reading; overwriting is `Sig.ow`
(Cb/Req1/LdSegCarry.lean). A step without rounds: a reduction with no round: it maps the statement
and the oracles, or rejects, and no message is sent.

Main names:
  `Sig.ow_same`: overwriting depends on "own" as a set, and on the values at own entries only.
  `LdPend.stepD_same`: `LdPend.StepD m β γ` gives `LdPend.StepD m β γ'`, for γ' := γ with the same
    set "own" and the same values at it, written otherwise.

Limits: This file says nothing on any instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayDKit

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

theorem Sig.ow_same {E : Type} [Field E] (S : Sig E) (own own' : S.Ent → Prop) (v v' : S.Ent → E)
    (h1 : ∀ n, own n ↔ own' n) (h2 : ∀ n, own n → v n = v' n) (m : S.Msg) :
    S.ow own v m = S.ow own' v' m := by
  classical
  refine funext fun o => funext fun j => ?_
  show (if own ⟨o, j⟩ then v ⟨o, j⟩ else m o j) = if own' ⟨o, j⟩ then v' ⟨o, j⟩ else m o j
  by_cases h : own ⟨o, j⟩
  · rw [if_pos h, if_pos ((h1 _).1 h), h2 _ h]
  · rw [if_neg h, if_neg fun h' => h ((h1 _).2 h')]

theorem LdPend.stepD_same {E Kc : Type} [Field E] [Fintype E] {a b : LdStage E Kc}
    (m : a.X × a.W → b.X × b.W) (β : LdPend a) (γ : LdPend b) (own : b.S.Ent → Prop)
    (val : γ.Mk → b.S.Ent → E) (h1 : ∀ n, γ.own n ↔ own n)
    (h2 : ∀ M n, γ.own n → γ.val M n = val M n) (h : LdPend.StepD m β γ) :
    LdPend.StepD m β ⟨γ.Rd, γ.Rr, own, γ.Mk, val⟩ := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun x w w' M hk => ⟨(he x w w' M hk).1, ?_⟩⟩
  have h3 : b.S.wide b.Wp γ.Rd γ.Rr (m (x, w')).2 =
      (b.S.ow γ.own (γ.val (e M)) (b.S.wide b.Wp γ.Rd γ.Rr (m (x, w)).2).1,
        (b.S.wide b.Wp γ.Rd γ.Rr (m (x, w)).2).2) :=
    (he x w w' M hk).2
  show b.S.wide b.Wp γ.Rd γ.Rr (m (x, w')).2 =
    (b.S.ow own (val (e M)) (b.S.wide b.Wp γ.Rd γ.Rr (m (x, w)).2).1,
      (b.S.wide b.Wp γ.Rd γ.Rr (m (x, w)).2).2)
  rw [← Sig.ow_same b.S γ.own own (γ.val (e M)) (val (e M)) h1 (h2 (e M))]
  exact h3

end Cb
