-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req2/LdSeg2Step.lean: a reduction without rounds that only maps the statement's explicit part,
and keeps the record, keeps its four clauses (`LdStepOK`) when its relations, which also read the
message that the index's oracle encodes, are made relations in whose relaxed relation the index's
message is decoded by the statement (`idxAt`).

One theorem: an auxiliary lemma that connects two files. `idxAt C rc A` (Cb/Ld/LdWfIdx.lean) makes
relations A on tuples (U, m) (message of the encoded index, messages) relations on m. Knowledge
soundness speaks of statements whose oracle has no collision at the record's seed and that meet A's
own condition (`A.on`).

Main names:
  `LdStepOK.idx` (Cb/Req1/LdSegFrontTab.lean: `LdStepOK`; Cb/Ld/LdWfIdx.lean: `idxAt`).

Why: whoever builds a front on tuples shows its steps' clauses where the index's message is a
parameter; that the relaxed relation speaks of the decoding of the statement costs nothing.

Limits: This file says nothing on any protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req2.LdSeg2Idx
import Cb.Req1.LdSegFrontTab

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob

theorem LdStepOK.idx {E Kc : Type} [Field E] (C : ConfigurationWithOutOfDomainSample) (S : Sig E) {St St' Wp : Type}
    (A : Rels Kc St C.E0 ((C.Msg × S.Msg) × Wp)) (A' : Rels Kc St' C.E0 ((C.Msg × S.Msg) × Wp))
    (rc : St → C.Rec) (rc' : St' → C.Rec) (f : St → St') (hr : ∀ st, rc' (f st) = rc st)
    (fw : ∀ st y w, A.rel st y w → A'.rel (f st) y w) (on : ∀ st y, A.on (st, y) → A'.on (f st, y))
    (core : ∀ w, A'.core w = A.core w)
    (bw : ∀ st y w, A.on (st, y) → A'.relR (f st, y) w → A.relR (st, y) w) :
    LdStepOK S (idxAt C rc A) (idxAt C rc' A') f where
  fw := fun st y w h => ⟨by rw [hr st]; exact h.1, fw st y _ h.2⟩
  on := fun st y h => ⟨by show ¬ C.coll y (rc' (f st)).1; rw [hr st]; exact h.1, on st y h.2⟩
  core := fun w => core _
  bw := fun st y w ho h => by
    obtain ⟨U, hU, hA⟩ := h
    have hU' : C.dcd y (rc' (f st)) = some U := hU
    rw [hr st] at hU'
    exact ⟨U, hU', bw st y _ ho.2 hA⟩

end Cb
