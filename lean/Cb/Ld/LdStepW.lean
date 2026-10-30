-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdStepW.lean: a step in which no message is sent: the verifier rewrites the explicit part of
the statement, the honest prover computes a new part of its witness, and the extractor gives the old
part back.

Definitions, statements as theorems, proofs. Generic. A tool; no block of a protocol.

Why: Cb/Req1/LdSegClose.lean has `ldStepF`: only the explicit part is mapped. Here the honest prover
may also compute a new further witness (up) and the extractor gives the old one back (dn). This
serves the entry step of a segment. What a later segment's first oracle messages will hold must be
in the further witness, with its exact claim, all through the segments before (behind a sending the
exact relation knows of the new messages only what the old witness, read back off them, says). If
these data are a function of what the prover has, the step that begins the first segment puts them
there.

Main names:
  `ldStepW S A A' f up dn`: the move, between the stages (S, St, E₀, Wp, A) and (S, St', E₀, Wp',
    A'); up may read state, messages, further witness.
  `StepWOK`: four clauses on the base joints A, A': exact forth at the computed witness; relaxed
    back at what dn gives; condition; core.
  `ldStepW_hyp`: under `StepWOK` the move has `Hyp` (by the rule of Cb/Ld/LdBatPeel.lean).
  `ldStepW_fmt`: under `h`, `hp` the move has `Fmt` (readers of the record and of the further
    witness go over; the demand is unchanged).
  `ldStepW_after`: which facts on fresh masks pass it (`ldStepW`): a fact (`IOR.MaskFact`,
    Cb/Req1/LdSegFresh.lean) passes the step (`After base`, Cb/Req1/LdReq.lean): fa: a fact that is
    fresh before (`hb : base fa`); kc', put': the reading and the overwriting behind; asked:
    overwriting before the step is overwriting behind it, at every state.

Limits: this file does not say that `StepWOK` can be met.



Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCloseProofs
import Cb.Req1.LdSegFormatMoves
import Cb.Req1.LdSegCarry
import Cb.Req1.LdSegRefLkpPreProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E Kc : Type} [Field E] [Fintype E] (S : Sig E) {St St' Wp Wp' : Type} {E₀ : ExtSpec}
  (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp')) (f : St → St')
  (up : St → S.Msg × Wp → Wp') (dn : St × E₀.Str → S.Msg × Wp' → Wp)

/-- The move. -/
def ldStepW : LdMv (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀, Wp', A'⟩ :=
  .step _ _ (sideF S f) (sideG S (ExtMap.id E₀)) (sideM S f up) (sideB S dn)

/-- What is assumed, on the base joints. -/
structure StepWOK : Prop where
  fw   : ∀ st y w, A.rel st y w → A'.rel (f st) y (w.1, up st w)
  on   : ∀ st y, A.on (st, y) → A'.on (f st, y)
  core : ∀ st w, A'.core (w.1, up st w) = A.core w
  bw   : ∀ st y w, A.on (st, y) → A'.relR (f st, y) w → A.relR (st, y) (w.1, dn (st, y) w)

theorem ldStepW_hyp (h : StepWOK S A A' f up dn) : (ldStepW S A A' f up dn).Hyp :=
  ldPeel_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldPeel_base E Kc St St' Wp Wp' S E₀ E₀ A A' f (ExtMap.id E₀) up dn
      (extMap_isLocal.1 E₀) h.fw h.on h.core h.bw)

theorem ldStepW_fmt {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 E₀) (rc : St → Rc) (rc' : St' → Rc)
    (px : Wp → Pw) (px' : Wp' → Pw) (q : Finset (E₀.prod S.ext).Pos → Prop)
    (h : ∀ x, rc' (f x) = rc x) (hp : ∀ st w, px' (up st w) = px w.2) :
    (ldStepW S A A' f up dn).Fmt ((⟨S, St, E₀, Wp, A⟩ : LdStage E Kc).fmt i rc px q)
      ((⟨S, St', E₀, Wp', A'⟩ : LdStage E Kc).fmt i rc' px' q) := by
  refine ldFmt_step E Kc E0 Rc Pw _ _ _ _ _ _ _ _
    (ExtMap.Moves.pair_left (ExtMap.Moves.comp (ExtMap.Moves.id i) (ExtMap.Moves.fst i S.ext))
      (ExtMap.Avoids.snd i S.ext))
    ?_ (fun p => hp p.1.1 (S.msgs p.2.1, p.2.2)) ?_
  · intro x x' e
    obtain rfl := Option.some.inj e
    exact h x.1
  · intro U V hV hU
    have e : V = U :=
      Finset.ext fun x =>
        (hV x).trans ⟨fun ⟨u, hu, hx⟩ => ((sideG_id_mem S E₀ u x).1 hx) ▸ hu,
          fun hx => ⟨x, hx, (sideG_id_mem S E₀ x x).2 rfl⟩⟩
    rw [e]
    exact hU

/-- A fact passes the step: fa: a fact that is fresh before; kc', put': the reading and the
overwriting behind; asked: overwriting before the step is overwriting behind it, at every state. -/
theorem ldStepW_after (base : MaskFact (S.Wit × Wp) → Prop) (fa : MaskFact (S.Wit × Wp)) (Kf : Type)
    (kc' : S.Wit × Wp' → Kf) (put' : fa.Mk → Kf → Kf) (hb : base fa)
    (h : ∀ st (w w' : S.Wit × Wp) M, fa.kc w' = fa.put M (fa.kc w) →
      kc' (w'.1, up st (S.msgs w'.1, w'.2)) = put' M (kc' (w.1, up st (S.msgs w.1, w.2)))) :
    (ldStepW S A A' f up dn).After base ⟨Kf, kc', fa.Mk, put'⟩ :=
  segCarry_step (⟨S, St, E₀, Wp, A⟩ : LdStage E Kc) ⟨S, St', E₀, Wp', A'⟩
    _ _ _ _ base fa Kf kc' put' hb fun x w w' M e => ⟨rfl, h x.1 w w' M e⟩

end
end Cb
