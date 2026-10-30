-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontFresh.lean: under the hypotheses of `Spec.front_fresh`, if the wide fact on masks is
fresh after a chain, it is fresh after that chain followed by a front that does not look.

Statements; the proofs are in Cb/Ld/LdFrontFreshProofs.lean. Generic: no protocol.
It builds on Cb/Ld/LdFront.lean (a front: steps without rounds, batchings, splittings over one
signature; `p.Quiet Rd own`; `front_carry`, in the bookkeeping of Cb/Req1/LdReq.lean),
Cb/Req1/LdSegCarry.lean (the wide fact) and Ior/KnowCollRulesChain.lean (`c.FreshFor`).

Why: in a closing "front ; tests ; front ; tests" (Cb/Ld/LdLinCloseAlt.lean) the mask entry of a
splitting of the second front has to be fresh after all that stands before that front: the first
front is a part of it.

Main names:
  `Spec.front_fresh`: Mk nonempty; c any chain that ends at the front's first stage. The moves' own
    hypotheses; no move of the front looks at the entries "own" (`p.Quiet Rd own`); the wide fact
    (Rd, Rr, own, Mk, val) is fresh after c ⇒ it is fresh after c and the front.
  `Spec.idle_fresh`: Mk nonempty: the link that does nothing carries every fact.
  `Spec.subQ_one`: "the one entry (a, j)" of the oracle messages that are kept is "the one entry
    (a.1, j)" of all, read on those that are kept: so a fact for one entry keeps its form when
    oracle messages leave the statement.

The wide fact (`LdStage.wideFact`) is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a
reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type `Mk`, and a map
`put : Mk → Kc → Kc`. (`MaskFact.Kc` is a field of that record, not the `Kc` that `Spec.front_fresh`
binds.)

Limits: this file does not say that the fact was fresh before. It does not say that anything is zero
knowledge: `FreshFor` is a condition; it stands as a clause in `Chain.Ok`
(Ior/KnowCollRulesChain.lean) and in `Chain.OkFrom` (Ior/KnowCollPiece.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdFront

set_option autoImplicit false

namespace Cb
namespace Spec
open Iop Prob Hiop Cb.Ood IOR

/-- Through a front (in words: the head's row of `Spec.front_fresh`). -/
def front_fresh : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
      (x y : FSt S E₀ Wp Kc) (p : Front x y) (Z : Joint Kc) (c : Chain Kc Z x.stage.J)
      (Rd : S.Ent → Prop) (Rr : S.O → Prop) (own : S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → S.Ent → E),
    p.prog.Hyp → p.Quiet Rd own →
    c.FreshFor (x.stage.wideFact Rd Rr own Mk val).kc Mk (x.stage.wideFact Rd Rr own Mk val).put →
    (p.prog.onto c).FreshFor (y.stage.wideFact Rd Rr own Mk val).kc
      Mk (y.stage.wideFact Rd Rr own Mk val).put

/-- The link that does nothing (in words: the head's row of `Spec.idle_fresh`). -/
def idle_fresh : Prop :=
  ∀ (E Kc : Type) [Field E] (a : LdStage E Kc) (Z : Joint Kc) (c : Chain Kc Z a.J) (Kr : Type)
      (kc : a.J.W → Kr) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kr → Kr),
    c.FreshFor kc Mk put → (c.append (.one a.idLink)).FreshFor kc Mk put

/-- One entry, read on the oracle messages that are kept (in words: the head's row of
`Spec.subQ_one`). -/
def subQ_one : Prop :=
  ∀ (E : Type) (S : Sig E) (kp : S.O → Prop) [DecidablePred kp]
      (a : (S.sub kp).O) (j : ((S.sub kp).om a).C.J),
    S.subQ kp (fun n => n = (⟨a.1, j⟩ : S.Ent)) = fun n => n = (⟨a, j⟩ : (S.sub kp).Ent)

end Spec
end Cb
