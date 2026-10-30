-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverOthers.lean: the hypotheses `hmk₂` and `hmk₃` of `falls_asks`
(Honest/Law/CoverAsks.lean) at the proof file's shared and second chain, where the marks of these
chains are our own `fitMarks` alone. The two hypotheses say that no mark of the chain speaks at a
typed message. A mark of `fitMarks` (Honest/Law/CoverFit.lean) speaks where a sub-protocol's rounds
cannot draw the challenges at hand, and typed challenges can always be drawn.

  1  `hmk_fit`   GENERAL: at a chain whose only marks are `fitMarks`, no mark speaks at a typed
     message
  2  `hmk₂_head`, `hmk₃_head`   the two hypotheses under the library's `P5J.AtMg`

Limits.
  * The lists hold no mark of an owner of a sub-protocol. The three groups of authors known to own
    sub-protocols of these two chains were asked whether they own a mark or a fall there. If one
    does, these lemmas do not serve as they are: `hsil_own` (Honest/Law/CoverOwn.lean) then serves
    only where no owner's mark may stand.
  * K12: proved at no place of these chains. They
    have typed no fall and no mark there and know of none. They name one candidate that is owed:
    three conditions of theirs hang on the challenges of the sub-protocols before K12's, and that
    these cannot fail is held by nobody.
  * All that is assumed of the other two chains sits in `hf₂` and `hf₃`, which are hypotheses. The
    lists `ms₂` and `ms₃` occur in `falls_asks` in `hmk₂` and `hmk₃` and in the gates of these
    chains, of which the bound reads the prices alone. So laying them as `fitMarks` says nothing on
    whether an owner has a mark there. None of the three groups of authors that were asked answered
    that these chains have no fall. If a fall is found there, `falls_asks` itself must turn: it has
    no bounds for these chains.
  * Four sub-protocols of the other two chains are of the kind `frame` and so are ours: at ⟨2,
    none, 0⟩, ⟨2, none, 11⟩, ⟨3, none, 1⟩ and ⟨3, none, 3⟩. We lay no fall and no mark there. The
    grade: by our own reading of the blocks' texts; at ⟨2, none, 0⟩ the block's decision cannot
    refuse; at the three others the decision tests book-keeping fields of the state, and that the
    test is true at every state that an honest run reaches is owed by us and proved at no place.
    Three of the four have no round; the round at ⟨2, none, 11⟩ draws nothing.
  * `hC` (what the kit of challenges shows fits its round) is a hypothesis. `kit_two`
    (Honest/Law/KitTwo.lean) proves it at one kit.
  * `P5J.AtMg` is a hypothesis. The full size alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverOwn
import Johnson.Desc.ProofFile.Honest.Law.CoverDraws
import Johnson.Desc.ProofFile.Honest.Law.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT)
open _root_.Run.PQ (CK)
open P5J (TS)

/-- At a chain whose only marks are `fitMarks`, no mark speaks at a typed message. -/
theorem hmk_fit {S Cl : Type} (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (bs : List (Block S Cl)) (ds : List RDT)
    (hfit : List.Forall₂ KindFits ds (bs.flatMap (·.rounds)))
    (hz : ∀ b ∈ bs, ∀ z ∈ b.rounds, z.entry.drawNZ ≤ z.entry.drawE)
    (hnd : (bs.map (·.place)).Nodup) :
    ∀ A b B, bs = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf (fitMarks bs) b.place fr (drawnT C _ ρ) = none := fun A b B e fr ρ =>
  hsil_own C hC bs ds hfit hz hnd [] (fun _ => false) (fun _ h => by cases h) A b B e rfl fr ρ

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The hypothesis `hmk₂` of `falls_asks`, at `ms₂ := fitMarks` of the shared chain. -/
theorem hmk₂_head (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ A b B, (P5J.F0T o Zp Np cF).shared.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₂.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf (fitMarks (P5J.F0T o Zp Np cF).shared.blocksInOrder) b.place fr (drawnT C _ ρ) = none :=
  hmk_fit C hC _ _ (kinds_of_data h.laid.data).2.1 (hz_shared_head h)
    (places_nodup (file_head h).2.1).2.1

/-- The hypothesis `hmk₃` of `falls_asks`, at `ms₃ := fitMarks` of the second chain. -/
theorem hmk₃_head (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (h : P5J.AtMg o Z D r Zp Np cF) :
    ∀ A b B, (P5J.F0T o Zp Np cF).second.blocksInOrder = A ++ b :: B →
      ∀ fr (ρ : Iop.Rho (uLT C
        ((D.ds₃.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf (fitMarks (P5J.F0T o Zp Np cF).second.blocksInOrder) b.place fr (drawnT C _ ρ) = none :=
  hmk_fit C hC _ _ (kinds_of_data h.laid.data).2.2.1 (hz_second_head h)
    (places_nodup (file_head h).2.1).2.2

end ProofFile.Honest

#print axioms ProofFile.Honest.hmk_fit
#print axioms ProofFile.Honest.hmk₂_head
#print axioms ProofFile.Honest.hmk₃_head
