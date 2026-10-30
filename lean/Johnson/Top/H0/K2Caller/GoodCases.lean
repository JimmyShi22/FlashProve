-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/GoodCases.lean: THREE TOOLS ON `Piece.GoodIn`
(Johnson/Desc/Sound/GoodIn.lean), general in the piece: for laws whose condition in front holds a
fact that every acceptance gives anyhow.

Main names:
  `goodIn_cases`: a law may be shown in two cases of the condition in front.
  `goodIn_of_yes`: a fact that every acceptance gives may be added to the condition in front for
    nothing: where it fails the piece never accepts (`goodIn_of_sure`,
    Johnson/Desc/ChainEndGoodIn.lean).
  `seated_goodIn_imp`: at a seated sub-protocol (SeatedAt.lean) the condition in front may be said
    as an implication: «at every state that the way in lets in» in the place of «the way in lets a
    state in, at which»: so whoever pays the condition need not show that the way in lets in. By
    `seated_out` and `goodIn_weaken` (Johnson/Desc/Sound/GoodInStretch.lean).
Limits. Tools: they would stay proved if the protocol were another. Nothing on soundness. On hiding
nothing.

-/
import Johnson.Top.H0.K2Caller.TopFam
import Johnson.Desc.Sound.GoodInStretch
import Johnson.Desc.ChainEndGoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Maker Iop
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece below goodIn_weaken goodIn_of_sure)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

variable {F : Frame}

section
variable {C : CK} {S Cl W : Type} (q : Piece C F S Cl W)

/-- **A law may be shown in two cases of the condition in front.** -/
theorem goodIn_cases (P : S × F.E.Str → Prop) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (h1 : q.GoodIn (fun a => on a ∧ P a) on' R R')
    (h2 : q.GoodIn (fun a => on a ∧ ¬ P a) on' R R') : q.GoodIn on on' R R' := by
  classical
  intro a ha
  by_cases hp : P a
  · exact h1 a ⟨ha, hp⟩
  · exact h2 a ⟨ha, hp⟩

/-- **A fact that every acceptance gives may be added to the condition in front for nothing.** -/
theorem goodIn_of_yes (P : S × F.E.Str → Prop) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (hP : ∀ a τ b, on a → q.ior.red.out a τ = some b → P a)
    (h : q.GoodIn (fun a => on a ∧ P a) on' R R') : q.GoodIn on on' R R' :=
  goodIn_cases q P on on' R R' h
    (goodIn_of_sure q _ _ _ _ fun a τ b ha hb => absurd (hP a τ b ha.1 hb) ha.2)

end

/-- **At a seated sub-protocol the condition in front may be said as an implication**: "at every
    state
that the way in lets in" in the place of "the way in lets a state in, at which": where the way in
refuses, the seated piece never accepts. -/
theorem seated_goodIn_imp {S T Cl Cl' W₀ W' : Type} (q : Piece (ckP .two) F T Cl' W₀)
    (K : Block T Cl') (hq : q.b = below K) (hback : q.back = []) (B : Block S Cl)
    (enter : S → Except String T) (leave : S → T → Except String S) (hr : B.rounds = K.rounds)
    (hs : SeatStep B K enter leave)
    (ext' : S × F.E.Str → Tr (uLT (ckP .two) q.ds) → W' → W')
    (on : T × F.E.Str → Prop) (on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W' → Prop)
    (h : (seatedAt q B ext').GoodIn (fun a => ∃ t, enter a.1 = .ok t ∧ on (t, a.2)) on' R R') :
    (seatedAt q B ext').GoodIn (fun a => ∀ t, enter a.1 = .ok t → on (t, a.2)) on' R R' := by
  refine goodIn_of_yes _ (fun a => ∃ t, enter a.1 = .ok t) _ _ _ _ ?_ ?_
  · intro a τ b _ hb
    obtain ⟨t, _, e, _⟩ := seated_out q K hq hback B enter leave hr hs ext' a b τ hb
    exact ⟨t, e⟩
  · exact goodIn_weaken _ _ _ _ _ _ _ _ _ (fun a ha => ha.2.imp fun t e => ⟨e, ha.1 t e⟩)
      (fun _ hb => hb) (fun _ _ hw => hw) (fun _ _ hw => hw) h

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.goodIn_cases
#print axioms VerifiableInference.Desc.First.K2Caller.goodIn_of_yes
#print axioms VerifiableInference.Desc.First.K2Caller.seated_goodIn_imp
