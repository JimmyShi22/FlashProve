-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinkChain.lean: the interactive oracle reduction of Cb/Ld/LdLink.lean (two encoded indices
decode to messages that agree on fixed coordinates), put together anew as a list of steps, so that
its last part may be analysed together with the steps before it and not only by itself.

Definitions, statements and proofs. The blocks, joints and errors are those of Cb/Ld/LdLink.lean;
the rules for chains are those of Ior/KnowCollRulesChain.lean, Ior/KnowCollPiece.lean and
Cb/Ld/LdTowerKitChain.lean.
"The link" is the protocol of Cb/Ld/LdLink.lean between two encoded indices; "a link" is a step of a
chain (`IOR.Link`, Ior/KnowCollRulesChain.lean).

Why: `Spec.ldLk_tail` (Cb/Ld/LdLink.lean) takes "a closing that is a tail by itself". A closing
whose splittings use mask-only messages that were sent in the core (as further members of the family
that holds G_u0 and G_u1) is no tail by itself: it is not zero knowledge for every witness (proved
of one masked block, under its premises: `Spec.masked_not_exact`, Ior/Masked.lean; the step to such
a closing is an argument in words). This file takes such a closing as a chain behind the core: its
masked links ask that their masks be fresh after all that comes before them, the core included.

Main names. ι is not empty. "The three premises" are `P.FoldErr on0 on1 ε₀ ε₁`, `P.D.pl` injective,
`S.OK` (Cb/Ld/LdLink.lean).
  `P.J0` to `P.J4`, `ldJT`: the joints of Cb/Ld/LdLink.lean with their types, at the form whose
    condition may fail (`Rels.cf`); the trivial joint.
  `P.coreC`: the core: the chain of the four blocks as links.
  `Spec.ldLc_ok`: under the three premises `P.coreC.Ok` (Ior/KnowCollRulesChain.lean).
  `Spec.ldLc_sides`: under the three premises, the budgets' half (`SidesC`,
    Cb/Ld/LdTowerKitChain.lean), from "at most t₀ and t₁ positions of the two indices" to "at most
    `t a` long positions of each member a of the family".
  `Spec.ldLc_tail`: under the three premises, for every closing chain cZ from `J4` to the trivial
    joint with `cZ.OkFrom` (Ior/KnowCollPiece.lean) of `P.coreC` and `cZ.SidesCT`: `P.linkC` (that
    is `(P.coreC.append cZ).link d`) is a tail from the first joint `j0` (on the statements with the
    conditions) to the trivial statement.

The term is bracketed to the left (all links of core and closing in a row); `P.link` of
Cb/Ld/LdLink.lean is bracketed otherwise: another term with the same rounds.

`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Notation: `P.q0`: of the input: at most t₀ positions of the first index, t₁ of the further one;
`P.q3 S`: `P.N.qT S.t`: at most `t a` long positions of each member a of the family; `on0`, `on1`:
the conditions, parameters (Cb/Ld/LdLink.lean).

Limits: no closing chain is given (one, with no splitting: `K.cZ d`, `Spec.ldLkC_chain`,
`Spec.ldLkC_tail`, Cb/Ld/LdLinkClose.lean; its test `K.T` is a field there); that a closing's masks
are fresh after the core is the closing's hypothesis (`cZ.OkFrom`), to be shown from the honest
sender of the family. Otherwise what the head of Cb/Ld/LdLink.lean lists as not said is not said
here either.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinkProofs
import Cb.Ld.LdTowerKitChain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The trivial joint. -/
@[reducible] def ldJT : Joint Unit := ⟨Unit, extNone, Unit, trivRels⟩

namespace LdLkP
variable {E ι κ J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Λ] (P : LdLkP E ι κ J Λ)
variable (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)

@[reducible] def J0 : Joint Unit := ⟨P.X0, P.E0, P.W0, (P.j0 on0 on1).cf⟩
@[reducible] def J1 : Joint Unit := ⟨P.X1, P.E0, P.W1, (P.j1 on0 on1).cf⟩
@[reducible] def J2 : Joint Unit := ⟨P.X2, P.E2, P.W2, (P.j2 on0 on1).cf⟩
@[reducible] def J3 : Joint Unit := ⟨P.X3, P.E3, P.W2, P.j3.cf⟩
@[reducible] def J4 : Joint Unit := ⟨P.X4, P.E3, P.W2, P.j4.cf⟩

variable (S : P.Snd) (ε₀ ε₁ : ℕ)

def lGam : Link Unit (P.J0 on0 on1) (P.J1 on0 on1) :=
  ⟨P.gam, P.hGam, fun _ _ w => w.2, Nums.peek Unit P.vGam (P.errGam ε₀ ε₁)⟩
def lSnd : Link Unit (P.J1 on0 on1) (P.J2 on0 on1) :=
  ⟨P.snd S, ldSendFamHon S.Sd P.X1 P.E0 S.dS,
    fun _ _ w => P.back (P.N.msgs w.1) w.2,
    ldSendFamNums P.N S.Sd P.X1 P.E0 Unit S.L S.t⟩
def lLoc : Link Unit (P.J2 on0 on1) P.J3 :=
  ⟨P.loc, P.hLoc, fun _ _ w => w, Nums.peek Unit P.vLoc P.errLoc⟩
def lPhi : Link Unit P.J3 P.J4 :=
  ⟨P.phi, P.hPhi, fun _ _ w => w, Nums.peek Unit P.vPhi P.errPhi⟩

/-- The core of the link, as a chain. -/
def coreC : Chain Unit (P.J0 on0 on1) P.J4 :=
  .snoc (.snoc (.snoc (.one (P.lGam on0 on1 ε₀ ε₁)) (P.lSnd on0 on1 S)) (P.lLoc on0 on1)) P.lPhi

/-- The link with a closing chain. -/
def linkC (cZ : Chain Unit P.J4 ldJT) (d : P.W0) : Link Unit (P.J0 on0 on1) ldJT :=
  ((P.coreC on0 on1 S ε₀ ε₁).append cZ).link d

end LdLkP

namespace Spec
section
variable (E ι κ J Λ : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ]

def ldLc_ok : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (ε₀ ε₁ : ℕ) (S : P.Snd),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK → (P.coreC on0 on1 S ε₀ ε₁).Ok

def ldLc_sides : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (ε₀ ε₁ : ℕ) (S : P.Snd),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK →
    (P.coreC on0 on1 S ε₀ ε₁).SidesC P.q0 (P.q3 S)

/-- The link, with any closing chain that stands behind its core (`cZ.OkFrom`), is a tail of a chain
from `j0`, on the statements with the conditions, to the trivial statement, for ι not empty and
under the five premises below. -/
def ldLc_tail : Prop :=
  ∀ (P : LdLkP E ι κ J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (ε₀ ε₁ : ℕ) (S : P.Snd)
      (cZ : Chain Unit P.J4 ldJT) (d : P.W0),
    P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective P.D.pl → S.OK →
    cZ.OkFrom (P.coreC on0 on1 S ε₀ ε₁) → cZ.SidesCT (P.q3 S) →
    TailTr (P.linkC on0 on1 S ε₀ ε₁ cZ d).R (P.linkC on0 on1 S ε₀ ε₁ cZ d).H (P.j0 on0 on1) trivRels
      (P.linkC on0 on1 S ε₀ ε₁ cZ d).ext (P.linkC on0 on1 S ε₀ ε₁ cZ d).P P.q0

end
end Spec

section
variable {E ι κ J Λ : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ]

theorem ldLc_ok : Spec.ldLc_ok E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S hF hpl hS
  have hG := ldk_pieceTr_cf (ldLk_gam P on0 on1 ε₀ ε₁ P.q0 hF)
  have hN := ldLk_send P.N S.Sd P.X1 P.W1 P.W0 P.E0 (P.j1 on0 on1) P.back S.dS S.L S.t P.q0 hS.laws
    hS.fair hS.list hS.ev hS.snd hS.bl hS.hid
  have hL := ldk_pieceTr_cf (ldLk_loc P on0 on1 S)
  have hP := ldk_pieceTr_cf (ldLk_phi P (P.q3 S) hpl)
  unfold LdLkP.coreC
  simp only [Chain.Ok]
  exact ⟨⟨⟨hG.good, Or.inl hN.good⟩, Or.inl hL.good⟩, Or.inl hP.good⟩

theorem ldLc_sides : Spec.ldLc_sides E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S hF hpl hS
  have hG := ldLk_gam P on0 on1 ε₀ ε₁ P.q0 hF
  have hN := ldLk_send P.N S.Sd P.X1 P.W1 P.W0 P.E0 (P.j1 on0 on1) P.back S.dS S.L S.t P.q0 hS.laws
    hS.fair hS.list hS.ev hS.snd hS.bl hS.hid
  have hL := ldLk_loc P on0 on1 S
  have hP := ldLk_phi P (P.q3 S) hpl
  refine sidesC_of_sides Unit _ _ _ _ _ ?_
  have sG : (P.lGam on0 on1 ε₀ ε₁).Side P.q0 P.q0 := ⟨hG.noHid, hG.noTie, hG.bears⟩
  have sN : (P.lSnd on0 on1 S).Side P.q0 (P.q2 S) := ⟨hN.noHid, hN.noTie, hN.bears⟩
  have sL : (P.lLoc on0 on1).Side (P.q2 S) (P.q3 S) := ⟨hL.noHid, hL.noTie, hL.bears⟩
  have sP : P.lPhi.Side (P.q3 S) (P.q3 S) := ⟨hP.noHid, hP.noTie, hP.bears⟩
  unfold LdLkP.coreC
  simp only [Chain.Sides]
  exact ⟨P.q3 S, ⟨P.q2 S, ⟨P.q0, sG, sN⟩, sL⟩, sP⟩

theorem ldLc_tail : Spec.ldLc_tail E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S cZ d hF hpl hS hZ hs
  have h := chain_tail_append Unit (P.J0 on0 on1) P.J4 Unit Unit trivRels (P.coreC on0 on1 S ε₀ ε₁)
    cZ d P.q0 (P.q3 S) (ldLc_ok P on0 on1 ε₀ ε₁ S hF hpl hS) hZ
    (ldLc_sides P on0 on1 ε₀ ε₁ S hF hpl hS) hs
  exact ⟨goodT_cf_out _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ => trivial) h.good,
    h.noHid, h.tied, h.bears⟩

end
end Cb
