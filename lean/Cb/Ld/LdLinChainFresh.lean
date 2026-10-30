-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChainFresh.lean: three statements on the core of the interactive test that an encoded
index meets linear constraints (Cb/Ld/LdLinChain.lean). Under the hypotheses of the three
statements, masks that ride with one of the three sendings of the test for linear constraints are
fresh after its core.

Definitions, statements (`Cb.Spec.ldLinC_freshO`, `Cb.Spec.ldLinC_freshU`, `Cb.Spec.ldLinC_freshW`)
and proofs.
The three sendings (`sW`, `sU`, `sO`), W, G_u, Ω, u and ω are told in the head of
Cb/Ld/LdLinChain.lean.

Why: Cb/Ld/LdLinChain.lean has the core of the test as a chain, and takes the closing as a chain cZ
that stands behind the core (Ior/KnowCollPiece.lean: cZ.OkFrom core). For a masked link of the
closing (a splitting, say) that condition asks: its masks are fresh after all that comes before it
(Ior/KnowCollRulesChain.lean: `FreshFor`).
Here the part of that condition which concerns the core: under the hypotheses of the three
statements, mask entries that stand in a member of the family sent with W, with G_u, or with Ω are
fresh after the whole core. What is left to a closing: its own links before the masked one do not
look at these masks (`freshFor_snoc`, second case).

Main names (in the statements ι and the type Mb are nonempty):
  `S.Apart`: a condition on the senders: the messages of the family sent with G_u are made from the
    folded message u and the sender's coins alone; those of the family sent with Ω from ω and coins
    alone. So no later prover message depends on masks, pads or encoding randomness of an earlier
    family.
  `Spec.ldLinC_freshO`: masks in the family of Ω: from the conditions of Cb/Ld/LdSendFresh.lean on
    the sender (own masks, other coins, pads: `Own.Laws`) and `S.dO.Nn.Hides (P.NO.budT S.tO)`. The
    reading: rd (messages of Ω's family) (the witness before, `P.W3`, Cb/Ld/LdLin.lean).
  `Spec.ldLinC_freshU`, under the hypotheses of its statement (`Own.Laws`, `Hides`, the two laws of
    keep, `S.dO.Laws P.backO`, `S.Apart`): masks in the family of G_u. The reading at the end of the
    core: all of the witness of Ω's family, and rd (messages of G_u's family) (the witness before,
    `P.W1`).
  `Spec.ldLinC_freshW`, under the hypotheses of its statement (these, and `S.dU.Laws P.backU`):
    masks in the family of W. The reading: all of the witnesses of Ω's and G_u's families, and rd
    (messages of W's family) (the witness before, `P.W0`).
In the last two the reading rd holds the whole witness one step before the sending (keep: `P.W1` at
`P.J1`, `P.W0` at `P.J0`, Cb/Ld/LdLinChain.lean), which the overwriting does not touch: the honest
prover's later computations (the fold of the index at the shared point, ω) read that witness.
A coarser reading (what a masked block really reads) is had by Ior/KnowCollRulesChainConseq.lean:
`freshFor_conseq`.

In the three statements `Hides` is a premise (`S.dO.Nn.Hides ..`, `S.dU.Nn.Hides ..`,
`S.dW.Nn.Hides ..`). `N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with
`bud S` and all messages m and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd`
equal that of `N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of
S.

Limits: this file does not say that senders with these properties exist (under `T.Places`, T an
`LdLinP.Std` (Cb/Ld/LdLinStd.lean), and the three layouts' `OK` the standard senders have them:
Cb/Ld/LdLinStdFresh.lean). It says nothing on the closing's own links. It says nothing on batches.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChain
import Cb.Ld.LdSendFreshProofs
import Cb.Ld.LdSendBlind
import Ior.KnowCollRulesChainConseq

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- A condition on the senders: no later family's messages read an earlier family's witness. -/
structure LdLinP.Snd.Apart {E ι κ J Y : Type} [Field E] {P : LdLinP E ι κ J Y} (S : P.Snd) :
    Prop where
  putU : ∀ (w w' : P.W2) k, w'.1 = w.1 → S.dU.put w' k = S.dU.put w k
  putO : ∀ (w w' : P.W4) k, w'.1 = w.1 → S.dO.put w' k = S.dO.put w k

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- Masks in the family of Ω. -/
def ldLinC_freshO : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd)
      (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : S.dO.Own Mb) (Kc : Type)
      (rd : P.NO.Msg → P.W3 → Kc) (put : Mb → Kc → Kc),
    U.Laws P.SdO rd put → S.dO.Nn.Hides (P.NO.budT S.tO) →
    (P.chain on0 S εf).FreshFor (fun v : P.W5 => rd (P.NO.msgs v.1) v.2) Mb put

/-- Masks in the family of G_u. -/
def ldLinC_freshU : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd)
      (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : S.dU.Own Mb) (Kc : Type)
      (rd : P.NU.Msg → P.W1 → Kc) (put : Mb → Kc → Kc) (keep : Kc → P.W1),
    (∀ m w, keep (rd m w) = w) → (∀ M k, keep (put M k) = keep k) →
    U.Laws P.SdU rd put → S.dU.Nn.Hides (P.NU.budT S.tU) → S.dO.Laws P.backO → S.Apart →
    (P.chain on0 S εf).FreshFor
      (fun v : P.W5 => (v.1, rd (P.NU.msgs v.2.1) v.2.2)) Mb (fun M k => (k.1, put M k.2))

/-- Masks in the family of W. -/
def ldLinC_freshW : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd)
      (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : S.dW.Own Mb) (Kc : Type)
      (rd : P.NW.Msg → P.W0 → Kc) (put : Mb → Kc → Kc) (keep : Kc → P.W0),
    (∀ m w, keep (rd m w) = w) → (∀ M k, keep (put M k) = keep k) → U.Laws P.SdW rd put →
    S.dW.Nn.Hides (P.NW.budT S.tW) → S.dU.Laws P.backU → S.dO.Laws P.backO → S.Apart →
    (P.chain on0 S εf).FreshFor (fun v : P.W5 => (v.1, v.2.1, rd (P.NW.msgs v.2.2.1) v.2.2.2))
      Mb (fun M k => (k.1, k.2.1, put M k.2.2))

end
end Spec

theorem LdLinP.restU {E ι κ J Y : Type} (P : LdLinP E ι κ J Y) (S : P.Snd)
    (h : S.dU.Laws P.backU) (w : P.W2) : S.dU.rest w = w.2 :=
  congrArg Prod.snd (h.back w (Classical.arbitrary _))

theorem LdLinP.restO {E ι κ J Y : Type} (P : LdLinP E ι κ J Y) (S : P.Snd)
    (h : S.dO.Laws P.backO) (w : P.W4) : S.dO.rest w = w.2 :=
  congrArg Prod.snd (h.back w (Classical.arbitrary _))

/-- ζ hands the witness on: blind for every reading -/
theorem LdLinP.blindZeta {E ι κ J Y : Type} [Field E] [Fintype E] (P : LdLinP E ι κ J Y) {Kc : Type}
    (kc : P.W5 → Kc) (Mb : Type) (put : Mb → Kc → Kc) :
    P.hZeta.Blind kc kc Mb put put :=
  blind_peek _ _ _ _ _ _ P.vZeta _ _ _ _ kc kc Mb put put fun _ _ _ _ _ h => ⟨rfl, h⟩

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinC_freshO : Spec.ldLinC_freshO E ι κ J Y := by
  intro P on0 εf S Mb _ _ U Kc rd put hU hH
  refine (freshFor_snoc _ P.lkZeta _ Mb put).2
    (Or.inr ⟨Kc, fun v : P.W5 => rd (P.NO.msgs v.1) v.2, put, ?_, P.blindZeta _ Mb put⟩)
  refine (freshFor_snoc _ (P.lkO S) _ Mb put).2 (Or.inl ?_)
  exact ldSendFam_fresh E P.NO P.SdO P.X4 P.W4 P.W3 P.E4 S.dO S.tO _ Mb U Kc rd put hU hH

theorem ldLinC_freshU : Spec.ldLinC_freshU E ι κ J Y := by
  intro P on0 εf S Mb _ _ U Kc rd put keep hk1 hk2 hU hH hLO hA
  refine (freshFor_snoc _ P.lkZeta _ Mb _).2
    (Or.inr ⟨_, fun v : P.W5 => (v.1, rd (P.NU.msgs v.2.1) v.2.2), fun M k => (k.1, put M k.2),
        ?_, P.blindZeta _ Mb _⟩)
  refine (freshFor_snoc _ (P.lkO S) _ Mb _).2
    (Or.inr
      ⟨_, fun w : P.W4 => (w.1, rd (P.NU.msgs w.2.1) w.2.2), fun M k => (k.1, put M k.2), ?_, ?_⟩)
  · refine (freshFor_snoc _ (P.lkLoc on0) _ Mb _).2
      (Or.inr ⟨Kc, fun v : P.W3 => rd (P.NU.msgs v.1) v.2, put, ?_, ?_⟩)
    · refine (freshFor_snoc _ (P.lkU on0 S) _ Mb put).2 (Or.inl ?_)
      exact ldSendFam_fresh E P.NU P.SdU P.X2 P.W2 P.W1 P.E1 S.dU S.tU _ Mb U Kc rd put hU hH
    · refine blind_peek _ _ _ _ _ _ P.vLoc _ _ _ _ _ _ Mb _ _ fun w w' M x c h => ?_
      have e : w'.2 = w.2 := by
        have h' := congrArg keep h
        rwa [hk1, hk2, hk1] at h'
      exact ⟨by rw [e], Prod.ext (by rw [e]) h⟩
  · refine ldSendFam_blind E P.NO P.SdO P.X4 P.W4 P.W3 P.E4 S.dO _ _ Mb _ _ _ _
      (fun w w' M h k => hA.putO w w' k (Prod.mk.inj h).1) fun w w' M nw h => ?_
    rw [P.restO S hLO, P.restO S hLO]
    exact Prod.ext rfl (Prod.mk.inj h).2

theorem ldLinC_freshW : Spec.ldLinC_freshW E ι κ J Y := by
  intro P on0 εf S Mb _ _ U Kc rd put keep hk1 hk2 hU hH hLU hLO hA
  refine (freshFor_snoc _ P.lkZeta _ Mb _).2
    (Or.inr ⟨_, fun v : P.W5 => (v.1, v.2.1, rd (P.NW.msgs v.2.2.1) v.2.2.2),
        fun M k => (k.1, k.2.1, put M k.2.2), ?_, P.blindZeta _ Mb _⟩)
  refine (freshFor_snoc _ (P.lkO S) _ Mb _).2
    (Or.inr ⟨_, fun w : P.W4 => (w.1, w.2.1, rd (P.NW.msgs w.2.2.1) w.2.2.2),
        fun M k => (k.1, k.2.1, put M k.2.2), ?_, ?_⟩)
  · refine (freshFor_snoc _ (P.lkLoc on0) _ Mb _).2
      (Or.inr
        ⟨_, fun v : P.W3 => (v.1, rd (P.NW.msgs v.2.1) v.2.2), fun M k => (k.1, put M k.2), ?_, ?_⟩)
    · refine (freshFor_snoc _ (P.lkU on0 S) _ Mb _).2
        (Or.inr ⟨_, fun w : P.W2 => (w.1, rd (P.NW.msgs w.2.1) w.2.2),
            fun M k => (k.1, put M k.2), ?_, ?_⟩)
      · refine (freshFor_snoc _ (P.lkPt on0 εf) _ Mb _).2
          (Or.inr ⟨Kc, fun v : P.W1 => rd (P.NW.msgs v.1) v.2, put, ?_, ?_⟩)
        · refine (freshFor_snoc _ (P.lkW on0 S) _ Mb put).2 (Or.inl ?_)
          exact ldSendFam_fresh E P.NW P.SdW P.X0 P.WA P.W0 P.E0 S.dW S.tW _ Mb U Kc rd put hU hH
        · refine blind_peek _ _ _ _ _ _ P.vPt _ _ _ _ _ _ Mb _ _ fun w w' M x c h => ?_
          have e : w'.2 = w.2 := by
            have h' := congrArg keep h
            rwa [hk1, hk2, hk1] at h'
          exact ⟨rfl, Prod.ext (by rw [e]) h⟩
      · refine ldSendFam_blind E P.NU P.SdU P.X2 P.W2 P.W1 P.E1 S.dU _ _ Mb _ _ _ _
          (fun w w' M h k => hA.putU w w' k (Prod.mk.inj h).1) fun w w' M nw h => ?_
        rw [P.restU S hLU, P.restU S hLU]
        exact Prod.ext rfl (Prod.mk.inj h).2
    · refine blind_peek _ _ _ _ _ _ P.vLoc _ _ _ _ _ _ Mb _ _ fun w w' M x c h => ?_
      have e : w'.2.2 = w.2.2 := by
        have h' := congrArg keep (congrArg Prod.snd h)
        rwa [hk1, hk2, hk1] at h'
      exact ⟨by rw [e], Prod.ext (by rw [e]) h⟩
  · refine ldSendFam_blind E P.NO P.SdO P.X4 P.W4 P.W3 P.E4 S.dO _ _ Mb _ _ _ _
      (fun w w' M h k => hA.putO w w' k (Prod.mk.inj h).1) fun w w' M nw h => ?_
    rw [P.restO S hLO, P.restO S hLO]
    exact Prod.ext rfl (Prod.mk.inj h).2

end
end Cb
