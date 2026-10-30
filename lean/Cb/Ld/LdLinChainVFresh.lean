-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChainVFresh.lean: three statements on the core of the interactive test that an encoded
index meets linear constraints, for a batch (several instances proved in one run), and two generic
lemmas. Under the hypotheses of its statements, masks that ride in the core of the test for linear
constraints are fresh after the core, for sets of slots.

Statements (`Iop.Spec.chainV_fresh_conseq`, `Iop.Spec.blindV_conseq`; `Cb.Spec.ldLinV_freshW`,
`Cb.Spec.ldLinV_freshU`, `Cb.Spec.ldLinV_freshO`) and proofs. The analogue for batches of
Cb/Ld/LdLinChainFresh.lean.
The three sendings (`sW`, `sU`, `sO`), W, G_u, Ω, u and ω are told in the head of
Cb/Ld/LdLinChain.lean.
The slots: j : `Fin N` (`BTr`, Iop/Batch.lean). In this head the shared part and a slot are the
parts of the honest prover (`SStratR`, `LStratR`, Ior/BatchSeqZk.lean; `HonestV.strat0`,
`HonestV.strat`, Ior/LinkV.lean); what the shared part of the prover holds: `JV.W0`,
Cb/Ld/LdLinChainV.lean.

Why: Cb/Ld/LdLinBHonTop.lean takes the closing as a chain cZ that stands behind the core for sets of
slots (cZ.OkFromV core). For a masked link of the closing (a splitting, say) that condition asks:
its masks are fresh after all that comes before it (Cb/Ld/LdLinChainVMask.lean: `FreshForV`, by
recursion from `FreshV`, on which see (1) below). This file has the part of that condition which
concerns the core `P.chainV` (Cb/Ld/LdLinBHon.lean).
What is left to a closing: its own links before the masked one do not look at these masks
(`freshForV_snoc`, second case), and a coarser reading (`Spec.chainV_fresh_conseq`).

Main names, each (it concludes `FreshForV` of `P.chainV`) under the hypotheses of its statement
(`Own.Laws`, `Hides`, the laws of keep or of nm, `Laws` of the later senders and, for shared masks,
of the family's own sender, `S.Apart`; ι and Mb are nonempty):
  `Spec.ldLinV_freshW`: a slot's masks, in a member of the family that the slot sends with W: fresh
    for each slot, jointly over the slots. The shared part has no mask; all that it holds may be
    read. A slot's reading at the end of the core: all of the witnesses of Ω's and G_u's families,
    and rd (messages of W's family) (the witness before), as for one instance.
  `Spec.ldLinV_freshU`: shared masks, in a member of the family sent with G_u: one value for all
    slots. Read of what the shared part holds: all that it held before the sending, the samples, and
    rd of the family's messages (not the words as sent, not the encoding randomness); then the
    locations, all of Ω's family, ζ. Read of a slot's witness: the whole witness one step before the
    sending (`P.W1` at `P.J1`, Cb/Ld/LdLinChain.lean), and a part nm (rd ..) of the family's
    messages that the overwriting does not move (the slot may read u, not the masks); then all of
    Ω's family.
  `Spec.ldLinV_freshO`: shared masks in a member of the family sent with Ω: likewise (`P.W3`).
In the last two: the shared part runs a sender on a witness of its own, whose part "the witness
before" is a fixed value (`S.dU.w0.2`, `S.dO.w0.2`); rd is read at that value on both sides.

Limits: that senders with these properties exist is not said here (under `T.Places`, T an
`LdLinP.Std` (Cb/Ld/LdLinStd.lean), and the three layouts' `OK` the standard senders have them:
Cb/Ld/LdLinStdFresh.lean). This file says nothing on the closing's own links. x₄, y₄, x₂, y₂: any
values (a sender reads neither its explicit part nor the oracles).
Two declarations (by a reading of a print of the technical report; not held against the report's
latest edition).
(1) Stated here for sets of slots: "Still uniform, given all that is shown to a set of slots
together" is the form stated here, for batches, of the technical report's lemma on masks sent in
advance (as in Cb/Ld/LdSendFreshSh.lean) (exactly: `FreshV`, Ior/LinkVMasked.lean); the report has a
form of that lemma for sets of instances; whether it is the same is not held here.
(2) Narrower than the report: the readings here forget the words as sent and the encoding
randomness of the whole family; its hypothesis speaks only of the oracle message that holds the
masks (its mask coordinates, its pad, its randomness).

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdLinBHonTop
import Cb.Ld.LdSendFreshSh
import Ior.LinkVMaskedRulesShared
import Ior.LinkVMaskedRulesProofs

set_option autoImplicit false

namespace Iop
open Prob

namespace Spec
open IOR

/-- Coarser readings at the end of a link that does not look at the masks. -/
def blindV_conseq : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (W0 Wj W0' Wj' : Type)
      (H : R.HonestV A W0 Wj W0' Wj') (K0 Kj K0' Kj' K0'' Kj'' : Type) (k0 : W0 → K0) (kj : Wj → Kj)
      (k0' : W0' → K0') (kj' : Wj' → Kj') (g0 : K0' → K0'') (gj : Kj' → Kj'') (M0 Mj : Type)
      (put0 : M0 → K0 → K0) (putj : Mj → Kj → Kj) (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj')
      (put0'' : M0 → K0'' → K0'') (putj'' : Mj → Kj'' → Kj''),
    (∀ M k, g0 (put0' M k) = put0'' M (g0 k)) → (∀ M k, gj (putj' M k) = putj'' M (gj k)) →
    H.BlindV k0 kj k0' kj' M0 Mj put0 putj put0' putj' →
    H.BlindV k0 kj (fun w => g0 (k0' w)) (fun w => gj (kj' w)) M0 Mj put0 putj put0'' putj''

/-- Coarser readings at the end of a chain. -/
def chainV_fresh_conseq : Prop :=
  ∀ (K : Type) (N : ℕ) (A B : Joint K) (VA : JV N A) (VB : JV N B) (c : ChainV K N VA VB)
      (K0 Kj K0' Kj' : Type) (k0 : VB.W0 → K0) (kj : B.W → Kj) (g0 : K0 → K0') (gj : Kj → Kj')
      (M0 : Type) [Fintype M0] [Nonempty M0] (Mj : Type) [Fintype Mj] [Nonempty Mj]
      (put0 : M0 → K0 → K0) (putj : Mj → Kj → Kj) (put0' : M0 → K0' → K0') (putj' : Mj → Kj' → Kj'),
    (∀ M k, g0 (put0 M k) = put0' M (g0 k)) → (∀ M k, gj (putj M k) = putj' M (gj k)) →
    c.FreshForV k0 kj M0 put0 Mj putj →
    c.FreshForV (fun w => g0 (k0 w)) (fun w => gj (kj w)) M0 put0' Mj putj'

end Spec

open IOR

theorem blindV_conseq :
    Spec.blindV_conseq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g0 gj _ _ _ _ _ _ _ _ h0 hj h =>
  ⟨fun w0 v0 M c0 σ hk => (congrArg g0 (h.shared w0 v0 M c0 σ hk)).trans (h0 _ _),
    fun w0 v0 wj vj M Ms x c ρ hk hkj =>
      ⟨(h.slot w0 v0 wj vj M Ms x c ρ hk hkj).1,
        (h.slot w0 v0 wj vj M Ms x c ρ hk hkj).2.1,
        (congrArg gj (h.slot w0 v0 wj vj M Ms x c ρ hk hkj).2.2).trans (hj _ _)⟩⟩

theorem chainV_fresh_conseq : Spec.chainV_fresh_conseq := by
  intro K N A B VA VB c K0 Kj K0' Kj' k0 kj g0 gj M0 _ _ Mj _ _ put0 putj put0' putj' h0 hj h
  cases c with
  | one v =>
      exact (ChainV.freshForV_one v _ _ M0 put0' Mj putj').2
        (freshV_conseq _ _ _ _ _ _ _ _ _ _ v.hv _ _ N _ _ _ _ _ _ k0 kj g0 gj M0 Mj put0 putj put0'
          putj' (fun _ _ _ h => h) (fun _ _ _ h => h) h0 hj
          ((ChainV.freshForV_one v k0 kj M0 put0 Mj putj).1 h))
  | snoc c v =>
      refine (ChainV.freshForV_snoc c v _ _ M0 put0' Mj putj').2 ?_
      rcases (ChainV.freshForV_snoc c v k0 kj M0 put0 Mj putj).1
        h with h | ⟨K0a, Kja, k0a, kja, put0a, putja, h1, h2⟩
      · exact Or.inl
          (freshV_conseq _ _ _ _ _ _ _ _ _ _ v.hv _ _ N _ _ _ _ _ _ k0 kj g0 gj M0 Mj put0 putj
            put0' putj' (fun _ _ _ h => h) (fun _ _ _ h => h) h0 hj h)
      · exact Or.inr
          ⟨K0a, Kja, k0a, kja, put0a, putja, h1,
            blindV_conseq _ _ _ _ _ _ _ _ _ _ v.hv _ _ _ _ _ _ k0a kja k0 kj g0 gj M0 Mj put0a putja
              put0 putj put0' putj' h0 hj h2⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- A slot's masks, in the family of W. -/
def ldLinV_freshW : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (Mb : Type) [Fintype Mb] [Nonempty Mb] (U : S.dW.Own Mb)
      (Kc : Type) (rd : P.NW.Msg → P.W0 → Kc) (put : Mb → Kc → Kc) (keep : Kc → P.W0),
    (∀ m w, keep (rd m w) = w) → (∀ M k, keep (put M k) = keep k) → U.Laws P.SdW rd put →
    S.dW.Nn.Hides (P.NW.budT S.tW) → S.dU.Laws P.backU → S.dO.Laws P.backO → S.Apart →
    (P.chainV S qa N on0 εf).FreshForV (fun s : P.Sh6 => s)
      (fun v : P.W5 => (v.1, v.2.1, rd (P.NW.msgs v.2.2.1) v.2.2.2)) Unit (fun _ k => k)
      Mb (fun M k => (k.1, k.2.1, put M k.2.2))

/-- Shared masks, in the family of Ω. -/
def ldLinV_freshO : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (_x₄ : P.X4) (_y₄ : P.E4.Str) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : S.dO.Own Mb) (Kc Kn : Type) (rd : P.NO.Msg → P.W3 → Kc)
      (put : Mb → Kc → Kc) (nm : Kc → Kn),
    (∀ M k, nm (put M k) = nm k) → U.Laws P.SdO rd put → S.dO.Nn.Hides (P.NO.budT S.tO) →
    S.dO.Laws P.backO → S.Apart →
    (P.chainV S qa N on0 εf).FreshForV
      (fun s : P.Sh6 => ((s.1.1, s.1.2.1, rd (P.NO.msgs s.1.2.2.2) S.dO.w0.2), s.2))
      (fun v : P.W5 => (v.2, nm (rd (P.NO.msgs v.1) S.dO.w0.2))) Mb
      (fun M k => ((k.1.1, k.1.2.1, put M k.1.2.2), k.2)) Unit (fun _ k => k)

/-- Shared masks, in the family of G_u. -/
def ldLinV_freshU : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (_x₂ : P.X2) (_y₂ : P.E1.Str) (Mb : Type) [Fintype Mb]
      [Nonempty Mb] (U : S.dU.Own Mb) (Kc Kn : Type) (rd : P.NU.Msg → P.W1 → Kc)
      (put : Mb → Kc → Kc) (nm : Kc → Kn),
    (∀ M k, nm (put M k) = nm k) → U.Laws P.SdU rd put → S.dU.Nn.Hides (P.NU.budT S.tU) →
    S.dU.Laws P.backU → S.dO.Laws P.backO → S.Apart →
    (P.chainV S qa N on0 εf).FreshForV
      (fun s : P.Sh6 =>
        ((((s.1.1.1.1, s.1.1.1.2.1, rd (P.NU.msgs s.1.1.1.2.2.2) S.dU.w0.2), s.1.1.2), s.1.2), s.2))
      (fun v : P.W5 => (v.1, (v.2.2, nm (rd (P.NU.msgs v.2.1) S.dU.w0.2)))) Mb
      (fun M k => ((((k.1.1.1.1, k.1.1.1.2.1, put M k.1.1.1.2.2), k.1.1.2), k.1.2), k.2)) Unit
      (fun _ k => k)

end
end Spec

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinV_freshW : Spec.ldLinV_freshW E ι κ J Y := by
  intro P on0 εf N S qa Mb _ _ U Kc rd put keep hk1 hk2 hU hH hLU hLO hA
  unfold LdLinP.chainV
  refine (ChainV.freshForV_snoc _ (P.lvZeta S qa N) _ _ Unit _ Mb _).2
    (Or.inr ⟨P.Sh5, _, fun s => s, fun v : P.W5 => (v.1, v.2.1, rd (P.NW.msgs v.2.2.1) v.2.2.2),
        fun _ k => k, fun M k => (k.1, k.2.1, put M k.2.2), ?_, ?_⟩)
  swap
  · exact blindV_shared _ _ _ _ P.zeta _ _ _ _ P.hZeta P.sZeta0 _ _ _ _ _ _ _ _ Unit Mb _ _ _ _
      (fun w0 v0 _ c ρ h => by obtain rfl : v0 = w0 := h; exact ⟨rfl, rfl⟩) (P.blindZeta _ Mb _)
  refine (ChainV.freshForV_snoc _ (P.lvO S qa N) _ _ Unit _ Mb _).2
    (Or.inr ⟨P.Sh4, _, fun s => s, fun w : P.W4 => (w.1, w.2.1, rd (P.NW.msgs w.2.2.1) w.2.2.2),
        fun _ k => k, fun M k => (k.1, k.2.1, put M k.2.2), ?_, ?_⟩)
  swap
  · refine ldSendFam_blindSh E P.NO P.SdO P.X4 P.W4 P.W3 P.Sh4 P.E4 S.dO (P.wO S) _ _ _ _ Unit Mb _
      _ _ _ _ _ _ _ (fun s s' _ h k => by obtain rfl : s' = s := h; rfl)
      (fun s s' _ z h => by obtain rfl : s' = s := h; rfl)
      (fun w w' M h k => hA.putO w w' k (Prod.mk.inj h).1) fun w w' M nw h => ?_
    rw [P.restO S hLO, P.restO S hLO]
    exact Prod.ext rfl (Prod.mk.inj h).2
  refine (ChainV.freshForV_snoc _ (P.lvLoc S qa N on0) _ _ Unit _ Mb _).2
    (Or.inr ⟨P.Sh3, _, fun s => s, fun v : P.W3 => (v.1, rd (P.NW.msgs v.2.1) v.2.2), fun _ k => k,
        fun M k => (k.1, put M k.2), ?_, ?_⟩)
  swap
  · refine blindV_shared _ _ _ _ P.loc _ _ _ _ P.hLoc P.sLoc0 _ _ _ _ _ _ _ _ Unit Mb _ _ _ _
      (fun w0 v0 _ c ρ h => by obtain rfl : v0 = w0 := h; exact ⟨rfl, rfl⟩) ?_
    refine blind_peek _ _ _ _ _ _ P.vLoc _ _ _ _ _ _ Mb _ _ fun w w' M x c h => ?_
    have e : w'.2.2 = w.2.2 := by
      have h' := congrArg keep (congrArg Prod.snd h)
      rwa [hk1, hk2, hk1] at h'
    exact ⟨by rw [e], Prod.ext (by rw [e]) h⟩
  refine (ChainV.freshForV_snoc _ (P.lvU S qa N on0) _ _ Unit _ Mb _).2
    (Or.inr ⟨P.Sh2, _, fun s => s, fun w : P.W2 => (w.1, rd (P.NW.msgs w.2.1) w.2.2), fun _ k => k,
        fun M k => (k.1, put M k.2), ?_, ?_⟩)
  swap
  · refine ldSendFam_blindSh E P.NU P.SdU P.X2 P.W2 P.W1 P.Sh2 P.E1 S.dU (P.wU S) _ _ _ _ Unit Mb _
      _ _ _ _ _ _ _ (fun s s' _ h k => by obtain rfl : s' = s := h; rfl)
      (fun s s' _ z h => by obtain rfl : s' = s := h; rfl)
      (fun w w' M h k => hA.putU w w' k (Prod.mk.inj h).1) fun w w' M nw h => ?_
    rw [P.restU S hLU, P.restU S hLU]
    exact Prod.ext rfl (Prod.mk.inj h).2
  refine (ChainV.freshForV_snoc _ (P.lvPt S qa N on0 εf) _ _ Unit _ Mb _).2
    (Or.inr
      ⟨P.Sh0, Kc, fun s => s, fun v : P.W1 => rd (P.NW.msgs v.1) v.2, fun _ k => k, put, ?_, ?_⟩)
  swap
  · refine blindV_shared _ _ _ _ P.pt _ _ _ _ P.hPt P.sPt0 _ _ _ _ _ _ _ _ Unit Mb _ _ _ _
      (fun w0 v0 _ c ρ h => by obtain rfl : v0 = w0 := h; exact ⟨rfl, rfl⟩) ?_
    refine blind_peek _ _ _ _ _ _ P.vPt _ _ _ _ _ _ Mb _ _ fun w w' M x c h => ?_
    have e : w'.2 = w.2 := by
      have h' := congrArg keep h
      rwa [hk1, hk2, hk1] at h'
    exact ⟨rfl, Prod.ext (by rw [e]) h⟩
  refine (ChainV.freshForV_snoc _ (P.lvW S qa N on0) _ _ Unit _ Mb _).2 (Or.inl ?_)
  exact ldSendFam_freshLoc E P.NW P.SdW P.X0 P.WA P.W0 P.Sh0 P.E0 S.dW S.tW N _ Mb U Kc _
    rd put (fun s => s) hU hH

omit [Fintype E] [Nonempty ι] in
/-- Under `hA` (`S.Apart`) and `hV`: on tied statements a slot's witness gives the messages that the
shared part's own witness gives. -/
theorem LdLinP.putU_eq (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (N : ℕ)
    (S : P.Snd) (qa : Finset P.Ea.Pos → Prop) (hA : S.Apart) (x : P.X2) (y : P.E1.Str)
    (w : P.Sh2 × P.W2) (hV : (P.V2 S qa N on0).rel x y w) (k : S.dU.Mk) :
    S.dU.put w.2 k = S.dU.put (P.wU S w.1) k := by
  refine hA.putU _ _ k ?_
  have h1 : w.2.1 = foldAll x.2.1 w.2.2.2.1 := hV.1.2
  have h2 : w.2.2.2.1 = w.1.1.1.2 := hV.2.1.1.2
  have h3 : x.2 = w.1.2 := hV.2.2
  show w.2.1 = foldAll w.1.2.1 w.1.1.1.2
  rw [h1, h2, h3]

omit [Fintype E] [Fintype ι] [Nonempty ι] in
theorem LdLinP.putO_eq [Fintype ι] (P : LdLinP E ι κ J Y) (N : ℕ) (S : P.Snd)
    (qa : Finset P.Ea.Pos → Prop) (hA : S.Apart) (x : P.X4) (y : P.E4.Str) (w : P.Sh4 × P.W4)
    (hV : (P.V4 S qa N).rel x y w) (k : S.dO.Mk) :
    S.dO.put w.2 k = S.dO.put (P.wO S w.1) k := by
  refine hA.putO _ _ k ?_
  have h1 : w.2.1 = P.D.omOf (P.D.X.view w.2.2.2.2.1) x.1.1.2 := hV.1.2.2.2.2.2.2.2.2
  have h2 : w.2.2.2.2.1 = w.1.1.1.1.1.2 := hV.2.1.1.1.1
  have h3 : x.1.1.2 = w.1.1.1.2 := hV.2.1.1.2
  show w.2.1 = P.D.omOf (P.D.X.view w.1.1.1.1.1.2) w.1.1.1.2
  rw [h1, h2, h3]

theorem ldLinV_freshO : Spec.ldLinV_freshO E ι κ J Y := by
  intro P on0 εf N S qa x₄ y₄ Mb _ _ U Kc Kn rd put nm hnm hU hH hLO hA
  unfold LdLinP.chainV
  refine (ChainV.freshForV_snoc _ (P.lvZeta S qa N) _ _ Mb _ Unit _).2
    (Or.inr ⟨_, _, fun s : P.Sh5 => (s.1, s.2.1, rd (P.NO.msgs s.2.2.2) S.dO.w0.2),
        fun v : P.W5 => (v.2, nm (rd (P.NO.msgs v.1) S.dO.w0.2)),
        fun M k => (k.1, k.2.1, put M k.2.2), fun _ k => k, ?_, ?_⟩)
  swap
  · exact blindV_shared _ _ _ _ P.zeta _ _ _ _ P.hZeta P.sZeta0 _ _ _ _ _ _ _ _ Mb Unit _ _ _ _
      (fun w0 v0 M c ρ h => ⟨rfl, Prod.ext h rfl⟩) (P.blindZeta _ Unit _)
  refine (ChainV.freshForV_snoc _ (P.lvO S qa N) _ _ Mb _ Unit _).2 (Or.inl ?_)
  have hr : ∀ s : P.Sh4, S.dO.rest (P.wO S s) = S.dO.w0.2 := fun s => P.restO S hLO _
  exact ldSendFam_freshSh E P.NO P.SdO P.X4 P.W4 P.W3 P.Sh4 P.E4 S.dO S.tO N (P.wO S)
    (P.V4 S qa N).rel x₄ y₄ Mb U Kc _ _ rd put _ _ _ (fun s σ k => (s, σ, k))
    (fun _ w k => (S.dO.rest w, nm k)) hU hH (fun x y w hV k => P.putO_eq N S qa hA x y w hV k)
    (fun s σ f v => by rw [hr]) (fun _ _ _ _ => rfl) (fun x y w v _ => by rw [hr])
    (fun _ w M k => congrArg (Prod.mk (S.dO.rest w)) (hnm M k))

theorem ldLinV_freshU : Spec.ldLinV_freshU E ι κ J Y := by
  intro P on0 εf N S qa x₂ y₂ Mb _ _ U Kc Kn rd put nm hnm hU hH hLU hLO hA
  unfold LdLinP.chainV
  refine (ChainV.freshForV_snoc _ (P.lvZeta S qa N) _ _ Mb _ Unit _).2
    (Or.inr ⟨_, _,
        fun s : P.Sh5 => (((s.1.1.1, s.1.1.2.1, rd (P.NU.msgs s.1.1.2.2.2) S.dU.w0.2), s.1.2), s.2),
        fun v : P.W5 => (v.1, (v.2.2, nm (rd (P.NU.msgs v.2.1) S.dU.w0.2))),
        fun M k => (((k.1.1.1, k.1.1.2.1, put M k.1.1.2.2), k.1.2), k.2),
        fun _ k => k, ?_, ?_⟩)
  swap
  · exact blindV_shared _ _ _ _ P.zeta _ _ _ _ P.hZeta P.sZeta0 _ _ _ _ _ _ _ _ Mb Unit _ _ _ _
      (fun w0 v0 M c ρ h => ⟨rfl, Prod.ext h rfl⟩) (P.blindZeta _ Unit _)
  refine (ChainV.freshForV_snoc _ (P.lvO S qa N) _ _ Mb _ Unit _).2
    (Or.inr ⟨_, _, fun s : P.Sh4 => ((s.1.1, s.1.2.1, rd (P.NU.msgs s.1.2.2.2) S.dU.w0.2), s.2),
        fun w : P.W4 => (w.1, (w.2.2, nm (rd (P.NU.msgs w.2.1) S.dU.w0.2))),
        fun M k => ((k.1.1, k.1.2.1, put M k.1.2.2), k.2), fun _ k => k, ?_, ?_⟩)
  swap
  · refine ldSendFam_blindSh E P.NO P.SdO P.X4 P.W4 P.W3 P.Sh4 P.E4 S.dO (P.wO S) _ _ _ _ Mb Unit _
      _ _ _ _ _ _ _ (fun s s' M h k => ?_) (fun s s' M z h => Prod.ext h rfl)
      (fun w w' _ h k => hA.putO w w' k (Prod.mk.inj h).1) fun w w' _ nw h => ?_
    · have e : s'.1.1 = s.1.1 := congrArg (fun z => z.1.1) h
      have e' : P.wO S s' = P.wO S s := by
        unfold LdLinP.wO
        rw [e]
      rw [e']
    · rw [P.restO S hLO, P.restO S hLO]
      exact Prod.ext rfl (Prod.mk.inj h).2
  refine (ChainV.freshForV_snoc _ (P.lvLoc S qa N on0) _ _ Mb _ Unit _).2
    (Or.inr ⟨_, _, fun s : P.Sh3 => (s.1, s.2.1, rd (P.NU.msgs s.2.2.2) S.dU.w0.2),
        fun v : P.W3 => (v.2, nm (rd (P.NU.msgs v.1) S.dU.w0.2)),
        fun M k => (k.1, k.2.1, put M k.2.2), fun _ k => k, ?_, ?_⟩)
  swap
  · refine blindV_shared _ _ _ _ P.loc _ _ _ _ P.hLoc P.sLoc0 _ _ _ _ _ _ _ _ Mb Unit _ _ _ _
      (fun w0 v0 M c ρ h => ⟨rfl, Prod.ext h ?_⟩) ?_
    · have e : v0.1 = w0.1 := (Prod.mk.inj h).1
      show ((show (Fin P.t → ι) × Unit from ρ).1,
          fun i =>
            P.D.X.G.mulVec (foldAll v0.1.2.1 v0.1.1.1.2) ((show (Fin P.t → ι) × Unit from ρ).1 i)) =
        ((show (Fin P.t → ι) × Unit from ρ).1,
          fun i =>
            P.D.X.G.mulVec (foldAll w0.1.2.1 w0.1.1.1.2) ((show (Fin P.t → ι) × Unit from ρ).1 i))
      rw [e]
    · refine blind_peek _ _ _ _ _ _ P.vLoc _ _ _ _ _ _ Unit _ _ fun w w' _ x c h => ?_
      have e : w'.2 = w.2 := (Prod.mk.inj h).1
      exact ⟨by rw [e], Prod.ext (by rw [e]) h⟩
  refine (ChainV.freshForV_snoc _ (P.lvU S qa N on0) _ _ Mb _ Unit _).2 (Or.inl ?_)
  have hr : ∀ s : P.Sh2, S.dU.rest (P.wU S s) = S.dU.w0.2 := fun s => P.restU S hLU _
  exact ldSendFam_freshSh E P.NU P.SdU P.X2 P.W2 P.W1 P.Sh2 P.E1 S.dU S.tU N (P.wU S)
    (P.V2 S qa N on0).rel x₂ y₂ Mb U Kc _ _ rd put _ _ _ (fun s σ k => (s, σ, k))
    (fun _ w k => (S.dU.rest w, nm k)) hU hH (fun x y w hV k => P.putU_eq on0 N S qa hA x y w hV k)
    (fun s σ f v => by rw [hr]) (fun _ _ _ _ => rfl) (fun x y w v _ => by rw [hr])
    (fun _ w M k => congrArg (Prod.mk (S.dU.rest w)) (hnm M k))

end
end Cb
