-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseSplitTop.lean: under the hypotheses of its statements, the test for linear
constraints on the encoded index, with the closing of the plan with two splittings, is a tail: no
hypothesis on fresh masks is left.

In standard terms: the test for linear constraints (a proximity test with claims on the encoded
index) with the closing of Cb/Ld/LdLinCloseDemandS.lean; two hypotheses of that file's last
statement are derived here from conditions on the honest senders.

Statements (`Cb.Spec.ldLinSpTop_O`, `Cb.Spec.ldLinSpTop_U`) and proofs (an assembly).
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge. Both statements conclude `TailTr`.

Main names: `Spec.ldLinSpTop_O`, `Spec.ldLinSpTop_U`.
Cb/Ld/LdLinCloseDemandS.lean (`ldLinPsT_tail`) has the same conclusion from two hypotheses "the wide
fact for the splitting's entry is fresh after the core and the step". Here they are discharged by
Cb/Ld/LdLinCloseSplit.lean (`ldLinSp_entO`, `ldLinSp_entU`, `ldLinSp_entW`), so that what is asked
for the masks is asked of the senders:
  the shared entry κ° is an entry n₀ of a member of the family sent with Ω (`ldLinSpTop_O`) or with
    G_u (`ldLinSpTop_U`); the instance's entry κ_c is an entry n₁ of a member of the family sent
    with W;
  for each of the two senders a split of its coins (Cb/Ld/LdSendFresh.lean: the entry's value; other
    coins; pads) with the conditions `Own.Laws` for the reading (its messages cut to Rd, the witness
    handed on): Cb/Ld/LdLinCloseSplit.lean's `own_laws_cut` gives them from plain conditions;
  both entries lie in Rd; later families' messages do not read earlier families' witnesses
    (`Sn.Apart`, Cb/Ld/LdLinChainFresh.lean).
  No encoding randomness is read (Rr is empty): all splittings come before the tests.
All other hypotheses are those of `ldLinPsT_tail`, word for word; ι, the set of positions of the
encoded index, is nonempty. The conclusion: a tail from the claim on the encoded index to the
trivial statement: in particular honest-verifier exact zero knowledge (`GoodT.exact`:
`Honest.Exact`, Ior/Honest.lean) of the whole test, its two splittings included.

Notation: κ°: `p.k₀`; κ_c: `p.k₁` (Cb/Ld/LdLinClosePlanS.lean); the families sent with Ω, G_u, W:
the signatures `C.NO`, `C.NU`, `C.NW` (Cb/Ld/LdLinClosePre.lean).

Limits: this file does not say that all these hypotheses can be met together. One instance only.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseDemandS

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
/-- The case in which the shared entry rides with Ω. What is stated: the head. -/
def ldLinSpTop_O : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (T : LdLinPsT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₄.O → ℕ) (Rd : C.S.Ent → Prop) (n₀ : C.NO.Ent) (n₁ : C.NW.Ent)
      (U₀ : Sn.dO.Own E) (U₁ : Sn.dW.Own E),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.GcW.msg m) = C.rest sa (C.aM m)) → p.Plain → p.Kept →
    (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) ≠ ⟨p.k₁.o, p.k₁.j⟩ → p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK →
    T.D₃.OK → T.D₄.OK → T.Q'.OK → (∀ V, T.Q'.q V → p.S₄.qFam q₀ b' V) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inr a) ≤ Sn.tO a) →
    (∀ n, p.Rs₀ n → Rd n) → (∀ n, p.Rs₁ n → Rd n) → (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) = C.eO n₀ →
    (⟨p.k₁.o, p.k₁.j⟩ : C.S.Ent) = C.eW n₁ → Rd (C.eO n₀) → Rd (C.eW n₁) → Sn.Apart →
    U₀.Laws C.SdO (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
      (fun u k => (C.NO.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    U₁.Laws C.SdW (fun m w' => (C.NW.cut (fun n => Rd (C.eW n)) m, w'))
      (fun u k => (C.NW.ow (fun n => n = n₁) (fun _ => u) k.1, k.2)) →
    TailTr (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).R
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).H (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).ext
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).P (C.P.q0 qa)

open Classical in
/-- The case in which the shared entry rides with G_u. What is stated: the head. -/
def ldLinSpTop_U : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPs C) (T : LdLinPsT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₄.O → ℕ) (Rd : C.S.Ent → Prop) (n₀ : C.NU.Ent) (n₁ : C.NW.Ent)
      (U₀ : Sn.dU.Own E) (U₁ : Sn.dW.Own E),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.GcW.msg m) = C.rest sa (C.aM m)) → p.Plain → p.Kept →
    (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) ≠ ⟨p.k₁.o, p.k₁.j⟩ → p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK →
    T.D₃.OK → T.D₄.OK → T.Q'.OK → (∀ V, T.Q'.q V → p.S₄.qFam q₀ b' V) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inr a) ≤ Sn.tO a) →
    (∀ n, p.Rs₀ n → Rd n) → (∀ n, p.Rs₁ n → Rd n) → (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) = C.eU n₀ →
    (⟨p.k₁.o, p.k₁.j⟩ : C.S.Ent) = C.eW n₁ → Rd (C.eU n₀) → Rd (C.eW n₁) → Sn.Apart →
    U₀.Laws C.SdU (fun m w' => (C.NU.cut (fun n => Rd (C.eU n)) m, w'))
      (fun u k => (C.NU.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    U₁.Laws C.SdW (fun m w' => (C.NW.cut (fun n => Rd (C.eW n)) m, w'))
      (fun u k => (C.NW.ow (fun n => n = n₁) (fun _ => u) k.1, k.2)) →
    TailTr (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).R
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).H (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).ext
      (C.P.linC on0 Sn εf (C.cZf p.x T.Q C.fqS T.front) d).P (C.P.q0 qa)

end
end Spec

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinSpTop_O : Spec.ldLinSpTop_O E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd n₀ n₁ U₀ U₁ hF hpy hS hr hP hK hne hA h₁ h₂ h₃ h₄ hQ' hq
    hqa i1 i2 i3 i4 r0 r1 e0 e1 d0 d1 hAp l0 l1
  refine ldLinPsT_tail E ι κ J Y C p T on0 εf Sn qa d q₀ ba b' Rd (fun _ => False)
    hF hpy hS hr hP hK hne hA h₁ h₂ h₃ h₄ hQ' hq hqa i1 i2 i3 i4 r0 r1 ?_ ?_
  · rw [e0]
    exact ldLinSp_entO E ι κ J Y C on0 εf Sn p.x C.fqS U₀ Rd (fun _ => False)
      n₀ l0 hS.hidO (fun _ h => h) d0
  · rw [e1]
    exact ldLinSp_entW E ι κ J Y C on0 εf Sn p.x C.fqS U₁ Rd (fun _ => False)
      n₁ l1 hS.hidW hS.sndU hS.sndO hAp (fun _ h => h) d1

theorem ldLinSpTop_U : Spec.ldLinSpTop_U E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd n₀ n₁ U₀ U₁ hF hpy hS hr hP hK hne hA h₁ h₂ h₃ h₄ hQ' hq
    hqa i1 i2 i3 i4 r0 r1 e0 e1 d0 d1 hAp l0 l1
  refine ldLinPsT_tail E ι κ J Y C p T on0 εf Sn qa d q₀ ba b' Rd (fun _ => False)
    hF hpy hS hr hP hK hne hA h₁ h₂ h₃ h₄ hQ' hq hqa i1 i2 i3 i4 r0 r1 ?_ ?_
  · rw [e0]
    exact ldLinSp_entU E ι κ J Y C on0 εf Sn p.x C.fqS U₀ Rd (fun _ => False)
      n₀ l0 hS.hidU hS.sndO hAp (fun _ h => h) d0
  · rw [e1]
    exact ldLinSp_entW E ι κ J Y C on0 εf Sn p.x C.fqS U₁ Rd (fun _ => False)
      n₁ l1 hS.hidW hS.sndU hS.sndO hAp (fun _ h => h) d1

end
end Cb
