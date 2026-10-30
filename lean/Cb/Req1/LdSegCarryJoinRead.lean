-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCarryJoinRead.lean: under the hypotheses of its statement, in a set of facts that is
closed under joining (`MaskFact.JCl X`: join, coarser readings, another type), the wide fact gives
the fact that a masked block needs.

Statements (`Cb.Spec.wideJ_readG`, `Cb.Spec.jcl_narrows`) and proofs. A rule of the framework only.
A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type
`Mk`, and a map `put : Mk → Kc → Kc`. (facts: `IOR.MaskFact`, Cb/Req1/LdSegFresh.lean.)
Names and paths: the wide fact: `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean); masked block:
`Link.GoodM` (Ior/KnowCollRulesChain.lean); the fact that it needs: `MaskData.fact`
(Cb/Req1/LdSegFresh.lean).
Cb/Req1/LdSegRefFactG.lean (`segWide_readG`) goes, after any chain, from the wide fact on fresh
masks to the fact of a block whose reading is any function of entries; its proof uses "a coarser
reading" alone. Cb/Req1/LdSegFreshS.lean closes a set X of facts under join at one reading, coarser
readings, another type for the same masks (`MaskFact.JCl X`). So the same rule holds inside every
closed set.

Why: Cb/Ld/LdMia.lean's clause on a block with masked messages asks that the block's fact lie in the
closure of the pending blocks' wide facts.

Main names:
  `Spec.wideJ_readG`: the premises of `segWide_readG`, word for word, with the type Mk of masks
    finite and non-empty; MaskFact.JCl X (the wide fact) → MaskFact.JCl X (the block's fact).
  `Spec.jcl_narrows`: a.Narrows (MaskFact.JCl X), for every stage a and every set X
    (`LdStage.Narrows`, Cb/Req1/LdSegRefFactG.lean: a set of facts that is closed under
    `segWide_readG`'s rule).

Limits: no instance in this file. Used: `wideJ_readG`, in Cb/Ld/LdBattVSegProofs.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefFactG
import Cb.Req1.LdSegFreshS

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

/-- Under the hypotheses below, the wide fact gives the fact of a block whose reading is any
function of entries: both as members of `MaskFact.JCl X`. -/
def Spec.wideJ_readG : Prop :=
  ∀ (E Kc : Type) [Field E] (a : LdStage E Kc) (X : MaskFact a.J.W → Prop)
      (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E) (J Ix : Type) (plJ : Ix → J)
      (at' : Ix → a.S.Ent) (ve : Mk → Ix → E) (RdJ : J → Prop) (rdJ : a.S.Msg × a.Wp → J → E)
      (kc' : a.J.W → J → E) (put' : Mk → (J → E) → J → E),
    Function.Injective plJ → (∀ m wp i, rdJ (m, wp) (plJ i) = a.S.ents m (at' i)) →
    (∀ m m' wp j, RdJ j → (∀ i, plJ i ≠ j) →
      (∀ n : a.S.Ent, Rd n → ¬ own n → m' n.1 n.2 = m n.1 n.2) → rdJ (m', wp) j = rdJ (m, wp) j) →
    (∀ w j, RdJ j → kc' w j = rdJ (a.S.msgs w.1, w.2) j) → (∀ w j, ¬ RdJ j → kc' w j = 0) →
    (∀ M k, put' M k = Function.extend plJ (ve M) k) → (∀ i, own (at' i)) → (∀ i, Rd (at' i)) →
    (∀ M i, val M (at' i) = ve M i) → (∀ i, RdJ (plJ i)) →
    MaskFact.JCl X (a.wideFact Rd Rr own Mk val) → MaskFact.JCl X ⟨J → E, kc', Mk, put'⟩

open Classical in
theorem wideJ_readG : Spec.wideJ_readG := by
  intro E Kc _ a X Rd Rr own Mk _ _ val J Ix plJ at' ve RdJ rdJ kc' put' hinj hp1 hp2 hk1 hk0
    hput hown hRd hval hpl h
  let g : (a.wideFact Rd Rr own Mk val).Kc → J → E := fun k j =>
    if RdJ j then rdJ (k.1, k.2.2) j else 0
  have hc := MaskFact.JCl.conseq (X := X) (a.wideFact Rd Rr own Mk val) (J → E) g put' ?_ h
  · have ek : (fun w => g ((a.wideFact Rd Rr own Mk val).kc w)) = kc' := by
      funext w j
      show (if RdJ j then rdJ (a.S.cut Rd (a.S.msgs w.1), w.2) j else 0) = kc' w j
      by_cases hj : RdJ j
      · rw [if_pos hj, hk1 w j hj]
        by_cases hi : ∃ i, plJ i = j
        · obtain ⟨i, rfl⟩ := hi
          rw [hp1, hp1]
          show (if Rd ⟨(at' i).1, (at' i).2⟩ then a.S.msgs w.1 (at' i).1 (at' i).2 else 0) = _
          rw [if_pos (hRd i)]
          rfl
        · refine hp2 _ _ _ j hj (fun i e => hi ⟨i, e⟩) fun n hn _ => ?_
          show (if Rd ⟨n.1, n.2⟩ then a.S.msgs w.1 n.1 n.2 else 0) = _
          rw [if_pos hn]
      · rw [if_neg hj, hk0 w j hj]
    rw [ek] at hc
    exact hc
  · intro M k
    funext j
    rw [hput]
    show (if RdJ j then rdJ (a.S.ow own (val M) k.1, k.2.2) j else 0) = _
    by_cases hi : ∃ i, plJ i = j
    · obtain ⟨i, rfl⟩ := hi
      rw [hinj.extend_apply (ve M) (g k) i, if_pos (hpl i), hp1]
      show (if own ⟨(at' i).1, (at' i).2⟩ then val M ⟨(at' i).1, (at' i).2⟩
          else k.1 (at' i).1 (at' i).2) = _
      rw [if_pos (hown i)]
      exact hval M i
    · rw [Function.extend_apply' _ _ _ hi]
      show _ = if RdJ j then rdJ (k.1, k.2.2) j else 0
      by_cases hj : RdJ j
      · rw [if_pos hj, if_pos hj]
        refine hp2 _ _ _ j hj (fun i e => hi ⟨i, e⟩) fun n _ hn => ?_
        show (if own ⟨n.1, n.2⟩ then val M ⟨n.1, n.2⟩ else k.1 n.1 n.2) = _
        rw [if_neg hn]
      · rw [if_neg hj, if_neg hj]

def Spec.jcl_narrows : Prop :=
  ∀ (E Kc : Type) [Field E] (a : LdStage E Kc) (X : MaskFact a.J.W → Prop),
    a.Narrows (MaskFact.JCl X)

theorem jcl_narrows :
    Spec.jcl_narrows := fun E Kc _ a X Rd Rr own Mk _ _ val J G kc' put' hF hU h =>
  wideJ_readG E Kc a X Rd Rr own Mk val J G.Ix G.plJ G.at' G.ve G.RdJ G.rdJ kc' put' hF.inj hF.p1
    hU.p2 hF.k1 hF.k0 hF.put hU.own hU.rd hU.val hF.rdP h

end Cb
