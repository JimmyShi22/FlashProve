-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefFact.lean: from the wide fact on fresh masks to the fact that a masked block needs,
for blocks that read entries.

One statement (`Cb.Spec.segWide_read`) and its proof. A rule of the framework only; nothing of a
text is rendered here.
A fact is a `MaskFact` (Cb/Req1/LdSegFresh.lean). A `MaskFact W` is a reading `kc` of witnesses of
type W into a type `Kc`, a finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`. "Fresh" is
`Chain.FreshGiven`, defined there too.

Why: along a list of moves the wide fact is carried, under the hypotheses of the statements of
Cb/Req1/LdSegCarry.lean (`a.wideFact Rd Rr own Mk val`: the entries in Rd of all messages, encoding
randomness at Rr, the whole further witness; the masks are at the entries with "own"). A masked
block needs a fact in its own parameters (`MaskData.fact`). This rule is for masked blocks with
parameters of one shape:
  what is read of a witness: a vector on names J, cut to a set RdJ of names:
    kc w j = rdJ (messages, further witness) j if RdJ j, and 0 otherwise
  the names J hold the entries of the messages (emb : entries → J, injective); what stands at other
    names (the matrix of an encoded index, say) does not depend on the messages
  own masks: put M k = k overwritten at the names emb (at' i) by ve M i (`Function.extend`),
    at' injective
(The batching of tensor rows: `BattPar.maskData`, Cb/Ld/LdBatt.lean, by `PscPar.maskDataC`,
Cb/Ld/LdPscZk.lean; the assembled lookup: Cb/Ld/LdLkpMaskPut*.lean.)
Another shape of reading: `Spec.segWide_readG`, Cb/Req1/LdSegRefFactG.lean.

Main names:
  `Spec.segWide_read`: for this shape, Mk finite and not empty, after any chain: if the wide fact
    is fresh, with own = the places at' i, val M (at' i) = ve M i, every entry that the block reads
    in Rd, every place read by the block: then the block's fact is fresh.
-/
import Cb.Req1.LdSegCarry

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR IOR.Chain

/-- States, under the hypotheses below: the wide fact gives the fact of a block that reads
entries. -/
def Spec.segWide_read : Prop :=
  ∀ (E Kc : Type) [Field E] (A : Joint Kc) (a : LdStage E Kc) (c : Chain Kc A a.J)
      (base : MaskFact A.W → Prop) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop) (own : a.S.Ent → Prop)
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → a.S.Ent → E) (J I : Type)
      (emb : a.S.Ent → J) (at' : I → a.S.Ent) (ve : Mk → I → E) (RdJ : J → Prop)
      (rdJ : a.S.Msg × a.Wp → J → E) (kc' : a.J.W → J → E) (put' : Mk → (J → E) → J → E),
    Function.Injective emb → Function.Injective at' →
    (∀ m wp n, rdJ (m, wp) (emb n) = a.S.ents m n) →
    (∀ m m' wp j, (∀ n, emb n ≠ j) → rdJ (m, wp) j = rdJ (m', wp) j) →
    (∀ w j, RdJ j → kc' w j = rdJ (a.S.msgs w.1, w.2) j) → (∀ w j, ¬ RdJ j → kc' w j = 0) →
    (∀ M k, put' M k = Function.extend (fun i => emb (at' i)) (ve M) k) →
    (∀ n, own n ↔ ∃ i, at' i = n) → (∀ M i, val M (at' i) = ve M i) →
    (∀ n, RdJ (emb n) → Rd n) → (∀ i, RdJ (emb (at' i))) →
    c.FreshGiven base (a.wideFact Rd Rr own Mk val) → c.FreshGiven base ⟨J → E, kc', Mk, put'⟩

open Classical in
theorem segWide_read : Spec.segWide_read := by
  intro E Kc _ A a c base Rd Rr own Mk _ _ val J I emb at' ve RdJ rdJ kc' put' hemb hat he1 he2 hk1
    hk0 hput hown hval hRd hpl h
  -- the block's reading, computed from the wide reading
  let g : (a.wideFact Rd Rr own Mk val).Kc → J → E := fun k j =>
    if RdJ j then rdJ (k.1, k.2.2) j else 0
  have hinj : Function.Injective fun i => emb (at' i) := fun i i' e => hat (hemb e)
  have hc := freshGiven_conseq Kc A a.J c base (a.wideFact Rd Rr own Mk val) (J → E) g put' ?_ h
  · have ek : (fun w => g ((a.wideFact Rd Rr own Mk val).kc w)) = kc' := by
      funext w j
      show (if RdJ j then rdJ (a.S.cut Rd (a.S.msgs w.1), w.2) j else 0) = kc' w j
      by_cases hj : RdJ j
      · rw [if_pos hj, hk1 w j hj]
        by_cases hn : ∃ n, emb n = j
        · obtain ⟨n, rfl⟩ := hn
          rw [he1, he1]
          show (if Rd ⟨n.1, n.2⟩ then a.S.msgs w.1 n.1 n.2 else 0) = _
          rw [if_pos (hRd n hj)]
          rfl
        · exact he2 _ _ _ _ fun n e => hn ⟨n, e⟩
      · rw [if_neg hj, hk0 w j hj]
    rw [ek] at hc
    exact hc
  · intro M k
    funext j
    rw [hput]
    show (if RdJ j then rdJ (a.S.ow own (val M) k.1, k.2.2) j else 0) = _
    by_cases hi : ∃ i, emb (at' i) = j
    · obtain ⟨i, rfl⟩ := hi
      rw [hinj.extend_apply (ve M) (g k) i, if_pos (hpl i), he1]
      show (if own ⟨(at' i).1, (at' i).2⟩ then val M ⟨(at' i).1, (at' i).2⟩
          else k.1 (at' i).1 (at' i).2) = _
      rw [if_pos ((hown (at' i)).2 ⟨i, rfl⟩)]
      exact hval M i
    · rw [Function.extend_apply' _ _ _ hi]
      show _ = if RdJ j then rdJ (k.1, k.2.2) j else 0
      by_cases hj : RdJ j
      · rw [if_pos hj, if_pos hj]
        by_cases hn : ∃ n, emb n = j
        · obtain ⟨n, rfl⟩ := hn
          rw [he1, he1]
          show (if own ⟨n.1, n.2⟩ then val M ⟨n.1, n.2⟩ else k.1 n.1 n.2) = _
          rw [if_neg fun ho => hi (((hown n).1 ho).elim fun i e => ⟨i, by rw [e]⟩)]
          rfl
        · exact he2 _ _ _ _ fun n e => hn ⟨n, e⟩
      · rw [if_neg hj, if_neg hj]

end Cb
