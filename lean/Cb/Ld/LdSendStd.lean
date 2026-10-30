-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStd.lean: the standard sender of any family of oracle messages in the plain format: all
that `Spec.ldSendFam_goodT` (Cb/Ld/LdSendFam.lean) and, for the reading `G.rd`,
`Spec.ldSendFam_fresh` (Cb/Ld/LdSendFresh.lean) ask of a sender, from conditions on codes and
samples and bk (dat w) (rest w) = w alone.

This file defines, from a layout, the data of the honest prover (`Sig.Sender`, Cb/Ld/LdSendFam.lean)
of a reduction that sends several words in one prover message, each sent as a word of its own code;
the layout says which coordinates of each message are read off the witness and which are the
prover's coins.

Definitions, statement (`Cb.Spec.stdSig_all`) and proof.
It widens Cb/Ld/LdSendToyFam.lean (two members: a vector; masks only) to any finite family, and lets
the pad lie in a subfield.

The family (`G.sig`). Any finite set O of names. The message of the member a has three kinds of
entries, told apart by a layout ν a:
  data (Dt a): read off the witness; free entries (Fr a): uniform elements of E, coins of the
  sender: masks of coming blocks; pad (Pd a): uniform elements of the subfield F, for the privacy of
  the member's sample.
  Any of the three may be empty: a member with no free entry only holds data; a member with no data
  is a mask-only message. Each member has its own code (`C a`), sample (`Z a`) and radius (`e a`);
  plain format (`OMsg.plain`, Cb/Ld/LdSig.lean).
The sender (`G.snd dat rest w0`). For any types W, W' of witnesses:
dat : W → the data of all members; rest : W → W': what is handed on; w0 : W: a fixed witness. All
coins are independent (Cb/Ld/LdSendMem.lean: `Sig.Sender.ofMem`).
  `G.back bk`: the extractor: bk (data) (what was handed on).
  `G.rd`, `G.putM`: the reading (data, free entries, what is handed on) for coming masked blocks: it
    forgets the pads and all encoding randomness; all free entries overwritten.
What is asked: `G.Priv`: every member's sample is private under its pad at every seed
(`Sample.Private F`); `G.Zk t`: the encoding of the member a hides `t a` long positions;
of (dat, rest, bk): bk (dat w) (rest w) = w.

Main names:
  `Spec.stdSig_all`: under `G.Priv`, `G.Zk t` and bk (dat w) (rest w) = w:
    the sender's laws for `G.back bk`;
    at every joint seed, however seeds are shared, the joint law of all answers does not depend on
    the witness (`Blind`);
    the family's encoding hides t (in this sense: `(G.snd dat rest w0).Nn.Hides (G.sig.budT t)`);
    two witnesses with the same data give the same messages (so: if dat reads a part of the witness
    alone, so do the messages)
    (in this sense: ∀ (w w' : W) k, dat w' = dat w →
      (G.snd dat rest w0).put w' k = (G.snd dat rest w0).put w k);
    the conditions of Cb/Ld/LdSendFresh.lean (`Own.Laws`: over, lay, pad) for the reading above;
    the reading keeps what is handed on, and the overwriting does not touch it.

What `Sig.Sender.Laws`, `Blind` and `Hides` ask: the head of Cb/Ld/LdRng.lean ("What the sending's
hypotheses ask").

Limits: this file says nothing on the conditions on codes and samples that do not concern the sender
(laws, lists, "two messages of a list agree at few seeds", fair seeds). It says nothing on masks of
one block among the free entries: by a coarser reading (see Ior/KnowCollRulesChainConseq.lean). It
says nothing on formats other than the plain one.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendMem
import Cb.Ld.LdSendFreshProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data. -/
structure StdSig (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  O : Type
  [finO : Fintype O]
  [decO : DecidableEq O]
  P : O → Type
  [finP : ∀ a, Fintype (P a)]
  C : ∀ a, LdCode E (P a)
  Dt : O → Type
  [finDt : ∀ a, Fintype (Dt a)]
  Fr : O → Type
  [finFr : ∀ a, Fintype (Fr a)]
  Pd : O → Type
  [finPd : ∀ a, Fintype (Pd a)]
  ν : ∀ a, (C a).J ≃ (Dt a ⊕ Fr a) ⊕ Pd a
  Z : ∀ a, Sample E ((Dt a ⊕ Fr a) ⊕ Pd a)
  e : O → ℕ

attribute [instance] StdSig.finO StdSig.decO StdSig.finP StdSig.finDt StdSig.finFr StdSig.finPd

namespace StdSig
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (G : StdSig F E)

/-- The family. -/
@[reducible] def sig : Sig E :=
  { O := G.O, om := fun a => OMsg.plain (G.C a) ((G.Z a).comap (G.ν a)) (G.e a) fun _ => 0 }

/-- What is asked of samples and codes. -/
def Priv : Prop := ∀ a, (G.Z a).Private F fun _ => True
def Zk (t : G.O → ℕ) : Prop := ∀ a, (G.C a).Zk (t a)

/-- data and free entries, read off the messages -/
def dataOf (m : G.sig.Msg) : ∀ a, G.Dt a → E := fun a c => m a ((G.ν a).symm (Sum.inl (Sum.inl c)))
def freeOf (m : G.sig.Msg) : ∀ a, G.Fr a → E := fun a i => m a ((G.ν a).symm (Sum.inl (Sum.inr i)))

variable {W W' : Type} (dat : W → ∀ a, G.Dt a → E) (rest : W → W') (w0 : W)

open Classical in
/-- the sender of a member -/
@[reducible] def mem : ∀ a, (G.sig.om a).Sender W Unit := fun a =>
  { N := (G.C a).Nn
    upM := fun m => m
    upR := fun r => r
    Mk := (G.Fr a → E) × (G.Pd a → F)
    put := fun w k j => withPad (F := F) (Sum.elim (dat w a) k.1) k.2 (G.ν a j)
    rest := fun _ => ()
    w0 := w0 }

open Classical in
/-- the same with the free entries fixed -/
@[reducible] def mem' (M : ∀ a, G.Fr a → E) :
    ∀ a, (G.sig.om a).Sender W Unit := fun a =>
  { N := (G.C a).Nn
    upM := fun m => m
    upR := fun r => r
    Mk := G.Pd a → F
    put := fun w η j => withPad (F := F) (Sum.elim (dat w a) (M a)) η (G.ν a j)
    rest := fun _ => ()
    w0 := w0 }

/-- The sender. -/
@[reducible] def snd : G.sig.Sender W W' := Sig.Sender.ofMem (G.mem dat w0) rest w0

/-- The extractor. -/
def back (bk : (∀ a, G.Dt a → E) → W' → W) (m : G.sig.Msg) (r : W') : W := bk (G.dataOf m) r

/-- The reading; all free entries overwritten. -/
def rd (m : G.sig.Msg) (r : W') : (∀ a, G.Dt a → E) × (∀ a, G.Fr a → E) × W' :=
  (G.dataOf m, G.freeOf m, r)
def putM (M : ∀ a, G.Fr a → E) (k : (∀ a, G.Dt a → E) × (∀ a, G.Fr a → E) × W') :
    (∀ a, G.Dt a → E) × (∀ a, G.Fr a → E) × W' := (k.1, M, k.2.2)

open Classical in
/-- The coins, split: the free entries; nothing else; the pads. -/
@[reducible] def own : (G.snd dat rest w0).Own (∀ a, G.Fr a → E) where
  M0 := Unit
  Pd := ∀ a, G.Pd a → F
  κ := { toFun := fun k => ((fun a => (k a).1, ()), fun a => (k a).2)
         invFun := fun z a => (z.1.1 a, z.2 a)
         left_inv := fun _ => rfl
         right_inv := fun _ => rfl }

end StdSig

namespace Spec

/-- All that is asked of a sender (by `Spec.ldSendFam_goodT` and, for the reading `G.rd`, by
`Spec.ldSendFam_fresh`). -/
def stdSig_all : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (G : StdSig F E) (t : G.O → ℕ) (W W' : Type) (dat : W → ∀ a, G.Dt a → E)
      (rest : W → W') (w0 : W) (bk : (∀ a, G.Dt a → E) → W' → W),
    G.Priv → G.Zk t → (∀ w, bk (dat w) (rest w) = w) →
    (G.snd dat rest w0).Laws (G.back bk) ∧
    (∀ Sd : G.sig.Seeds, (G.snd dat rest w0).Blind Sd) ∧
    (G.snd dat rest w0).Nn.Hides (G.sig.budT t) ∧
    (∀ (w w' : W) k, dat w' = dat w → (G.snd dat rest w0).put w' k = (G.snd dat rest w0).put w k) ∧
    (∀ Sd : G.sig.Seeds, (G.own dat rest w0).Laws Sd G.rd G.putM) ∧
    (∀ (m : G.sig.Msg) (r : W'), (G.rd m r).2.2 = r) ∧
    ∀ (M : ∀ a, G.Fr a → E) (k : (∀ a, G.Dt a → E) × (∀ a, G.Fr a → E) × W'),
      (G.putM M k).2.2 = k.2.2

end Spec

/-! ## Proofs -/

theorem Ood.Sample.comap_symm' {E J J' : Type} (Z : Sample E J) (ν : J' ≃ J) :
    (Z.comap ν).comap ν.symm = Z := by
  show ({ D := Z.D, S := Z.S, mat := fun ρ s n => Z.mat ρ s (ν (ν.symm n)),
          err := Z.err } : Sample E J) = Z
  simp only [Equiv.apply_symm_apply]

namespace StdSig
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (G : StdSig F E)
  {W W' : Type} (dat : W → ∀ a, G.Dt a → E) (rest : W → W') (w0 : W)

theorem unifM (h : G.Priv) (a : G.O) : (G.mem dat w0 a).Uniform := by
  classical
  refine ldSend_uniform_of_private E F (G.sig.om a) W Unit (G.mem dat w0 a) (G.Dt a ⊕ G.Fr a)
    (G.Pd a) (G.Fr a → E) (G.ν a) (Equiv.refl _) (fun w μ => Sum.elim (dat w a) μ) ?_ ?_
  · intro w k n
    show withPad (F := F) (Sum.elim (dat w a) k.1) k.2 (G.ν a ((G.ν a).symm n)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · show (((G.Z a).comap (G.ν a)).comap (G.ν a).symm).Private F fun _ => True
    rw [Sample.comap_symm']
    exact h a

theorem unifM' (h : G.Priv) (M : ∀ a, G.Fr a → E) (a : G.O) : (G.mem' dat w0 M a).Uniform := by
  refine ldSend_uniform_of_private E F (G.sig.om a) W Unit (G.mem' dat w0 M a) (G.Dt a ⊕ G.Fr a)
    (G.Pd a) Unit (G.ν a) (Equiv.punitProd _).symm (fun w _ => Sum.elim (dat w a) (M a)) ?_ ?_
  · intro w k n
    show withPad (F := F) (Sum.elim (dat w a) (M a)) k (G.ν a ((G.ν a).symm n)) = _
    rw [Equiv.apply_symm_apply]
    rfl
  · show (((G.Z a).comap (G.ν a)).comap (G.ν a).symm).Private F fun _ => True
    rw [Sample.comap_symm']
    exact h a

theorem data_put (w : W) (k : (G.snd dat rest w0).Mk) :
    G.dataOf ((G.snd dat rest w0).upM ((G.snd dat rest w0).put w k)) = dat w := by
  funext a c
  show withPad (F := F) (Sum.elim (dat w a) (k a).1) (k a).2
      (G.ν a ((G.ν a).symm (Sum.inl (Sum.inl c)))) = dat w a c
  rw [Equiv.apply_symm_apply]
  rfl

theorem free_put (w : W) (k : (G.snd dat rest w0).Mk) :
    G.freeOf ((G.snd dat rest w0).upM ((G.snd dat rest w0).put w k)) = fun a => (k a).1 := by
  funext a i
  show withPad (F := F) (Sum.elim (dat w a) (k a).1) (k a).2
      (G.ν a ((G.ν a).symm (Sum.inl (Sum.inr i)))) = (k a).1 i
  rw [Equiv.apply_symm_apply]
  rfl

end StdSig

theorem stdSig_all : Spec.stdSig_all := by
  intro F E _ _ _ _ _ G t W W' dat rest w0 bk hP hZ hb
  refine ⟨?_, fun Sd => ?_, ?_, ?_,
    fun Sd =>
      ⟨fun _ _ _ => rfl, ⟨fun w _ => (dat w, fun _ _ => 0, rest w), fun w M k₀ η => ?_⟩, ?_⟩,
    fun _ _ => rfl, fun _ _ => rfl⟩
  · refine ldSendMem_laws E G.sig W W' (G.mem dat w0) rest w0 (G.back bk)
      (fun _ _ _ => rfl) fun w k => ?_
    show bk (G.dataOf _) (rest w) = w
    rw [G.data_put dat rest w0 w k]
    exact hb w
  · exact ldSendMem_blind E G.sig W W' (G.mem dat w0) rest w0 Sd fun a =>
      ldSend_blind_of_uniform E (G.sig.om a) W Unit _ (G.unifM dat w0 hP a)
  · exact ldSendMem_hides E G.sig W W' (G.mem dat w0) rest w0 t hZ
  · intro w w' k hw
    funext a
    show (fun j => withPad (F := F) (Sum.elim (dat w' a) (k a).1) (k a).2 (G.ν a j)) =
      fun j => withPad (F := F) (Sum.elim (dat w a) (k a).1) (k a).2 (G.ν a j)
    rw [hw]
  · exact Prod.ext (G.data_put dat rest w0 w _) (Prod.ext (G.free_put dat rest w0 w _) rfl)
  · refine own_pad_of_uniform E G.sig W W' (G.snd dat rest w0) (∀ a, G.Fr a → E)
      (G.own dat rest w0) Sd fun s w M k₀ => ?_
    exact ldSendMem_uniform E G.sig W W' (G.mem' dat w0 M) rest w0 Sd (G.unifM' dat w0 hP M) s w

end Cb
