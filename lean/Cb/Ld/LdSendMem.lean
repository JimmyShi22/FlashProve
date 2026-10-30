-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendMem.lean: the honest sender of a family, made from senders of its members with
independent coins.

This file builds the data of the honest prover of a reduction that sends several words in one prover
message from the data of the honest prover for each word, with independent randomness.

Definitions, statements (Cb.Spec.ldSendMem_*) and proofs. It discharges the two joint hypotheses
(`D.Blind Sd`, `D.Nn.Hides (N.budT t)`) of Cb/Ld/LdSendFam.lean from the members' own.

Main names:
  `Sig.Sender.ofMem mem rest w0`: mem a : a sender of the member a (Cb/Ld/LdSend.lean: its encoding
    in the format, its coins that go into the message, its "put"; its fields rest, w0 are not read).
    The family's encoding encodes member by member with independent randomness; the coins that go
    into the messages are independent too.
  `Spec.ldSendMem_laws`: the laws of the family's sender, from the members' law on encodings and the
    law of the extractor.
  `Spec.ldSendMem_hides`: every member's encoding hides `t a` long positions ⇒ the family's encoding
    hides within the family's budget. No error is added (all are 0 here).
  `Spec.ldSendMem_blind`: at every seed of every member the law of its answers does not depend on
    the witness ⇒ at every joint seed, however the members' seeds are shared, the joint law of all
    answers does not depend on the witness.
  `Spec.ldSendMem_uniform`: if every member's answers are uniform at every seed, all answers
    together are uniform at every joint seed.

Why shared seeds do no harm: the coins of different members are independent, whatever the seeds. At
a fixed joint seed the answers of different members are independent random variables.

Limits: members whose messages share coins (a mask that stands in two oracle messages) are not
covered. This file says nothing on statistical errors.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendFamProofs
import Prob.Linear

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type}

/-- The sender of a family from senders of its members, with independent coins. -/
@[reducible] def Sig.Sender.ofMem (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W') (w0 : W) :
    N.Sender W W' where
  Nn := { Msg := ∀ a, (mem a).N.Msg, Rnd := ∀ a, (mem a).N.Rnd,
          enc := fun m r a => (mem a).N.enc (m a) (r a), dec := fun _ => none }
  upM := fun m a => (mem a).upM (m a)
  upR := fun r a => (mem a).upR (r a)
  Mk := ∀ a, (mem a).Mk
  put := fun w k a => (mem a).put w (k a)
  rest := rest
  w0 := w0

end

namespace Spec
section
variable (E : Type) [Field E]

def ldSendMem_laws : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W')
      (w0 : W) (back : N.Msg → W' → W),
    (∀ a m r, (N.om a).upW ((mem a).N.enc m r) = (N.om a).C.enc ((mem a).upM m) ((mem a).upR r)) →
    (∀ w (k : ∀ a, (mem a).Mk), back (fun a => (mem a).upM ((mem a).put w (k a))) (rest w) = w) →
    (Sig.Sender.ofMem mem rest w0).Laws back

def ldSendMem_hides : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit)
      (rest : W → W') (w0 : W) (t : N.O → ℕ),
    (∀ a, (mem a).N.Hides ((N.om a).C.budT (t a))) →
    (Sig.Sender.ofMem mem rest w0).Nn.Hides (N.budT t)

def ldSendMem_blind : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W')
      (w0 : W) (Sd : N.Seeds),
    (∀ a, (mem a).Blind) → (Sig.Sender.ofMem mem rest w0).Blind Sd

open Classical in
def ldSendMem_uniform [Fintype E] : Prop :=
  ∀ (N : Sig E) (W W' : Type) (mem : ∀ a, (N.om a).Sender W Unit) (rest : W → W')
      (w0 : W) (Sd : N.Seeds),
    (∀ a, (mem a).Uniform) →
    ∀ s w, (unif (∀ a, (mem a).Mk)).map ((Sig.Sender.ofMem mem rest w0).ans Sd s w) = unif N.Answ

end
end Spec

section
variable (E : Type) [Field E]

omit [Field E] in
theorem ldSendMem_laws : Spec.ldSendMem_laws E := fun _ _ _ _ _ _ _ he hb =>
  ⟨fun m r a => he a (m a) (r a), hb⟩

omit [Field E] in
theorem ldSendMem_hides : Spec.ldSendMem_hides E := by
  classical
  intro N W W' mem rest w0 t h
  refine (hides_iff_equiv N.nat (Sig.Sender.ofMem mem rest w0).Nn (N.budT t)).2 ?_
  intro U hU (m : ∀ a, (mem a).N.Msg) (m' : ∀ a, (mem a).N.Msg)
  have hm : ∀ a, ∃ e : (mem a).N.Rnd ≃ (mem a).N.Rnd, ∀ r, ∀ p, (⟨a, p⟩ : Σ a, (N.om a).C.NP) ∈ U →
      (mem a).N.enc (m a) r p = (mem a).N.enc (m' a) (e r) p := by
    intro a
    obtain ⟨Xs, hc, hX⟩ := hU a
    have key := (hides_iff_equiv (N.om a).nat (mem a).N ((N.om a).C.budT (t a))).1 (h a)
    let Ua : Finset (N.om a).C.NP :=
      U.preimage (fun p : (N.om a).C.NP => (⟨a, p⟩ : Σ a, (N.om a).C.NP))
        fun _ _ _ _ hxy => eq_of_heq (Sigma.mk.inj hxy).2
    have hUa : (N.om a).C.budT (t a) Ua := ⟨Xs, hc, fun p hp => hX p (Finset.mem_preimage.1 hp)⟩
    obtain ⟨e, he⟩ := key Ua hUa (m a) (m' a)
    exact ⟨e, fun r p hp => eq_of_heq (Sigma.mk.inj (he r p (Finset.mem_preimage.2 hp))).2⟩
  choose e he using hm
  refine ⟨(Equiv.piCongrRight e : (∀ a, (mem a).N.Rnd) ≃ ∀ a, (mem a).N.Rnd), ?_⟩
  intro (r : ∀ a, (mem a).N.Rnd) p hp
  obtain ⟨a, p⟩ := p
  have h2 := he a (r a) p hp
  show (⟨⟨a, p⟩, (mem a).N.enc (m a) (r a) p⟩ : N.nat.Sym) =
    ⟨⟨a, p⟩, (mem a).N.enc (m' a) (e a (r a)) p⟩
  rw [h2]

theorem ldSendMem_blind : Spec.ldSendMem_blind E := by
  classical
  intro N W W' mem rest w0 Sd h s w w'
  have hm : ∀ a, ∃ σ : (mem a).Mk ≃ (mem a).Mk,
      ∀ k, (mem a).ans (Sd.sd a s) w k = (mem a).ans (Sd.sd a s) w' (σ k) := fun a =>
    exists_equiv_of_map_eq _ _ (h a (Sd.sd a s) w w')
  choose σ hσ using hm
  exact map_unif_reindex (Equiv.piCongrRight σ) _ _ fun k => funext fun a => hσ a (k a)

theorem ldSendMem_uniform [Fintype E] : Spec.ldSendMem_uniform E := by
  classical
  intro N W W' mem rest w0 Sd h s w
  exact map_unif_pi (fun a => (mem a).ans (Sd.sd a s) w) fun a => h a (Sd.sd a s) w

end
end Cb
