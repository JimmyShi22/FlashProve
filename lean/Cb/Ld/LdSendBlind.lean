-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendBlind.lean: under the hypotheses of its statements, a sending does not look at masks
that stand in older oracle messages.

Statements and proofs.

Why: masks of a later block may have been sent long before it, in an oracle message of the
statement. The rule for chains with masked blocks (Ior/KnowCollRulesMask.lean) asks of every link
between that sending and the block that it is blind for these masks (`Honest.Blind`): overwrite the
masks in what is read of the link's input witness: the link's messages and its explicit output stay,
and what is read of its output witness is overwritten in the same way.
Under the hypotheses below, a sending of new oracle messages is such a link, if what it lays into
the new messages ("put") does not read those masks: it only hands the old pairs on.

Main names: the statements, for any readers kci, kco of the witnesses before and after, and any
overwriting puti, puto. Asked:
  (1) "put" gives the same messages for two witnesses of which the second is read as the first
      overwritten;
  (2) what is handed on ("rest", beside any new pairs) is then read as overwritten.
  Each states `Honest.Blind kci kco Mk puti puto` of the honest side of:
  `Spec.ldSendFam_blind`: the sending of a family from any joint (Cb/Ld/LdSendFam.lean).
  `Spec.ldSendSig_blind`: the sending to a statement over S (Cb/Ld/LdSigSum.lean).

Limits: this file says nothing on masks that stand in the new messages: for these the sending is
fresh, under the hypotheses of its statement (Cb/Ld/LdSendFresh.lean). The two conditions are to be
shown where readers and "put" are given; here they are hypotheses.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSigSum
import Ior.KnowCollRulesMask

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec

def ldSendFam_blind : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (X W W' : Type) (E₀ : ExtSpec)
      (D : N.Sender W W') (Ki Ko Mk : Type) (kci : W → Ki) (kco : N.Wit × W' → Ko)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    (∀ w w' M, kci w' = puti M (kci w) → ∀ k, D.put w' k = D.put w k) →
    (∀ w w' M (nw : N.Wit),
      kci w' = puti M (kci w) → kco (nw, D.rest w') = puto M (kco (nw, D.rest w))) →
    (ldSendFamHon Sd X E₀ D).Blind kci kco Mk puti puto

def ldSendSig_blind : Prop :=
  ∀ (E : Type) [Field E] (S N : Sig E) (Sd : N.Seeds) (St Wp Wp' : Type) (E₀ : ExtSpec)
      (D : N.Sender (S.Wit × Wp) (S.Wit × Wp')) (Ki Ko Mk : Type) (kci : S.Wit × Wp → Ki)
      (kco : (S.sum N).Wit × Wp' → Ko) (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    (∀ w w' M, kci w' = puti M (kci w) → ∀ k, D.put w' k = D.put w k) →
    (∀ w w' M (nw : N.Wit), kci w' = puti M (kci w) →
      kco (S.join N (T := OMsg.Wit) (D.rest w').1 nw, (D.rest w').2) =
        puto M (kco (S.join N (T := OMsg.Wit) (D.rest w).1 nw, (D.rest w).2))) →
    (ldSendSigHon Sd St E₀ D).Blind kci kco Mk puti puto

end Spec

theorem ldSendFam_blind : Spec.ldSendFam_blind := by
  intro E _ N Sd X W W' E₀ D Ki Ko Mk kci kco puti puto h1 h2 w w' M x c ρ h
  obtain ⟨ρ₁, u, u'⟩ := ρ
  have hp := h1 w w' M h c.1
  have ha : D.ans Sd ρ₁ w' c.1 = D.ans Sd ρ₁ w c.1 := by
    unfold Sig.Sender.ans
    rw [hp]
  refine ⟨?_, ?_, ?_⟩
  · show ((D.Nn.enc (D.put w' c.1) c.2, ()), ρ₁, ((), D.ans Sd ρ₁ w' c.1), u, ()) =
      (((D.Nn.enc (D.put w c.1) c.2, ()), ρ₁, ((), D.ans Sd ρ₁ w c.1), u, ()) : Tr (N.sh Sd))
    rw [hp, ha]
    rfl
  · show (x, fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ w' c.1 a)) =
      (x, fun a => (Sd.sd a ρ₁, D.ans Sd ρ₁ w c.1 a))
    rw [ha]
  · show kco (fun a => (D.upM (D.put w' c.1) a, D.upR c.2 a), D.rest w') =
      puto M (kco (fun a => (D.upM (D.put w c.1) a, D.upR c.2 a), D.rest w))
    rw [hp]
    exact h2 w w' M _ h

theorem ldSendSig_blind : Spec.ldSendSig_blind := by
  intro E _ S N Sd St Wp Wp' E₀ D Ki Ko Mk kci kco puti puto h1 h2 w w' M x c ρ h
  have key : ∀ v, ((ldSendSigHon Sd St E₀ D).strat v x c).run ρ =
      ((((ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D).strat v x c).run ρ).1,
        S.mergeW N St Wp'
          (((ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D).strat v x c).run ρ).2) :=
    fun v => by
      show (Strat.map (S.mergeW N St Wp')
          ((ldSendFamHon Sd (St × S.Smp) (E₀.prod S.ext) D).strat v x c)).run ρ = _
      exact Strat.run_map _ _ _
  have hf := ldSendFam_blind E N Sd (St × S.Smp) (S.Wit × Wp) (S.Wit × Wp') (E₀.prod S.ext) D Ki Ko
    Mk kci (fun v => kco (S.join N (T := OMsg.Wit) v.2.1 v.1, v.2.2)) puti puto h1 h2 w w' M x c ρ h
  rw [key w', key w]
  refine ⟨hf.1, ?_, hf.2.2⟩
  show ((S.mergeW N St Wp' _).1 = (S.mergeW N St Wp' _).1)
  unfold Sig.mergeW
  rw [hf.2.1]

end Cb
