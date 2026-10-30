-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ChecksPaid.lean: THE FORMS OF THE LAWS OF Paid.lean, TRIED AGAINST THE
VERIFIER THAT SAYS YES TO ALL. Statements and proofs.

  `payK_no_group`: at a record whose statement has no group under the record's number `PayK` holds.
  `yesAll_failsPaid`, `yesAll_failsPaidO`: a piece that puts out at every transcript from one such
    statement, at errors below its rounds' numbers of challenges, has neither law's form.
Limits: the checks stand at a statement WITHOUT A GROUP alone: they show that the form can fail;
that it bites a block which runs the front and the batching and then skips the chain is not shown.
The laws of Paid.lean say something only where their first error, v₀ times the sampler's number, is
below the number of "BAT"'s challenges: v₀ is evaluated nowhere. A verifier that says no to all has
both forms.

-/
import Johnson.Desc.K12.Coin.ChecksN
import Johnson.Desc.K12.Coin.Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayK)

theorem payK_no_group (π : P12) (rad : Sg → ℕ) (v₀ : ℕ) (t : T12)
    (h : t.st.groups[t.g]? = none) : PayK π rad v₀ t :=
  fun a rest G0 Ly D hf => absurd hf (fixes_no_group π t h a rest G0 Ly D)

theorem yesAll_failsPaid {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (v₀ : ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpens π num no base x.1 ∧ PayK π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x ⟨(promN_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) x hg).1,
      payK_no_group π rad v₀ x.1 hg⟩))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π _ x hg (hτ b hb')

theorem yesAll_failsPaidO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (v₀ : ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpensOwn π num no base x.1 ∧ PayK π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x ⟨(promNO_no_group F π num no rad rd base dB 0 (NTuple F π no rad rd) x hg).1,
      payK_no_group π rad v₀ x.1 hg⟩))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π _ x hg (hτ b hb')

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsPaid
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsPaidO
