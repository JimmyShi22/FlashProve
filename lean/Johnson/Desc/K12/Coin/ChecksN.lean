-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/ChecksN.lean: THE FORMS OF THE LAWS WITH A LETTER (`K12LawN`, LawN.lean;
`K12LawNO`, OwnArm.lean), TRIED AGAINST THE VERIFIER THAT SAYS YES TO ALL. Statements and proofs.

  `qn_no_group`: whatever N: the conclusion is false at a record whose statement has no group under
    the record's number. `promN_no_group`, `promNO_no_group`: there both promises hold.
  `yesAll_failsN`, `yesAll_failsNO`: **whatever N**: a piece that puts out at every transcript from
    one such statement, at errors below its rounds' numbers of challenges, has neither law's form.
A verifier that says no to all has both, as it has every statement on soundness alone.

-/
import Johnson.Desc.K12.Coin.SheetChecks
import Johnson.Desc.K12.Coin.OwnArm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

theorem qn_no_group {F : Frame} (π : P12) (N : ConclK F) (x : T12 × F.E.Str)
    (h : x.1.st.groups[x.1.g]? = none) : ¬ QN π N x := by
  rintro ⟨a, rest, G0, Ly, D, hf, _⟩
  exact fixes_no_group π x.1 h a rest G0 Ly D hf

theorem promN_no_group (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ) (N : ConclK F) (x : T12 × F.E.Str)
    (h : x.1.st.groups[x.1.g]? = none) :
    FirstOpens π num no base x.1 ∧ BatAtN F π no rad rd dB e₀ N x :=
  ⟨fun a rest G0 Ly D hf => absurd hf (fixes_no_group π x.1 h a rest G0 Ly D),
    fun a rest G0 Ly D _ _ hf => absurd hf (fixes_no_group π x.1 h a rest G0 Ly D)⟩

theorem promNO_no_group (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ) (N : ConclK F) (x : T12 × F.E.Str)
    (h : x.1.st.groups[x.1.g]? = none) :
    FirstOpensOwn π num no base x.1 ∧ BatAtN F π no rad rd dB e₀ N x :=
  ⟨fun a rest G0 Ly D hf => absurd hf (fixes_no_group π x.1 h a rest G0 Ly D),
    fun a rest G0 Ly D _ _ hf => absurd hf (fixes_no_group π x.1 h a rest G0 Ly D)⟩

theorem yesAll_failsN {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ) (N : ConclK F)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) :
    ¬ p.ior.red.Leads (fun x => FirstOpens π num no base x.1 ∧ BatAtN F π no rad rd dB e₀ N x)
      (fun x _ => QN π N x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x (promN_no_group F π num no rad rd base dB e₀ N x hg)))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π N x hg (hτ b hb')

theorem yesAll_failsNO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ) (N : ConclK F)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b)
    (hs : Small p.err) :
    ¬ p.ior.red.Leads
      (fun x => FirstOpensOwn π num no base x.1 ∧ BatAtN F π no rad rd dB e₀ N x)
      (fun x _ => QN π N x) p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x (promNO_no_group F π num no rad rd base dB e₀ N x hg)))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qn_no_group π N x hg (hτ b hb')

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsN
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_failsNO
