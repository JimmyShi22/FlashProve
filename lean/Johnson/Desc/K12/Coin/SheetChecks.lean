-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/SheetChecks.lean: THE FORM OF THE LAW ON Sheet.lean, TRIED
AGAINST THE SILLY VERIFIERS; and a small fact that the sheet's head leans on. Statements and proofs.

  `yOf_indep`: the word of the group under test does not hang on the row, nor on the proof, under
    which `yOf` is handed the plain data: so the first two "there is" of `NearAll` pick nothing.
  `qk_no_group`: the conclusion is false at a record whose statement has no group under the
    record's number. `onK_no_group`: there the promise in front asks only that a mask is named.
  `Small`, `not_doomed_false`: at errors that are below their rounds' numbers of challenges no
    prover has lost towards "false".
  `yesAll_fails`: **A VERIFIER THAT SAYS YES TO ALL DOES NOT MEET THE FORM**: whatever block a piece
    holds: if it puts out at every transcript from one statement with a mask named and no such
    group, and its errors are small, it has not the law.
THE VERIFIER THAT SAYS NO TO ALL MEETS THE FORM, as it meets every statement on soundness alone
(`noAll_meets`): the form bounds what a cheating prover reaches; that the block says yes at an
honest transcript is not said by it, and is shown nowhere here.

-/
import Johnson.Desc.K12.Coin.Sheet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open H2K.JointK (WO yOf)
open H2K.Pub (sgOf)
open H2K.First (gpL Plain)

theorem yOf_indep (π : P12) (a : Fmt.M1.Stage) (row row' : GroupRow) (D : Plain)
    (hok : H2K.First.ok (gpL π a row D) = true) (hok' : H2K.First.ok (gpL π a row' D) = true)
    (rd : ℕ → ℕ) (V : ℕ → WO) : yOf π a row D hok rd V = yOf π a row' D hok' rd V := rfl

theorem fixes_no_group (π : P12) (t : T12) (h : t.st.groups[t.g]? = none) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain) :
    ¬ Fixes π t a rest G0 Ly D := by
  rintro ⟨_, hg, _⟩
  rw [h] at hg
  cases hg

theorem qk_no_group (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (x : T12 × F.E.Str) (h : x.1.st.groups[x.1.g]? = none) : ¬ QK F π no rad rd x := by
  rintro ⟨a, rest, G0, Ly, D, hf, _⟩
  exact fixes_no_group π x.1 h a rest G0 Ly D hf

theorem onK_no_group (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rad : Sg → ℕ)
    (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ) (x : T12 × F.E.Str)
    (h : x.1.st.groups[x.1.g]? = none) (hm : x.1.mask.isSome = true) :
    OnK F π num no rad rd base dB e₀ x :=
  ⟨hm, fun a rest G0 Ly D hf => absurd hf (fixes_no_group π x.1 h a rest G0 Ly D),
    fun a rest G0 Ly D _ _ hf => absurd hf (fixes_no_group π x.1 h a rest G0 Ly D)⟩

/-- Every error is below its round's number of challenges. -/
def Small : {s : Shape} → Err s → Prop
  | [], _ => True
  | r :: _, (e, ε) => e < Nat.card r.Chal ∧ Small ε

theorem not_doomed_false : ∀ (s : Shape) (ε : Err s), Small ε → ¬ Doomed s ε fun _ => False
  | [], _, _, h => h
  | r :: s, (e, ε), hs, h => by
    have h1 := h (r.dOrc, r.dPlain)
    have h2 : cnt (fun _ : r.Chal => ¬ Doomed s ε fun _ => False) = Nat.card r.Chal := by
      unfold Prob.cnt
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => not_doomed_false s ε hs.2)
    have h3 : cnt (fun _ : r.Chal => ¬ Doomed s ε fun _ => False) ≤ e := h1
    have := hs.1
    omega

/-- **A verifier that says yes to all has not the law.** -/
theorem yesAll_fails {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (x : T12 × F.E.Str)
    (hg : x.1.st.groups[x.1.g]? = none) (hm : x.1.mask.isSome = true)
    (hyes : ∀ τ, ∃ b, p.ior.red.out x τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads (OnK F π num no rad rd base dB e₀) (fun x _ => QK F π no rad rd x)
      p.err := by
  intro h
  refine not_doomed_false _ _ hs (Doomed.mono _ _ (fun τ hτ => ?_)
    (h x (onK_no_group F π num no rad rd base dB e₀ x hg hm)))
  obtain ⟨b, hb'⟩ := hyes τ
  exact qk_no_group F π no rad rd x hg (hτ b hb')

/-- A verifier that says no to all has it, as it has every law of this form. -/
theorem noAll_meets {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (e₀ : ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (hno : ∀ x τ, p.ior.red.out x τ = none) :
    p.ior.red.Leads (OnK F π num no rad rd base dB e₀) (fun x _ => QK F π no rad rd x) p.err :=
  fun x _ => Doomed.of_forall _ _ fun τ b hb => by
    rw [hno x τ] at hb
    cases hb

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yOf_indep
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_fails
#print axioms VerifiableInference.Desc.K12.Coin.noAll_meets
