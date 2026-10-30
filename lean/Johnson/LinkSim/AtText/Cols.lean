-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Cols.lean: the prover's tree columns and the base case's two rounds, under a
change of the message. General lemmas.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Three facts about the prover's algorithm at fixed codes.
  Columns are equal where their symbols are.
    firstColW_congr   the first tree's column at a position is the same if the symbols of the R
                      rows in which each folded row is laid out, and of the row beside them, are
                      (Johnson/Prover/Link/FrontCols.lean).
    stageColW_congr   a later tree's column is the same if the symbols of its three kinds of rows
                      are (Johnson/Prover/Link/SwitchCols.lean).
    baseColW_congr    the last tree's column is the same if its four symbols are
                      (Johnson/Prover/Link/Base.lean).
  A change of the last message is compensated by a change of the masking word.
    shownAll_shift    for every sampled element: the four lists that the base case's second round
                      sends, at the last message (m0 + dm0, r0 + dr0, m1 + dm1, r1 + dr1) and
                      the masking word (h0, s0, h1, s1), equal the lists at (m0, r0, m1, r1) and
                      the masking word plus the sampled element times the change.
  The masking word's own symbols then do not change where the change's symbols are 0.
    mask_sym_same     where (dm, dr) has the symbol 0 at a position, the masking word plus a
                      multiple of (dm, dr) has its old symbol there.
    tauSW_line        the first round's element at such a masking word is the old value plus the
                      multiple of the claim's left side at the change.
The proofs use symG_line, formG_line (Johnson/Prover/Link/Base.lean) and wr_congr
(Johnson/LinkSim/AtText/Sym.lean).

How it fits. FrontStep.lean, Step.lean and LastStep.lean use these lemmas to compare the two runs'
columns and the base case; MustFail.lean uses them in its negative tests.

Limits.
  - These are congruences and identities: that any symbols are equal is a premise here.
Sources. This file carries out the plan of AtText/ShiftDefs.lean, and the note on sources in that
file's head holds here too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontCols
import Johnson.Prover.Link.SwitchCols
import Johnson.LinkSim.AtText.Sym

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

theorem firstColW_congr (S : Sz) (mN mN' tN tN' : Bool → ℕ → ℕ → GE) (φN φN' ψN ψN' : ℕ → GE)
    (x : ℕ)
    (h : ∀ a i, i < S.P.R → symG S.P.C x (mN a i) (tN a i) = symG S.P.C x (mN' a i) (tN' a i))
    (hf : symG S.P.Z (x % 2 ^ S.P.Z.a) φN ψN = symG S.P.Z (x % 2 ^ S.P.Z.a) φN' ψN') :
    firstColW S mN tN φN ψN x = firstColW S mN' tN' φN' ψN' x := by
  unfold firstColW firstSyms
  rw [wr_congr S.P.R _ _ (h false), wr_congr S.P.R _ _ (h true), hf]

theorem stageColW_congr (s : Sg) (tabM tabM' tabZ tabZ' : ℕ → GE)
    (tM tM' tZ tZ' fM fM' fT fT' : ℕ → ℕ → GE) (x : ℕ)
    (h1 : ∀ b, b < 2 ^ (s.h + s.g) → mainSym s tabM tM x b = mainSym s tabM' tM' x b)
    (h2 : ∀ b, b < 2 ^ s.h → maskSym s tabZ tZ x b = maskSym s tabZ' tZ' x b)
    (h3 : ∀ b, b < 2 ^ s.h → freshSym s fM fT x b = freshSym s fM' fT' x b) :
    stageColW s tabM tabZ tM tZ fM fT x = stageColW s tabM' tabZ' tM' tZ' fM' fT' x := by
  unfold stageColW
  rw [wr_congr _ _ _ h1, wr_congr _ _ _ h2, wr_congr _ _ _ h3]

theorem baseColW_congr (C Z : Fmt.M1.Code)
    (m0 r0 m1 r1 h0 s0 h1 s1 m0' r0' m1' r1' h0' s0' h1' s1' : ℕ → GE) (x : ℕ)
    (e1 : symG C x m0 r0 = symG C x m0' r0')
    (e2 : symG C x h0 s0 = symG C x h0' s0')
    (e3 : symG Z (x % 2 ^ Z.a) m1 r1 = symG Z (x % 2 ^ Z.a) m1' r1')
    (e4 : symG Z (x % 2 ^ Z.a) h1 s1 = symG Z (x % 2 ^ Z.a) h1' s1') :
    baseColW C Z m0 r0 m1 r1 h0 s0 h1 s1 x = baseColW C Z m0' r0' m1' r1' h0' s0' h1' s1' x := by
  unfold baseColW
  rw [e1, e2, e3, e4]

/-- The base case's second round sends the same lists at the last message plus a change as at
the last message with the sampled element times the change added to the masking word. -/
theorem shownAll_shift (C Z : Fmt.M1.Code) (lam : Fmt.M1.E)
    (m0 r0 m1 r1 dm0 dr0 dm1 dr1 h0 s0 h1 s1 : ℕ → GE) :
    shownAll C Z lam (m0 + dm0) (r0 + dr0) (m1 + dm1) (r1 + dr1) h0 s0 h1 s1 =
      shownAll C Z lam m0 r0 m1 r1 (fun j => h0 j + toE lam * dm0 j)
        (fun q => s0 q + toE lam * dr0 q) (fun j => h1 j + toE lam * dm1 j)
        fun q => s1 q + toE lam * dr1 q := by
  unfold shownAll
  have k : ∀ (n : ℕ) (h m dm : ℕ → GE),
      (wr n fun j => h j + toE lam * (m + dm) j) =
        wr n fun j => h j + toE lam * dm j + toE lam * m j := fun n h m dm =>
    wr_congr n _ _ fun j _ => by
      show h j + toE lam * (m j + dm j) = _
      ring
  rw [k, k, k, k]

theorem mask_sym_same (C : Fmt.M1.Code) (x : ℕ) (h s dm dr : ℕ → GE) (μ : GE)
    (h0 : symG C x dm dr = 0) :
    symG C x (fun j => h j + μ * dm j) (fun q => s q + μ * dr q) = symG C x h s := by
  rw [symG_line, h0, mul_zero, add_zero]

theorem tauSW_line (C Z : Fmt.M1.Code) (c d : Array Fmt.M1.E) (h0 h1 dm0 dm1 : ℕ → GE) (μ : GE) :
    formG C.l c (fun j => h0 j + μ * dm0 j) + formG Z.l d (fun j => h1 j + μ * dm1 j) =
      (formG C.l c h0 + formG Z.l d h1) + μ * (formG C.l c dm0 + formG Z.l d dm1) := by
  rw [formG_line, formG_line]
  ring

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.firstColW_congr
#print axioms OnBytes.LinkSim.AtText.stageColW_congr
#print axioms OnBytes.LinkSim.AtText.shownAll_shift
#print axioms OnBytes.LinkSim.AtText.mask_sym_same
