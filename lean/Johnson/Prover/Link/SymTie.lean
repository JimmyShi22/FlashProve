-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/SymTie.lean: the code word's symbol as this folder writes it (`symG`,
Johnson/Prover/Link/Base.lean) is the library's encoders' (`ldOf`, `ldRep`,
OnBytes/Slice/LinkAt.lean); so the written columns of a later stage's tree
(Johnson/Prover/Link/SwitchCols.lean), read as the soundness side reads them, are the code words of
the stage's message and of the rider's. General in the code and in the stage. No premise on a code.

Main names (namespace `Johnson.Prover.Link`).
  `enc_ldOf`, `read_ldOf`   one row under C: the encoder at a position of C's own; the code word
      read at a position p of a group of 2^a positions: `symG` at p modulo C's length
  `enc_ldRep`   one row under C repeated to 2^a positions: the same
  `ext0`, `ext0_val`   a function on Fin n as a function on ℕ, 0 from n on
  `wordIn_written`   the word of main rows and carried mask rows that the written columns show
      (`wordIn`, OnBytes/Slice/Stage.lean) is the stage's code word of (μ, ρ), where the tables and
      tails that the columns were written of are μ's and ρ's by index
  `wordFr_written`   the like for the rider: the word of the fresh mask rows (`wordFr`)

By unfolding and `Finset.sum_range`, as the library's `toE_symE_enc` (OnBytes/Slice/SimBasic.lean);
`stageCol_written`.

Limits. Equations. Nothing on trees, salts or hashes; nothing on which columns a verifier is
handed. The first stage's tree and the last stage's have other columns. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.SwitchCols
import OnBytes.Slice.Stage

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes.Slice Cb

/-- One row under C: the library's encoder at a position of C's own. -/
theorem enc_ldOf (C : Fmt.M1.Code) (a : ℕ) (x : Fin (2 ^ C.a)) (m r : ℕ → GE) :
    (ldOf C a).enc (fun j => m j.val) (fun q => r q.val) x () = symG C x.val m r := by
  unfold symG
  rw [Finset.sum_range, Finset.sum_range]
  rfl

/-- The code word, read at a position of a group of 2^a positions. -/
theorem read_ldOf (C : Fmt.M1.Code) (a : ℕ) (p : Fin (2 ^ a)) (m r : ℕ → GE) :
    (ldOf C a).T ((ldOf C a).enc (fun j => m j.val) fun q => r q.val) p () =
      symG C (p.val % 2 ^ C.a) m r :=
  enc_ldOf C a (posIn C p) m r

/-- One row under C, repeated to 2^a positions. -/
theorem enc_ldRep (C : Fmt.M1.Code) (a : ℕ) (p : Fin (2 ^ a)) (m r : ℕ → GE) :
    (ldRep C a).enc (fun j => m j.val) (fun q => r q.val) p () = symG C (p.val % 2 ^ C.a) m r :=
  enc_ldOf C a (posIn C p) m r

/-- A function on Fin n as a function on ℕ, 0 from n on. -/
def ext0 {n : ℕ} (f : Fin n → GE) (j : ℕ) : GE := if h : j < n then f ⟨j, h⟩ else 0

theorem ext0_val {n : ℕ} (f : Fin n → GE) : (fun j : Fin n => ext0 f j.val) = f :=
  funext fun j => dif_pos j.isLt

variable (s' : Sg) (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) (col : ℕ → Fmt.M1.Col)

/-- **The written columns show the stage's code word.** -/
theorem wordIn_written (μ : s'.cIn.J → GE) (ρ : s'.cIn.Q → GE)
    (hM : ∀ b j, μ (.inl (b, j)) = tabM (Sz.rowNo b + 2 ^ (s'.h + s'.g) * j.val))
    (hZ : ∀ b j, μ (.inr (b, j)) = tabZ (Sz.rowNo b + 2 ^ s'.h * j.val))
    (hTM : ∀ b q, ρ (.inl (b, q)) = tM (Sz.rowNo b) q.val)
    (hTZ : ∀ b q, ρ (.inr (b, q)) = tZ (Sz.rowNo b) q.val)
    (hcol : ∀ x, x < 2 ^ s'.C.a → Fmt.M1.stageCol s'.st 0 (2 ^ s'.st.k)
      (stageColW s' tabM tabZ tM tZ fM fT x) = some (col x)) :
    wordIn s' col = s'.cIn.enc μ ρ := by
  funext p
  rcases p with x | x
  · funext a
    obtain ⟨b, ⟨⟩⟩ := a
    obtain ⟨c, hc, h1, -, -⟩ := stageCol_written s' tabM tabZ tM tZ fM fT x.val
    obtain rfl : c = col x.val := Option.some.inj (hc.symm.trans (hcol x.val x.isLt))
    show vec (col x.val).main (Sz.rowNo b) =
      (ldOf s'.C s'.C.a).enc (fun j => μ (.inl (b, j))) (fun q => ρ (.inl (b, q))) x ()
    rw [h1 _ (rowNo_lt b), funext (hM b), funext (hTM b)]
    exact (enc_ldOf s'.C s'.C.a x _ _).symm
  · funext a
    obtain ⟨b, ⟨⟩⟩ := a
    obtain ⟨c, hc, -, h2, -⟩ := stageCol_written s' tabM tabZ tM tZ fM fT x.val
    obtain rfl : c = col x.val := Option.some.inj (hc.symm.trans (hcol x.val x.isLt))
    show vec (col x.val).mask (Sz.rowNo b) =
      (ldRep s'.Z s'.C.a).enc (fun j => μ (.inr (b, j))) (fun q => ρ (.inr (b, q))) x ()
    rw [h2 _ (rowNo_lt b), funext (hZ b), funext (hTZ b)]
    exact (enc_ldRep s'.Z s'.C.a x _ _).symm

/-- **And the rider's code word.** -/
theorem wordFr_written (φ : s'.cFr.J → GE) (ψ : s'.cFr.Q → GE)
    (hF : ∀ b j, φ (b, j) = fM (Sz.rowNo b) j.val) (hT : ∀ b q, ψ (b, q) = fT (Sz.rowNo b) q.val)
    (hcol : ∀ x, x < 2 ^ s'.C.a → Fmt.M1.stageCol s'.st 0 (2 ^ s'.st.k)
      (stageColW s' tabM tabZ tM tZ fM fT x) = some (col x)) :
    wordFr s' col = s'.cFr.enc φ ψ := by
  funext x a
  obtain ⟨b, ⟨⟩⟩ := a
  obtain ⟨c, hc, -, -, h3⟩ := stageCol_written s' tabM tabZ tM tZ fM fT x.val
  obtain rfl : c = col x.val := Option.some.inj (hc.symm.trans (hcol x.val x.isLt))
  show vec (col x.val).fresh (Sz.rowNo b) =
    (ldRep s'.Z s'.C.a).enc (fun j => φ (b, j)) (fun q => ψ (b, q)) x ()
  rw [h3 _ (rowNo_lt b), funext (hF b), funext (hT b)]
  exact (enc_ldRep s'.Z s'.C.a x _ _).symm

end Johnson.Prover.Link
