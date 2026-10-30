-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Written.lean: a tree whose written columns hold code words' symbols, read as
the library reads a sent message, is that message's encoding. The library reads a written oracle as
the sent word of a message (`Mb.ofOrc`) and as the word of a stage's fresh mask rows (`frOf`), both
in OnBytes/Slice/KeyGroup.lean. Here the oracle is the one that a function from positions to columns
makes (`orcOf`, Johnson/Prover/Link/HyStage.lean). A symbol is written as
Johnson/Prover/Link/Base.lean writes it (`symG`). Definitions and theorems, general in the format of
the message or stage, the round's data and the columns. The file uses nothing of the frame for an
honest side (Johnson/Desc/ProofFile/Honest/Frame.lean), and its imports do not reach that file.

In the list: d is a round's data (`PQ.RD`, Run/PlanQTypes.lean); its tree has `PQ.posN d.tree`
positions and columns of `PQ.colW d.tree` words. f gives for each position a column, a list of
64-bit words. M is the format of a sent message (`Mb`): C is the code of a main row, Z the code of a
mask row, a the depth of the message's tree, nM and nZ the numbers of main and mask rows. L says
where the rows are in a column (`Lay`): oM and oZ are the first word of the main symbols and of the
mask symbols; `base` says that a main symbol is one word (otherwise three). m is a message of the
code `M.cd` and r its tail. s is a stage (`Sg`, OnBytes/Slice/Stage.lean), φ a message of its code
`s.cFr` and ψ its tail. A code's length is 2 ^ a at its own a.

  `ofOrc_enc`: the column at x holds, from the message's two first words on, the symbols at x of
    the message's main rows (one word each over the base field, else three) and, at x modulo the
    mask code's length, of its mask rows ⟹ `M.ofOrc L d (orcOf d f) = M.cd.enc m r`
  `frOf_enc`: the like for a stage's fresh mask rows in a tree of depth a
  `wordAt_orcOf`, `symF_orcOf`, `symW_orcOf`: at a position x of the tree of d at which the column
    `f x` has the tree's width, the library's readers at `orcOf d f` read `f x`: `wordAt`
    (OnBytes/Slice/CorePeel.lean) returns word number j of `f x`, and 0 from its length on; `symF`
    and `symW` (OnBytes/Slice/KeyGroup.lean) return `read1 (f x) k` and `read3 (f x) k`
  `read1 c k`, `read3 c k`: definitions: word number k of the column c as an element of the base
    field in the extension field; the three words from word number k on as an element of the
    extension field. A word that the column does not have counts 0

By what. `wordAt_orcOf` unfolds `wordAt`; `symF_orcOf` and `symW_orcOf` rewrite by it. The two main
theorems go symbol by symbol: the reader is rewritten by `symF_orcOf` or `symW_orcOf`, then by the
hypothesis on the column; `enc_ldOf` and `enc_ldRep` (Johnson/Prover/Link/SymTie.lean) say that the
symbols of the library's encoders `ldOf` and `ldRep` (OnBytes/Slice/LinkAt.lean) are `symG`.
Of these four, `frOf_enc` calls `symW_orcOf` and `enc_ldRep`. `ext0` (same file as `enc_ldOf`) makes
of a function on Fin n a function on ℕ, 0 from n on; `ext0_val` (same file): on Fin n it is that
function again.

Hypotheses of `ofOrc_enc`. hpos: the tree of d has 2 ^ M.a positions. hlen: at each of them the
column has the tree's width. hC: if the message has a main row, `M.C.a` = `M.a`. hMain: at every
position x and every main row i, `read1 (f x)` at word L.oM + i if `L.base`, else `read3 (f x)` at
word L.oM + 3 * i, is `symG M.C x` at main row i of m and of r. hMask: at every position x and every
mask row i, `read3 (f x)` at word L.oZ + 3 * i is `symG M.Z`, at x modulo the length of M.Z, at mask
row i of m and of r.

Hypotheses of `frOf_enc`. hpos, hlen: the same at the depth a. hz: `s.Z.a` ≤ a. hF: at every
position x and every row b (`Fin s.h → Bool`), `read3 (f x)` at word oF + 3 * `Sz.rowNo b` is
`symG s.Z`, at x modulo the length of s.Z, at row b of φ and of ψ. No hypothesis ties a to `s.C.a`:
`frOf` reads the column at the stage's position modulo 2 ^ a.

Limits. Every hypothesis on the columns is assumed, not proved, and is asked at every position of
the tree. Who proves them for a given sender's columns is not said here. At a message without rows
(nM = 0 and nZ = 0) `ofOrc_enc` is vacuous: a word of `M.cd` has no symbol. Nothing on trees' hashes
or salts, on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Prover.Link.HyStage
import OnBytes.Slice.KeyGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes.Slice Cb _root_.Run
open Johnson.Prover.Link (symG orcOf ext0 ext0_val enc_ldOf enc_ldRep)

/-- Word number k of a column, as an element of the base field in the extension field. -/
def read1 (c : List UInt64) (k : ℕ) : GE := algebraMap GF GE (toF (c.getD k 0))

/-- The three words from word number k on of a column, as an element of the extension field. -/
def read3 (c : List UInt64) (k : ℕ) : GE := toE (c.getD k 0, c.getD (k + 1) 0, c.getD (k + 2) 0)

section Made
variable (d : PQ.RD) (f : ℕ → List UInt64) (x : ℕ) (hx : x < PQ.posN d.tree)
  (hl : (f x).length = PQ.colW d.tree)
include hx hl

/-- Word number j of the column at x of `orcOf d f` is word number j of `f x`, and 0 from its length
on. -/
theorem wordAt_orcOf (j : ℕ) : wordAt d (orcOf d f) x j = (f x).getD j 0 := by
  unfold wordAt
  rw [dif_pos hx]
  by_cases hj : j < PQ.colW d.tree
  · rw [dif_pos hj]
    rfl
  · rw [dif_neg hj, List.getD_eq_default _ _ (by rw [hl]; exact Nat.le_of_not_lt hj)]

theorem symF_orcOf (k : ℕ) : symF d (orcOf d f) x k = read1 (f x) k := by
  unfold symF read1
  rw [wordAt_orcOf d f x hx hl]

theorem symW_orcOf (k : ℕ) : symW d (orcOf d f) x k = read3 (f x) k := by
  unfold symW read3
  rw [wordAt_orcOf d f x hx hl, wordAt_orcOf d f x hx hl, wordAt_orcOf d f x hx hl]

end Made

/-- **A tree whose columns hold a message's rows' symbols is read as the message's encoding.** -/
theorem ofOrc_enc (M : Mb) (L : Lay) (d : PQ.RD) (f : ℕ → List UInt64)
    (hpos : PQ.posN d.tree = 2 ^ M.a) (hlen : ∀ x, x < 2 ^ M.a → (f x).length = PQ.colW d.tree)
    (hC : 0 < M.nM → M.C.a = M.a) (m : M.cd.J → GE) (r : M.cd.Q → GE)
    (hMain : ∀ x, x < 2 ^ M.a → ∀ i : Fin M.nM,
      (if L.base then read1 (f x) (L.oM + i.val) else read3 (f x) (L.oM + 3 * i.val)) =
        symG M.C x (ext0 fun j => m (.inl (i, j))) (ext0 fun q => r (.inl (i, q))))
    (hMask : ∀ x, x < 2 ^ M.a → ∀ i : Fin M.nZ, read3 (f x) (L.oZ + 3 * i.val) =
        symG M.Z (x % 2 ^ M.Z.a) (ext0 fun j => m (.inr (i, j))) (ext0 fun q => r (.inr (i, q)))) :
    M.ofOrc L d (orcOf d f) = M.cd.enc m r := by
  funext p
  rcases p with x | x
  · funext a
    obtain ⟨i, ⟨⟩⟩ := a
    have hx : x.val < 2 ^ M.a :=
      lt_of_lt_of_eq x.isLt
        (congrArg (2 ^ ·) (hC (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)))
    show (if L.base then symF d (orcOf d f) x.val (L.oM + i.val)
        else symW d (orcOf d f) x.val (L.oM + 3 * i.val)) =
      (ldOf M.C M.a).enc (fun j => m (.inl (i, j))) (fun q => r (.inl (i, q))) x ()
    rw [symF_orcOf d f x.val (by rw [hpos]; exact hx) (hlen _ hx),
      symW_orcOf d f x.val (by rw [hpos]; exact hx) (hlen _ hx), hMain x.val hx i,
      ← enc_ldOf M.C M.a x, ext0_val, ext0_val]
  · funext a
    obtain ⟨i, ⟨⟩⟩ := a
    show symW d (orcOf d f) x.val (L.oZ + 3 * i.val) =
      (ldRep M.Z M.a).enc (fun j => m (.inr (i, j))) (fun q => r (.inr (i, q))) x ()
    rw [symW_orcOf d f x.val (by rw [hpos]; exact x.isLt) (hlen _ x.isLt), hMask x.val x.isLt i,
      ← enc_ldRep M.Z M.a x, ext0_val, ext0_val]

/-- **A tree whose columns hold a stage's fresh mask rows' symbols is read as their encoding.** a:
the tree's depth. oF: the first word of these symbols in a column. -/
theorem frOf_enc (s : Sg) (a oF : ℕ) (d : PQ.RD) (f : ℕ → List UInt64)
    (hpos : PQ.posN d.tree = 2 ^ a) (hlen : ∀ x, x < 2 ^ a → (f x).length = PQ.colW d.tree)
    (hz : s.Z.a ≤ a) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hF : ∀ x, x < 2 ^ a → ∀ b : Fin s.h → Bool, read3 (f x) (oF + 3 * Sz.rowNo b) =
        symG s.Z (x % 2 ^ s.Z.a) (ext0 fun j => φ (b, j)) (ext0 fun q => ψ (b, q))) :
    frOf s a oF d (orcOf d f) = s.cFr.enc φ ψ := by
  funext x c
  obtain ⟨b, ⟨⟩⟩ := c
  have hx : x.val % 2 ^ a < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
  show symW d (orcOf d f) (x.val % 2 ^ a) (oF + 3 * Sz.rowNo b) =
    (ldRep s.Z s.C.a).enc (fun j => φ (b, j)) (fun q => ψ (b, q)) x ()
  rw [symW_orcOf d f _ (by rw [hpos]; exact hx) (hlen _ hx), hF _ hx b,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hz), ← enc_ldRep s.Z s.C.a x, ext0_val, ext0_val]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.wordAt_orcOf
#print axioms ProofFile.Honest.K12.symF_orcOf
#print axioms ProofFile.Honest.K12.symW_orcOf
#print axioms ProofFile.Honest.K12.ofOrc_enc
#print axioms ProofFile.Honest.K12.frOf_enc
#print axioms ProofFile.Honest.K12.read1
#print axioms ProofFile.Honest.K12.read3
