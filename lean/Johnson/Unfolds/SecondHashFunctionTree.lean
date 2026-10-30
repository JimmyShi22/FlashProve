-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SecondHashFunctionTree.lean: WHETHER the second hash function's tree hash returns, as a test on a
number; and with it: `hParO secondHashFunction pol KL (some lay)` returns, from three sizes.
Why. `publicOfO` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) calls the tree hash in one place:
`let _ ← hParO o pol KL layout`: the digest is thrown away; the call must only RETURN. At the stored
full-size files that one line costs 486 calls of the second hash function (1,924 compressions) a run
(a count by Lean's evaluator: the hash behind a line to stderr at each call), over
pieces that are cut out of an array by their index. Whether
it returns hangs on the files' sizes alone (`isSome_olderTK`, OnBytes/K/ServedFreeItem.lean). Here
that is a function with code on the size.
  `lvOk k sz`, `tkOk sz`: do k levels end at 32 bytes; is sz a number of whole words, at least 32.
  `isSome_olderLevels_eq`, `isSome_olderTK_eq`, `isSome_fmtOlderTK_eq`: the tree hash returns just
    where the test accepts the size.
  `textSize n`: the size of the list that `textTHO` hashes for a text of n bytes.
  `textTHO_returns`, **`hParO_returns`**. `tkOk_full`: the test at the stored example's three sizes.
Whose text. The tests follow `OnBytes.secondHashFunctionTreeLevels` and `secondHashFunctionTree` (OnBytes/Hash/SecondHashFunction.lean).
Source. `secondHashFunction`, of which these laws speak, calls the functions of Run/Blake2b/Hash.lean; no text
of that file is followed here.
That file's head says (its lines 10 to 13, copied here):
The definitions of sections 2 to 5 are adapted from blake2b-ref.c, blake2.h and blake2-impl.h of the
BLAKE2 reference source code package (reference C implementations), Copyright 2012, Samuel Neves.
The files' head offers "the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at your
option"; they are used here under CC0 1.0 Universal (SPDX: CC0-1.0).
Limits. Nothing on the digests' values: whoever needs one has to compute it. At `secondHashFunction` alone.
A LAW ON `publicOfO`'s VALUE: that the digest is thrown away THERE does not say that the verifier
makes no use of the three files' bytes: `VerifierAndGoals.verifyAt` (Ladder.lean) calls `readConfig Z` and
hands its value on to `D.readMore` and `D.input`: not traced here.

-/
import OnBytes.K.ServedFreeItem
import OnBytes.Tie.Decl.RequestItemLaw
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Config
open VerifiableInference.PlanWritten
open OnBytes.K (size_olderLevel size_olderTK size_word32)
open OnBytes.Tie.Decl.RequestItemLaw (olderTK_eq)

theorem size_zeroBytes (n : Nat) : (Fmt.zeroBytes n).size = n := by
  show (Array.replicate n (0 : UInt8)).size = n
  exact Array.size_replicate

/-- Do k levels of the tree hash, from sz bytes, end at 32 bytes. -/
def lvOk : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, sz => 32 * ((sz + 511) / 512) == 32 || lvOk k (32 * ((sz + 511) / 512))

theorem isSome_olderLevels_eq : ∀ (k num : Nat) (w : ByteArray),
    (secondHashFunctionTreeLevels k num w).isSome = lvOk k w.size
  | 0, _, _ => rfl
  | k + 1, num, w => by
    unfold secondHashFunctionTreeLevels lvOk
    dsimp only
    rw [size_olderLevel]
    by_cases hc : (32 * ((w.size + 511) / 512) == 32) = true
    · rw [if_pos hc, hc]
      rfl
    · rw [if_neg hc, isSome_olderLevels_eq k 11, size_olderLevel, Bool.eq_false_iff.2 hc,
        Bool.false_or]

/-- Does the tree hash return at sz bytes. -/
def tkOk (sz : Nat) : Bool := !(sz % 4 != 0 || decide (sz < 32)) && lvOk 16 sz

theorem isSome_olderTK_eq (w : ByteArray) : (secondHashFunctionTree w).isSome = tkOk w.size := by
  unfold secondHashFunctionTree tkOk
  by_cases hc : (w.size % 4 != 0 || decide (w.size < 32)) = true
  · rw [if_pos hc, hc]
    rfl
  · rw [if_neg hc, isSome_olderLevels_eq, Bool.eq_false_iff.2 hc]
    rfl

theorem isSome_fmtOlderTK_eq (w : ByteArray) : (Fmt.olderTK secondHashFunction w).isSome = tkOk w.size := by
  rw [← olderTK_eq, isSome_olderTK_eq]

/-- Where the test accepts, the tree hash returns 32 bytes. -/
theorem fmtOlderTK_returns {w : ByteArray} (h : tkOk w.size = true) :
    ∃ d, Fmt.olderTK secondHashFunction w = some d ∧ d.size = 32 := by
  have hs := isSome_fmtOlderTK_eq w
  rw [h] at hs
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨d, hd, size_olderTK (by rw [olderTK_eq]; exact hd)⟩

/-- The size of the list that `textTHO` hashes for a text of n bytes. -/
def textSize (n : Nat) : Nat := 4 + (n + (4 - n % 4) % 4) + 28

theorem size_textList (t : ByteArray) :
    (word32 t.size ++ OnBytes.textWords t ++ Fmt.zeroBytes 28).size = textSize t.size := by
  unfold OnBytes.textWords textSize
  simp only [ByteArray.size_append, size_word32, size_zeroBytes]

theorem textTHO_returns {t : ByteArray} (h1 : t.size < 2 ^ 32)
    (h2 : tkOk (textSize t.size) = true) :
    ∃ d n, textTHO secondHashFunction t = .ok (d, n) ∧ d.size = 32 := by
  obtain ⟨d, hd, hs⟩ := fmtOlderTK_returns (w := word32 t.size ++ OnBytes.textWords t ++
    Fmt.zeroBytes 28) (by rw [size_textList]; exact h2)
  refine ⟨d, (word32 t.size ++ OnBytes.textWords t ++ Fmt.zeroBytes 28).size / 4, ?_, hs⟩
  unfold textTHO refuseIf
  rw [if_neg (by simpa using h1)]
  show (match Fmt.olderTK secondHashFunction _ with | some d => _ | none => _) = _
  rw [hd]
  rfl

theorem tkOk_108 : tkOk 108 = true := by decide

/-- The test at three numbers, TYPED: 2,629 · 2,784 · 224,975: the sizes that Ladder/Stored.lean's
head and Ladder/Guards.lean's `#guard` give for the stored full-size example's three files. No
theorem here says that `storedPublicFiles`'s fields have these sizes. -/
theorem tkOk_full :
    tkOk (textSize 2629) = true ∧ tkOk 2784 = true ∧ tkOk (textSize 224975) = true := by decide

/-- **`hParO` at the second hash function returns, from three sizes.** -/
theorem hParO_returns {pol KL lay : ByteArray} (hp : pol.size < 2 ^ 32)
    (hp' : tkOk (textSize pol.size) = true) (hk : tkOk KL.size = true) (hl : lay.size < 2 ^ 32)
    (hl' : tkOk (textSize lay.size) = true) : ∃ x, hParO secondHashFunction pol KL (some lay) = .ok x := by
  obtain ⟨dp, np, ep, sp⟩ := textTHO_returns hp hp'
  obtain ⟨dl, nl, el, sl⟩ := textTHO_returns hl hl'
  obtain ⟨dk, ek, sk⟩ := fmtOlderTK_returns hk
  have hheld : klHeld KL = .ok () := by
    unfold klHeld refuseIf
    have : (KL.size % 4 != 0 || decide (KL.size < 32)) = false := by
      unfold tkOk at hk
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
      exact hk.1
    rw [this]
    rfl
  obtain ⟨x, hx, -⟩ := fmtOlderTK_returns
    (w := dp ++ word32 np ++ dk ++ word32 (klWords KL) ++ dl ++ word32 nl) (by
      simp only [ByteArray.size_append, size_word32, sp, sk, sl]
      exact tkOk_108)
  refine ⟨x, ?_⟩
  unfold hParO parDigestsO hParOfO
  simp only [ep, el, ek, hheld, hx, bind, Except.bind, pure, Except.pure]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.size_zeroBytes
#print axioms Johnson.Unfolds.isSome_olderLevels_eq
#print axioms Johnson.Unfolds.isSome_olderTK_eq
#print axioms Johnson.Unfolds.isSome_fmtOlderTK_eq
#print axioms Johnson.Unfolds.fmtOlderTK_returns
#print axioms Johnson.Unfolds.size_textList
#print axioms Johnson.Unfolds.textTHO_returns
#print axioms Johnson.Unfolds.tkOk_108
#print axioms Johnson.Unfolds.tkOk_full
#print axioms Johnson.Unfolds.hParO_returns
