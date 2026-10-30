-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/DigestPoint.lean: the parameters' digest as a constant, for a reader at any function on
byte strings.

The strict reader begins by hashing the parameter bytes (the format's call number 169). The library
spells the compiled verifier's typed first query as a call of the format's hash (`Run.PQ.firstX`),
and that spelling holds the format's own digest of these bytes as a constant, whatever O is. So
OnBytes/Tie/StoredAt.lean asks of a function O on byte strings that the hash which it induces gives
that digest (`DigestAt`). A function drawn at random does not.

This file takes any O and changes it at one string: `pinned O params` answers the string of that one
call with the format's digest of `params`, and every other string as O does. The reader at
`pinned O params` meets `DigestAt`, and the typed oracle functions that `pinned O params` induces
are those that O induces, because no typed query is spelled as a call number 169. So an experiment
with a random O needs no O with a fixed point: the conclusion of `readInPinned_compiled` is at O
itself.

Main definitions: `digestStr`, `pinned`.
Main theorems.
 `oStr_number`      the number of a call can be read off its string, modulo 65536.
 `oStr_ne_digestStr`, `HO_pinned`   under a number other than 169 the hash that `pinned O params`
                    induces is the hash that O induces.
 `digestAt_pinned`, `size_pinned`   `pinned O params` meets the two hypotheses on a function.
 `size_oB`          the function on byte strings that an oracle on bit strings induces has answers
                    of 32 bytes.
 `famX_pinned`      the typed oracle functions of `pinned O params` are those of O.
 `readInPinned_compiled`   if the reader at `pinned O S.base.params` has read the chain and the
                    decision says yes on its view, the compiled verifier under the typed oracle
                    functions that O ITSELF induces accepts what was read. The one hypothesis on O:
                    its answers have 32 bytes.
 `pinned_oracle`    for parameter bytes within the hash's domain (`Fmt.hDom`: here, at most
                    2^32 - 144 bytes), `pinned Fmt.oracle params` is `Fmt.oracle`.
 `readInPinned_oracle`   within `smallFX` the reader at `pinned Fmt.oracle S.base.params` is the
                    program's reader. "The program" is the Lean port built from OnBytes/, not the
                    C++ verifier.

What is not claimed. Nothing on soundness, and no probability. The reader at `pinned O params` is
not the reader at O: at one string it takes BLAKE2b's value, a constant that depends on `params`
alone. Whoever states an experiment with a random O through this file has BLAKE2b's digest of the
parameter bytes in the reader as a plain value, and must say so. `pinned O params` depends on
`params`: chains with other parameter bytes want another function. That the reader makes one call
under the number 169 is read off its text (Fmt/Rules8X.lean, `readChainX`) and is no theorem here.
The reader also asks O for the run's value (the format's call number 172). No typed query is spelled
so: in the typed string the run's value is the salt, and the compiled verifier does not test where
it comes from. That the reader at O reads any file, for any O other than `Fmt.oracle`, is not
proved; a test shows one file of a made-up example read at one other function
(a test that is not in this library). The typed oracle functions that a random O induces are not
shown
to be random typed oracles: they answer every typed query without a call with zeros, and the map
from typed queries to strings is not shown to be one to one (Run/CodingFn.lean). A constant `stm`
meets the hypothesis on the statement, and then the typed first query does not read the roots; the
root of a table that the chain does not open is free (head of OnBytes/Tie/StoredMain.lean). How many
strings that reader asks O for is not said here (OnBytes/Tie/CostX.lean, AskX.lean). The program
does not call any function of this file. Nothing on the C++ verifier or on machine code.

-/
import OnBytes.Tie.StoredAt
import Run.OCompM
import Run.CodingPage160

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-! ## The number of a call, read off its string -/

/-- `Fmt.fit n` gives n bytes. -/
theorem size_fit (n : ℕ) (b : ByteArray) : (Fmt.fit n b).size = n := by
  unfold Fmt.fit
  split
  · rw [ByteArray.size_extract]
    omega
  · rw [ByteArray.size_append, Fmt.size_zeros]
    omega

/-- The parameter block has 64 bytes, whatever the start. -/
theorem size_pblock_any (n : ℕ) (s : ByteArray) : (Fmt.pblock n s).size = 64 := by
  unfold Fmt.pblock
  rw [ByteArray.size_append, ByteArray.size_append, Fmt.size_four, Fmt.size_zeros, size_fit]

/-- The lowest 16 bits of the word at byte 65 of a call's string are the call's number modulo 65536.
No condition on the arguments. -/
theorem oStr_number (h : UInt8) (n t i : ℕ) (s b : ByteArray) :
    (Fmt.wordAt (Fmt.oStr h n t i s b) 65).toNat % 65536 = n % 65536 := by
  have h1 := Fmt.wordAt_mid (⟨#[h]⟩ ++ Fmt.pblock n s) (Fmt.label n t i) b 0
    (by have := Fmt.size_label n t i; omega)
  rw [ByteArray.size_append, Fmt.size_one, size_pblock_any] at h1
  have h2 := Fmt.wordAt_mid ByteArray.empty (Fmt.u64n (n + 65536 * t)) (Fmt.u64n i) 0
    (by have := Fmt.size_u64n (n + 65536 * t); omega)
  rw [ByteArray.empty_append, ByteArray.size_empty] at h2
  have h3 : Fmt.wordAt (Fmt.oStr h n t i s b) 65 = Fmt.wordAt (Fmt.u64n (n + 65536 * t)) 0 :=
    Eq.trans h1 h2
  rw [h3]
  unfold Fmt.u64n
  rw [Fmt.wordAt_u64, UInt64.toNat_ofNat']
  omega

/-! ## One string pinned -/

/-- The string of the call that hashes the parameter bytes. -/
def digestStr (params : ByteArray) : ByteArray := Fmt.oStr 0 169 0 1 Fmt.zero32 params

/-- O, but for one string: the string of the call that hashes `params` is answered with the format's
own digest of `params`, which is a value of BLAKE2b. -/
def pinned (O : ByteArray → ByteArray) (params : ByteArray) : ByteArray → ByteArray :=
  fun s => if s = digestStr params then Fmt.paramsDigest params else O s

/-- The string of a call whose number is not 169 modulo 65536 is not the pinned string. -/
theorem oStr_ne_digestStr (h : UInt8) (n t i : ℕ) (s b params : ByteArray)
    (hn : n % 65536 ≠ 169) : Fmt.oStr h n t i s b ≠ digestStr params := by
  intro e
  have h1 := oStr_number h n t i s b
  have h2 := oStr_number 0 169 0 1 Fmt.zero32 params
  unfold digestStr at e
  rw [e, h2] at h1
  exact hn (by omega)

/-- Under such a number the hash that `pinned O params` induces is the hash that O induces. -/
theorem HO_pinned (O : ByteArray → ByteArray) (params : ByteArray) (n t i : ℕ) (s b : ByteArray)
    (hn : n % 65536 ≠ 169) : Fmt.HO (pinned O params) n t i s b = Fmt.HO O n t i s b := by
  have hp : ∀ h : UInt8, pinned O params (Fmt.oStr h n t i s b) = O (Fmt.oStr h n t i s b) :=
    fun h => if_neg (oStr_ne_digestStr h n t i s b params hn)
  unfold Fmt.HO
  rw [hp 0, hp 1]

/-- The hash that `pinned O S.base.params` induces gives the format's digest of the parameter
bytes. -/
theorem digestAt_pinned (O : ByteArray → ByteArray) (S : Fmt.SpecX) :
    DigestAt (pinned O S.base.params) S := by
  unfold DigestAt Fmt.HO
  rw [if_neg (by decide)]
  show (if Fmt.oStr 0 169 0 1 Fmt.zero32 S.base.params = digestStr S.base.params then
    Fmt.paramsDigest S.base.params else O _) = _
  exact if_pos rfl

/-- If O's answers have 32 bytes, so have those of `pinned O params`. -/
theorem size_pinned (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (params : ByteArray) :
    ∀ s, (pinned O params s).size = 32 := by
  intro s
  unfold pinned
  split
  · exact Fmt.size_H 169 0 1 Fmt.zero32 params
  · exact hO s

/-- The function on byte strings that an oracle f on bit strings induces (`Run.oB f`) has answers of
32 bytes. -/
theorem size_oB (f : ZKCP.Oracle 256) (s : ByteArray) : (oB f s).size = 32 :=
  size_digToBytes _

/-- At a call whose number is not 169 modulo 65536, and where there is no call, the answers of
`pinned O params` and of O are the same. -/
theorem ansOf_pinned (O : ByteArray → ByteArray) (params : ByteArray) (c : Option Fmt.OQ)
    (hc : ∀ q, c = some q → q.number % 65536 ≠ 169) :
    ansOf (pinned O params) c = ansOf O c := by
  cases c with
  | none => rfl
  | some q =>
    have hne : strOf q ≠ digestStr params :=
      oStr_ne_digestStr q.half q.number q.tree q.index q.start q.bytes params (hc q rfl)
    show bytesToDig (pinned O params (strOf q)) = bytesToDig (O (strOf q))
    unfold pinned
    rw [if_neg hne]

/-! ## No typed query is a call number 169 -/

/-- `fbCall` spells a chain query as a call number 160 or 162. -/
theorem fbCallX_number (D : XD) (dec : View → Bool) (K : ℕ) (q : FbIn 256 (D.L dec) .link)
    (j : Fin (K + 1)) (c : Fmt.OQ) (h : fbCall (PDX D dec) K q j = some c) :
    c.number = 160 ∨ c.number = 162 := by
  unfold fbCall at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact Or.inl rfl
    · cases h
  · injection h with h
    subst h
    exact Or.inr rfl
  · cases h

/-- A chain query is spelled as a call number 160 or 162. -/
theorem firstX_number (D : XD) (dec : View → Bool) (K : ℕ) (q : FbIn 256 (D.L dec) .link)
    (j : Fin (K + 1)) (c : Fmt.OQ) (h : firstX D dec K q j = some c) :
    c.number = 160 ∨ c.number = 162 := by
  unfold firstX at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact Or.inl rfl
    · cases h
  · cases h
  · exact fbCallX_number D dec K q j c h

/-- A leaf query is spelled as a call number 164 or 174. -/
theorem leafX_number (D : XD) (dec : View → Bool) (q : LeafIn (D.L dec)) (c : Fmt.OQ)
    (h : leafX D dec q = some c) : c.number = 164 ∨ c.number = 174 := by
  unfold leafX at h
  split at h
  · split at h
    · injection h with h
      subst h
      exact Or.inr rfl
    · cases h
  · unfold leafCall at h
    split at h
    · obtain ⟨s, -, hs⟩ := Option.map_eq_some_iff.1 h
      subst hs
      exact Or.inl rfl
    · cases h

/-- The typed oracle functions that `pinned O params` induces are those that O induces. -/
theorem famX_pinned (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (params : ByteArray)
    (K : ℕ) : famX D dec (pinned O params) K = famX D dec O K := by
  funext o
  match o with
  | .leaf =>
    funext q
    exact ansOf_pinned O params _ fun c hc => by
      rcases leafX_number D dec q c hc with h | h <;> rw [h] <;> decide
  | .node =>
    funext q
    exact ansOf_pinned O params (nodeCallC D.base.cfg q) fun c hc => by
      have h : c.number = 166 := by
        unfold nodeCallC at hc
        injection hc with hc
        subst hc
        rfl
      rw [h]
      decide
  | .fb .link =>
    funext q
    refine Prod.ext (funext fun k => ?_) ?_
    · exact ansOf_pinned O params _ fun c hc => by
        rcases firstX_number D dec K q _ c hc with h | h <;> rw [h] <;> decide
    · exact ansOf_pinned O params _ fun c hc => by
        rcases firstX_number D dec K q _ c hc with h | h <;> rw [h] <;> decide
  | .fb .test => rfl
  | .fb .onl => rfl
  | .fbw _ _ => rfl
  | .rleaf => rfl
  | .rnode => rfl
  | .g _ => rfl
  | .ann => rfl
  | .other => rfl

/-! ## The tie with no condition on O but the length of its answers -/

/-- **If the reader at `pinned O S.base.params` has read a chain that opens stored tables, and a
decision says yes on its view, the compiled verifier under the typed oracle functions that O itself
induces accepts what was read.** O is any function on byte strings with answers of 32 bytes. The
other hypotheses are those of `readInAtX_compiled` without `DigestAt`. The reader takes BLAKE2b's
digest of the parameter bytes as a constant. By `HO_pinned` its calls under other numbers go to O;
that it makes one call under 169 is read off its text and is no theorem here. An implication between
two yeses: nothing on soundness; no probability. -/
theorem readInPinned_compiled (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (S : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32) (hw : withinX S = true)
    (hst : S.base.statement = stm r0 r1)
    (hroot : ∀ t ∈ S.stored.flatten,
      Fmt.itemRoot S.base.statement t.item = some (if t.item == 1 then r1 else r0))
    (s : Session) (b : ByteArray) (i : ℕ) (r : ChainRead) (s' : Session)
    (e : readInAt (pinned O S.base.params) S b i s = some (r, s')) (hdec : dec r.view = true) :
    CompiledAcceptsXAt O S stm dec r0 r1 r.out := by
  have h := readInAtX_compiled (pinned O S.base.params) (size_pinned O hO _) S stm dec r0 r1 h0 h1
    hw hst hroot (digestAt_pinned O S) s b i r s' e hdec
  unfold CompiledAcceptsXAt at h ⊢
  rw [famX_pinned] at h
  exact h

/-- For parameter bytes within the hash's domain, pinning changes nothing at the format's own
oracle. -/
theorem pinned_oracle (params : ByteArray)
    (hd : Fmt.hDom 169 0 1 Fmt.zero32 params = true) :
    pinned Fmt.oracle params = Fmt.oracle := by
  funext s
  unfold pinned
  split
  · rename_i hs
    have h := Fmt.HO_oracle 169 0 1 Fmt.zero32 params hd
    unfold Fmt.HO at h
    rw [if_neg (by decide)] at h
    rw [hs]
    exact h.symm
  · rfl

/-- Within `smallFX` the reader at `pinned Fmt.oracle S.base.params` is the program's reader. -/
theorem readInPinned_oracle (S : Fmt.SpecX) (b : ByteArray) (i : ℕ) (s : Session)
    (hsm : smallFX S b = true) :
    readInAt (pinned Fmt.oracle S.base.params) S b i s = readIn S b i s := by
  have hB : S.base.params.size ≤ 2 ^ 32 - 144 := by
    have hsm' := hsm
    unfold smallFX smallF smallB at hsm'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm'
    exact hsm'.1.1.1.1.1.1
  rw [pinned_oracle _ (dom0 169 1 S.base.params (by decide) (by decide) (by decide) hB)]
  exact readInAt_oracle S b i s hsm

end OnBytes.Tie
