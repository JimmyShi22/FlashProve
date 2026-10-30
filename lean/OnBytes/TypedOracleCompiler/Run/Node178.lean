-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/Node178.lean: THE CODE OF A VERTEX QUERY AT ANY CALL NUMBER; AT 178: THE REQUEST
(BINDING) TREE's VERTICES.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY: the typed oracle rnode (l, r) is, on bytes, the call 178, tree 0, index 0, start cfg, bytes l ‖
r (not checked here). The sibling's page sends rnode behind the escape; the library's pNode has the
number 166 written in.
  pNodeAt n start : PCode (bits × bits)   the library's pNode, ITS TEXT, with the call's number a
                                          parameter: (l, r) is written exactly if both have 256
                                          bits: header, l, r; read back by cutting
  pNodeAt_put      what it writes IS the bits of the format's string of the call (n, 0, 0, start;
                   the bytes of l, the bytes of r) (the library's oStr_bits: nothing of the format's
                   text is unfolded)
  pNodeAt_hdr          every string that it writes begins with the header hdr 0 n 0 0 start
  pNodeAt_166          at 166 it is the library's pNode
  pNode178 cfg         the request tree's
WHAT IS NOT SAID. That two headers with different numbers are apart (Apart.lean: t178). Which start.
That the program's climb asks these strings (the fit).

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage166

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Run

/-- A vertex query, at the call number n. -/
def pNodeAt (n : ℕ) (start : ByteArray) : PCode (List Bool × List Bool) where
  put := fun q =>
    if q.1.length = 256 ∧ q.2.length = 256 then some (hdr 0 n 0 0 start ++ (q.1 ++ q.2)) else none
  parse := fun s => match strip (hdr 0 n 0 0 start) s with
    | some t => if t.length = 512 then some (t.take 256, t.drop 256) else none
    | none => none
  parse_put := fun q s h => by
    by_cases hq : q.1.length = 256 ∧ q.2.length = 256
    · rw [if_pos hq] at h
      rw [← Option.some.inj h, strip_append]
      show (if (q.1 ++ q.2).length = 512 then some ((q.1 ++ q.2).take 256, (q.1 ++ q.2).drop 256)
          else none) = some q
      rw [if_pos (by rw [List.length_append, hq.1, hq.2]),
        List.take_left' hq.1, List.drop_left' hq.1]
    · rw [if_neg hq] at h
      cases h
  put_parse := fun s q h => by
    cases hs : strip (hdr 0 n 0 0 start) s with
    | none => simp only [hs] at h; cases h
    | some t =>
        simp only [hs] at h
        by_cases ht : t.length = 512
        · rw [if_pos ht] at h
          rw [← Option.some.inj h]
          show (if (t.take 256).length = 256 ∧ (t.drop 256).length = 256 then
                some (hdr 0 n 0 0 start ++ (t.take 256 ++ t.drop 256))
              else none) = some s
          rw [if_pos ⟨by rw [List.length_take, ht]; rfl, by rw [List.length_drop, ht]⟩,
            List.take_append_drop, eq_of_strip _ s t hs]
        · rw [if_neg ht] at h
          cases h

/-- What it writes is the format's string. -/
theorem pNodeAt_put (n : ℕ) (start : ByteArray) (l r : List Bool) (hl : l.length = 256)
    (hr : r.length = 256) :
    (pNodeAt n start).put (l, r) =
      some (bytesToBits (_root_.Fmt.oStr 0 n 0 0 start (bitsToBytes l ++ bitsToBytes r))) := by
  show (if l.length = 256 ∧ r.length = 256 then some (hdr 0 n 0 0 start ++ (l ++ r)) else none) = _
  rw [if_pos ⟨hl, hr⟩, oStr_bits, bytesToBits_append,
    bytesToBits_bitsToBytes l ((whole_iff l).2 ⟨32, hl⟩),
    bytesToBits_bitsToBytes r ((whole_iff r).2 ⟨32, hr⟩)]

/-- every string that it writes begins with the header -/
theorem pNodeAt_hdr (n : ℕ) (start : ByteArray) (q : List Bool × List Bool) (s : List Bool)
    (h : (pNodeAt n start).put q = some s) : ∃ x, s = hdr 0 n 0 0 start ++ x := by
  have h' : (if q.1.length = 256 ∧ q.2.length = 256 then some (hdr 0 n 0 0 start ++ (q.1 ++ q.2))
      else none) = some s := h
  by_cases hq : q.1.length = 256 ∧ q.2.length = 256
  · rw [if_pos hq] at h'
    exact ⟨_, (Option.some.inj h').symm⟩
  · rw [if_neg hq] at h'
    cases h'

theorem pNodeAt_166 (start : ByteArray) : pNodeAt 166 start = pNode start := rfl

/-- The request tree's vertices. -/
def pNode178 (cfg : ByteArray) : PCode (List Bool × List Bool) := pNodeAt 178 cfg

end TypedOracleCompiler.Run
