-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/CodingPage160.lean.
Run/CodingPage160.lean: the partial code of the first chain query in the programs' format.
Definitions that compute, with their laws. After the format page's rules R2.2, R2.4 (the oracle's
strings), R3.1 (the number of a chain's first value), R4.6 (what is hashed for it), not held
against the page as it ships; and after a convention of this library
that the protocol has a trivial round 0 whose query is that call: the one digest of the query's list
stands for the parameters' digest, the query's salt for the run's value (an empty salt: a chain
without random bytes), the record is empty.
   digOf l, digOf_ofFn, ofFn_digOf  a digest from 256 bits, and back
   runOf, saltOf  the typed salt as "the run's value or none", and back
   hdr160 lab  the constant header of the call: half 0, the number of a first value, no tree, the
       chain's label as index, no start
   pFirst0 lab stm unstm h1 h2 : PCode (digest × statement × salt)  written exactly if the statement
       has a spelling of fewer than 2^64 bytes and the salt is empty or has 256 bits: the header,
       then the bits of the bytes of R4.6 (Fmt/Rules4.lean: firstBytes); read back by stripping the
       header, asking for whole bytes, and the reader of Fmt/Rules4Laws.lean; a record that is not
       empty is refused. The statement's spelling is a parameter: stm, unstm with the two laws of a
       partial code
   fbSel0, fbMk0  a chain query of round 0 in the first format, with a list of one digest, no root
       and the trivial round's plain part p0, as (digest, statement, salt), and back. p0 and a test
       for it are parameters
   pFirst .. : PCode (FbIn 256 L t)  the same on typed queries, at any of the three tags t (read off
       p0's type)
   pFirst0_put  what is written is the bits of the format's string of the call
   pFirst0_hdr, pFirst_hdr  every string begins with the header
The block. This is the string of the chain value of the answer to a round-0 query; the blocks of the
verifier's message of round 0 have no string in the format. The pairing of queries with blocks is
the assembly's.
What is not said. That the verifier's parser puts the parameters' digest and the run's value where
this code reads them. A run's value of 32 zero bytes is written like any other: to refuse it is a
test of the verifier, not of the spelling.

Terms: lean/GLOSSARY.md.

-/
import Run.CodingPage160
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.CodingFn
import OnBytes.TypedOracleCompiler.Run.CodingPage164
import Fmt.Rules4Laws

set_option autoImplicit false

namespace TypedOracleCompiler.Run
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol
open _root_.Run

section
variable {X : Type} (lab : Nat) (stm : Option X → Option ByteArray)
  (unstm : ByteArray → Option (Option X))

variable (h1 : ∀ x b, stm x = some b → unstm b = some x)
  (h2 : ∀ b x, unstm b = some x → stm x = some b)

include h1 in

include h2 in

end

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (p0 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool)

/-- a chain query of round 0 in the first format, with one digest, no root, the trivial round's
plain part -/
def fbSel0 (q : FbIn 256 L t) : Option (Dig 256 × Option X × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [pd] x salt, [] => if isP0 q.plain = true then some (pd, x, salt) else none
  | _, _, _ => none

def fbMk0 (a : Dig 256 × Option X × List Bool) : FbIn 256 L t :=
  ⟨0, .f1 [a.1] a.2.1 a.2.2, [], p0⟩

variable (hp : ∀ p, isP0 p = true ↔ p = p0)

include hp in
theorem fbSel0_mk (a : Dig 256 × Option X × List Bool) : fbSel0 isP0 (fbMk0 p0 a) = some a := by
  show (if isP0 p0 = true then some (a.1, a.2.1, a.2.2) else none) = some a
  rw [if_pos ((hp p0).2 rfl)]

include hp in
theorem fbMk0_sel (q : FbIn 256 L t)
    (a : Dig 256 × Option X × List Bool) (h : fbSel0 isP0 q = some a) : fbMk0 p0 a = q := by
  obtain ⟨round, head, rt, plain⟩ := q
  unfold fbSel0 at h
  split at h
  · rename_i pd x salt e1 e2 e3
    by_cases hq : isP0 plain = true
    · have h' : (if isP0 plain = true then some (pd, x, salt) else none) = some a := h
      rw [if_pos hq] at h'
      rw [← Option.some.inj h']
      have e1' : round = 0 := e1
      have e2' : head = .f1 [pd] x salt := e2
      have e3' : rt = [] := e3
      rw [e1', e2', e3', (hp plain).1 hq]
      rfl
    · have h' : (if isP0 plain = true then some (pd, x, salt) else none) = some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

variable (lab : Nat) (stm : Option X → Option ByteArray) (unstm : ByteArray → Option (Option X))
  (h1 : ∀ x b, stm x = some b → unstm b = some x) (h2 : ∀ b x, unstm b = some x → stm x = some b)

/-- THE FIRST CHAIN QUERY. -/
def pFirst : PCode (FbIn 256 L t) :=
  (pFirst0 lab stm unstm h1 h2).via
    (fbSel0 isP0) (fbMk0 p0) (fbSel0_mk p0 isP0 hp) (fbMk0_sel p0 isP0 hp)

theorem pFirst_mk (a : Dig 256 × Option X × List Bool) :
    (pFirst p0 isP0 hp lab stm unstm h1 h2).put (fbMk0 p0 a) =
      (pFirst0 lab stm unstm h1 h2).put a :=
  PCode.via_put _ _ _ _ _ a

theorem pFirst_hdr (q : FbIn 256 L t) (s : List Bool)
    (h : (pFirst p0 isP0 hp lab stm unstm h1 h2).put q = some s) : ∃ r, s = hdr160 lab ++ r := by
  have h0 : (fbSel0 isP0 q).bind (pFirst0 lab stm unstm h1 h2).put = some s := h
  cases hf : fbSel0 isP0 q with
  | none => rw [hf] at h0; cases h0
  | some a => rw [hf] at h0; exact pFirst0_hdr lab stm unstm h1 h2 a s h0

end

/-! ## Guards: the format page's toy chain (known answers, both fields; see the head): the
string that is written, asked of the format's oracle, gives the chain's first value, with and
without random bytes; it is read back; a bit more, a bit less, another label are refused -/

namespace G160

end G160
end TypedOracleCompiler.Run
