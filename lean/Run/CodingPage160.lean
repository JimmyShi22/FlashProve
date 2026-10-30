-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPage160.lean: the partial code of the first chain query in the programs' format. (160: the
number under which the format makes the hash that is a chain's first value.)

Definitions that compute, with their laws.
A partial code (`PCode`, Run/CodingPart.lean) writes some points of a type as bit strings,
injectively, with a parser. A chain query (`FbIn`, Compile/Batch/Oracles.lean) is the typed query
that draws a round's verifier message (Fiat-Shamir). The programs are the implementation that comes
with this Lean code.

The code is written after a convention of this library: the protocol has a trivial round 0 whose
query is the call that makes a chain's first value. There the one digest of the query's list stands
for the parameters' digest, the query's salt for the run's value (an empty salt: a chain without
random bytes). The record is empty there. The code is also written after the format page's rules
R2.2, R2.4 (the oracle's strings), R3.1 (the number of a chain's first value), R4.6 (what is hashed
for it), in an edition not in this repository (these rules' bytes are a second such edition's).

Main names:
  `hdr160 lab`: the constant header of the call: half 0, the number of a first value, no tree, the
    chain's label as index, no start.
  `pFirst0 lab stm unstm h1 h2`, a `PCode` on (digest, statement, salt): written exactly if the
    statement has a spelling of fewer than 2^64 bytes and the salt is empty or has 256 bits: the
    header, then the bits of the bytes of R4.6 (`firstBytes`, Fmt/Rules4.lean); read back by
    stripping the header, asking for whole bytes, and the reader of Fmt/Rules4Laws.lean; a record
    that is not empty is refused. The statement's spelling is a parameter: stm, unstm with the two
    laws of a partial code.
  `pFirst`, a `PCode (FbIn 256 L t)`: the same on typed queries (which, and how: `fbSel0`, `fbMk0`),
    at any of the three tags t (read off p0's type). The trivial round's plain part p0 and a test
    for it are parameters.
  `pFirst0_put`: where `pFirst0` writes, what is written is the bits of the format's string of the
    call (`oStr`, Fmt/Rules23.lean).

Limits: the string that `pFirst` writes is the string of the chain value of the answer to a round-0
query; the blocks of the verifier's message of round 0 have no string in the format. The pairing of
queries with blocks is the assembly's (`pFirstJ`, Run/CodingPage.lean).
This file does not say that the verifier's parser puts the parameters' digest and the run's value
where this code reads them. A run's value of 32 zero bytes is written like any other: to refuse it
is a test of the verifier, not of the spelling.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage164
import Fmt.Rules4Laws

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

/-- A digest from a list of bits. -/
def digOf (l : List Bool) : Dig 256 := fun i => l.getD i.val false

theorem digOf_ofFn (d : Dig 256) : digOf (List.ofFn d) = d := by
  funext i
  unfold digOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt),
    Option.getD_some, List.getElem_ofFn]

theorem ofFn_digOf (l : List Bool) (h : l.length = 256) : List.ofFn (digOf l) = l := by
  apply List.ext_getElem
  · rw [List.length_ofFn, h]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    unfold digOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem size_digToBytes (d : Dig 256) : (digToBytes d).size = 32 :=
  size_bitsToBytes _ 32 (by rw [List.length_ofFn])

theorem bits_digToBytes (d : Dig 256) : bytesToBits (digToBytes d) = List.ofFn d :=
  bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, by rw [List.length_ofFn]⟩)

theorem digToBytes_digOf (b : ByteArray) (h : b.size = 32) :
    digToBytes (digOf (bytesToBits b)) = b := by
  unfold digToBytes
  rw [ofFn_digOf _ (by rw [length_bytesToBits, h]), bitsToBytes_bytesToBits]

/-- The typed salt as "the run's value or none"; and back (`saltOf`). -/
def runOf (salt : List Bool) : Option ByteArray :=
  if salt.isEmpty then none else some (bitsToBytes salt)
def saltOf : Option ByteArray → List Bool
  | none => []
  | some r => bytesToBits r

theorem saltOf_runOf (salt : List Bool) (h : salt = [] ∨ salt.length = 256) :
    saltOf (runOf salt) = salt := by
  rcases h with rfl | h
  · rfl
  · have hne : salt.isEmpty = false := by
      cases salt with
      | nil => cases h
      | cons _ _ => rfl
    unfold runOf
    rw [hne]
    exact bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, h⟩)

theorem runOf_saltOf (run : Option ByteArray) (h : ∀ r, run = some r → r.size = 32) :
    runOf (saltOf run) = run := by
  cases run with
  | none => rfl
  | some r =>
      have hl : (bytesToBits r).length = 256 := by rw [length_bytesToBits, h r rfl]
      have hne : (bytesToBits r).isEmpty = false := by
        cases hb : bytesToBits r with
        | nil => rw [hb] at hl; cases hl
        | cons _ _ => rfl
      show (if (bytesToBits r).isEmpty then none else some (bitsToBytes (bytesToBits r))) = some r
      rw [hne, bitsToBytes_bytesToBits]
      rfl

theorem empty_of_size (b : ByteArray) (h : b.size = 0) : b = ByteArray.empty := by
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero h

/-- The constant header of the call. -/
def hdr160 (lab : Nat) : List Bool := hdr 0 160 0 lab _root_.Fmt.zero32

section
variable {X : Type} (lab : Nat) (stm : Option X → Option ByteArray)
  (unstm : ByteArray → Option (Option X))

def put160 (a : Dig 256 × Option X × List Bool) : Option (List Bool) :=
  (stm a.2.1).bind fun st =>
    if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
      some (hdr160 lab ++
          bytesToBits (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
    else none

def parse160 (s : List Bool) : Option (Dig 256 × Option X × List Bool) :=
  (strip (hdr160 lab) s).bind fun t =>
    if whole t = true then
      (_root_.Fmt.readFirst (bitsToBytes t)).bind fun y =>
        if y.2.2.1.size = 0 then
          (unstm y.2.1).map fun x => (digOf (bytesToBits y.1), x, saltOf y.2.2.2) else none
    else none

variable (h1 : ∀ x b, stm x = some b → unstm b = some x)
  (h2 : ∀ b x, unstm b = some x → stm x = some b)

include h1 in
theorem parse_put160 (a : Dig 256 × Option X × List Bool)
    (s : List Bool) (h : put160 lab stm a = some s) :
    parse160 lab unstm s = some a := by
  obtain ⟨pd, x, salt⟩ := a
  unfold put160 at h
  cases hst : stm x with
  | none => rw [hst] at h; cases h
  | some st =>
      rw [hst] at h
      have h' : (if st.size < 2 ^ 64 ∧ (salt = [] ∨ salt.length = 256) then
              some (hdr160 lab ++
                  bytesToBits
                    (_root_.Fmt.firstBytes (digToBytes pd) st ByteArray.empty (runOf salt)))
            else none) = some s := h
      by_cases hc : st.size < 2 ^ 64 ∧ (salt = [] ∨ salt.length = 256)
      · rw [if_pos hc] at h'
        have hok : _root_.Fmt.First.ok (digToBytes pd, st, ByteArray.empty, runOf salt) := by
          refine ⟨size_digToBytes pd, hc.1, Nat.two_pow_pos 64, fun r hr => ?_⟩
          rcases hc.2 with rfl | hl
          · cases hr
          · have e := congrArg saltOf hr
            rw [saltOf_runOf salt (Or.inr hl)] at e
            have e2 : (bytesToBits r).length = 256 := by rw [← hl, e]; rfl
            rw [length_bytesToBits] at e2
            omega
        unfold parse160
        rw [← Option.some.inj h', strip_append, Option.bind_some, if_pos (whole_bytesToBits _),
          bitsToBytes_bytesToBits, _root_.Fmt.readFirst_firstBytes _ _ _ _ hok, Option.bind_some]
        dsimp only
        rw [if_pos (show ByteArray.empty.size = 0 from rfl), h1 x st hst, Option.map_some,
          bits_digToBytes, digOf_ofFn, saltOf_runOf salt hc.2]
      · rw [if_neg hc] at h'
        cases h'

include h2 in
theorem put_parse160 (s : List Bool) (a : Dig 256 × Option X × List Bool)
    (h : parse160 lab unstm s = some a) : put160 lab stm a = some s := by
  unfold parse160 at h
  cases hs : strip (hdr160 lab) s with
  | none => rw [hs] at h; cases h
  | some t =>
      rw [hs] at h
      have h' : (if whole t = true then
              (_root_.Fmt.readFirst (bitsToBytes t)).bind (fun y =>
                if y.2.2.1.size = 0 then
                  (unstm y.2.1).map (fun x => (digOf (bytesToBits y.1), x, saltOf y.2.2.2))
                else none)
            else none) = some a := h
      by_cases hw : whole t = true
      · rw [if_pos hw] at h'
        cases hr : _root_.Fmt.readFirst (bitsToBytes t) with
        | none => rw [hr] at h'; cases h'
        | some y =>
            obtain ⟨pdB, st, rc, run⟩ := y
            rw [hr] at h'
            have h3 : (if rc.size = 0 then
                    (unstm st).map (fun x => (digOf (bytesToBits pdB), x, saltOf run))
                  else none) = some a := h'
            by_cases hz : rc.size = 0
            · rw [if_pos hz] at h3
              cases hu : unstm st with
              | none => rw [hu] at h3; cases h3
              | some x =>
                  rw [hu] at h3
                  obtain ⟨e, hok⟩ := _root_.Fmt.firstBytes_readFirst _ _ _ _ _ hr
                  rw [← Option.some.inj h3]
                  unfold put160
                  show (stm x).bind _ = _
                  rw [h2 st x hu]
                  have hsalt : saltOf run = [] ∨ (saltOf run).length = 256 := by
                    cases run with
                    | none => exact Or.inl rfl
                    | some r => exact Or.inr (by show (bytesToBits r).length = 256; rw [length_bytesToBits, hok.2.2.2 r rfl])
                  show (if st.size < 2 ^ 64 ∧ (saltOf run = [] ∨ (saltOf run).length = 256) then
                        some (hdr160 lab ++
                            bytesToBits
                              (_root_.Fmt.firstBytes (digToBytes (digOf (bytesToBits pdB)))
                                st ByteArray.empty (runOf (saltOf run))))
                      else none) = some s
                  rw [if_pos ⟨hok.2.1, hsalt⟩, digToBytes_digOf pdB hok.1,
                    runOf_saltOf run hok.2.2.2, ← empty_of_size rc hz, ← e,
                    bytesToBits_bitsToBytes t hw, eq_of_strip _ s t hs]
            · rw [if_neg hz] at h3
              cases h3
      · rw [if_neg hw] at h'
        cases h'

/-- The partial code of the first chain query, on its fields. -/
def pFirst0 : PCode (Dig 256 × Option X × List Bool) where
  put := put160 lab stm
  parse := parse160 lab unstm
  parse_put := parse_put160 lab stm unstm h1
  put_parse := put_parse160 lab stm unstm h2

/-- Where `pFirst0` (with `h1`, `h2`) writes (`hx`, `hs`, `hl`), what it writes is the bits of the
format's string. -/
theorem pFirst0_put (pd : Dig 256) (x : Option X) (salt : List Bool) (st : ByteArray)
    (hx : stm x = some st) (hs : st.size < 2 ^ 64) (hl : salt = [] ∨ salt.length = 256) :
    (pFirst0 lab stm unstm h1 h2).put (pd, x, salt) =
      some (bytesToBits
          (_root_.Fmt.oStr 0 160 0 lab _root_.Fmt.zero32
            (_root_.Fmt.firstBytes (digToBytes pd) st ByteArray.empty (runOf salt)))) := by
  show (stm x).bind _ = _
  rw [hx, oStr_bits]
  exact if_pos ⟨hs, hl⟩

/-- Every string that it writes begins with the header. -/
theorem pFirst0_hdr (a : Dig 256 × Option X × List Bool) (s : List Bool)
    (h : (pFirst0 lab stm unstm h1 h2).put a = some s) : ∃ r, s = hdr160 lab ++ r := by
  have h0 : (stm a.2.1).bind (fun st =>
        if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
          some (hdr160 lab ++
              bytesToBits (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
        else none) = some s := h
  cases hst : stm a.2.1 with
  | none => rw [hst] at h0; cases h0
  | some st =>
      rw [hst] at h0
      have h' : (if st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256) then
              some (hdr160 lab ++
                  bytesToBits
                    (_root_.Fmt.firstBytes (digToBytes a.1) st ByteArray.empty (runOf a.2.2)))
            else none) = some s := h0
      by_cases hc : st.size < 2 ^ 64 ∧ (a.2.2 = [] ∨ a.2.2.length = 256)
      · rw [if_pos hc] at h'
        exact ⟨_, (Option.some.inj h').symm⟩
      · rw [if_neg hc] at h'
        cases h'

end

section
variable {I X : Type} {L : BatchProtocol I X} {t : Tag} (p0 : PlainPart (shapeOf L t) (annOf L t))
  (isP0 : PlainPart (shapeOf L t) (annOf L t) → Bool)

/-- A chain query of round 0 in the first format, with one digest, no root, the trivial round's
plain part, as (digest, statement, salt); `none` on every other query. -/
def fbSel0 (q : FbIn 256 L t) : Option (Dig 256 × Option X × List Bool) :=
  match q.round, q.head, q.rt with
  | 0, .f1 [pd] x salt, none => if isP0 q.plain = true then some (pd, x, salt) else none
  | _, _, _ => none

def fbMk0 (a : Dig 256 × Option X × List Bool) : FbIn 256 L t :=
  ⟨0, .f1 [a.1] a.2.1 a.2.2, none, p0⟩

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
      have e3' : rt = none := e3
      rw [e1', e2', e3', (hp plain).1 hq]
      rfl
    · have h' : (if isP0 plain = true then some (pd, x, salt) else none) = some a := h
      rw [if_neg hq] at h'
      cases h'
  · cases h

variable (lab : Nat) (stm : Option X → Option ByteArray) (unstm : ByteArray → Option (Option X))
  (h1 : ∀ x b, stm x = some b → unstm b = some x) (h2 : ∀ b x, unstm b = some x → stm x = some b)

/-- The partial code of the first chain query, on typed queries. -/
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

/-! ## Guards: the format page's toy chain (known answers of another edition, both fields)

The string that is written, asked of the format's oracle, gives the chain's first value, with and
without random bytes; it is read back; a bit more, a bit less, another label are refused. -/

namespace G160

def stB : ByteArray := _root_.Fmt.Toy4.statement
def stm1 : Option Unit → Option ByteArray := fun _ => some stB
def unstm1 : ByteArray → Option (Option Unit) := fun b => if b = stB then some (some ()) else none
def dg (s : String) : Dig 256 := bytesToDig (_root_.Fmt.unhex s)
def bt (s : String) : List Bool := bytesToBits (_root_.Fmt.unhex s)
def show1 (a : Dig 256 × Option Unit × List Bool) : String × Bool × String :=
  (_root_.Fmt.hex (digToBytes a.1), a.2.1.isSome, _root_.Fmt.hex (bitsToBytes a.2.2))
def ask (s : List Bool) : String := _root_.Fmt.hex (_root_.Fmt.oracle (bitsToBytes s))

#guard (put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")).map ask == some "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72"
#guard (put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), [])).map ask == some "8f1d3a0a2a3f69ec890ce893d576a15eb38d2f9f11f497eee333c9eb23247f33"
#guard (put160 7 stm1 (dg "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82", some (), bt "fd50818f742a65f3a1585c667ae07d35b3759f5e922910132b6d953d9feee385")).map ask == some "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c"
#guard (put160 7 stm1 (dg "7de82393ca9b1c414194f8ba35e40fd5b2aa2a9ad637d741cea7e93a9c257f82", some (), [])).map ask == some "3d779f4e33228af38fe59cf4b550a6d778a1bcbe51b9fb5e9d3ad2800fb427cd"
#guard ((put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")).bind (parse160 7 unstm1)).map show1 == some ("f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", true, "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")
#guard ((put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), [])).bind (parse160 7 unstm1)).map show1 == some ("f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", true, "")
#guard (put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986" ++ [true])).isNone && (put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), (bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986").drop 1)).isNone
#guard ((put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")).bind fun s => parse160 7 unstm1 (s ++ [false])).isNone
#guard ((put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")).bind fun s => parse160 7 unstm1 (s ++ bytesToBits (_root_.Fmt.zeroBytes 1))).isNone
#guard ((put160 7 stm1 (dg "f540c46adb9f25462db0a42935663304d066b78a92bfc4da9d3faa592ceda8f1", some (), bt "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986")).bind (parse160 8 unstm1)).isNone

end G160
end Run
