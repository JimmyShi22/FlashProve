-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPage164.lean: the partial code of a leaf query in the programs' format. (164: the number
under which the format hashes a leaf of a tree of a run.)

Definitions that compute, with their laws.
A partial code (`PCode`, Run/CodingPart.lean) writes some points of a type as bit strings,
injectively, with a parser. A leaf query (`LeafIn`, Compile/Batch/Oracles.lean) is the typed query
that hashes one leaf of a tree over oracles: a body and a salt.

After the format page's rules R2.2, R2.4 (the oracle's strings), R7.3, R7.4 (a leaf's bytes and
digest), in an edition that is not the one that ships (the same in a second edition, also not the
one that ships); and after a convention of this library that the start of a
leaf rides in the typed salt: the first 256 bits of the typed salt stand for the run's value, the
rest is the file's salt.

Main names:
  `pSalted pre n p`: on (a, salt): written exactly if the salt has 256 + n bits and p writes a. The
    string: pre, the salt's first 256 bits, p's string of a, the salt's last n bits. It is read back
    by cutting from both ends.
  `pre33`: the half 0; digest length, key length, fanout, depth (the first bytes of BLAKE2b's
    parameter block: `Fmt.pblock`, Fmt/Rules23.lean); 28 zero bytes.
  `pLeaf n p : PCode (LeafIn L)`: from the bits n of the file's salt and a partial code p of the
    symbols with their positions, which writes what stands between start and salt: the 16 bytes of
    the label (the leaves' number, what stands in the tree's place (`Fmt.leafPlace`,
    Fmt/Rules23.lean); 2^depth + position), the column, the fill.
  `pLeaf_pre`: every string that it writes begins with `pre33`; `pre33_not_prefix`: so with the byte
    0.
  `oStr32_bits`: the bits of the format's string of a call with a 32-byte digest and a start of 32
    bytes, at the half 0: `pre33`, the start, the label, the bytes: the tie of `pLeaf`'s strings to
    the format.

Limits: this file does not say which p: p is data, the field `leafP` of `PageC`
(Run/CodingPage.lean). The verifier tests only the length of a typed salt: that its first 256 bits
are the run's value is the parser's doing.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage166
import Run.CodingFn
import Compile.Batch.Oracles

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

namespace PCode
variable {A B : Type}

/-- A partial code carried to another type along a partial reading f with its section g (`h1`,
`h2`). -/
def via (p : PCode A) (f : B → Option A) (g : A → B)
    (h1 : ∀ a, f (g a) = some a) (h2 : ∀ b a, f b = some a → g a = b) : PCode B where
  put := fun b => (f b).bind p.put
  parse := fun s => (p.parse s).map g
  parse_put := fun b s h => by
    cases hf : f b with
    | none => rw [hf] at h; cases h
    | some a =>
        rw [hf] at h
        rw [p.parse_put a s h]
        exact congrArg some (h2 b a hf)
  put_parse := fun s b h => by
    cases hp : p.parse s with
    | none => rw [hp] at h; cases h
    | some a =>
        rw [hp] at h
        rw [← Option.some.inj h, h1]
        exact p.put_parse s a hp

theorem via_put (p : PCode A) (f : B → Option A) (g : A → B) (h1 : ∀ a, f (g a) = some a)
    (h2 : ∀ b a, f b = some a → g a = b) (a : A) :
    (p.via f g h1 h2).put (g a) = p.put a := by
  show (f (g a)).bind p.put = _
  rw [h1]
  rfl

end PCode

/-- A code with a salt around it. -/
def pSalted {A : Type} (pre : List Bool) (n : ℕ) (p : PCode A) : PCode (A × List Bool) where
  put := fun x =>
    if x.2.length = 256 + n then
      (p.put x.1).map fun m => pre ++ (x.2.take 256 ++ (m ++ x.2.drop 256)) else none
  parse := fun s => match strip pre s with
    | none => none
    | some t =>
      if 256 + n ≤ t.length then
        (p.parse ((t.drop 256).take (t.length - 256 - n))).map fun a =>
          (a, t.take 256 ++ (t.drop 256).drop (t.length - 256 - n))
      else none
  parse_put := fun x s h => by
    obtain ⟨a, sa⟩ := x
    by_cases hl : sa.length = 256 + n
    · have h' : (p.put a).map (fun m => pre ++ (sa.take 256 ++ (m ++ sa.drop 256))) = some s := by
        have h0 : (if sa.length = 256 + n then
                (p.put a).map (fun m => pre ++ (sa.take 256 ++ (m ++ sa.drop 256)))
              else none) = some s := h
        rwa [if_pos hl] at h0
      cases hm : p.put a with
      | none => rw [hm] at h'; cases h'
      | some m =>
          rw [hm] at h'
          rw [← Option.some.inj h', strip_append]
          have e1 : (sa.take 256).length = 256 := by rw [List.length_take, hl]; omega
          have e2 : (sa.drop 256).length = n := by rw [List.length_drop, hl]; omega
          have e3 : (sa.take 256 ++ (m ++ sa.drop 256)).length = 256 + (m.length + n) := by
            rw [List.length_append, List.length_append, e1, e2]
          show (if 256 + n ≤ (sa.take 256 ++ (m ++ sa.drop 256)).length then _ else none) =
            some (a, sa)
          rw [if_pos (by rw [e3]; omega), e3, List.drop_left' e1, List.take_left' e1]
          have e4 : 256 + (m.length + n) - 256 - n = m.length := by omega
          rw [e4, List.take_left' rfl, List.drop_left' rfl, p.parse_put a m hm]
          show some (a, sa.take 256 ++ sa.drop 256) = _
          rw [List.take_append_drop]
    · have h0 : (if sa.length = 256 + n then
              (p.put a).map (fun m => pre ++ (sa.take 256 ++ (m ++ sa.drop 256)))
            else none) = some s := h
      rw [if_neg hl] at h0
      cases h0
  put_parse := fun s x h => by
    cases hs : strip pre s with
    | none => simp only [hs] at h; cases h
    | some t =>
        simp only [hs] at h
        by_cases ht : 256 + n ≤ t.length
        · rw [if_pos ht] at h
          cases hp : p.parse ((t.drop 256).take (t.length - 256 - n)) with
          | none => rw [hp] at h; cases h
          | some a =>
              rw [hp] at h
              rw [← Option.some.inj h]
              have e1 : (t.take 256).length = 256 := by rw [List.length_take]; omega
              have e2 : ((t.drop 256).drop (t.length - 256 - n)).length = n := by
                rw [List.length_drop, List.length_drop]; omega
              show (if (t.take 256 ++ (t.drop 256).drop (t.length - 256 - n)).length = 256 + n then
                    (p.put a).map (fun m =>
                      pre ++ ((t.take 256 ++ (t.drop 256).drop (t.length - 256 - n)).take 256 ++
                          (m ++ (t.take 256 ++ (t.drop 256).drop (t.length - 256 - n)).drop 256)))
                  else none) = some s
              rw [if_pos (by rw [List.length_append, e1, e2]), p.put_parse _ a hp,
                List.take_left' e1, List.drop_left' e1]
              show some (pre ++
                    (t.take 256 ++
                      ((t.drop 256).take (t.length - 256 - n) ++
                        (t.drop 256).drop (t.length - 256 - n)))) = some s
              rw [List.take_append_drop, List.take_append_drop, eq_of_strip pre s t hs]
        · rw [if_neg ht] at h
          cases h

theorem pSalted_pre {A : Type} (pre : List Bool) (n : ℕ) (p : PCode A) (x : A × List Bool)
    (s : List Bool) (h : (pSalted pre n p).put x = some s) : ∃ r, s = pre ++ r := by
  have h0 : (if x.2.length = 256 + n then
          (p.put x.1).map (fun m => pre ++ (x.2.take 256 ++ (m ++ x.2.drop 256)))
        else none) = some s := h
  by_cases hl : x.2.length = 256 + n
  · rw [if_pos hl] at h0
    cases hm : p.put x.1 with
    | none => rw [hm] at h0; cases h0
    | some m => rw [hm] at h0; exact ⟨_, (Option.some.inj h0).symm⟩
  · rw [if_neg hl] at h0
    cases h0

/-- The 33 bytes with which the string of a call with a digest of 32 bytes, at the half 0,
begins. -/
def pre33 : List Bool := bytesToBits (⟨#[0]⟩ ++ (⟨#[32, 0, 1, 1]⟩ ++ _root_.Fmt.zeroBytes 28))

theorem pre33_not_prefix (e : UInt8) (he : e ≠ 0) (x : List Bool) :
    ¬ bitsOfByte e <+: pre33 ++ x := by
  rintro ⟨t, ht⟩
  have h0 : pre33 = bitsOfByte 0 ++ bytesToBits (⟨#[32, 0, 1, 1]⟩ ++ _root_.Fmt.zeroBytes 28) :=
    bytesToBits_append _ _
  rw [h0, List.append_assoc] at ht
  exact he (bitsOfByte_inj (List.append_inj_left ht (by rw [length_bitsOfByte, length_bitsOfByte])))

theorem fit32 (b : ByteArray) (h : b.size = 32) : _root_.Fmt.fit 32 b = b := by
  unfold _root_.Fmt.fit
  rw [if_pos (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  have h' : b.data.size = 32 := h
  rw [← h']
  exact Array.extract_size

/-- The bits of the format's string of a call with a digest of 32 bytes (`hn`) and a start of 32
bytes (`hs`), at the half 0. -/
theorem oStr32_bits (number tree index : Nat) (start bytes : ByteArray)
    (hn : number ≠ 162) (hs : start.size = 32) :
    bytesToBits (_root_.Fmt.oStr 0 number tree index start bytes) =
      pre33 ++ (bytesToBits start ++
          (bytesToBits (_root_.Fmt.label number tree index) ++ bytesToBits bytes)) := by
  unfold _root_.Fmt.oStr _root_.Fmt.pblock _root_.Fmt.dlen pre33
  rw [if_neg hn, fit32 start hs]
  simp only [bytesToBits_append, List.append_assoc]
  rfl

variable {I X : Type} {L : BatchProtocol I X} {t : Tag}

/-- A leaf query on a symbol of the protocol under the tag t, as (symbol with position, salt);
`none` on every other leaf query. -/
def leafSel (q : LeafIn L) : Option (SymAny (shapeOf L t) × List Bool) :=
  match q.body with
  | some (.inr ⟨t', s⟩) =>
    (castTag (F := fun t => SymAny (shapeOf L t)) t t' s).map fun s => (s, q.salt)
  | _ => none

def leafMk (x : SymAny (shapeOf L t) × List Bool) : LeafIn L := ⟨some (.inr ⟨t, x.1⟩), x.2⟩

theorem leafSel_mk (x : SymAny (shapeOf L t) × List Bool) : leafSel (leafMk x) = some x := by
  show (castTag (F := fun t => SymAny (shapeOf L t)) t t x.1).map (fun s => (s, x.2)) = some x
  rw [castTag_self]
  rfl

theorem leafMk_sel (q : LeafIn L) (x : SymAny (shapeOf L t) × List Bool) (h : leafSel q = some x) :
    leafMk x = q := by
  obtain ⟨body, salt⟩ := q
  rcases body with _ | (_ | ⟨t', s⟩)
  · cases h
  · cases h
  · have h0 : (castTag (F := fun t => SymAny (shapeOf L t)) t t' s).map (fun s => (s, salt)) =
        some x := h
    cases hc : castTag (F := fun t => SymAny (shapeOf L t)) t t' s with
    | none => rw [hc] at h0; cases h0
    | some y =>
        rw [hc] at h0
        rw [← Option.some.inj h0]
        show (⟨some (.inr ⟨t, y⟩), salt⟩ : LeafIn L) = ⟨some (.inr ⟨t', s⟩), salt⟩
        rw [castTag_some hc]

/-- The partial code of a leaf query. -/
def pLeaf (n : ℕ) (p : PCode (SymAny (shapeOf L t))) : PCode (LeafIn L) :=
  (pSalted pre33 n p).via leafSel leafMk leafSel_mk leafMk_sel

theorem pLeaf_pre (n : ℕ) (p : PCode (SymAny (shapeOf L t))) (q : LeafIn L)
    (s : List Bool) (h : (pLeaf n p).put q = some s) : ∃ r, s = pre33 ++ r := by
  cases hq : leafSel (t := t) q with
  | none =>
      have h0 : (leafSel q).bind (pSalted pre33 n p).put = some s := h
      rw [hq] at h0
      cases h0
  | some x =>
      have h0 : (leafSel q).bind (pSalted pre33 n p).put = some s := h
      rw [hq] at h0
      exact pSalted_pre pre33 n p x s h0

end Run
