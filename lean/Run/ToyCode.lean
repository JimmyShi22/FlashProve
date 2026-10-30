-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyCode.lean: the encoding of the typed queries into the single oracle's strings at the protocol
of a small toy of this library's own (`Run.Toy1`; on bytes: Fmt.Toy1): all data of
Run/CodingPage.lean (`PageC`), with their laws; so a family over a single oracle (`Rom.OracleCoding`) with
its inverse and both laws, as a closed term in one parameter, the configuration's digest.

Definitions that compute, theorems. The strings are the format page's in an edition that is
not the one that ships (the chain's label 7 in a round's call; a vertex starts from the
configuration's digest), but for a leaf's label (`Fmt.leafPlace`: as in a second edition of
the format page, not held against the page that ships: see `leafPT`). The toy is this
library's
own (Run/ToyQ.lean): round 0 trivial; round 1: a root, 8 bits of work, three positions; round 2: one
element in plain.
The compiled verifier is a computation over typed oracles (`Compile.Batch.OracleName`: leaves, nodes, chain
queries and others), each with its own types of queries and answers. A family over a single oracle
(`OracleCoding`, Rom/Family.lean) gives each oracle, query and number of a block of the answer one bit
string (the query to the single oracle for that block), one to one and onto, with the inverse as
data; its two laws are `inv_code` and `code_inv`. A partial code (`PCode`, Run/CodingPart.lean)
writes some values as strings and parses them back.

Main names:
  `rc1`, `rc2`, `rcT`: what a round's message is, as a partial code of (root or none, typed plain
    part): round 1, round 2; no other round.
  `chainT`: label 7; kinds 4 and 7; work 8 and 0.
  `leafPT`: a symbol at position x: the word of the leaves' number (tree 0, with the words of the
    column (3) and of the file's salt (5): `Fmt.leafPlace`), the word 16 + x, the three words of the
    symbol; no fill.
  `saltBits := 320`: a file's salt has 40 bytes (the typed salt: 256 + 320 bits, as Run/ToyQ.lean's
    verifier asks).
  `pageT cfg h`; `mT cfg h`: all data, and the family, for a configuration's digest cfg of 32 bytes
    (h).

Limits: this file does not say that these strings are those of the functions of Run/CodingFn.lean at
Run/ToyQ.lean's spellings: not proved here. A word of a symbol, of the statement or of the element
that is not below the field's prime has a string all the same. It says nothing on a hash; nothing on
soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.ToyQ
import Run.CodingPage
import Run.CodingAtoms
import Compile.Batch.Ser

set_option autoImplicit false

namespace Run

namespace PCode
variable {A B : Type}

theorem via_put' (p : PCode A) (f : B → Option A) (g : A → B) (h1 : ∀ a, f (g a) = some a)
    (h2 : ∀ b a, f b = some a → g a = b) (b : B) (s : List Bool)
    (h : (p.via f g h1 h2).put b = some s) :
    ∃ a, f b = some a ∧ p.put a = some s := by
  have h0 : (f b).bind p.put = some s := h
  cases hf : f b with
  | none => rw [hf] at h0; cases h0
  | some a => rw [hf] at h0; exact ⟨a, rfl, h0⟩

theorem via_len (p : PCode A) (f : B → Option A) (g : A → B) (h1 : ∀ a, f (g a) = some a)
    (h2 : ∀ b a, f b = some a → g a = b) (n : ℕ) (hp : p.Len n) :
    (p.via f g h1 h2).Len n := fun b s h => by
  obtain ⟨a, -, ha⟩ := via_put' p f g h1 h2 b s h
  exact hp a s ha

end PCode

namespace Toy1
open Iop Rom Compile Compile.Batch

abbrev PBt : Type := PlainPart (shapeOf Lt .test) (annOf Lt .test)
abbrev RcT : Type := Option (Dig 256) × PBt

/-! ### The rounds' messages -/

def sel1 : RcT → Option (Dig 256 × ℕ)
  | (some r, .inr (.inl (.inr ((), n)))) => some (r, n)
  | _ => none

def mk1 (a : Dig 256 × ℕ) : RcT := (some a.1, .inr (.inl (.inr ((), a.2))))

theorem sel1_mk1 (a : Dig 256 × ℕ) : sel1 (mk1 a) = some a := rfl

theorem mk1_sel1 (b : RcT) (a : Dig 256 × ℕ) (h : sel1 b = some a) : mk1 a = b := by
  obtain ⟨rt, pl⟩ := b
  rcases rt with _ | r
  · cases h
  · rcases pl with (_ | _) | ((_ | ⟨⟨⟩, n⟩) | ((_ | _) | e))
    · cases h
    · cases h
    · cases h
    · rw [← Option.some.inj h]; rfl
    · cases h
    · cases h
    · exact e.elim

/-- Round 1: the root, then the nonce's word. -/
def rc1 : PCode RcT := (pDig.cons 256 pDig_len fun _ => pWord).via sel1 mk1 sel1_mk1 mk1_sel1

theorem rc1_len : rc1.Len (256 + 64) :=
  PCode.via_len _ _ _ _ _ _ (PCode.cons_len _ _ _ _ 64 fun _ => pWord_len)

def sel2 : RcT → Option (E3 × Unit)
  | (none, .inr (.inr (.inl (.inr s)))) => some (s, ())
  | _ => none

def mk2 (a : E3 × Unit) : RcT := (none, .inr (.inr (.inl (.inr a.1))))

theorem sel2_mk2 (a : E3 × Unit) : sel2 (mk2 a) = some a := rfl

theorem mk2_sel2 (b : RcT) (a : E3 × Unit) (h : sel2 b = some a) : mk2 a = b := by
  obtain ⟨rt, pl⟩ := b
  rcases rt with _ | r
  · rcases pl with (_ | _) | ((_ | _) | ((_ | s) | e))
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · rw [← Option.some.inj h]; rfl
    · exact e.elim
  · cases h

def word0 : List Bool := bytesToBits (_root_.Fmt.u64n 0)

/-- Round 2: the element, then the word 0. -/
def rc2 : PCode RcT := (pE3.cons 192 pE3_len fun _ => pUnit word0).via sel2 mk2 sel2_mk2 mk2_sel2

theorem rc2_len : rc2.Len (192 + 64) :=
  PCode.via_len _ _ _ _ _ _ (PCode.cons_len _ _ _ _ 64 fun _ => pUnit_len word0)

def rcT : ℕ → PCode RcT
  | 1 => rc1
  | 2 => rc2
  | _ => PCode.empty RcT

theorem rcT_ge : ∀ (i : ℕ) (y : RcT) (s : List Bool), (rcT i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | 1, y, s, h => by rw [rc1_len y s h]; omega
  | 2, y, s, h => by rw [rc2_len y s h]; omega
  | _ + 3, _, _, h => by cases h

/-- The chain's data. -/
def chainT : ChainD Lt :=
  ⟨7, fun i => if i = 1 then 4 else 7, fun i => if i = 1 then 8 else 0, rcT, rcT_ge⟩

theorem chainT_tag :
    (bytesToBits (_root_.Fmt.u64n (162 + 65536 * chainT.label))).take 16 = t162 := by decide +kernel

/-! ### A leaf -/

def selL : SymAny (shapeOf Lt .test) → Option (Fin 16 × E3)
  | ⟨.inr (.inl x), e⟩ => some (x, e)
  | ⟨.inl p, _⟩ => p.elim
  | ⟨.inr (.inr (.inl p)), _⟩ => p.elim
  | ⟨.inr (.inr (.inr p)), _⟩ => p.elim

def mkL (a : Fin 16 × E3) : SymAny (shapeOf Lt .test) := ⟨.inr (.inl a.1), a.2⟩

theorem selL_mkL (a : Fin 16 × E3) : selL (mkL a) = some a := rfl

theorem mkL_selL (b : SymAny (shapeOf Lt .test)) (a : Fin 16 × E3) (h : selL b = some a) :
    mkL a = b := by
  obtain ⟨p, e⟩ := b
  rcases p with p | (x | (p | p))
  · exact p.elim
  · rw [← Option.some.inj h]; rfl
  · exact p.elim
  · exact p.elim

def word164 : List Bool := bytesToBits (_root_.Fmt.u64n (164 + 65536 * _root_.Fmt.leafPlace 0 3 5))

/-- A symbol with its position: label, column. -/
def leafPT : PCode (SymAny (shapeOf Lt .test)) :=
  (PCode.pre word164 ((pFinAt 16 16).cons 64 (pFinAt_len 16 16) fun _ => pE3)).via
    selL mkL selL_mkL mkL_selL

theorem leafPT_tag (y : SymAny (shapeOf Lt .test)) (m : List Bool) (h : leafPT.put y = some m) :
    16 ≤ m.length ∧ m.take 16 = t164 := by
  obtain ⟨a, -, ha⟩ := PCode.via_put' _ _ _ _ _ y m h
  obtain ⟨u, -, rfl⟩ := PCode.pre_put' _ _ _ m ha
  have hl : word164.length = 64 := length_u64n _
  exact ⟨by rw [List.length_append, hl]; omega, take16 word164 u (by rw [hl]; omega)⟩

/-! ### The statement and the first query -/

def hdrSt : List Bool := bytesToBits (_root_.Fmt.textS "toy: claim" ++ _root_.Fmt.u64n 24)

/-- The statement's one item, as bits. -/
def pSt : PCode (Option E3) :=
  (PCode.pre hdrSt pE3).via id some (fun _ => rfl) (fun _ _ h => h.symm)

theorem pSt_whole (x : Option E3) (s : List Bool) (h : pSt.put x = some s) : whole s = true := by
  have hl := PCode.via_len _ _ _ _ _ _ (PCode.pre_len hdrSt pE3 192 pE3_len) x s h
  refine (whole_iff s).2 ⟨(_root_.Fmt.textS "toy: claim" ++ _root_.Fmt.u64n 24).size + 24, ?_⟩
  rw [hl]
  show (bytesToBits _).length + 192 = _
  rw [length_bytesToBits]
  omega

def stmT (x : Option E3) : Option ByteArray := (pSt.put x).map bitsToBytes
def unstmT (b : ByteArray) : Option (Option E3) := pSt.parse (bytesToBits b)

theorem unstm_stm (x : Option E3) (b : ByteArray) (h : stmT x = some b) : unstmT b = some x := by
  unfold stmT at h
  unfold unstmT
  cases hs : pSt.put x with
  | none => rw [hs] at h; cases h
  | some s =>
      rw [hs] at h
      rw [← Option.some.inj h]
      show pSt.parse (bytesToBits (bitsToBytes s)) = some x
      rw [bytesToBits_bitsToBytes s (pSt_whole x s hs)]
      exact pSt.parse_put x s hs

theorem stm_unstm (b : ByteArray) (x : Option E3) (h : unstmT b = some x) : stmT x = some b := by
  unfold unstmT at h
  unfold stmT
  rw [pSt.put_parse _ x h]
  show some (bitsToBytes (bytesToBits b)) = some b
  rw [bitsToBytes_bytesToBits]

/-- The plain part of the trivial round 0. -/
def p0T : PBt := .inl (.inr ())

def isP0T : PBt → Bool
  | .inl (.inr ()) => true
  | _ => false

theorem isP0T_iff (p : PBt) : isP0T p = true ↔ p = p0T := by
  rcases p with (_ | ⟨⟩) | _
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- The first chain query. -/
def firstT : PCode (FbIn 256 Lt .test) :=
  pFirst p0T isP0T isP0T_iff 7 stmT unstmT unstm_stm stm_unstm

theorem firstT_tag (q : FbIn 256 Lt .test) (s : List Bool) (h : firstT.put q = some s) :
    tag16 s = t160 := by
  obtain ⟨r, rfl⟩ := pFirst_hdr p0T isP0T isP0T_iff 7 stmT unstmT unstm_stm stm_unstm q s h
  exact tag16_hdr 0 160 0 7 _root_.Fmt.zero32 rfl r

theorem firstT_hd (q : FbIn 256 Lt .test) (s : List Bool) (h : firstT.put q = some s)
    (e : UInt8) (he : e ≠ 0) : ¬ bitsOfByte e <+: s := by
  obtain ⟨r, rfl⟩ := pFirst_hdr p0T isP0T isP0T_iff 7 stmT unstmT unstm_stm stm_unstm q s h
  exact hdr_not_prefix e 0 he 160 0 7 _root_.Fmt.zero32 r

/-! ### The total code behind the escape, and the assembly -/

def serU64 : Ser UInt64 :=
  Ser.ofEquiv ⟨UInt64.toFin, UInt64.ofFin, fun _ => rfl, fun _ => rfl⟩ (Ser.fin UInt64.size)

def serE3 : Ser E3 := Ser.prod serU64 (Ser.prod serU64 serU64)

/-- No position: nothing to write. -/
def serNoPos (α : Empty → Type) : Ser (Σ p : Empty, α p) :=
  Ser.ofEquiv ⟨fun x => x.1, fun e => e.elim, fun x => x.1.elim, fun e => e.elim⟩ Ser.empty

/-- Serialisers of the toy's interface. -/
def serT : SerLHB Lt where
  tag := []
  x := serE3
  sg := Ser.unit
  T := ((serNoPos _, Ser.unit),
    ((Ser.sigma (Ser.fin 16) fun _ => serE3, Ser.prod Ser.unit Ser.nat), ((serNoPos _, serE3), ())))
  Lk := ()
  O := ()
  A := ()

/-- A total code of all real and ghost points. -/
def backT : StrCode (AllPts 256 2 Lt) :=
  (Ser.sum (serReal serT 256 2) (serGhost serT 256 2)).toStrCode

/-- All data of the encoding of the queries, at the toy. -/
def pageT (cfg : ByteArray) (h : cfg.size = 32) : PageC Lt 2 where
  cfg := cfg
  hcfg := h
  chain := chainT
  chainTag := chainT_tag
  first := firstT
  firstTag := firstT_tag
  firstHd := firstT_hd
  saltBits := 320
  leafP := leafPT
  leafTag := leafPT_tag
  back := backT

/-- The family over a single oracle, at the toy. -/
def mT (cfg : ByteArray) (h : cfg.size = 32) : OracleCoding (spec 256 2 Lt) 256 := theImpl (pageT cfg h)

end Toy1
end Run
