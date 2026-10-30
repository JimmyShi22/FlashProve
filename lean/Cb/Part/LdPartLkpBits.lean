-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartLkpBits.lean: the bits of the front lookups' multiplicities as data of a request that
is built from a partition: a value for the parameters "honest bits" (`LdPartBits`,
Cb/Part/LdPartCf.lean), its law, and the tie from the bits of a layer to the lookup's own clause.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartLkpBitsProofs.lean. No
protocol.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
L : `LdPartLk E St J` is a segment's key functions with their tables (Cb/Part/LdPartLkp.lean), K :
`LdPartKeys` its key families (Cb/Part/LdPartLkpFam.lean), P : `LdPartD Cf` the data of a partition
(Cb/Part/LdPartDef.lean). The bits of a layer are `LdPartW.bit j`: the bits of segment j in the
further witness (Cb/Part/LdPartRide.lean).

Why: the bits go out with a segment's cells, before the shift is drawn. Until then they are in the
further witness, numbered (`LdPartW.bit`, Cb/Part/LdPartRide.lean: segment, number of a name). The
exact relation says of them a predicate that is a parameter there. After the sending they are
entries of messages, at the places of the lookup's names (e, Cb/Part/LdPartLkp.lean).



Main names:
  `L.ValidN st m b`: the predicate of Cb/Ld/LdLkpMult.lean (`Valid`), function by function; no shift
    occurs. The predicate, not one vector: as in this protocol's technical report (lean/CREDITS.md;
    by inspection), whose relation before the shift asks the predicate.
  `L.honN st m`: the honest bits by number: first-occurrence rule, function by function.
  `P.bitsV`: the value of `LdPartBits P`.
  `Spec.ldPartLk_honN`: every key in its table ⇒ the honest bits by number are valid.
  `Spec.ldPartLk_validN`: if the entries m hold b at the places of the bits' names:
    `L.ValidN st m b` ⇔ `L.ValidU e st m`.
  `Spec.ldPartBits_ok`: see its docstring. The premise "the conditions hold" is used: a key outside
    its table is counted by no entry.
  `Spec.ldPartBits_tie`: for a well-formed segment j, a reading R, entries mm with: the index
    matrix read off mm is the image of W; the cells read off mm are g at the places that segment j
    reads; mm holds b at the places of the bits' names: `P.bitsV.ok j (xs st) W g b` ⇒
    `L.ValidU e st mm` for L := segment j's key functions at the reading R.

Limits: this file says nothing on who lays the bits and where (e is a letter). It says nothing in
the relaxed world: a lookup's relaxed claim does not read multiplicities.
This file gives no instance that meets its hypotheses, so as far as this file shows its theorems may
hold of nothing. ldPartBits_tie is applied for arbitrary parameters (Cb/Part/LdPartTie0Of.lean,
Cb/Part/LdPartTieOfProofs.lean). ldPartLk_honN, ldPartLk_validN are named by no file but this one's
proofs (by a search by name): no value known.

Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartLkpFam
import Cb.Part.LdPartCf
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset Cb.LdLkp Cb.Lkp

/-- the number of a bit's name -/
def LdPartSz.bitNo (L : LdPartSz) (Y j : ℕ) : ℕ := Y * 2 ^ L.w + j

namespace LdPartLk
variable {E St J : Type} [Field E] (L : LdPartLk E St J)

/-- The numbered bits are valid multiplicities, function by function. -/
def ValidN (st : St) (m : J → E) (b : ℕ → E) : Prop :=
  ∀ f < 2 ^ L.g, Valid L.v L.d L.w (L.n + 1) (L.P.key st m f) (L.P.tab st f) fun u j =>
    b (L.bitNo (f * 2 ^ L.d + u) j)

/-- the honest bits by number -/
def honN (st : St) (m : J → E) : ℕ → E := fun N =>
  hbit L.v (L.n + 1) (L.P.key st m (N / 2 ^ L.w / 2 ^ L.d)) (L.P.tab st (N / 2 ^ L.w / 2 ^ L.d))
    (N / 2 ^ L.w % 2 ^ L.d) (N % 2 ^ L.w)

end LdPartLk

/-- the key functions at given instance, index matrix and cells: no state, no entries -/
def LdPartKeys.at {X F E : Type} [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E) (h k : ℕ)
    (x : X) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) : LdPartLk E Unit Unit :=
  K.lk h k ⟨fun _ => WE, fun _ => A⟩ fun _ => x

namespace LdPartD
variable {F E : Type} [Field F] [Field E] [Algebra F E] {Cf : LdCf F E} (P : LdPartD Cf)

/-- segment j's key families with their tables -/
def keysOf (j : ℕ) : LdPartKeys Cf.Xm F E := LdPartKeys.ofList (P.seg j).keys

/-- segment j's key functions at (x, the image of W, the integers g) -/
def lkAt (j : ℕ) (x : Cf.Xm) (W : ℕ → ℕ → F) (g : LdPartGh) : LdPartLk E Unit Unit :=
  (P.keysOf j).at P.fmt.h (P.fmt.hi + P.fmt.lo) x
    (fun y c => algebraMap F E (W y c)) (castM (E := E) g)

/-- The value of the parameters `LdPartBits P`. -/
def bitsV : LdPartBits P where
  ok  := fun j x W g b => (P.lkAt j x W g).ValidN () 0 b
  hon := fun j x W g => (P.lkAt j x W g).honN () 0

end LdPartD

namespace Spec

def ldPartLk_honN : Prop :=
  ∀ (E St J : Type) [Field E] (L : LdPartLk E St J) (st : St) (m : J → E),
    L.P.inC st m → L.ValidN st m (L.honN st m)

def ldPartLk_validN : Prop :=
  ∀ (E St J : Type) [Field E] [Fintype E] [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J)
      (st : St) (m : J → E) (b : ℕ → E),
    (∀ (Y : Fin (2 ^ L.dd)) (j : Fin (2 ^ L.w)), m (e (.inl (Y, j))) = b (L.bitNo Y j)) →
    (L.ValidN st m b ↔ L.ValidU e st m)

/-- States: if all segments are well formed, honest bits are valid where the segment's conditions
hold. -/
def ldPartBits_ok : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf),
    (∀ s < P.n, (P.seg s).WF P.fmt) → P.BitsOK P.bitsV

/-- From the bits of a layer to the lookup's own clause. -/
def ldPartBits_tie : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Fintype E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (j : ℕ) (St J : Type) [Fintype J] (R : LdPartRd E J) (xs : St → Cf.Xm)
      (e : ((P.keysOf j).lk P.fmt.h (P.fmt.hi + P.fmt.lo) R xs).Nm E → J) (st : St) (mm : J → E)
      (W : ℕ → ℕ → F) (g : LdPartGh) (b : ℕ → E),
    (P.seg j).WF P.fmt → (R.W mm = fun y c => algebraMap F E (W y c)) →
    (∀ q ∈ (P.seg j).places, R.A mm q.1 q.2.1 q.2.2 = ((g q.1 q.2.1 q.2.2 : ℤ) : E)) →
    (∀ (Y : Fin (2 ^ (P.keysOf j).sz.dd)) (i : Fin (2 ^ (P.keysOf j).sz.w)),
      mm (e (.inl (Y, i))) = b ((P.keysOf j).sz.bitNo Y i)) →
    P.bitsV.ok j (xs st) W g b → ((P.keysOf j).lk P.fmt.h (P.fmt.hi + P.fmt.lo) R xs).ValidU e st mm

end Spec
end Cb
