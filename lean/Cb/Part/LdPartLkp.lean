-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartLkp.lean: from a segment's key functions and tables, of any sizes, to the data of
"shift ; assembled lookup": all numbers, tags, names and places are computed.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Part/LdPartLkpProofs.lean. No
protocol: data and conditions on data.
A lookup claims that every key is an entry of its table (`InTable`, Cb/Gen/LkpAlg.lean). Each entry
of the table has a multiplicity, written in bits; for each value, the multiplicities of the entries
with that value add up to the number of keys with it (a clause of `Valid`, Cb/Ld/LdLkpMult.lean).
The shift joins several functions into one lookup: keys and entries of the function f get tag f · θ
added, θ the shift (`shKey`, `shTab`, Cb/Ld/LdLkpShift.lean).

Why: a segment's front begins
with a random shift (`ShiftP`, Cb/Ld/LdLkpShift.lean) and the
assembled lookup (`LkAsm2`, Cb/Ld/LdLkpAsm2.lean). Their data are parameters there, and
conditions on them are asked of
whoever builds a request. Here the parameters are functions of what a model gives.

Statements here have premises of their own: "the
bits are the multiplicities" is asked of what rides along on the honest side (`L.ValidU`); the
conditions on the places of masks ask where the data lie and what the keys read.



What a model gives: L : `LdPartLk E St J`, over the sizes `LdPartSz`: nk, kv, kT. All numbers and
names read the sizes alone, so the entries J of a block can be made from them before the keys are.
There are nk key functions; the function f has 2^(kv f) keys "key st m f b", functions of a public
state and of the entries m : J → E that the block reads, and a public table of 2^(kT f) entries
"tab st f u". No reading of entries as cells or as an index is fixed here: key is a letter.

What is computed:
  `L.g`, `L.v`, `L.d`: the least g with nk ≤ 2^g; the largest kv, at least 1; the largest kT.
  `L.P : ShiftP`: 2^g functions with 2^v keys and 2^d entries each. Keys and tables are padded by
    repeating (the key number b is the key number b mod 2^(kv f), the entry number u the entry
    number u mod 2^(kT f)); a function f ≥ nk has the key 0 and the table 0; the tag of f is the
    number f, read in E.
  `L.v'`, `L.dd`, `L.n`, `L.w`: the lookup's numbers: 2^(v'+1) = 2^(g+v) keys; 2^dd = 2^(g+d)
    entries; n + 1 = g + v + 1 bit positions that count; the least w with n + 1 ≤ 2^w.
  `LkOwn`, `LkNm`, `lkStd`: the standard data of an assembled lookup with given numbers. Its
    entries are names: the bits of the multiplicities (entry of the table, bit position) and the
    own masks that are played (the names of Cb/Ld/LdLkpMaskPlaces2.lean); each played place is its
    name. Places that the data name and the protocol does not play stand at one played place (they
    are free).
  `L.Nm E`, `L.A0 e`, `L.A e`: the names at L's numbers; the lookup's data among the block's
    entries, carried along one map e : L.Nm E → J (Cb/Ld/LdLkpRe2.lean); the lookup that runs:
    states (state, shift), joint keys, joint table.
  `L.ValidU e st m`: the bits that m holds at the named places are valid multiplicities function by
    function (Cb/Ld/LdLkpMult.lean): no shift occurs.
  `L.Fits p`: a condition on numbers: 2^(g+d) · (2^(g+v+1) - 1) < p.

Main names:
  `Spec.ldPartLk_inC`: padding adds and drops nothing: the shift's claim before holds ⇔ for every f
    < nk every key of f on its cube is an entry of its table.
  `Spec.ldPartLk_nums`: the two equations between the shift's and the lookup's numbers.
  `Spec.ldPartLk_tags`: p the characteristic, `L.Fits p` ⇒ different functions have different tags.
  `Spec.ldPartLk_adm`: `L.Fits p` ⇒ the lookup's conditions on numbers.
  `Spec.ldPartLk_mu`: "valid" (wide form) meets `MuOn` (Cb/Ld/LdLkpHead2.lean: what is asked of
    "the vector is the multiplicities": for keys in the table, the claim after the first challenge
    λ holds at every λ): the statement has no premise.
  `Spec.ldPartLk_honest`: the claim before, and the bits by the first-occurrence rule function by
    function at the named places ⇒ `L.ValidU`.
  `Spec.ldPartSz_fits`, `Spec.ldPartLk_muU`, `Spec.ldPartLk_honestNm`: see their docstrings.
  `Spec.ldPartLk_placesIn`: all places that the data name lie in the range of e.
  `Spec.ldPartLk_placesOK`: the four plain conditions on the places of masks
    (Cb/Ld/LdLkpMaskPlaces2.lean), from: e injective; the data Dt hold e of every bit's name and e
    of no mask's name; the keys read Dt only.

Limits: this file does not say that `L.Fits p` holds at some model. It says nothing on what the keys
are (families of a partition: Cb/Part/LdPartLkpFam.lean), on who sends the bits, on e (beyond what
`Spec.ldPartLk_placesIn` states and `Spec.ldPartLk_placesOK` asks of it). It says nothing on zero
knowledge, formats, errors. It says nothing on the record into which these data go and its
conditions.
This file gives no instance that meets its hypotheses.
Declared differences from a write-up of ours (lean/CREDITS.md; by inspection of it). There
tables and key maps of different sizes are laid on sub-cubes, with one filler value elsewhere. Here,
because `ShiftP` has 2^g equal blocks: every key map is repeated up to 2^v keys, every table up to
2^d entries, and the number of tables is filled up to a power of two with idle functions. The same
claim (`ldPartLk_inC`); more keys and entries, so other numbers of rounds, other errors, other
multiplicities. The vector of bits has 2^(g+d) · 2^w entries, where the write-up has
(the sum of the tables' sizes, rounded up) · 2^w: the message that holds it has another size than
the write-up's, so numbers that the write-up's reference parameters give for that
message do not fit it as they stand. The tag is the table's number, from 0, in both. A segment
without keys
still runs a lookup here (two keys 0, a table with the one entry 0); the write-up is silent
on such a segment. Order of variables: there a key map's own variables come first and the bits of
its
place last, and the first coordinate is the lowest bit; here the function's number stands in the
leading bits and the first coordinate is the top bit: a mirror image; no number moves. The
write-up also allows the tables of a segment to be looked up in turn: not rendered. "The vector
is the multiplicities" is there an equality of two polynomials, here a count value by value (two
products of monic linear factors: the same). At least two keys (v ≥ 1): the write-up asks at
least one key variable too: no difference.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpRe2
import Cb.Ld.LdLkpMaskPlaces2Proofs
import Cb.Ld.LdLkpMult

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp Finset

noncomputable section

/-! ## The standard data of an assembled lookup with given numbers -/

section Std
variable (E : Type) [Field E] [Fintype E] (v' d w n : ℕ)

/-- the numbers alone, as data of a lookup with one entry; `LkOwn` is its type of names -/
@[reducible] def lkNums : LkAsm2 E where
  St := Unit
  J := Unit
  v' := v'
  d := d
  w := w
  n := n
  key := fun _ _ _ => 0
  tab := fun _ _ => 0
  bAt := fun _ _ => ()
  wS := fun _ => ()
  cS := fun _ => ()
  wAt := fun _ _ => ()
  cAt := fun _ _ => ()
  wK := fun _ _ => ()
  cK := fun _ _ => ()
  wT := fun _ _ => ()
  cT := fun _ _ => ()
  wE := fun _ => ()
  wB := fun _ => ()
  cB := ()

/-- the names of the own masks that are played -/
abbrev LkOwn : Type := (lkNums E v' d w n).Nm

instance LkOwn.fintype : Fintype (LkOwn E v' d w n) :=
  Fintype.ofEquiv _ ((lkNums E v' d w n).nmEquiv E).symm

/-- the names of all entries of the lookup's own: bits of the multiplicities (entry, bit position);
own masks -/
abbrev LkNm : Type := (Fin (2 ^ d) × Fin (2 ^ w)) ⊕ LkOwn E v' d w n

/-- The standard data: every played place is its name. -/
def lkStd : LkAsm2 E where
  St := Unit
  J := LkNm E v' d w n
  v' := v'
  d := d
  w := w
  n := n
  key := fun _ _ _ => 0
  tab := fun _ _ => 0
  bAt := fun u j =>
    .inl
      (⟨u % 2 ^ d, Nat.mod_lt _ (Nat.two_pow_pos d)⟩, ⟨j % 2 ^ w, Nat.mod_lt _ (Nat.two_pow_pos w)⟩)
  wS := fun i => .inr (.s (.inl i))
  cS := fun b => .inr (.s (.inr b))
  wAt := fun l i => if h : l < n then .inr (.t l h (.inl i)) else .inr (.s (.inr false))
  cAt := fun l b => if h : l < n then .inr (.t l h (.inr b)) else .inr (.s (.inr false))
  wK := fun l i => if h : l ≤ v' then .inr (.k l h (.inl i)) else .inr (.s (.inr false))
  cK := fun l b => if h : l ≤ v' then .inr (.k l h (.inr b)) else .inr (.s (.inr false))
  wT := fun l i => if h : l < d then .inr (.f l h (.inl i)) else .inr (.s (.inr false))
  cT := fun l b => if h : l < d then .inr (.f l h (.inr b)) else .inr (.s (.inr false))
  wE := fun i => .inr (.e i)
  wB := fun i => .inr (.b (.inl i))
  cB := .inr (.b (.inr ()))

end Std

/-! ## A segment's key functions and tables -/

/-- The sizes. -/
structure LdPartSz where
  /-- the number of key functions -/
  nk : ℕ
  /-- the function f has 2^(kv f) keys and a table of 2^(kT f) entries -/
  kv : ℕ → ℕ
  kT : ℕ → ℕ

namespace LdPartSz
variable (L : LdPartSz)

def g : ℕ := Nat.clog 2 L.nk
/-- the largest kv, less 1 (0 if that is 0); v is written as a successor, so that g + v is v' + 1
by definition -/
def vm : ℕ := (range L.nk).sup L.kv - 1
def v : ℕ := L.vm + 1
def d : ℕ := (range L.nk).sup L.kT

/-- the lookup's numbers -/
def v' : ℕ := L.g + L.vm
def dd : ℕ := L.g + L.d
def n : ℕ := L.g + L.v
def w : ℕ := Nat.clog 2 (L.n + 1)

/-- A condition on numbers. -/
def Fits (p : ℕ) : Prop := 2 ^ (L.g + L.d) * (2 ^ (L.g + L.v + 1) - 1) < p

/-- the names at these numbers -/
abbrev Nm (E : Type) [Field E] [Fintype E] : Type := LkNm E L.v' L.dd L.w L.n

end LdPartSz

/-- What a model gives. -/
structure LdPartLk (E St J : Type) extends LdPartSz where
  key : St → (J → E) → ℕ → ℕ → E
  tab : St → ℕ → ℕ → E

namespace LdPartLk
variable {E St J : Type} [Field E] (L : LdPartLk E St J)

/-- The shift's data. -/
def P : ShiftP E St (J → E) where
  g := L.g
  v := L.v
  d := L.d
  key := fun st m f b => if f < L.nk then L.key st m f (b % 2 ^ L.kv f) else 0
  tab := fun st f u => if f < L.nk then L.tab st f (u % 2 ^ L.kT f) else 0
  tag := fun f => (f : E)

variable [Fintype E] [Fintype J] (e : L.Nm E → J)

/-- numbers, entries and places of the lookup; its states, keys and table are not read -/
def A0 : LkAsm2 E := (lkStd E L.v' L.dd L.w L.n).re Unit J e (fun _ _ _ => 0) fun _ _ => 0

/-- The lookup that runs. -/
def A : LkAsm2 E :=
  (lkStd E L.v' L.dd L.w L.n).re (St × E) J e (fun x m => shKey L.P.v (L.P.key x.1 m) L.P.tag x.2)
    fun x => shTab L.P.d (L.P.tab x.1) L.P.tag x.2

/-- The bits are valid multiplicities, function by function. -/
def ValidU (st : St) (m : J → E) : Prop :=
  ∀ f < 2 ^ L.g, Valid L.v L.d L.w (L.n + 1) (L.P.key st m f) (L.P.tab st f) fun u j =>
    m ((L.A0 e).bAt (f * 2 ^ L.d + u) j)

end LdPartLk
end

namespace Spec

/-- The condition on numbers, from bounds on the sizes. -/
def ldPartSz_fits : Prop :=
  ∀ (L : LdPartSz) (G V D p : ℕ), L.nk ≤ 2 ^ G → (∀ f < L.nk, L.kv f ≤ V) → 1 ≤ V →
    (∀ f < L.nk, L.kT f ≤ D) → 2 ^ (G + D) * (2 ^ (G + V + 1) - 1) < p → L.Fits p

section
variable (E : Type) [Field E]

/-- Padding adds and drops nothing. -/
def ldPartLk_inC : Prop :=
  ∀ (St J : Type) (L : LdPartLk E St J) (st : St) (m : J → E),
    L.P.inC st m ↔ ∀ f < L.nk, InTable (L.kv f) (L.kT f) (L.key st m f) (L.tab st f)

def ldPartLk_tags : Prop :=
  ∀ (p : ℕ) [CharP E p] (St J : Type) (L : LdPartLk E St J), L.Fits p → TagInj L.P.g L.P.tag

variable [Fintype E]

def ldPartLk_nums : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J),
    L.P.g + L.P.v = (L.A0 e).v' + 1 ∧ L.P.g + L.P.d = (L.A0 e).d

def ldPartLk_adm : Prop :=
  ∀ (p : ℕ) (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J),
    L.Fits p → (L.A e).H.lkb.Adm p

def ldPartLk_mu : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J), (L.A e).H.MuOn (L.A e).ValidMu

/-- Valid function by function: valid for the lookup that runs, at every shift. -/
def ldPartLk_muU : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J) (st : St) (m : J → E),
    L.ValidU e st m → ∀ θ : E, (L.A e).ValidMu (st, θ) m

/-- The honest bits. -/
def ldPartLk_honest : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J) (st : St) (m : J → E),
    L.P.inC st m →
    (∀ f < 2 ^ L.g, ∀ u < 2 ^ L.d, ∀ j < 2 ^ L.w, m ((L.A0 e).bAt (f * 2 ^ L.d + u) j) =
      hbit L.v (L.n + 1) (L.P.key st m f) (L.P.tab st f) u j) → L.ValidU e st m

/-- The same, with the bits given name by name. -/
def ldPartLk_honestNm : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J) (st : St) (m : J → E),
    L.P.inC st m →
    (∀ (Y : Fin (2 ^ L.dd)) (j : Fin (2 ^ L.w)), m (e (.inl (Y, j))) =
      hbit L.v (L.n + 1) (L.P.key st m (Y / 2 ^ L.d)) (L.P.tab st (Y / 2 ^ L.d)) (Y % 2 ^ L.d) j) →
    L.ValidU e st m

def ldPartLk_placesIn : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J),
    (L.A e).PlacesIn fun j => j ∈ Set.range e

/-- The four plain conditions on the places of masks. -/
def ldPartLk_placesOK : Prop :=
  ∀ (St J : Type) [Fintype J] (L : LdPartLk E St J) (e : L.Nm E → J) (Dt : J → Prop),
    Function.Injective e → (∀ x, Dt (e (.inl x))) → (∀ x, ¬ Dt (e (.inr x))) →
    (∀ st m m', (∀ j, Dt j → m j = m' j) → L.key st m = L.key st m') → (L.A e).PlacesOK Dt

end
end Spec
end Cb
