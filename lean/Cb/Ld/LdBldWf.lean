-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWf.lean: definitions (a builder) that make, from one record of parameters, all data of
the sub-protocol for the claim that an encoded index is well formed (`LdWfE`, Cb/Ld/LdWfEnd.lean),
with the standard sender's data (`LdWfE.StdW`, Cb/Obj/LdObjectDataSnd.lean).

Definitions only, but for the lemma `pIdx_nonemptyB`; the conditions and the statements are in
Cb/Ld/LdBldWfSpec.lean. Generic: any finite fields F, Fp and any finite field E that is an algebra
over both. Nothing assumed beyond the argument hpl : `X.Hpl` of `X.Zw` and `X.V` and the proofs that
are fields of the parameters (among them `Cf.hp`, Cb/Obj/LdObjectConf.lean).
The index set is described by lookups: the law `LdWfP.Laws.describes` asks that a message of the
encoded index holds an index if and only if, for each of n + 1 forests, every key of the forest lies
in its table; for this builder it is a field of `X.Room` (Cb/Ld/LdBldWfSpec.lean). The lookups are
lookup arguments with multiplicities: for each table entry the honest prover sends the lowest nd f +
1 binary digits of the number of keys equal to it and to no earlier entry (`hmult`, `hbit`,
Cb/Gen/LkpAlg.lean). The oracle messages that the preamble (this sub-protocol) sends hold these
digits, and masks. A layout (`Sig.StdL`, Cb/Ld/LdSendStdL.lean) sorts the entries of each message
into data entries, free entries and pad entries.

Why: the records on the object ask a value of `LdWfE`. The toys' values (on the data of
Cb/GlVal/GlToyWf.lean) have one or two forests, a hand-made
finite type of named entries, and places by cases. Here the named entries are one explicit sum type,
so that "different places" come from constructors and from the two placings being injective.

Main names:
  `BldWfN`: the numbers x: forests 0 .. n; k column variables; for each forest: rv key row
    variables, d table variables, w variables of digit positions, nd + 1 digits that count. `x.v' f`
    := rv f + k - 1 (on ℕ: 0 if rv f + k = 0): the lookup has 2^(v' + 1) keys.
  `x.Msk E`: the masks: (forest f ≤ n, a name of an own mask of its lookup), or a hiding coefficient
    of the batching.
  `BldWf F E Fp`: the parameters. Cf is a configuration. Rw, klo, lay are the index matrix's rows,
    the column variables inside a code row, and the place of an entry in a code row. n, rv, d, w, nd
    are the forests' and the lookups' numbers (any number of forests). The keys have o, co, tab:
    offsets, coefficients, tables. Z: the batching's zero-evader. S, Sd, Y are the messages, their
    seeds, their layout (pads in Fp). L, t: bounds on lists, positions borne. pB, pM are the two
    placings: where the digits of the multiplicities stand among the data entries, where the masks
    stand among the free entries. gR: the public supports of the rows (a parameter). p0, r0 are
    fixed values. The rest is what the offline linear test needs beside (l, py; and e', tt, its
    three families, which `LdOWf.withBld`, Cb/Ld/LdBldLin.lean, overwrites).
  `X.bitN`, `X.mkN`, `X.wSn` to `X.cBn`: the place maps, total on ℕ as the records need them. Off
    the ranges (a forest beyond n; a level that is not played): a digit position is taken modulo its
    range (a table entry too; a digit of a forest beyond n is `X.dN`), a mask's place is the fixed
    name `X.dN` (digit 0 of entry 0 of forest 0): a data entry, never a mask.
  `X.mat U`: the first v column variables name the code row, the last klo the place inside (in the
    order of `Alg.bits`: coordinate 0 is the top digit).
  `X.P : LdWfP` (Cb/Ld/LdWf.lean): `mult`: "the digits at their places write a valid vector of
    multiplicities" (`Valid`, Cb/Ld/LdLkpMult.lean); `gC f`: the two inner masks of the last level
    of the keys' tree.
  `X.Rl f`: what the item of lookup f reads: its data and own masks. `RdB`: everything. `RdW`: every
    entry that is no pad.
  `X.Zw hpl : LdWfE F E`, `X.V hpl : (X.Zw hpl).StdW Fp`, with hpl : `X.Hpl`, "the masks of all
    blocks stand at different free entries": stated under `X.Room p` in Cb/Ld/LdBldWfSpec.lean
    (`Spec.bldWf_hpl`), proved in Cb/Ld/LdBldWfProofs.lean; it is an argument here because the
    records hold it as a field.

Limits: no condition, no theorem (but for the lemma `pIdx_nonemptyB`). This file does not say which
messages there are and which entry lies where: the placings are parameters (no value is fixed).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataSnd
import Cb.Ld.LdLkpMaskPlaces2Proofs
import Cb.Ld.LdLkpMult
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp Cb.Lkp

/-- every list of formats has a name of a hiding coefficient -/
theorem pIdx_nonemptyB (E : Type) [Field E] : ∀ l : List (PFmt E), Nonempty (PIdx l)
  | [] => ⟨()⟩
  | _ :: l => (pIdx_nonemptyB E l).map Sum.inr

/-- an assembled lookup's data with given numbers and no content: only its type of names is used
(`LkAsm2.Nm`, Cb/Ld/LdLkpMaskPlaces2.lean: the masks that are played) -/
def lkBare (E : Type) [Field E] [Fintype E] (v' d w n : ℕ) : LkAsm2 E :=
  { St := Unit, J := Unit, v' := v', d := d, w := w, n := n, key := fun _ _ _ => 0,
    tab := fun _ _ => 0, bAt := fun _ _ => (), wS := fun _ => (), cS := fun _ => (),
    wAt := fun _ _ => (), cAt := fun _ _ => (), wK := fun _ _ => (), cK := fun _ _ => (),
    wT := fun _ _ => (), cT := fun _ _ => (), wE := fun _ => (), wB := fun _ => (), cB := () }

/-- The numbers. -/
structure BldWfN where
  n  : ℕ
  k  : ℕ
  rv : ℕ → ℕ
  d  : ℕ → ℕ
  w  : ℕ → ℕ
  nd : ℕ → ℕ

namespace BldWfN
variable (x : BldWfN)

def v' (f : ℕ) : ℕ := x.rv f + x.k - 1
/-- the forests -/
abbrev Fo : Type := {f : ℕ // f ≤ x.n}
/-- the digits of the multiplicities -/
abbrev Bit : Type := Σ f : x.Fo, Fin (2 ^ x.d f.1) × Fin (2 ^ x.w f.1)

variable (E : Type) [Field E] [Fintype E]

/-- the names of the own masks of the lookup on forest f -/
abbrev LkM (f : ℕ) : Type := (lkBare E (x.v' f) (x.d f) (x.w f) (x.nd f)).Nm
/-- the masks: the lookups', the batching's -/
abbrev Msk : Type := (Σ f : x.Fo, x.LkM E f.1) ⊕ PIdx (List.replicate x.k (pfCube E 2))
/-- The named entries. -/
abbrev N : Type := x.Bit ⊕ x.Msk E

/-- finiteness, as terms (no instances are declared: they are passed by name) -/
@[reducible] def finFo : Fintype x.Fo :=
  Fintype.ofEquiv (Fin (x.n + 1))
    (Fin.equivSubtype.trans (Equiv.subtypeEquivRight fun _ => Nat.lt_succ_iff))
@[reducible] def finLkM (f : ℕ) : Fintype (x.LkM E f) :=
  Fintype.ofEquiv _ (lkBare E (x.v' f) (x.d f) (x.w f) (x.nd f)).nmEquiv.symm
@[reducible] def finN : Fintype (x.N E) :=
  letI := x.finFo
  letI := fun f : x.Fo => x.finLkM E f.1
  inferInstanceAs (Fintype
    ((Σ f : x.Fo, Fin (2 ^ x.d f.1) × Fin (2 ^ x.w f.1))
      ⊕ ((Σ f : x.Fo, x.LkM E f.1) ⊕ PIdx (List.replicate x.k (pfCube E 2)))))

/-- the number of rows that the lookup on forest f files -/
def nR (f : ℕ) : ℕ := (x.nd f + 1) + ((x.v' f + 1) + ((x.d f + 3) + 1))

end BldWfN

/-- The parameters. -/
structure BldWf (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
    [Fintype Fp] [Algebra Fp E] : Type 1 where
  Cf  : LdCf F E
  /-- the index matrix in the layout of the encoded index -/
  Rw  : Type
  [finRw : Fintype Rw]
  klo : ℕ
  lay : Rw × (Fin klo → Bool) → Cf.J₀
  /-- the forests -/
  n   : ℕ
  rv  : ℕ → ℕ
  d   : ℕ → ℕ
  w   : ℕ → ℕ
  nd  : ℕ → ℕ
  o   : ℕ → ℕ → E
  co  : ℕ → ℕ → Rw → E
  tab : ℕ → ℕ → E
  Z   : Evader E (Fin (n + 1))
  /-- the messages -/
  S   : Sig E
  Sd  : S.Seeds
  Y   : S.StdL Fp
  L   : S.O → ℕ
  t   : S.O → ℕ
  /-- the two placings -/
  pB  : (BldWfN.mk n (Cf.X.v + klo) rv d w nd).Bit → Σ a, Y.Dt a
  pM  : (BldWfN.mk n (Cf.X.v + klo) rv d w nd).Msk E → Σ a, Y.Fr a
  /-- the public supports of the rows -/
  gR  : ∀ f, Fin ((BldWfN.mk n (Cf.X.v + klo) rv d w nd).nR f) →
    (BldWfN.mk n (Cf.X.v + klo) rv d w nd).N E → Prop
  /-- fixed values -/
  p0  : Cf.conf.PIdx
  r0  : S.Rnd
  /-- what the offline linear test needs beside -/
  l   : ℕ
  py  : Rw → Fin l → Bool
  e'  : ℕ
  tt  : ℕ
  NW  : Sig E
  SdW : NW.Seeds
  iW  : NW.O
  lW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) → (NW.om iW).C.J
  NU  : Sig E
  SdU : NU.Seeds
  iU  : NU.O
  lU  : Fin Cf.C₀.k → (NU.om iU).C.J
  NO  : Sig E
  SdO : NO.Seeds
  iO  : NO.O
  lO  : Rw → (NO.om iO).C.J

attribute [instance] BldWf.finRw

namespace BldWf
variable {F E Fp : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
  [Fintype Fp] [Algebra Fp E] (X : BldWf F E Fp)

/-- the numbers -/
@[reducible] def num : BldWfN := ⟨X.n, X.Cf.X.v + X.klo, X.rv, X.d, X.w, X.nd⟩

/-! ### The place maps, total on ℕ -/

/-- the fixed name: digit 0 of entry 0 of forest 0 -/
def dB : X.num.Bit :=
  ⟨⟨0, Nat.zero_le _⟩,
    (⟨0, Nat.pos_of_ne_zero (by positivity)⟩, ⟨0, Nat.pos_of_ne_zero (by positivity)⟩)⟩
def dN : X.num.N E := Sum.inl X.dB

/-- the digit j of the entry u of the table of forest f -/
def bitB (f u j : ℕ) : X.num.Bit :=
  if h : f ≤ X.n then
    ⟨⟨f, h⟩, (⟨u % 2 ^ X.d f, Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩,
        ⟨j % 2 ^ X.w f, Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩)⟩
  else X.dB
def bitN (f u j : ℕ) : X.num.N E := Sum.inl (X.bitB f u j)

/-- a name of an own mask of the lookup on forest f -/
def mkN (f : ℕ) (a : X.num.LkM E f) : X.num.N E :=
  if h : f ≤ X.n then Sum.inr (Sum.inl ⟨⟨f, h⟩, a⟩) else X.dN

def wSn (f : ℕ) (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 1])) : X.num.N E :=
  X.mkN f (.s (Sum.inl i))
def cSn (f : ℕ) (b : Bool) : X.num.N E := X.mkN f (.s (Sum.inr b))
def wAtn (f l : ℕ) (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 3])) : X.num.N E :=
  if h : l < X.nd f then X.mkN f (.t l h (Sum.inl i)) else X.dN
def cAtn (f l : ℕ) (b : Bool) : X.num.N E :=
  if h : l < X.nd f then X.mkN f (.t l h (Sum.inr b)) else X.dN
def wKn (f l : ℕ) (i : PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2])) : X.num.N E :=
  if h : l ≤ X.num.v' f then X.mkN f (.k l h (Sum.inl i)) else X.dN
def cKn (f l : ℕ) (b : Bool) : X.num.N E :=
  if h : l ≤ X.num.v' f then X.mkN f (.k l h (Sum.inr b)) else X.dN
def wTn (f l : ℕ) (i : PIdx (List.replicate (X.w f + l) (pfCube E 2) ++ [pDummy E 2])) :
    X.num.N E :=
  if h : l < X.d f then X.mkN f (.f l h (Sum.inl i)) else X.dN
def cTn (f l : ℕ) (b : Bool) : X.num.N E :=
  if h : l < X.d f then X.mkN f (.f l h (Sum.inr b)) else X.dN
def wEn (f : ℕ) (i : PIdx (List.replicate (X.w f + X.d f) (pfCube E 2))) : X.num.N E :=
  X.mkN f (.e i)
def wBn (f : ℕ) (i : PIdx (List.replicate (X.w f + X.d f) (pfCube E 2) ++ [pDummy E 2])) :
    X.num.N E :=
  X.mkN f (.b (Sum.inl i))
def cBn (f : ℕ) : X.num.N E := X.mkN f (.b (Sum.inr ()))
/-- a hiding coefficient of the batching -/
def wBt (i : PIdx (List.replicate X.num.k (pfCube E 2))) : X.num.N E := Sum.inr (Sum.inr i)

/-- Where a named entry stands in the messages. -/
def nAt : X.num.N E → X.S.Ent :=
  Sum.elim (fun b => ⟨(X.pB b).1, X.Y.atD (X.pB b).1 (X.pB b).2⟩) fun m => X.Y.entF (X.pM m)

/-! ### The index matrix, the keys -/

/-- The index matrix read off a message of the encoded index. -/
def mat (U : X.Cf.conf.Msg) : X.Rw × (Fin X.num.k → Bool) → E :=
  fun rc =>
    X.Cf.upM U (fun i => rc.2 (finSumFinEquiv (Sum.inl i)),
      Sum.inl (X.lay (rc.1, fun i => rc.2 (finSumFinEquiv (Sum.inr i)))))

/-- A key: affine in one column. -/
def key (f : ℕ) (U : X.Cf.conf.Msg) (b : ℕ) : E :=
  X.o f (b / 2 ^ X.num.k) +
    ∑ r, X.co f (b / 2 ^ X.num.k) r * X.mat U (r, Alg.bits X.num.k (b % 2 ^ X.num.k))

/-- the digits that data entries hold, at their places -/
def bitOf (bd : ∀ a, X.Y.Dt a → E) (f u j : ℕ) : E :=
  bd (X.pB (X.bitB f u j)).1 (X.pB (X.bitB f u j)).2

open Classical in
/-- The honest data: the honest digits at their places, 0 elsewhere. -/
def bodyOf (U : X.Cf.conf.Msg) : ∀ a, X.Y.Dt a → E := fun a i =>
  if h : ∃ b : X.num.Bit, X.pB b = ⟨a, i⟩ then
      hbit (X.rv h.choose.1.1 + X.num.k) (X.nd h.choose.1.1 + 1) (X.key h.choose.1.1 U)
        (X.tab h.choose.1.1) h.choose.2.1 h.choose.2.2
    else 0

/-- The data of the preamble. -/
@[reducible] def P : LdWfP E X.Cf.conf where
  S := X.S
  Sd := X.Sd
  Body := ∀ a, X.Y.Dt a → E
  body := X.Y.dataOf
  bodyOf := X.bodyOf
  N := X.num.N E
  finN := X.num.finN E
  ent := fun m n => X.S.ents m (X.nAt n)
  n := X.n
  v := fun f => X.rv f + X.num.k
  d := X.d
  key := X.key
  tab := X.tab
  mult := fun f U bd =>
    Valid (X.rv f + X.num.k) (X.d f) (X.w f) (X.nd f + 1) (X.key f U) (X.tab f) (X.bitOf bd f)
  nR := X.num.nR
  gC := fun f n => ∃ b, n = X.cKn f (X.num.v' f) b
  gR := X.gR
  Rw := X.Rw
  k := X.num.k
  mat := X.mat
  off := fun f z => ext (X.rv f) (X.o f) z
  gOf := fun f z r => ext (X.rv f) (fun u => X.co f u r) z
  cOf := fun f z i => z (X.rv f + (i : ℕ))
  Z := X.Z
  deg := 2
  wAt := X.wBt

/-- The data of the preamble and of the test. -/
@[reducible] def W : LdOWf F E where
  Cf := X.Cf
  P := X.P
  klo := X.klo
  e := finSumFinEquiv.symm
  l := X.l
  lay := X.lay
  py := X.py
  e' := X.e'
  t := X.tt
  NW := X.NW
  SdW := X.SdW
  iW := X.iW
  lW := X.lW
  NU := X.NU
  SdU := X.SdU
  iU := X.iU
  lU := X.lU
  NO := X.NO
  SdO := X.SdO
  iO := X.iO
  lO := X.lO

/-- The further data of the lookups. -/
@[reducible] def K : X.P.Lks where
  v' := X.num.v'
  w := X.w
  n := X.nd
  bAt := X.bitN
  wS := X.wSn
  cS := X.cSn
  wAt := X.wAtn
  cAt := X.cAtn
  wK := X.wKn
  cK := X.cKn
  wT := X.wTn
  cT := X.cTn
  wE := X.wEn
  wB := X.wBn
  cB := X.cBn

/-! ### Readings; the masks of the blocks; all data -/

/-- what the item of lookup f reads: its data and its own masks -/
def Rl (f : ℕ) : X.P.bt.J → Prop := (X.K.asm f).srAll (X.K.Dt f)

/-- the name of a mask of the lookup l, read off the lookup's own table of places -/
def atL (l : Fin (X.P.n + 1)) (i : (X.K.pl X.Rl l).I) : X.P.N :=
  Sum.elim (fun _ => X.dN) id ((X.K.pl X.Rl l).pl i)

/-- the free entry of a name (of a digit's name: that of some coefficient of the batching, picked by
choice: never used) -/
def frOf : X.num.N E → Σ a, X.Y.Fr a :=
  Sum.elim (fun _ => X.pM (Sum.inr (Classical.choice (pIdx_nonemptyB E _)))) X.pM

/-- The free entry at which the mask i of the block b stands. -/
def plV : ∀ b, X.K.wfI X.Rl b → Σ a, X.Y.Fr a
  | some l => fun i => X.frOf (X.atL l i)
  | none => fun i => X.pM (Sum.inr i)

/-- the vectors of masks of a block are finitely many: a term, passed by name -/
@[reducible] def finWfI : ∀ b, Fintype (X.K.wfI X.Rl b → E)
  | some l => Fintype.ofEquiv (X.K.dc X.Rl l).Mk (X.K.pl X.Rl l).ve
  | none => by classical exact inferInstanceAs (Fintype (PIdx X.P.bt.fmt → E))

/-- "the masks of all blocks stand at different free entries" -/
def Hpl : Prop := Function.Injective fun y : Σ b, X.K.wfI X.Rl b => X.plV y.1 y.2

/-- the sender's fixed witness -/
def w0 : X.P.Body × X.P.Wp := (fun _ _ => 0, (X.p0, ()))

/-- All data of weights-formedness, with the standard sender. -/
@[reducible] def Zw (hpl : X.Hpl) : LdWfE F E :=
  letI := X.finWfI
  ⟨X.W, X.K, X.P.stdD X.Y (fun b => b) X.w0, X.L, X.t, X.Rl, fun _ => True,
    X.K.stdX X.Rl X.Y (fun b => b) X.w0 X.nAt X.Y.NoPad X.atL X.plV hpl,
    X.p0, X.r0, X.rv, X.o, X.co⟩

/-- The data of the standard sender, beside `Zw`. -/
@[reducible] def V (hpl : X.Hpl) : (X.Zw hpl).StdW Fp :=
  ⟨X.Y, fun b => b, X.w0, fun b => b, X.nAt, X.Y.NoPad, X.atL, X.plV, hpl⟩

end BldWf
end Cb
