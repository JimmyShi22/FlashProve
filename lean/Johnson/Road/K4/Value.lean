-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Value.lean: A VALUE OF THE LETTERS OF THE CHAIN OF A LAYERS' SUB-PROOF's OWN ROUNDS
(`FullPar`, Cb/Pv/Lay/At/OwnW.lean) IN THE SHAPE THAT A REAL PLAN WANTS: entries that are cells,
entries of the sub-proof's own mask row, entries of the committed matrix and entries of the
request's index-mask message; every mask but one at a slot of the own mask row. Definitions and four
theorems.

Why. The library's knowledge soundness of that chain (`FullPar.own_knowAt`) is said at letters. The
one value in the library is a toy with one entry (Cb/Pv/Lay/At/TestOwn.lean). This file makes the
record from fewer letters, `Plan4`, and pays the three fields that follow from the shape: `hrd` (the
cells are read linearly), `hrw` (the weights are the library's reading of the matrix) and the
instances on J.

  `Plan4 E M X`: the letters that stay: the sizes, tables and first layer; a finite type Jc of
    cells' names with `nameOf : Cell → Option Jc`; the number ns of slots of the mask row; the
    committed matrix's kW and hW; how a tuple of messages is read (`cellAt`, `maskAt`, `matAt`,
    `idxAt`); what the lookup left (`zOf`, `kTg`, `kIncS`: its end form's coefficient at each slot);
    the three orders; THE FIRST SLOT OF EACH OF THE SEVEN SUMCHECKS' OWN COEFFICIENTS and of each
    run of hidden values; numberings of the end values; the numbering of the weight claims; and the
    six conditions on sizes.
  `Plan4.J` := Jc ⊕ Fin (ns + 1) ⊕ (Fin hW × Fin (2 ^ kW)) ⊕ Fin (nx + 1). `Plan4.sl n`: slot n of
    the own mask row as an entry (slot ns stands for every n beyond). `Plan4.ix n`: entry n of the
    index-mask message. THE MASK OF THE MERGE's SHOWN VALUE (c7) IS `ix v7`: an entry of the
    index-mask message, not a slot of the own row (OnBytes/Model/Merge.lean's comment on that
    value).
  `Plan4.full : FullPar E M X`: the value. A hiding coefficient q of a sumcheck whose slots begin at
    s lies at slot `slotP fmt s q` (OnBytes/Tie/Pv/SeamRun.lean).
  `Plan4.rd_valid`, `rd_invalid`: a cell with a name reads as its entry; a cell without a name as 0.
  `Plan4.rd_linear`: the cells are read linearly off the entries.
  `Plan4.know`: `own_knowAt` at the value.

Limits. NOTHING HERE SAYS THAT THE LETTERS ARE A PLAN's OR A PROGRAM's: which slot is which, the
numberings and the readings are choices that no type checks. The first slots are numbers, not
functions of the statement: they must be public. As a statement of soundness `know` says what
`own_knowAt` says.
-/
import Cb.Pv.Lay.At.OwnW
import OnBytes.Tie.Pv.SeamRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl Tables)
open Inst.Model.Layout (units off)
open Inst.Model.FFSeg (Dim Cell LW layerR lDd lF lFe)
open OnBytes.Tie.Pv (slotP)

noncomputable section

/-- The letters that stay. -/
structure Plan4 (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type) where
  D : Dim
  tb : Tables
  L0 : ℕ
  /-- the cells' names -/
  Jc : Type
  [finJc : Fintype Jc]
  [decJc : DecidableEq Jc]
  nameOf : Cell → Option Jc
  /-- the mask row's slots; the committed matrix's column bits and rows; the entries of the
  request's index-mask message -/
  ns : ℕ
  kW : ℕ
  hW : ℕ
  nx : ℕ
  /-- how a tuple of messages is read -/
  cellAt : M → Jc → E
  maskAt : M → ℕ → E
  matAt : M → ℕ → ℕ → E
  idxAt : M → ℕ → E
  two : (2 : E) ≠ 0
  /-- what the lookup left -/
  zOf : X → ℕ → E
  kTg : X → E
  kIncS : X → ℕ → E
  /-- the three orders -/
  eS : Fin (D.lL + 1 + (lDd D + D.lT)) ≃ Fin (D.lL + 1 + (lDd D + D.lT))
  e5 : Fin (D.lL + lF D + D.lT) ≃ Fin (D.lL + lF D + D.lT)
  e6 : Fin (D.lL - 1 + (lFe D + D.lT)) ≃ Fin (D.lL - 1 + (lFe D + D.lT))
  /-- first slots: the sums; the squares' own, its end values; the products; their claimed sum,
  its own, its end values; the terms' claimed sum, its own, its end values; the batched
  sumcheck's own, its end values; the two layers' own and end values; the merge's own. v7: NO
  slot: the entry of the index-mask message that masks the merge's shown value -/
  sW : ℕ
  fS : ℕ
  vS : ℕ
  sP : ℕ
  cP0 : ℕ
  fP : ℕ
  vP : ℕ
  cT0 : ℕ
  fT : ℕ
  vT : ℕ
  fI : ℕ
  vI : ℕ
  f5 : ℕ
  v5 : ℕ
  f6 : ℕ
  v6 : ℕ
  f7 : ℕ
  v7 : ℕ
  /-- numberings of the end values -/
  numT : ShA D → ℕ
  numI : IA D ⊕ IB D → ℕ
  /-- a numbering of the weight claims -/
  nW : ℕ
  num : Fin nW ≃ Piece D
  /-- conditions on the sizes -/
  hfe : D.fe ≤ D.f
  h0 : L0 % 2 = 0
  hf : D.f = 2 * D.fe
  hh : D.P.nq + D.P.nkv ≤ 64
  hLay : L0 + D.nl ≤ D.P.layers
  hH : off kW (units D.P) (units D.P).length ≤ hW

attribute [instance] Plan4.finJc Plan4.decJc

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace Plan4
variable (Q : Plan4 E M X)

/-- The entries: cells, entries of the sub-proof's own mask row, entries of the committed matrix,
entries of the request's index-mask message. -/
abbrev J : Type := Q.Jc ⊕ (Fin (Q.ns + 1) ⊕ ((Fin Q.hW × Fin (2 ^ Q.kW)) ⊕ Fin (Q.nx + 1)))

/-- Slot n of the mask row as an entry. -/
def sl (n : ℕ) : Q.J := .inr (.inl ⟨min n Q.ns, Nat.lt_succ_of_le (Nat.min_le_right n Q.ns)⟩)

/-- Entry n of the index-mask message as an entry. -/
def ix (n : ℕ) : Q.J :=
  .inr (.inr (.inr ⟨min n Q.nx, Nat.lt_succ_of_le (Nat.min_le_right n Q.nx)⟩))

/-- The messages as entries. -/
def msg (m : M) : Q.J → E
  | .inl c => Q.cellAt m c
  | .inr (.inl s) => Q.maskAt m s
  | .inr (.inr (.inl (r, c))) => Q.matAt m r c
  | .inr (.inr (.inr i)) => Q.idxAt m i

/-- The entries as cells: a cell without a name reads as 0. -/
def rd (m : Q.J → E) (c : Cell) : E :=
  match Q.nameOf c with
  | some j => m (.inl j)
  | none => 0

/-- The entries as the committed matrix: 0 outside it. -/
def Wn (m : Q.J → E) (r c : ℕ) : E :=
  if h : r < Q.hW ∧ c < 2 ^ Q.kW then m (.inr (.inr (.inl (⟨r, h.1⟩, ⟨c, h.2⟩)))) else 0

theorem rd_valid (m : Q.J → E) {c : Cell} {j : Q.Jc} (h : Q.nameOf c = some j) :
    Q.rd m c = m (.inl j) := by
  unfold rd
  rw [h]

theorem rd_invalid (m : Q.J → E) {c : Cell} (h : Q.nameOf c = none) : Q.rd m c = 0 := by
  unfold rd
  rw [h]

theorem rd_linear (a b : E) (m m' : Q.J → E) (c : Cell) :
    Q.rd (fun j => a * m j + b * m' j) c = a * Q.rd m c + b * Q.rd m' c := by
  unfold rd
  cases Q.nameOf c with
  | some j => rfl
  | none => simp

/-- The lookup's end form's coefficients, as a function on the entries: on the mask row alone. -/
def kInc (x : X) : Q.J → E
  | .inr (.inl s) => Q.kIncS x s
  | _ => 0

/-- **The value.** -/
def full : FullPar E M X where
  D := Q.D
  tb := Q.tb
  L0 := Q.L0
  J := Q.J
  msg := Q.msg
  rd := Q.rd
  rw := fun m l => layerR Q.D.P Q.kW (Q.Wn m) (Q.L0 + l)
  two := Q.two
  zOf := Q.zOf
  kTg := Q.kTg
  kInc := Q.kInc
  eS := Q.eS
  mkS := fun i s => Q.sl (Q.sW + 9 * i + s)
  wS := fun q => Q.sl (slotP _ Q.fS q)
  cS := fun b => Q.sl (Q.vS + (if b then 1 else 0))
  mkP := fun i => Q.sl (Q.sP + i)
  rP := Q.sl Q.cP0
  wP := fun q => Q.sl (slotP _ Q.fP q)
  cP := fun x => Q.sl (Q.vP + 4 * x.1 + x.2)
  rT := Q.sl Q.cT0
  wT := fun q => Q.sl (slotP _ Q.fT q)
  cT := fun a => Q.sl (Q.vT + Q.numT a)
  hrd := Q.rd_linear
  hfe := Q.hfe
  wI := fun q => Q.sl (slotP _ Q.fI q)
  cI := fun a => Q.sl (Q.vI + Q.numI a)
  e5 := Q.e5
  e6 := Q.e6
  w5 := fun q => Q.sl (slotP _ Q.f5 q)
  c5 := fun b => Q.sl (Q.v5 + (if b then 1 else 0))
  w6 := fun q => Q.sl (slotP _ Q.f6 q)
  c6 := fun b => Q.sl (Q.v6 + (if b then 1 else 0))
  kW := Q.kW
  hW := Q.hW
  Wn := Q.Wn
  hrw := fun _ => rfl
  nW := Q.nW
  num := Q.num
  w7 := fun q => Q.sl (slotP _ Q.f7 q)
  c7 := Q.ix Q.v7
  h0 := Q.h0
  hf := Q.hf
  hh := Q.hh
  hLay := Q.hLay
  hH := Q.hH

/-- `own_knowAt` at the value. -/
theorem know {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (Q.full.own.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ Q.full.own.pT x m)
      (jt A0 (fun e => pr (Q.full.own.toOwn.ch.back e)) (Q.full.own.toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) (Q.full.own.toOwn.ch.eps Ex) :=
  Q.full.own_knowAt Ex A0 pr Dn

end Plan4
end
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.know
