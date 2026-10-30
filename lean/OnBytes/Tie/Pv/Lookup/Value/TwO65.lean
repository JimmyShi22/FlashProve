-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwO65.lean.
A lookup with one part, no shift, all planes counting and the range table, as a value of the record
`LkAsmH`; and the small lookup `o65A`.

Definitions, two lemmas on sizes, and examples and four lemmas by rfl. Every number and place is
read from OnBytes/Tie/Pv/Lookup/Port/TwNums.lean; the table (row u is u) and the orders are set
here.
Main names:
  `keyA E S : LkAsmH E`: the builder. It is total in the public numbers `S : TwNums.Sizes`.
  `o65A := keyA Cb.Gl.E TwNums.o65S`, where `TwNums.o65S` is `OnBytes.Lkp.o65` read off field by
    field.
  `JOf S := Fin nKeys ⊕ Fin nPlanes ⊕ Fin nMasks`: the entries of the caller's three messages, in
    the order keys, planes, masks, and nothing else.
  (`pEnt l i`, which mask entry of a sumcheck a name `i : PIdx l` is, stands in
    OnBytes/Tie/Pv/Lookup/Value/TwEnt.lean.)
  `kAt`: the keys' reading as data: key number b is an entry or a public constant (`keyRow` in
    OnBytes/Tie/Pv/Lookup/Value/TwForms.lean reads it).
  `o65J := Fin 15 ⊕ Fin 16 ⊕ Fin 104`: typed a second time here, since later statements' types name
    it, and tied: `o65A.J = o65J` by rfl below; to the numbers of `OnBytes.Lkp.o65`: `tie_J`
    (OnBytes/Tie/Pv/Lookup/Port/TwTies.lean); to the index types of OnBytes/G4/Index.lean
    [not in this library]: `tie_Ix` (OnBytes/Tie/Pv/Lookup/Port/TwSigma.lean [not in this library];
    so here read: not proved in this library).
Limits: `keyA E S` is meant as such a lookup only where `S.ok` holds, and as the lookup of
OnBytes/Iop/Lkp.lean only at `S = ofPublic P` with `served P` (the two Bool tests of
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean). No theorem says that `served P` gives `(ofPublic P).ok`.
Every tie to OnBytes/Iop/Lkp.lean is stated at the small lookup alone
(OnBytes/Tie/Pv/Lookup/Port/TwTies.lean). The orders are the total functions `E3.ordKeyW`,
`E3.ordDefault` of the numbers of S, not the lists of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean: the
two are one under `S.ok` (`ofFn_keyW`, `ofFn_default` in
OnBytes/Tie/Pv/Lookup/Value/TwNumsEq.lean; at the small lookup tie_ord* in
OnBytes/Tie/Pv/Lookup/Port/TwTies.lean); where `first` is not lawful no statement ties them.

-/
import Cb.Pv.Lookup.Asm.AsmH
import OnBytes.Tie.Pv.Lookup.Order.E3O65
import Cb.Gl.GlField
import OnBytes.Tie.Pv.Lookup.Port.TwNumsO65
import OnBytes.Tie.Pv.Lookup.Value.TwEnt

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp
open TwNums (Sizes)
open TwNums.Sizes (Ent)

theorem nMasks_pos (S : Sizes) : 0 < S.nMasks := by
  unfold Sizes.nMasks Sizes.scs
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, TwNums.Sc.masks]
  omega
theorem nPlanes_pos (S : Sizes) : 0 < S.nPlanes := Nat.pow_pos (by decide)

/-- the caller's entries: keys, planes, masks -/
abbrev JOf (S : Sizes) : Type := Fin S.nKeys ⊕ Fin S.nPlanes ⊕ Fin S.nMasks

/-- mask entry number s; `mkP` below: plane entry number s. A number out of range goes to entry 0.
That the lookup's blocks ask for none is held at the small lookup alone: for the masks by a guard
(OnBytes/Tie/Pv/Lookup/Test/TwNumsTest.lean [not in this library]), for the planes by `tie_bAt`
(OnBytes/Tie/Pv/Lookup/Port/TwTies.lean). -/
def mkM (S : Sizes) (s : ℕ) : JOf S := .inr (.inr (if h : s < S.nMasks then ⟨s, h⟩ else ⟨0,
    nMasks_pos S⟩))
def mkP (S : Sizes) (s : ℕ) : JOf S := .inr (.inl (if h : s < S.nPlanes then ⟨s, h⟩ else ⟨0,
    nPlanes_pos S⟩))

/-- The keys' reading, as data: key number b is an entry of the keys' message, or a public constant:
the padded place's row (a number out of range: the constant 0). -/
def kAt (E : Type) [Field E] (S : Sizes) (b : ℕ) : JOf S ⊕ E :=
  match S.keyEntry b with
  | some e => if h : e < S.nKeys then .inl (.inl ⟨e, h⟩) else .inr 0
  | none => .inr (((S.padRow b).getD 0 : ℕ) : E)

noncomputable section

/-- The builder: total in the public numbers. -/
def keyA (E : Type) [Field E] [Fintype E] (S : Sizes) : LkAsmH E where
  St := Unit
  J := JOf S
  v' := S.v'
  d := S.d
  w := S.w
  n := S.n
  key := fun _ m b => Sum.elim m id (kAt E S b)
  tab := fun _ u => (u : E)
  bAt := fun u j => mkP S (S.planeEntry u j)
  pads := S.pads
  wAt := fun j i => mkM S (S.pTie j (pEnt _ i))
  cZ := mkM S (S.pTie 0 (.shown (TwNums.shownTie0 none)))
  cAt := fun j b => mkM S (S.pTie j (.shown (if j = 0 then TwNums.shownTie0 (some b) else
      TwNums.shownBool b)))
  wK := fun l i => mkM S (S.pKey l (pEnt _ i))
  cK := fun l b => mkM S (S.pKey l (.shown (TwNums.shownBool b)))
  wT := fun l i => mkM S (S.pTab l (pEnt _ i))
  cT := fun l b => mkM S (S.pTab l (.shown (TwNums.shownBool b)))
  oE := E3.ordDefault (S.w + S.d)
  wE := fun i => mkM S (S.pEnd (pEnt _ i))
  oB := E3.ordDefault (S.w + S.d)
  wB := fun i => mkM S (S.pBit (pEnt _ i))
  cB := mkM S (S.pBit (.shown 0))
  oK := fun l => E3.ordKeyW S.v S.first (0 + l)
  oT := fun l => E3.ordDefault (S.w + l)

/-- the small lookup -/
def o65A : LkAsmH Cb.Gl.E := keyA Cb.Gl.E TwNums.o65S

end

abbrev o65J : Type := Fin 15 ⊕ Fin 16 ⊕ Fin 104

-- the numerals, by rfl
example : o65A.St = Unit := rfl
example : o65A.J = o65J := rfl
example : (o65A.v', o65A.d, o65A.w, o65A.n) = (3, 1, 3, 6) := rfl
example : o65A.pads = [(1, 1)] := rfl
theorem o65A_oK : o65A.oK = E3.o65K := rfl
theorem o65A_oT : o65A.oT = E3.o65T := rfl
theorem o65A_oE : o65A.oE = E3.o65E := rfl
theorem o65A_oB : o65A.oB = E3.o65B := rfl

end Cb.Tw
