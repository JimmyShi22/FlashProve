-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2.lean: a lookup argument by products, put together from its parts as one chain of
reductions in which the prover sends field elements only.

In the library's words: the lookup, assembled (`LkAsm2`): in the order and with the blocks of a
write-up of ours (lean/CREDITS.md). Definitions and statements (each a `Prop` in `Cb.Spec`);
the proofs are in Cb/Ld/LdLkpAsm2Proofs.lean. No oracle is sent. Nothing is assumed about any block
beyond the hypotheses of the statements. What a lookup claim, its multiplicities and its product
trees are is told in the head of Cb/Ld/LdLkp.lean.

The protocol, in order (v = v' + 1). The prover sends scalars only; all masks are entries of oracle
messages sent before.
  λ | the tie: n + 1 sumchecks without variable | the point for the table's products (w coordinates,
    one round) | the keys' tree: v levels (sumcheck, line step) | the table's forest: d levels | the
    table's factor: one sumcheck with w + d variables, where no map is revealed (`PscPar.core`,
    Cb/Ld/LdPsc.lean; w + d + 1 rounds, one row) | the bit test: zerocheck point, one sumcheck (two
    rows).

How it differs from `LkAsm` (Cb/Ld/LdLkpAsm.lean):
  (1) Order: the point for the table's products is drawn right after the tie, before the keys' tree.
    The claim at that point rides past the keys' side; a step without rounds (`enterT`) reads point
    and target off the state again.
  (2) As in `LkAsm`, that point is the block of Cb/Ld/LdLkpRoot.lean as it is: all claims on the 2^w
    products to one claim at a point of E^w.
  (3) Idle bit positions: the table's leaf carries the public factor that is 1 at the n + 1 counting
    positions and 0 at the others (Cb/Ld/LdLkpInst2.lean): the product at an idle position is 1 for
    all messages. No claim on idle positions rides along, but that the entries there are bits;
    nothing on them is asked of "the vector is the multiplicities", but that the entries there are
    bits (`H.MuOn`, Cb/Ld/LdLkpHead2.lean, in the place of `H.MuOK`).
  (4) The table's factor is closed without revealing a map (Cb/Ld/LdLkpEndU.lean): two rounds fewer,
    no inner mask, one row, which reads the closing's hiding coefficients, the incoming masks and
    the bits.
  (5) The order of the read-out's rows: in `LkAsm` the number of keys first and, on the table's
    side, bit test, closing, forest; here as told at `A.rd`.

Main names:
  `LkAsm2`: the data: states St; entries J; 2^(v'+1) keys `key st m`, any function of state and
    entries; a table of 2^d entries of E, read off the state; 2^w bit positions of which the first
    n + 1 count; bAt: where the bit (table entry u, position j) is; the places of all own masks (wS
    to cB). As `LkAsm`, but: wE names the coefficients of a hiding polynomial in w + d variables
    without a further variable; there is no cE. `oK`, `oT`: the order of the rounds of each level of
    the keys' tree and of the table's forest: which coordinate its j-th variable is (by default
    coordinate j). `oE`, `oB`: the same for the w + d variables of the closing and of the bit test.
  `A.formT`, `A.tgtT`: forms and public targets of the claims on the table's products, as the tie
    has left them: below n (made by the tie's steps), at n (the tie's open claim), above n (no form,
    target 1).
  `A.rd`: the read-out: (state, the masked claim on the keys, the list of all rows, in the order of
    the steps: tie; keys' levels; forest's levels; closing (1); bit test (2); number of keys last).
    Within the tie and within a tree the row of a later step comes first.
  `Spec.ldLkpAsm2_base`, `Spec.ldLkpAsm2_ok`: both under the conditions told first under Limits.
  `Spec.ldLkpAsm2_base`: at the base, any tuple type, any reading of the entries, any riding joint,
    any Mu with `H.MuOn`, under the conditions on numbers told first under Limits: `A.baseA` is
    `BkA.Good` (Cb/Ld/LdLkpTreeP.lean: `GoodAt` (Cb/Ld/LdSigLift.lean: knowledge sound for each
    fixed tuple of messages) with the identity as extractor) from every key is an entry of the table
    [exact: and Mu] to (extension of the keys at the end point) + (mask form) = public target, and
    all rows hold.
  `Spec.ldLkpAsm2_ok`: over a signature, under the hypotheses of its statement: `A.sub` is `SubR.OK`
    (Cb/Ld/LdLkp.lean): the interface of the sub-protocol is met, beside any riding joint, with a
    core of any type.
  `Spec.ldLkpAsm2_rounds`: the number of rounds: (1 + 3 (n + 1)) + 1 + Σ_{l ≤ v'} (l + 4) +
    Σ_{l < d} (w + l + 4) + (w + d + 1) + (1 + (w + d + 3)).

Limits: the conditions of the statements are on numbers only (n + 1 ≤ 2^w, 2^(v'+1) < 2^(n+1),
2^d (2^(n+1) - 1) < p, p the characteristic of E), and `H.MuOn Mu`.
"The vector is the multiplicities" is a parameter Mu, on the exact side only. The write-up
has one predicate: all entries are bits; 0 at the idle positions; the polynomial of the keys equals
that of the table with these multiplicities. It is one Mu that meets `H.MuOn`, if n + 1 ≤ 2^w (equal
polynomials give the identity at every λ and, by their degrees, the number of keys); the clause on
idle positions is not asked here, and with the public factor no step needs it. (That this predicate
meets `H.MuOn` is not written out in this file; for the counts by the first-occurrence rule:
`ldLkpHead2_mu`, Cb/Ld/LdLkpHead2.lean.)
All callers stand on `LkAsm2` (weights-formedness, a request's segments, the toys, the tops);
none stands on `LkAsm` (Cb/Ld/LdLkpAsm.lean).
This file says nothing on zero knowledge (the item "masked messages" for the whole chain:
Cb/Ld/LdLkpMaskAsm2.lean, Cb/Ld/LdLkpAsm2GoodM.lean), places of masks (Cb/Ld/LdLkpMaskPlaces2.lean),
support of forms (Cb/Ld/LdLkpAsm2Pull.lean), formats (Cb/Ld/LdLkpAsm2Fmt.lean), errors as a list
(Cb/Ld/LdLkpAsm2Err.lean): files of their own. One key (v = 0) is not covered. This file does not
compare a coordinate's place with another order: here the variable that a level splits off is the
last coordinate and the bit position's coordinates stand first; a renaming of coordinates.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpHead2
import Cb.Ld.LdLkpInst2
import Cb.Ld.LdLkpSegK
import Cb.Ld.LdLkpRoot
import Cb.Ld.LdLkpFormat

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset

noncomputable section

/-- The data of the assembled lookup. -/
structure LkAsm2 (E : Type) [Field E] [Fintype E] where
  St : Type
  J : Type
  [finJ : Fintype J]
  v' : ℕ
  d : ℕ
  w : ℕ
  n : ℕ
  key : St → (J → E) → ℕ → E
  tab : St → ℕ → E
  bAt : ℕ → ℕ → J
  wS  : PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) → J
  cS  : Bool → J
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cAt : ℕ → Bool → J
  wK : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cK : ℕ → Bool → J
  wT : (l : ℕ) → PIdx (List.replicate (w + l) (pfCube E 2) ++ [pDummy E 2]) → J
  cT : ℕ → Bool → J
  wE : PIdx (List.replicate (w + d) (pfCube E 2)) → J
  wB : PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 2]) → J
  cB : J
  /-- the order of the rounds at each level of the keys' tree and of the table's forest
  (`TreeP.sg`, Cb/Ld/LdLkpTreeP.lean); by default the j-th variable is coordinate j. A definition
  that builds an `LkAsm2` field by field and names no order has the default. -/
  oK : (l : ℕ) → Equiv.Perm (Fin (0 + l)) := fun _ => Equiv.refl _
  oT : (l : ℕ) → Equiv.Perm (Fin (w + l)) := fun _ => Equiv.refl _
  /-- the order of the rounds of the closing (`LkInst.oE`, Cb/Ld/LdLkpInst.lean); by default the
  j-th variable is coordinate j -/
  oE : Equiv.Perm (Fin (w + d)) := Equiv.refl _
  /-- the order of the rounds of the bit test (`LkInst.oB`, Cb/Ld/LdLkpInst.lean); by default the
  j-th variable is coordinate j -/
  oB : Equiv.Perm (Fin (w + d)) := Equiv.refl _

attribute [instance] LkAsm2.finJ

namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)

/-- the head's data -/
def H : LkHead E :=
  { St := A.St, J := A.J, v := A.v' + 1, d := A.d, w := A.w, n := A.n, key := A.key, tab := A.tab,
    bAt := A.bAt, wS := A.wS, cS := A.cS, wAt := A.wAt, cAt := A.cAt }

/-- the explicit part after the head; (state, λ) read off it -/
abbrev X2 : Type := E × (A.H.tie.lv (A.n + 1)).T.St
def b2 (x : A.X2) : A.St × E := (A.H.tie.lv (A.n + 1)).base x.2

open Classical in
/-- form and target of the masked claim on the product of the keys -/
def fK (x : A.X2) : A.J → E := fun j => if j = A.cS false then (A.H.tie.bK A.n x.2).1 else 0
def tK (x : A.X2) : E := (A.H.tie.bK A.n x.2).2

open Classical in
/-- forms and targets of the claims on the products of the table -/
def formT (x : A.X2) (θ : Fin (A.w + 0) → Bool) : A.J → E :=
  if numLE θ < A.n then
    fun j => if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n x.2 (numLE θ)).1 else 0
  else if numLE θ = A.n then pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS x.2)
  else 0
def tgtT (x : A.X2) (θ : Fin (A.w + 0) → Bool) : E :=
  if numLE θ < A.n then (A.H.tie.bT A.n x.2 (numLE θ)).2 else if numLE θ = A.n then x.1 else 1

/-- the table's data over the state after the head: for the point -/
def I1 : LkInst E :=
  { X := A.X2, St := A.St, st := fun x => (A.b2 x).1, lam := fun x => (A.b2 x).2, J := A.J,
    v := A.v' + 1, d := A.d, w := A.w, key := A.key, tab := A.tab, bAt := A.bAt, fK := A.fK,
    formT := A.formT, wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT, oK := A.oK, oT := A.oT,
    oE := A.oE, oB := A.oB }

/-- the point for the table's products -/
def R : RootP E := ⟨A.I1.DT2 A.n, A.formT, A.tgtT⟩

/-- the explicit part after the point: (target, (state after the head, point)) -/
abbrev XR : Type := E × ((A.I1.DT2 A.n).lv 0).T.St
def oR (x : A.XR) : A.X2 := x.2.1

/-- the keys' side, over the state after the point -/
def IK : LkInst E :=
  { X := A.XR, St := A.St, st := fun x => (A.b2 (A.oR x)).1,
    lam := fun x => (A.b2 (A.oR x)).2, J := A.J, v := A.v' + 1, d := A.d, w := A.w,
    key := A.key, tab := A.tab, bAt := A.bAt, fK := fun x => A.fK (A.oR x),
    formT := fun _ _ _ => 0, wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT, oK := A.oK,
    oT := A.oT, oE := A.oE, oB := A.oB }

/-- the explicit part after the keys' side; the explicit part after the point read off it -/
abbrev X4 : Type := E × ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.St
def o4 (x : A.X4) : A.XR := oldK A.IK A.v' x

/-- the table's forest, over the state after the keys' side -/
def IT : LkInst E :=
  { X := A.X4, St := A.St, st := fun x => (A.b2 (A.oR (A.o4 x))).1,
    lam := fun x => (A.b2 (A.oR (A.o4 x))).2, J := A.J, v := A.v' + 1, d := A.d, w := A.w,
    key := A.key, tab := A.tab, bAt := A.bAt, fK := fun _ _ => 0,
    formT := fun x => A.formT (A.oR (A.o4 x)), wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT,
    oK := A.oK, oT := A.oT, oE := A.oE, oB := A.oB }

abbrev D : TreeP E := A.IT.DT2 A.n

/-- the step without rounds into level 0 of the forest: target and point as they were left by the
point's round -/
def enterT (x : A.X4) : E × (A.D.lv 0).T.St := ((A.o4 x).1, (x, (A.o4 x).2.2))

/-- the closing, where no map is revealed (`PscPar.core`, Cb/Ld/LdPsc.lean); the bit test (its
states: the closing's end claims) -/
def En : LkEndU E := A.IT.endU A.n A.wE
def Bt : LkBit E := A.IT.bitB A.En.par.Mid A.wB A.cB

abbrev XE : Type := A.En.par.Mid
abbrev XB : Type := A.Bt.zc.next.par.Out

/-- the closing's end claim, and the state after the keys' side, read off the last explicit part -/
def outE (o : A.XB) : A.XE := o.st.1
def oldT (o : A.XB) : A.X4 := (A.D.root A.d (A.outE o).st).1

open Classical in
/-- The multiplicities sum to the number of keys, as a row. -/
def numRow : Row E A.J :=
  ⟨fun i => ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range (A.n + 1), if A.bAt u j = i then (2 : E) ^ j else 0,
    ((2 ^ (A.v' + 1) : ℕ) : E)⟩

/-- the rows of the tie, of the keys' side, of the table's side -/
def rows2 (x : A.X2) : List (Row E A.J) := A.H.tie.rowsAt (A.n + 1) x.2
def rows4 (x : A.X4) : List (Row E A.J) := rowsK A.IK A.v' x
def rowsB (o : A.XB) : List (Row E A.J) :=
  A.D.rowsAt A.d (A.outE o).st ++
  [⟨A.En.par.slU A.En.rowB (A.En.outOf (A.outE o)), A.En.par.tU (A.En.outOf (A.outE o))⟩,
    ⟨A.Bt.zc.next.par.slU (fun _ b => b.elim) o, A.Bt.zc.next.par.tU o⟩,
    ⟨A.Bt.zc.next.par.slE A.Bt.rowA () o, o.vals ()⟩]

/-- the masked claim on the keys -/
def clK (x : A.X4) : MCl E A.J := (A.IK.setV (A.v' + 1)).topCl x

/-- The read-out. -/
def rd (o : A.XB) : TX A.St E A.J :=
  ((A.b2 (A.oR (A.o4 (A.oldT o)))).1,
    A.clK (A.oldT o),
    A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++ [A.numRow])))

/-- the lookup claim, on entries -/
def lk : Lk E A.St (A.J → E) := ⟨A.v' + 1, A.d, A.key, A.tab, fun _ _ => True⟩

section
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)

/-- the keys' side, then the step into the forest; the levels below l -/
def forest : (l : ℕ) → BkA Kc M A.XR (E × (A.D.lv l).T.St) Ex Wp
  | 0 => (segK A.IK A.v' (fun x => A.tK (A.oR x)) Ex M Wp Kc msg).postM A.enterT
  | l + 1 => (forest l).seq (A.D.levA Ex Wp Kc msg l)

/-- the closing; the bit test -/
def endA : BkA Kc M (E × (A.D.lv A.d).T.St) A.XE Ex Wp :=
  ⟨A.En.par.core Ex, A.En.par.honC Ex fun w => msg w.1, A.En.par.numsC Ex Kc⟩
def bitA : BkA Kc M A.XE A.XB Ex Wp :=
  ⟨A.Bt.zc.toIn.chainAt Ex, A.Bt.zc.toIn.chainAtH Ex M Wp msg, A.Bt.zc.toIn.chainAtN Ex Kc⟩

/-- the chain before the read-out -/
def chainA : BkA Kc M A.St A.XB Ex Wp :=
  ((((A.H.headA Ex M Wp Kc msg).seq (A.R.rootA Ex M Wp Kc)).seq (A.forest Ex M Wp Kc msg A.d)).seq
      (A.endA Ex M Wp Kc msg)).seq
    (A.bitA Ex M Wp Kc msg)

/-- The lookup at the base. -/
def baseA : BkA Kc M A.St (TX A.St E A.J) Ex Wp := (A.chainA Ex M Wp Kc msg).postM A.rd

end

/-- The lookup over a signature. -/
def sub (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) :
    SubR S E₀ Kc A.St A.J Wp :=
  ⟨(A.baseA E₀ S.Msg Wp Kc msg).R.keep S.Smp S.ext,
    S.liftH (A.baseA E₀ S.Msg Wp Kc msg).H,
    fun _ _ w => w,
    (A.baseA E₀ S.Msg Wp Kc msg).P.keep S.Smp S.ext⟩

end LkAsm2
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The assembled lookup, at the base. -/
def ldLkpAsm2_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec)
      (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E),
    A.H.lkb.Adm p → A.H.MuOn Mu →
    (A.baseA Ex M Wp Kc msg).Good
      (cj R0 msg id (A.lk.inP Mu) A.lk.inR) (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))

/-- States, under the hypotheses of its statement: the assembled lookup meets the interface of the
sub-protocol. -/
def ldLkpAsm2_ok : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop) (S : Sig E) (E₀ : ExtSpec)
      (Kc Wp : Type) (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    A.H.lkb.Adm p → A.H.MuOn Mu →
    (A.sub S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => Mu st (msg ym.2)) R0 fun ym => msg ym.2

def ldLkpAsm2_rounds : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg).R.shape.length =
      (1 + 3 * (A.n + 1)) + 1 +
        ((∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
          ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) +
        (A.w + A.d + 1) + (1 + (A.w + A.d + 3))

end
end Cb.Spec
