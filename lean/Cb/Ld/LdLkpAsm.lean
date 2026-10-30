-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm.lean: the lookup, assembled (`LkAsm`). It is a lookup argument for the claim that
every key is an entry of a table, with multiplicities in bits and products computed along binary
trees, each level by a sumcheck. No oracle is sent. What is left is the masked claim on the
extension of the keys at a point, and linear rows on entries of messages that were sent before.
All callers stand on `LkAsm2` (Cb/Ld/LdLkpAsm2.lean), not on `LkAsm`: no protocol, toy or top
stands on it; its files are here because files of `LkAsm2` quote their generic parts.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLkpAsmProofs.lean. Nothing is assumed about any block beyond the hypotheses of the
statements: the parts are Cb/Ld/LdLkpHead.lean (first challenge, tie), Cb/Ld/LdLkpSegK.lean (keys'
side), Cb/Ld/LdLkpSegT.lean (table's side: point of the forest, forest, closing, bit test), which
build on the sumcheck for a polynomial summand, the line step and the zerocheck that are proved in
Cb/Ld/LdPsc*.lean, LdLine*.lean, LdZero*.lean. What a lookup claim, its multiplicities and its
product trees are is told in the head of Cb/Ld/LdLkp.lean.

The protocol, in order. The prover sends scalars only; all masks are entries of oracle messages sent
before.
  λ | the tie: n + 1 sumchecks without variable | the keys' tree: v = v' + 1 levels (sumcheck, line
    step) | the point of the table's forest | the forest: d levels | the closing of the forest's top
    claim: one sumcheck | the bit test: zerocheck point, one sumcheck.

Main names:
  `LkAsm`: the data: states St; entries J; 2^(v'+1) keys "key st m", any function of state and
    entries, never sent; a table of 2^d entries of E, read off the state; 2^w bit positions of which
    the first n + 1 count; bAt: where the bit (table entry u, position j) stands; the places of all
    own masks.
  `A.fK`, `A.tK`, `A.formT`, `A.tgtT`: forms and public targets of the masked claims on the roots,
    as the tie has left them: on the product of the keys; on the products of the table at the
    positions below n (made by the tie's steps), at n (the tie's open claim), above n (no form,
    target 1).
  `A.rd`: the read-out, a step without rounds: (state, the masked claim on the keys, the list of all
    rows).
  `Spec.ldLkpAsm_base`: under the conditions told first under Limits: at the base, for any tuple
    type M, any reading msg of the entries, any riding joint R0, any Mu with `H.MuOK`
    (Cb/Ld/LdLkpHead.lean: with `Mu`, for keys in the table, the claim after λ holds at every λ, and
    the idle positions are idle): from every key is an entry of the table [exact: and Mu, "the
    vector is the multiplicities"] to (extension of the keys at the end point) + (mask form) =
    public target, and all rows hold. `BkA.Good` (Cb/Ld/LdLkpTreeP.lean), that is `GoodAt`
    (Cb/Ld/LdSigLift.lean): strings (`point`), local (`isLocal`), complete outside the withheld set
    (`acc`), that set bounded by the block's numbers (`prBad`, `cover`, `prCov`), knowledge sound
    for each fixed tuple of messages on the statements with R0's condition (the field `on` of `cj`),
    with the identity as extractor.
  `Spec.ldLkpAsm_ok`: under the hypotheses of its statement, over a signature: `A.sub` is `SubR.OK`
    (Cb/Ld/LdLkp.lean): the interface of the sub-protocol is met, beside any riding joint, with a
    core of any type.
  `Spec.ldLkpAsm_rounds`: the number of rounds: 1 + 3 (n + 1) + Σ_{l ≤ v'} (l + 4) + 1 + Σ_{l < d}
    (w + l + 4) + (w + d + 3) + 1 + (w + d + 3). Nothing is merged.

Limits: the conditions of the statements are on numbers only (`A.H.lkb.Adm p`: n + 1 ≤ 2^w,
2^(v'+1) < 2^(n+1), 2^d (2^(n+1) - 1) < p; p the characteristic of E), and `H.MuOK Mu`.
Declared, ours: how the tie runs; the plain claim "product = 1" at the idle bit positions; a round
of its own for the forest's point. The bit test's zerocheck point is a round of its own.
Four differences to a write-up of ours (lean/CREDITS.md), which writes the lookup out
(declared; `LkAsm2` (Cb/Ld/LdLkpAsm2.lean) has none of (1), (3) and (4)) (by a reading):
  (1) Order. There the one claim on the table's products comes right after the tie, before the keys'
    grand product; here the forest's point is drawn after the keys' tree.
  (2) The forest's first point. There a line step on a map with as many parts as there are bit
    positions, counting and idle ones together (a power of two): one round; here a round of its own
    for the point (declared above).
  (3) Idle bit positions. There the table's factor carries a public factor, 1 at the counting
    positions and 0 at the others, so the product at an idle position is 1 for all messages and the
    claim "product = 1" there needs nothing; here that claim is added after the challenge and rides
    along, true because honest bits are 0 there: a hypothesis (`H.Idle`, asked through `H.MuOK`)
    that falls with the public factor.
  (4) The table's factor. There it is closed without revealing a map (two rounds fewer, one row);
    here by the closing that reveals (two rows). This bears on what the verifier sees, so on the
    block's item "masked messages" too, not only on counts.
Zero knowledge: the item "masked messages" for the whole chain is not here; that the places of the
masks are pairwise different, lie outside the bits and are read by nothing else is not asked by
these statements (they speak of completeness and knowledge soundness only). One key (v = 0) is not
covered. Errors are the blocks' errors in a row, by definition of the numbers; they are not summed
here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpHead
import Cb.Ld.LdLkpSegK
import Cb.Ld.LdLkpSegT

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp Finset

noncomputable section

/-- The data of the assembled lookup. -/
structure LkAsm (E : Type) [Field E] [Fintype E] where
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
  wE : PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 1]) → J
  cE : J
  wB : PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 2]) → J
  cB : J

attribute [instance] LkAsm.finJ

namespace LkAsm
variable {E : Type} [Field E] [Fintype E] (A : LkAsm E)

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

/-- the keys' side -/
def IK : LkInst E :=
  { X := A.X2, St := A.St, st := fun x => (A.b2 x).1, lam := fun x => (A.b2 x).2, J := A.J,
    v := A.v' + 1, d := A.d, w := A.w, key := A.key, tab := A.tab, bAt := A.bAt, fK := A.fK,
    formT := fun _ _ _ => 0, wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT }

/-- the explicit part after the keys' side; the explicit part after the head read off it -/
abbrev X4 : Type := E × ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.St
def o4 (x : A.X4) : A.X2 := oldK A.IK A.v' x

open Classical in
/-- forms and targets of the claims on the products of the table -/
def formT (x : A.X4) (θ : Fin (A.w + 0) → Bool) : A.J → E :=
  if numLE θ < A.n then
    fun j => if j = A.cAt (numLE θ) true then (A.H.tie.bT A.n (A.o4 x).2 (numLE θ)).1 else 0
  else if numLE θ = A.n then
    pushJ (A.H.tie.lv (A.n + 1)).toJ ((A.H.tie.lv (A.n + 1)).T.slS (A.o4 x).2)
  else 0
def tgtT (x : A.X4) (θ : Fin (A.w + 0) → Bool) : E :=
  if numLE θ < A.n then (A.H.tie.bT A.n (A.o4 x).2 (numLE θ)).2
  else if numLE θ = A.n then (A.o4 x).1
  else 1

/-- the table's side -/
def IT : LkInst E :=
  { X := A.X4, St := A.St, st := fun x => (A.b2 (A.o4 x)).1, lam := fun x => (A.b2 (A.o4 x)).2,
    J := A.J, v := A.v' + 1, d := A.d, w := A.w, key := A.key, tab := A.tab, bAt := A.bAt,
    fK := fun _ _ => 0, formT := A.formT, wK := A.wK, cK := A.cK, wT := A.wT, cT := A.cT }

def Q : SegTab E := { I := A.IT, tgt := A.tgtT, wE := A.wE, cE := A.cE, wB := A.wB, cB := A.cB }

open Classical in
/-- "The multiplicities sum to the number of keys", as a row. -/
def numRow : Row E A.J :=
  ⟨fun i => ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range (A.n + 1), if A.bAt u j = i then (2 : E) ^ j else 0,
    ((2 ^ (A.v' + 1) : ℕ) : E)⟩

/-- the rows of the tie, of the keys' side, of the table's side -/
def rows2 (x : A.X2) : List (Row E A.J) := A.H.tie.rowsAt (A.n + 1) x.2
def rows4 (x : A.X4) : List (Row E A.J) := rowsK A.IK A.v' x
def rowsB (o : A.Q.XB) : List (Row E A.J) := A.Q.rowsT o

/-- the masked claim on the keys -/
def clK (x : A.X4) : MCl E A.J := (A.IK.setV (A.v' + 1)).topCl x

/-- The read-out. -/
def rd (o : A.Q.XB) : TX A.St E A.J :=
  ((A.b2 (A.o4 (A.Q.oldT o))).1,
    A.clK (A.Q.oldT o),
    A.numRow :: (A.rows2 (A.o4 (A.Q.oldT o)) ++ (A.rows4 (A.Q.oldT o) ++ A.rowsB o)))

/-- the lookup claim, on entries -/
def lk : Lk E A.St (A.J → E) := ⟨A.v' + 1, A.d, A.key, A.tab, fun _ _ => True⟩

section
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)

/-- the chain before the read-out -/
def chainA : BkA Kc M A.St A.Q.XB Ex Wp :=
  ((A.H.headA Ex M Wp Kc msg).seq (segK A.IK A.v' A.tK Ex M Wp Kc msg)).seq (A.Q.segT Ex Wp Kc msg)

/-- The lookup at the base. -/
def baseA : BkA Kc M A.St (TX A.St E A.J) Ex Wp :=
  ⟨(A.chainA Ex M Wp Kc msg).R.post (fun o => some (A.rd o)) (ExtMap.id Ex),
    (A.chainA Ex M Wp Kc msg).H.post (fun o => some (A.rd o)) (ExtMap.id Ex) fun o =>
      (A.rd o.1, o.2),
    (A.chainA Ex M Wp Kc msg).P.post (fun o => some (A.rd o)) (ExtMap.id Ex)⟩

end

/-- The lookup over a signature. -/
def sub (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) :
    SubR S E₀ Kc A.St A.J Wp :=
  ⟨(A.baseA E₀ S.Msg Wp Kc msg).R.keep S.Smp S.ext,
    S.liftH (A.baseA E₀ S.Msg Wp Kc msg).H,
    fun _ _ w => w,
    (A.baseA E₀ S.Msg Wp Kc msg).P.keep S.Smp S.ext⟩

end LkAsm
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The assembled lookup, at the base. What is stated: see `Spec.ldLkpAsm_base` under "Main names:"
at the top of this file. -/
def ldLkpAsm_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) (Kc M Wp : Type)
      (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E),
    A.H.lkb.Adm p → A.H.MuOK Mu →
    (A.baseA Ex M Wp Kc msg).Good
      (cj R0 msg id (A.lk.inP Mu) A.lk.inR) (cj R0 msg Prod.fst (A.lk.out id id) (A.lk.out id id))

/-- Under the hypotheses below (E of characteristic p among them): the assembled lookup meets the
interface of the sub-protocol. -/
def ldLkpAsm_ok : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm E) (Mu : A.St → (A.J → E) → Prop) (S : Sig E) (E₀ : ExtSpec)
      (Kc Wp : Type) (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    A.H.lkb.Adm p → A.H.MuOK Mu →
    (A.sub S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => Mu st (msg ym.2)) R0 fun ym => msg ym.2

def ldLkpAsm_rounds : Prop :=
  ∀ (A : LkAsm E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg).R.shape.length =
      (1 + 3 * (A.n + 1)) + (∑ l ∈ Finset.range (A.v' + 1), (0 + l + 3 + 1)) +
        ((1 + ∑ l ∈ Finset.range A.d, (A.w + l + 3 + 1)) + (A.w + A.d + 3) + (1 + (A.w + A.d + 3)))

end
end Cb.Spec
