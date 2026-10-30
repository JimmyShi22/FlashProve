-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupStdMsg.lean: for toys: this file gives the messages of a standard group as standard
oracle messages, so that they can be sent.

In the words of lean/GLOSSARY.md: toy: a small example instance. guard: a proved statement that
stands beside a theorem or a notion: most often an instance that meets all hypotheses of the
theorem.


Definitions, statements as theorems, proofs. Abstract field, variable codes. A tool for guards
against empty theorems; no parameter of a protocol.
Cb/Ld/LdGroupStd.lean: a standard group (`StdG`): messages declared as main rows under a base code
beside mask rows under a mask code, with any sample maps. Cb/Obj/LdObjectToyKit.lean: a standard
oracle message (`StdM`): a code, data and one pad entry, the row with a pad as sample, and, under
`M.OK L t`, a sender whose answer is uniform (`stdM_uniform`). Here the two are one.

Main names:
  `StdGM E P`: the data: Cb, Zb, the names A, the rows Rm a, Rz a; pj a: the pad place of the
    message a (any entry); the values b of the pad's coefficient; one radius.
  `R.D : StdG E P`: the standard group with these samples (`(R.M a).Z`). (R.M a).om is R.D.S.om a,
    by definition (`StdGM.om`).
  `stdGM_ok`: `(R.M a).OK L t` from: the laws of Cb and Zb; each hides t long positions
    (`LdCode.Zk`, Cb/Ld/LdRel.lean; Cb/Ld/LdSumZkRows.lean, Cb/Ld/LdZkPair.lean); both have distance
    at least d (`Dist d`); lists of at most L at the radius for every code at these positions with
    its laws and distance at least d; b injective, never 0.

Limits: this file does not say that the conditions can be met (at a value: `LdGToy.first_ok`,
Cb/Obj/LdObjectPartReqToy.lean, at `LdGToy.R5`, Cb/Ld/LdGroupToy.lean). It says nothing on more than
one pad place.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupStd
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdZkPair
import Cb.Ld.LdSumZkRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

/-- a type, cut at one of its elements -/
def splitAt {X : Type} [DecidableEq X] (x₀ : X) : X ≃ {x // x ≠ x₀} ⊕ Unit where
  toFun x := if h : x = x₀ then .inr () else .inl ⟨x, h⟩
  invFun := Sum.elim (fun x => x.1) fun _ => x₀
  left_inv x := by
    by_cases h : x = x₀
    · simp [h]
    · simp [h]
  right_inv := by
    rintro (⟨x, h⟩ | ⟨⟩)
    · simp [h]
    · simp

theorem splitAt_self {X : Type} [DecidableEq X] (x₀ : X) : splitAt x₀ x₀ = .inr () := by
  simp [splitAt]
theorem splitAt_ne {X : Type} [DecidableEq X] {x₀ x : X} (h : x ≠ x₀) :
    splitAt x₀ x = .inl ⟨x, h⟩ := by
  simp [splitAt, h]

/-- each datum has a corner of its own -/
def ownC {X : Type} [DecidableEq X] : X → X → Bool := fun d m => decide (m = d)

theorem ownC_inj {X : Type} [DecidableEq X] : Function.Injective (ownC (X := X)) := fun d d' h => by
  have h1 : decide (d = d) = decide (d = d') := congrFun h d
  simpa using h1

/-- A standard group whose messages can be sent: the data. -/
structure StdGM (E P : Type) [Field E] [Fintype P] where
  Cb : LdCode E P
  Zb : LdCode E P
  A  : Type
  [finA : Fintype A]
  [decA : DecidableEq A]
  Rm : A → Type
  [finRm : ∀ a, Fintype (Rm a)]
  [decRm : ∀ a, DecidableEq (Rm a)]
  Rz : A → Type
  [finRz : ∀ a, Fintype (Rz a)]
  [decRz : ∀ a, DecidableEq (Rz a)]
  /-- the pad place of each message -/
  pj : ∀ a, ((Cb.il (Rm a)).pair (Zb.il (Rz a))).J
  /-- the values of the pad's coefficient -/
  B  : Type
  [finB : Fintype B]
  [neB : Nonempty B]
  b  : B → E
  e  : ℕ

attribute [instance] StdGM.finA StdGM.decA StdGM.finRm StdGM.decRm StdGM.finRz
  StdGM.decRz StdGM.finB StdGM.neB

namespace StdGM
variable {E P : Type} [Field E] [Fintype E] [Fintype P] (R : StdGM E P)

/-- The message a as a standard oracle message. -/
@[reducible] def M (a : R.A) : StdM E P where
  Cm := (R.Cb.il (R.Rm a)).pair (R.Zb.il (R.Rz a))
  Dt := {j // j ≠ R.pj a}
  place := (splitAt (R.pj a)).symm
  μ := {j // j ≠ R.pj a}
  plc := ownC
  B := R.B
  b := R.b
  e := R.e

/-- The standard group. -/
@[reducible] def D : StdG E P where
  Cb := R.Cb
  Zb := R.Zb
  A := R.A
  Rm := R.Rm
  Rz := R.Rz
  Zs := fun a => (R.M a).Z
  e := R.e

theorem om (a : R.A) : (R.M a).om = R.D.S.om a := rfl

end StdGM

theorem stdGM_ok {E P : Type} [Field E] [Fintype E] [Fintype P] (R : StdGM E P) (L t d : ℕ)
    (hC : R.Cb.Laws) (hZ : R.Zb.Laws) (dC : R.Cb.Dist d) (dZ : R.Zb.Dist d) (zC : R.Cb.Zk t)
    (zZ : R.Zb.Zk t) (hl : ∀ C : LdCode E P, C.Laws → C.Dist d → C.ListAt R.e L)
    (hb : Function.Injective R.b) (h0 : ∀ β, R.b β ≠ 0) (a : R.A) : (R.M a).OK L t where
  laws := ld_laws_pair E P _ _ (ld_laws_il E P _ _ hC) (ld_laws_il E P _ _ hZ)
  list := hl _ (ld_laws_pair E P _ _ (ld_laws_il E P _ _ hC) (ld_laws_il E P _ _ hZ))
    (ld_dist_pair E P _ _ d (ld_dist_il E P _ _ d dC) (ld_dist_il E P _ _ d dZ))
  zk := ld_zk_pair E P _ _ t (ld_zk_il E P _ _ t zC) (ld_zk_il E P _ _ t zZ)
  plc := ownC_inj
  inj := hb
  ne0 := h0

end Cb
