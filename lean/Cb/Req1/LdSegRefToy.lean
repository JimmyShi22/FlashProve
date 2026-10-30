-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefToy.lean: a toy of the body of the reference segment: the data; "read, then the
range check" with all its hypotheses met.

A small example instance: concrete numbers and oracle messages at which the side conditions of the
sequence of reductions of Cb/Req1/LdSegRefRng.lean hold.
Definitions, statement (`Cb.Spec.ldSegRef_toyRr`) and proof. A guard against empty theorems; no
parameter of a protocol.

The numbers (`RefToy.p`), over the field with 101 elements. One packed row, one column, two lanes
(so packing is real): two integer cells, honest bound 2 (cells -1, 0, 1), radix 7, window of
half-width 2, digits in two tables of 2 entries (2 · 2 = 2 · 2); one read; one combination.
The two conditions on radix and characteristic: 2 · 4 - 2 = 6 < 7, and 6 · (1 + 7) = 48 < 101.
The oracle messages: one datum a member (Cb/Req1/LdSegRefToyKit.lean).
  S, open at the start: the packed cell; the entries Xn that the front (Cb/Req1/LdSegFront.lean)
    has left (a parameter); the own masks of the digits' lookup (Cb/Ld/LdLkpStdPlaces2.lean: the
    names for n = 2, v' = 1, d = 2, w = 2); the coefficients of the hiding polynomial of the
    batching of tensor rows; the mask of the one tensor row; an idle entry.
  N: the one read.
  N': the four digits (two kinds, two rows of cells), and the 16 bits of the multiplicities of the
    digits' lookup (two kinds, two table entries, four bit positions), derived from the digits.
What the front hands over is a parameter (`RPar`): Xn; the states St; the weights of the read; how
the integer cells are read off the core; the claims cl on cell maps; what else is claimed, A₀; a
fixed further witness.

Main names:
  `Spec.ldSegRef_toyRr`: for all such parameters: the numbers are as asked (`p.OK`, `Uniq`); both
    sendings have their hypotheses; and so the list of five moves has all that a list of moves asks
    (`D.prog.Hyp`), and what zero knowledge asks of it, whatever is fresh at the start.

Limits: this file says nothing on real parameters: no security. It says nothing on the rest of the
body.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefToyKit
import Cb.Ld.LdLkpStdPlaces2
import Cb.Req1.LdSegRefRngProofs
import Cb.Ld.LdRngLkp

set_option autoImplicit false

namespace Cb
namespace RefToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

noncomputable section

/-- The numbers of the range check. -/
@[reducible] def p : RngPar :=
  { Rp := Unit, Rd := Unit, C := Unit, U := Unit, P := 2, rdx := 7, B := 2, D := 2, q := 2, H := 2 }

/-- the names of the own masks of the digits' lookup; of the coefficients of the batching's hiding
polynomial -/
abbrev LN : Type := LkNm2 K 2 1 2 2
abbrev WBt : Type := PIdx (List.replicate 1 (pfCube K 2))
instance decLN : DecidableEq LN := Classical.decEq _
instance decWBt : DecidableEq WBt := Classical.decEq _
/-- the real entries at the start, but for the packed cell (`LdRrD.J`; `CellRd.ent`,
Cb/Ld/LdRead.lean); all members of S -/
abbrev Jn (Xn : Type) : Type := Xn ⊕ (LN ⊕ (WBt ⊕ (Unit ⊕ Unit)))
abbrev So (Xn : Type) : Type := Unit ⊕ Jn Xn
/-- the bits: (kind, table entry, bit position); the members of N' -/
abbrev Bt : Type := Bool × (Bool × Fin 4)
abbrev No' : Type := (Bool × (p.Row × p.U)) ⊕ Bt

/-- the numbering of the digits of one kind -/
def eK : p.Row × p.U ≃ Fin 2 where
  toFun := fun x => x.1.2
  invFun := fun i => (((), i), ())
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- What the prover derives from the digits: the bits of "how many keys are equal to this table
entry and to no earlier one", kind by kind. -/
def mkV (dg : p.Dg K) : Bt → K := fun x =>
  hbit 1 3 (rngKeys p eK (if x.1 then dg.2 else dg.1)) (tabMod 2) x.2.1.toNat x.2.2.val

/-- What the front hands over. -/
structure RPar (Kc : Type) (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  Xn  : Type
  [finX : Fintype Xn]
  [decX : DecidableEq Xn]
  St  : Type
  W   : St → p.Rd → p.Row → K
  yz  : Kc → p.Cells
  cl  : ReadCl p K St (Jn Xn)
  A₀  : Rels Kc St E₀ ((datSig (So Xn)).Msg × Wp)
  wp0 : Wp

attribute [instance] RPar.finX RPar.decX

variable {Kc : Type} {E₀ : ExtSpec} {Wp : Type} (R : RPar Kc E₀ Wp)

/-- fixed witnesses -/
def wS0 : (datSig (So R.Xn)).Wit := fun _ => (fun _ => 0, fun _ => 0)
def wN0 : ((datSig (So R.Xn)).sum (datSig (Unit × Unit))).Wit := fun a => match a with
  | .inl _ => (fun _ => 0, fun _ => 0)
  | .inr _ => (fun _ => 0, fun _ => 0)

/-- "Read", then the range check: the data. -/
@[reducible] def D : LdRrD K Kc E₀ Wp where
  p := p
  S := datSig (So R.Xn)
  St := R.St
  J := Jn R.Xn
  c := ⟨R.W, fun m _ _ => datAt m (.inl ()), R.yz, fun m j => datAt m (.inr j)⟩
  cl := R.cl
  A₀ := R.A₀
  N := datSig (Unit × Unit)
  get := fun m k c => datAt m (k, c)
  Sd := Sig.Seeds.indep _
  Dn := datSnd (fun w i => w.2.2 i.1 i.2) (fun w => (w.1, w.2.1)) (wS0 R, (R.wp0, fun _ _ => 0))
  L := fun _ => 2
  t := fun _ => 1
  V := Bt → K
  mkV := mkV
  N' := datSig No'
  get' := fun m =>
    (fun r u => datAt m (.inl (false, (r, u))), fun r u => datAt m (.inl (true, (r, u))))
  getV := fun m x => datAt m (.inr x)
  Sd' := Sig.Seeds.indep _
  Dn' := datSnd (fun w i => match i with
      | .inl (b, (r, u)) => (if b then w.2.1.2.2 else w.2.1.2.1) r u
      | .inr x => w.2.2 x) (fun w => (w.1, w.2.1.1)) (wN0 R, ((R.wp0, (fun _ _ => 0, fun _ _ => 0)), fun _ => 0))
  L' := fun _ => 2
  t' := fun _ => 1

end

theorem pOK : p.OK := ⟨by decide, by decide, by decide, by decide⟩

theorem uniq : Uniq (2 * p.D) p.rdx p.P 101 := by
  refine ⟨by decide, ?_⟩
  show (2 * (2 * 2) - 2 : ℤ) * ∑ l ∈ Finset.range 2, (7 : ℤ) ^ l < ((101 : ℕ) : ℤ)
  norm_num [Finset.sum_range_succ]

variable {Kc : Type} {E₀ : ExtSpec} {Wp : Type} (R : RPar Kc E₀ Wp)

theorem send1 : (D R).d1.Hyp :=
  datSend_hyp (D R).s1 (Unit × Unit) Wp
      (readBk p (datSig (Unit × Unit)) (D R).get) _ _ _ fun w m h => by
    show (w.1, (w.2.1, fun k c => datAt m (k, c))) = w
    rw [show (fun k c => datAt m (k, c)) = w.2.2 from funext fun k => funext fun c => h (k, c)]

theorem send3 : (D R).d3.Hyp :=
  datSend_hyp (D R).s3v No' Wp
      (fun m wp => ((wp, (D R).get' m), (D R).getV m)) _ _ _ fun w m h => by
    show (w.1, ((w.2.1.1,
            ((fun r u => datAt m (.inl (false, (r, u)))),
              fun r u => datAt m (.inl (true, (r, u))))),
          fun x => datAt m (.inr x))) = w
    rw [show (fun r u => datAt m (.inl (false, (r, u)))) = w.2.1.2.1
          from funext fun r => funext fun u => h (.inl (false, (r, u))),
      show (fun r u => datAt m (.inl (true, (r, u)))) = w.2.1.2.2
        from funext fun r => funext fun u => h (.inl (true, (r, u))),
      show (fun x => datAt m (.inr x)) = w.2.2 from funext fun x => h (.inr x)]

end RefToy

namespace Spec
open Iop Prob Hiop IOR RefToy

def ldSegRef_toyRr : Prop :=
  p.OK ∧ RngPk.Uniq (2 * p.D) p.rdx p.P 101 ∧
  ∀ (Kc : Type) (E₀ : ExtSpec) (Wp : Type) (R : RPar Kc E₀ Wp), (D R).d1.Hyp ∧ (D R).d3.Hyp ∧
    (D R).prog.Hyp ∧ ∀ base : MaskFact (D R).s0.J.W → Prop, (D R).prog.Zk base

end Spec

open RefToy LdToy in
theorem ldSegRef_toyRr : Spec.ldSegRef_toyRr :=
  ⟨pOK, uniq,
    fun Kc E₀ Wp R =>
      ⟨send1 R, send3 R,
        ldSegRef_rr_hyp K Kc E₀ Wp 101 (D R) pOK uniq (send1 R) (send3 R),
        fun base => ldSegRef_rr_zk K Kc E₀ Wp (D R) base pOK⟩⟩

end Cb
