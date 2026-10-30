-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToy.lean: a small example instance of one part of the
interactive proof for a request: the prover sends values that it has computed from its witness (the
reads: `readsOf`, Cb/Ld/LdRead.lean), the verifier draws the challenge of a range check, and the
prover sends the digits.

Definitions, statement and proof. A guard against empty theorems; no parameter of a protocol.
"Read, then the range check" is a part of a segment's body: a list of five moves (`LdRrD.prog`) over
a record of data (`LdRrD`, Cb/Req1/LdSegRefRng.lean). This file fills that record. The front is the
list of moves before that part (`LdBodyD.front`, Cb/Req1/LdSegRefBody.lean).

Main names:
  `RefToy.RPar`: what the front hands over; `RefToy.D R`: the record.
  `Spec.ldSegRef_toyRr` states: `RefToy.p.OK`; the two conditions under which the packing determines
    the cells (`RngPk.Uniq (2 * p.D) p.rdx p.P pK`, Cb/Ld/LdRngAlg.lean), with `pK` the
    characteristic; for every `R`, both sendings have their hypotheses (`(D R).d1.Hyp`,
    `(D R).d3.Hyp`) and the list of five moves has all that a list of moves asks (`(D R).prog.Hyp`).
    For its last clause see the statement.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `datSig` and `datAt`, with the sender and facts,
Cb/GlVal/GlJ3RefKit.lean, `LJ3`, Cb/GlVal/GlJ3Base.lean, and `pK` with `lt_pKz`,
Cb/GlVal/GlToyNum.lean):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).
The names of codes, messages and their facts: Cb/GlVal/GlJ3Send.lean, Cb/GlVal/GlJ3StdNames.lean,
Cb/GlVal/GlJ3PackNames.lean.

Limits: this file says nothing on real parameters: no security. It says nothing on the rest of the
body: Cb/GlVal/GlJ3SegRefToyDig.lean and the files after it. The pads of the online oracle messages
lie in E: pads in the subfield F are not exercised. The bounds that the toys write (one hidden
position) are kept, though this code hides 3 (said of `RefToy.D`).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3RefKit
import Cb.Ld.LdLkpStdPlaces2
import Cb.Req1.LdSegRefRngProofs
import Cb.Ld.LdRngLkp

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace RefToy
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

noncomputable
section

/-- The numbers of the range check. Why these numbers: the head of Cb/Req1/LdSegRefToy.lean (there
over another field). -/
@[reducible] def p : RngPar :=
  { Rp := Unit, Rd := Unit, C := Unit, U := Unit, P := 2, rdx := 7, B := 2, D := 2, q := 2, H := 2 }

/-- `LN`: the names of the own masks of the digits' lookup; `WBt`: of the coefficients of the
batching's hiding polynomial. -/
abbrev LN : Type := LkNm2 E 2 1 2 2
abbrev WBt : Type := PIdx (List.replicate 1 (pfCube E 2))
instance decLN : DecidableEq LN := Classical.decEq _
instance decWBt : DecidableEq WBt := Classical.decEq _
/-- `Jn Xn`: the real entries at the start, but for the packed cell. `So Xn`: all members of S. -/
abbrev Jn (Xn : Type) : Type := Xn ⊕ (LN ⊕ (WBt ⊕ (Unit ⊕ Unit)))
abbrev So (Xn : Type) : Type := Unit ⊕ Jn Xn
/-- `Bt`: the bits: (kind, table entry, bit position). `No'`: the members of N'. -/
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
def mkV (dg : p.Dg E) : Bt → E := fun x =>
  hbit 1 3 (rngKeys p eK (if x.1 then dg.2 else dg.1)) (tabMod 2) x.2.1.toNat x.2.2.val

/-- What the front hands over, as parameters: the entries `Xn` that it has left; the states `St`;
the weights `W` of the read; how the integer cells are read off the core (`yz`); the claims `cl` on
cell maps; what else is claimed (`A₀`); a fixed further witness `wp0`. -/
structure RPar (Kc : Type) (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  Xn  : Type
  [finX : Fintype Xn]
  [decX : DecidableEq Xn]
  St  : Type
  W   : St → p.Rd → p.Row → E
  yz  : Kc → p.Cells
  cl  : ReadCl p E St (Jn Xn)
  A₀  : Rels Kc St E₀ ((datSig (So Xn)).Msg × Wp)
  wp0 : Wp

attribute [instance] RPar.finX RPar.decX

variable {Kc : Type} {E₀ : ExtSpec} {Wp : Type} (R : RPar Kc E₀ Wp)

/-- fixed witnesses -/
def wS0 : (datSig (So R.Xn)).Wit := fun _ => (fun _ => 0, fun _ => 0)
def wN0 : ((datSig (So R.Xn)).sum (datSig (Unit × Unit))).Wit := fun a => match a with
  | .inl _ => (fun _ => 0, fun _ => 0)
  | .inr _ => (fun _ => 0, fun _ => 0)

/-- "Read", then the range check: the data. Its three families of oracle messages have one datum a
member (`datSig`, Cb/GlVal/GlJ3RefKit.lean): `S`, open at the start; `N`, the read; `N'`, the digits
and the bits that `mkV` derives from them. -/
@[reducible] def D : LdRrD E Kc E₀ Wp where
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
  L := fun _ => LJ3
  t := fun _ => 1
  V := Bt → E
  mkV := mkV
  N' := datSig No'
  get' := fun m =>
    (fun r u => datAt m (.inl (false, (r, u))), fun r u => datAt m (.inl (true, (r, u))))
  getV := fun m x => datAt m (.inr x)
  Sd' := Sig.Seeds.indep _
  Dn' := datSnd (fun w i => match i with
      | .inl (b, (r, u)) => (if b then w.2.1.2.2 else w.2.1.2.1) r u
      | .inr x => w.2.2 x) (fun w => (w.1, w.2.1.1)) (wN0 R, ((R.wp0, (fun _ _ => 0, fun _ _ => 0)), fun _ => 0))
  L' := fun _ => LJ3
  t' := fun _ => 1

end

theorem pOK : p.OK := ⟨by decide, by decide, by decide, by decide⟩

theorem uniq : Uniq (2 * p.D) p.rdx p.P pK := by
  refine ⟨by decide, ?_⟩
  show (2 * (2 * 2) - 2 : ℤ) * ∑ l ∈ Finset.range 2, (7 : ℤ) ^ l < ((pK : ℕ) : ℤ)
  have h48 : (2 * (2 * 2) - 2 : ℤ) * ∑ l ∈ Finset.range 2, (7 : ℤ) ^ l = 48 := by
    norm_num [Finset.sum_range_succ]
  rw [h48]
  exact lt_pKz (by norm_num)

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
  p.OK ∧ RngPk.Uniq (2 * p.D) p.rdx p.P pK ∧
  ∀ (Kc : Type) (E₀ : ExtSpec) (Wp : Type) (R : RPar Kc E₀ Wp), (D R).d1.Hyp ∧ (D R).d3.Hyp ∧
    (D R).prog.Hyp ∧ ∀ base : MaskFact (D R).s0.J.W → Prop, (D R).prog.Zk base

end Spec

open RefToy in
theorem ldSegRef_toyRr : Spec.ldSegRef_toyRr :=
  ⟨pOK, uniq,
    fun Kc E₀ Wp R =>
      ⟨send1 R, send3 R,
        ldSegRef_rr_hyp E Kc E₀ Wp pK (D R) pOK uniq (send1 R) (send3 R),
        fun base => ldSegRef_rr_zk E Kc E₀ Wp (D R) base pOK⟩⟩

end Cb.GlJ3
