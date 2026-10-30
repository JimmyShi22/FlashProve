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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyS.lean: a small example instance of one part of the
interactive proof for a request: the prover sends values that it has computed from its witness (the
reads: `readsOf`, Cb/Ld/LdRead.lean), the verifier draws the challenge of a range check, and the
prover sends the digits; here over arbitrary oracle messages that are already open, and by the
library's standard honest sender.

Definitions, statement and proof. A guard against empty theorems; no parameter of a protocol.
Cb/GlVal/GlJ3SegRefToy.lean fixes the oracle messages that are open at the start. Here they are any
signature `R.S`, with an injective naming `R.at'` of the entries that the body reads or names.
`Spec.ldSegRef_toyRrS` states, for every `R`: both sendings are the standard ones
(`(D R).d1.IsStd E`, `(D R).d3.IsStd E`) and have their hypotheses (`(D R).d1.Hyp`, `(D R).d3.Hyp`),
and the list of five moves has all that a list of moves asks (`(D R).prog.Hyp`). For its last clause
see the statement. `LdSendD.IsStd` (Cb/Req1/LdReqProtoStd.lean) says that the sending equals
`LdSendD.std` at some layout and data map, and that the conditions listed there hold.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `StdKit` with its maps and facts, with `oneKit` as the default value of
`k1` and `k3`, Cb/GlVal/GlJ3SegRefToyStdKit.lean, the numbers `RefToy.p` with their facts, `mkV` and
the types of names of Cb/GlVal/GlJ3SegRefToy.lean, and `pK`, Cb/GlVal/GlToyNum.lean; S, `k1`, `k3`
are parameters):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).
The names of codes, messages and their facts: Cb/GlVal/GlJ3Send.lean, Cb/GlVal/GlJ3StdNames.lean,
Cb/GlVal/GlJ3PackNames.lean.

Limits: this file says nothing on real parameters: no security. Pads in the subfield F are not
exercised.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToy
import Cb.GlVal.GlJ3SegRefToyStdKit
import Cb.Req1.LdReqProtoStd
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace RefToyS
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp RefToy

/-- What the front hands over, and the oracle messages that are open. -/
structure RPar (Kc : Type) (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  Xn  : Type
  [finX : Fintype Xn]
  [decX : DecidableEq Xn]
  /-- the open oracle messages; the entries that the body reads or names -/
  S   : Sig E
  at' : So Xn → S.Ent
  inj : Function.Injective at'
  St  : Type
  W   : St → p.Rd → p.Row → E
  yz  : Kc → p.Cells
  cl  : ReadCl p E St (Jn Xn)
  A₀  : Rels Kc St E₀ (S.Msg × Wp)
  wp0 : Wp
  /-- the two families that the body sends, with their standard layouts: the read; digits and
  bits -/
  k1  : StdKit (Unit × Unit) := oneKit _
  k3  : StdKit No' := oneKit _

attribute [instance] RPar.finX RPar.decX

variable {Kc : Type} {E₀ : ExtSpec} {Wp : Type} (R : RPar Kc E₀ Wp)

/-- the entry with the name i -/
def RPar.get (m : R.S.Msg) (i : So R.Xn) : E := R.S.ents m (R.at' i)

/-- fixed witnesses -/
def wS0 : R.S.Wit := fun _ => (fun _ => 0, fun _ => 0)
def wN0 : (R.S.sum R.k1.N).Wit := fun a => match a with
  | .inl _ => (fun _ => 0, fun _ => 0)
  | .inr _ => (fun _ => 0, fun _ => 0)

/-- What the two senders lay down (`val1`: the reads; `val3`: digits and bits), read off the further
witness alone. -/
@[reducible] def val1 {W0 : Type} (w : W0 × (Wp × (Unit → Unit → E))) (i : Unit × Unit) : E :=
  w.2.2 i.1 i.2
@[reducible] def val3 {W0 : Type}
    (w : W0 × ((Wp × ((p.Row → p.U → E) × (p.Row → p.U → E))) × (Bt → E))) : No' → E
  | .inl (b, (r, u)) => (if b then w.2.1.2.2 else w.2.1.2.1) r u
  | .inr x => w.2.2 x

/-- "Read", then the range check: the data. -/
@[reducible] def D : LdRrD E Kc E₀ Wp where
  p := p
  S := R.S
  St := R.St
  J := Jn R.Xn
  c := ⟨R.W, fun m _ _ => R.get m (.inl ()), R.yz, fun m j => R.get m (.inr j)⟩
  cl := R.cl
  A₀ := R.A₀
  N := R.k1.N
  get := fun m k c => R.k1.get m (k, c)
  Sd := Sig.Seeds.indep _
  Dn := R.k1.Y.snd (R.k1.dat val1) (fun w => (w.1, w.2.1)) (wS0 R, (R.wp0, fun _ _ => 0))
  L := R.k1.L
  t := R.k1.t
  V := Bt → E
  mkV := mkV
  N' := R.k3.N
  get' := fun m =>
    (fun r u => R.k3.get m (.inl (false, (r, u))), fun r u => R.k3.get m (.inl (true, (r, u))))
  getV := fun m x => R.k3.get m (.inr x)
  Sd' := Sig.Seeds.indep _
  Dn' := R.k3.Y.snd (R.k3.dat val3) (fun w => (w.1, w.2.1.1))
    (wN0 R, ((R.wp0, (fun _ _ => 0, fun _ _ => 0)), fun _ => 0))
  L' := R.k3.L
  t' := R.k3.t

/-- Both sendings are the standard ones. -/
theorem std1 : (D R).d1.IsStd E :=
  ⟨R.k1.Y, R.k1.dat val1, fun wp => wp.1, fun dt wp => (wp, fun k c => R.k1.rdI dt (k, c)),
    (wS0 R, (R.wp0, fun _ _ => 0)), rfl, R.k1.ok,
    fun w => Prod.ext rfl (funext fun k => funext fun c => R.k1.rdI_dat val1 w (k, c)), R.k1.laws,
    (ldSendFam_fair_indep E R.k1.N).1, R.k1.list, R.k1.evades⟩

theorem std3 : (D R).d3.IsStd E :=
  ⟨R.k3.Y, R.k3.dat val3, fun wp => wp.1.1,
    fun dt wp =>
      ((wp, ((fun r u => R.k3.rdI dt (.inl (false, (r, u)))),
            fun r u => R.k3.rdI dt (.inl (true, (r, u))))),
        fun x => R.k3.rdI dt (.inr x)),
    (wN0 R, ((R.wp0, (fun _ _ => 0, fun _ _ => 0)), fun _ => 0)),
    rfl, R.k3.ok,
    fun w =>
      Prod.ext (Prod.ext rfl
          (Prod.ext (funext fun r => funext fun u => R.k3.rdI_dat val3 w (.inl (false, (r, u))))
            (funext fun r => funext fun u => R.k3.rdI_dat val3 w (.inl (true, (r, u))))))
        (funext fun x => R.k3.rdI_dat val3 w (.inr x)),
    R.k3.laws,
    (ldSendFam_fair_indep E R.k3.N).1,
    R.k3.list, R.k3.evades⟩

theorem send1 : (D R).d1.Hyp := ldReqProtoStd_send E E Kc _ _ (std1 R)
theorem send3 : (D R).d3.Hyp := ldReqProtoStd_send E E Kc _ _ (std3 R)

end RefToyS

namespace Spec
open Iop Prob Hiop IOR RefToyS

def ldSegRef_toyRrS : Prop :=
  ∀ (Kc : Type) (E₀ : ExtSpec) (Wp : Type) (R : RPar Kc E₀ Wp), (D R).d1.IsStd E ∧
    (D R).d3.IsStd E ∧ (D R).d1.Hyp ∧ (D R).d3.Hyp ∧ (D R).prog.Hyp ∧
    ∀ base : MaskFact (D R).s0.J.W → Prop, (D R).prog.Zk base

end Spec

open RefToyS in
theorem ldSegRef_toyRrS : Spec.ldSegRef_toyRrS :=
  fun Kc E₀ Wp R =>
    ⟨std1 R, std3 R, send1 R, send3 R,
      ldSegRef_rr_hyp E Kc E₀ Wp pK (D R) RefToy.pOK RefToy.uniq (send1 R) (send3 R),
      fun base => ldSegRef_rr_zk E Kc E₀ Wp (D R) base RefToy.pOK⟩

end Cb.GlJ3
