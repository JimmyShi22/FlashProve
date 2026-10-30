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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyStdKit.lean: a tool for small example instances: a
set of oracle messages whose data coordinates have names, with four of the conditions that a
standard sending asks (see `StdKit`).

Definitions, theorems. Building stone for toys; a guard against empty theorems; no parameter of a
protocol.

Main names:
  `StdKit I`: a family N with a layout Y (`Sig.StdL`, Cb/Ld/LdSendStdL.lean) whose data entries are
    named by I (e : I ≃ the data entries of all members), numbers L, t, and four conditions that a
    standard sending asks, as fields: `Y.OK t`, the codes' laws, lists, evading samples.
  `k.dat val`, `k.rdI`, `rdI_dat`: reading at a name gives back what the data map has put there.
  `k.get m i`: the datum with the name i in the messages m: it is the entry at `k.at' i`
    (`get_ents`, by definition), and a function of `Y.dataOf m`.
  `k.put_apart`: see its statement.
  `grpKit G hfr`: the kit of a family of Cb/GlVal/GlJ3SegRefToyGrp.lean all of whose named entries
    are data (`hfr`).
  `oneKit I`: one member holds all data.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `GrpD` with `ldToyGrp`, Cb/GlVal/GlJ3SegRefToyGrp.lean, and `LJ3`,
Cb/GlVal/GlJ3Base.lean; the family N of a `StdKit`, its layout and its numbers are fields of the
record): the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: this file says nothing on real parameters. Pads in the subfield F are not exercised.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToyGrp
import Cb.Obj.LdObjectSenders
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A family that holds named data, with its standard layout. -/
structure StdKit (I : Type) : Type 1 where
  N : Sig E
  Y : N.StdL E
  e : I ≃ Σ a, Y.Dt a
  L : N.O → ℕ
  t : N.O → ℕ
  ok : Y.OK t
  laws : ∀ a, (N.om a).C.Laws
  list : ∀ a, (N.om a).ListLE (L a)
  evades : ∀ a, (N.om a).Evades

namespace StdKit
variable {I : Type} (k : StdKit I)

/-- the entry with the name i -/
def at' (i : I) : k.N.Ent := ⟨(k.e i).1, k.Y.atD (k.e i).1 (k.e i).2⟩

theorem at_inj : Function.Injective k.at' := by
  intro i i' h
  have key : ∀ (x y : Σ a, k.Y.Dt a),
      (⟨x.1, k.Y.atD x.1 x.2⟩ : k.N.Ent) = ⟨y.1, k.Y.atD y.1 y.2⟩ → x = y := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have h1 : a = b := congrArg Sigma.fst h
    subst h1
    have h2 : k.Y.atD a x = k.Y.atD a y := eq_of_heq (Sigma.mk.inj h).2
    exact congrArg _ (Sum.inl_injective (Sum.inl_injective ((k.Y.ν a).symm.injective h2)))
  exact k.e.injective (key _ _ h)

/-- the data map; a vector of data, read at a name -/
def dat {W : Type} (val : W → I → E) (w : W) : ∀ a, k.Y.Dt a → E := fun a x =>
  val w (k.e.symm ⟨a, x⟩)
def rdI (dt : ∀ a, k.Y.Dt a → E) (i : I) : E := dt (k.e i).1 (k.e i).2

theorem rdI_dat {W : Type} (val : W → I → E) (w : W) (i : I) : k.rdI (k.dat val w) i = val w i := by
  show val w (k.e.symm ⟨(k.e i).1, (k.e i).2⟩) = val w i
  rw [Sigma.eta, Equiv.symm_apply_apply]

/-- the datum with the name i -/
def get (m : k.N.Msg) (i : I) : E := k.rdI (k.Y.dataOf m) i

theorem get_ents (m : k.N.Msg) (i : I) : k.get m i = k.N.ents m (k.at' i) := rfl

theorem put_apart {W W' : Type} (val : W → I → E) (rest : W → W') (w0 w w' : W)
    (c : (k.Y.snd (k.dat val) rest w0).Mk) (h : val w' = val w) :
    (k.Y.snd (k.dat val) rest w0).put w' c = (k.Y.snd (k.dat val) rest w0).put w c :=
  (stdL_all E E k.N k.Y k.t W W' (k.dat val) rest w0 k.ok).2.2.2.2.2.2
    w w' c (by unfold dat; rw [h])

end StdKit

/-- The kit of a family all of whose named entries are data. -/
def grpKit {I O : Type} [Fintype I] [Fintype O] [DecidableEq O]
    (G : GrpD I O) (hfr : ∀ i, ¬ G.fr i) : StdKit I where
  N := G.N
  Y := G.Y
  e := { toFun := fun i => ⟨G.mem i, ⟨(⟨i, rfl⟩ : G.X (G.mem i)), hfr i⟩⟩
         invFun := fun x => (x.2.1 : G.X x.1).1
         left_inv := fun _ => rfl
         right_inv := by
           rintro ⟨a, ⟨⟨i, h⟩, h'⟩⟩
           subst h
           rfl }
  L := fun _ => LJ3
  t := fun _ => 3
  ok := (ldToyGrp I O G).2.2.2.2.2.1
  laws := (ldToyGrp I O G).2.2.2.2.2.2.1
  list := (ldToyGrp I O G).2.2.2.2.2.2.2.1
  evades := (ldToyGrp I O G).2.2.2.2.2.2.2.2.1

/-- one member holds all data -/
def oneKit (I : Type) [Fintype I] : StdKit I :=
  grpKit (⟨fun _ => (), fun _ => False⟩ : GrpD I Unit) fun _ h => h

end Cb.GlJ3
