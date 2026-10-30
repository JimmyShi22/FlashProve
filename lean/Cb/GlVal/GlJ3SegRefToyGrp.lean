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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyGrp.lean: a tool for small example instances: named
values are packed into a few oracle messages.

Definitions, statements (`Cb.GlJ3.Spec.ldToyGrp`, `Cb.GlJ3.Spec.ldToyGrp_sent`) and proofs. A tool
for guards against empty theorems; no parameter of a protocol. The toys of a reference segment's
body name their entries by a finite set I.

Main names:
  `GrpD I O`: the data G. `mem i`: the member that holds the entry named i. `fr i`: the entry is
    free, else it is a datum.
  `G.N`, `G.Y`: the family (`stdMFam`, Cb/Obj/LdObjectSendersStdM.lean) and its layout (data, free
    entries, one pad a member) (`stdMFamLF`, Cb/Ld/LdSendStdMFree.lean).
  `G.at'`: the naming of the entries.
  `Spec.ldToyGrp` states, for every G over finite I and O: `at'` is injective; `at' i` lies in the
    member `mem i`; for `fr i` it is the free entry `G.frAt i`, else a data entry; no `at' i` is a
    pad; `G.Y.OK (fun _ => 3)` (`Sig.StdL.OK`, Cb/Ld/LdSendStdL.lean, at the number 3 for every
    member); the codes' laws (`LdCode.Laws`, Cb/Ld/LdRel.lean); lists of at most `LJ3`
    (`OMsg.ListLE`, Cb/Ld/LdSig.lean); evading samples (`OMsg.Evades`, the same file); distance 5
    (`LdCode.Dist`), transparent (`LdCode.Transparent`; both Cb/Ld/LdRel.lean) (for tests on groups
    at these positions).
  `Spec.ldToyGrp_sent` states: in the messages that the standard sender
    `G.Y.snd (G.dat val) rest w0` sends, the entry `at' i` is val w i if i is a datum, whatever the
    coins: so a map that reads data entries gives them back.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `toyStd74` with `toyStd74_ok`, Cb/GlVal/GlJ3StdNames.lean, `P74`,
Cb/GlVal/GlToyStdNames.lean, and `LJ3`, Cb/GlVal/GlJ3Base.lean): the fields are F, the integers
modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is that of
Cb/GlVal/GlToyBase4.lean: eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: this file says nothing on a protocol. It says nothing on real parameters: the cube of a
member has as many dimensions as the member has named entries. Pads in the subfield F are not
exercised.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.Ld.LdSendStdMFree
import Cb.Ld.LdSendStdOwn
import Cb.GlVal.GlJ3StdNames
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- Which member holds an entry; which entries are free. -/
structure GrpD (I O : Type) where
  mem : I → O
  fr  : I → Prop

namespace GrpD
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] (G : GrpD I O)

/-- the names that a member holds -/
abbrev X (a : O) : Type := {i : I // G.mem i = a}

instance xDec (a : O) : DecidableEq (G.X a) := Classical.decEq _

/-- each entry has a corner of its own -/
def ind (a : O) : G.X a → G.X a → Bool := fun d m => decide (m = d)

/-- The members. -/
@[reducible] def M (a : O) : StdM E P74 := toyStd74 (G.X a) (G.X a) (G.ind a)

def free (a : O) : (G.M a).Dt → Prop := fun x => G.fr (x : G.X a).1
instance freeDec (a : O) : DecidablePred (G.free a) := fun _ =>
  Classical.propDecidable _

/-- The family; its layout. -/
@[reducible] def N : Sig E := stdMFam G.M
@[reducible] def Y : G.N.StdL E := stdMFamLF G.M G.free

/-- The naming of the entries. -/
def at' (i : I) : G.N.Ent :=
  ⟨G.mem i, (G.M (G.mem i)).place (Sum.inl (⟨i, rfl⟩ : G.X (G.mem i)))⟩

/-- the free entry named i -/
def frAt (i : I) (h : G.fr i) : Σ a, G.Y.Fr a := ⟨G.mem i, ⟨(⟨i, rfl⟩ : G.X (G.mem i)), h⟩⟩

/-- The data map. -/
def dat {W : Type} (val : W → I → E) (w : W) : ∀ a, G.Y.Dt a → E := fun _ x => val w (x.1 : G.X _).1

theorem at_inj : Function.Injective G.at' := by
  intro i i' e
  have h1 : G.mem i = G.mem i' := congrArg Sigma.fst e
  have key : ∀ (a : O) (x : G.X (G.mem i)) (y : G.X a), G.mem i = a →
      HEq ((G.M (G.mem i)).place (Sum.inl x)) ((G.M a).place (Sum.inl y)) → x.1 = y.1 := by
    rintro a x y rfl h
    exact congrArg Subtype.val (Sum.inl_injective ((G.M (G.mem i)).place.injective (eq_of_heq h)))
  exact key _ ⟨i, rfl⟩ ⟨i', rfl⟩ h1 (Sigma.mk.inj e).2

omit [Fintype I] [Fintype O] [DecidableEq O] in
theorem ind_inj (a : O) : Function.Injective (G.ind a) := fun d d' h => by
  have h1 : decide (d = d) = decide (d = d') := congrFun h d
  simpa using h1

end GrpD

namespace Spec
open Iop Prob Hiop Blocks Cb.Ood IOR

def ldToyGrp : Prop :=
  ∀ (I O : Type) [Fintype I] [Fintype O] [DecidableEq O] (G : GrpD I O),
    Function.Injective G.at' ∧
    (∀ i, (G.at' i).1 = G.mem i) ∧
    (∀ i (h : G.fr i), G.at' i = G.Y.entF (G.frAt i h)) ∧
    (∀ i (h : ¬ G.fr i), G.at' i = ⟨G.mem i, G.Y.atD (G.mem i) ⟨(⟨i, rfl⟩ : G.X (G.mem i)), h⟩⟩) ∧
    (∀ i, G.Y.NoPad (G.at' i)) ∧
    G.Y.OK (fun _ => 3) ∧
    (∀ a, (G.N.om a).C.Laws) ∧
    (∀ a, (G.N.om a).ListLE LJ3) ∧
    (∀ a, (G.N.om a).Evades) ∧
    (∀ a, (G.M a).Cm.Dist 5) ∧
    ∀ a, (G.M a).Cm.Transparent

def ldToyGrp_sent : Prop :=
  ∀ (I O : Type) [Fintype I] [Fintype O] [DecidableEq O] (G : GrpD I O) (W W' : Type)
      (val : W → I → E) (rest : W → W') (w0 : W) (w : W)
      (k : (G.Y.snd (G.dat val) rest w0).Mk) (i : I),
    ¬ G.fr i →
    G.N.ents ((G.Y.snd (G.dat val) rest w0).upM ((G.Y.snd (G.dat val) rest w0).put w k)) (G.at' i) =
      val w i

end Spec

open Iop Prob Hiop Blocks Cb.Ood IOR in
theorem ldToyGrp : Spec.ldToyGrp := by
  intro I O _ _ _ G
  have hM : ∀ a, (G.M a).OK LJ3 3 ∧ (G.M a).Cm.Dist 5 ∧ (G.M a).Cm.Transparent := fun a =>
    toyStd74_ok _ _ _ (G.ind_inj a)
  obtain ⟨hY, hD, hF⟩ :=
    stdMFamF_ok E P74 O G.M G.free (fun _ => LJ3) (fun _ => 3) fun a => (hM a).1
  have e1 : ∀ i (h : G.fr i), G.at' i = G.Y.entF (G.frAt i h) := fun i h =>
    congrArg (Sigma.mk (G.mem i)) (hF (G.mem i) ⟨(⟨i, rfl⟩ : G.X (G.mem i)), h⟩).symm
  have e2 : ∀ i (h : ¬ G.fr i),
      G.at' i = ⟨G.mem i, G.Y.atD (G.mem i) ⟨(⟨i, rfl⟩ : G.X (G.mem i)), h⟩⟩ :=
    fun i h => congrArg (Sigma.mk (G.mem i)) (hD (G.mem i) ⟨(⟨i, rfl⟩ : G.X (G.mem i)), h⟩).symm
  refine ⟨G.at_inj, fun _ => rfl, e1, e2, fun i => ?_, hY, fun a => (hM a).1.laws,
    fun a => stdM_list _ (hM a).1, fun a => stdM_evades _ (hM a).1,
    fun a => (hM a).2.1, fun a => (hM a).2.2⟩
  by_cases h : G.fr i
  · rw [e1 i h]
    exact ⟨Sum.inr _, rfl⟩
  · rw [e2 i h]
    exact ⟨Sum.inl _, rfl⟩

open Iop Prob Hiop Blocks Cb.Ood IOR in
theorem ldToyGrp_sent : Spec.ldToyGrp_sent := by
  intro I O _ _ _ G W W' val rest w0 w k i h
  obtain ⟨-, -, -, e2, -, hY, -⟩ := ldToyGrp I O G
  rw [e2 i h]
  exact (stdL_all E E G.N G.Y (fun _ => 3) W W' (G.dat val) rest w0 hY).2.1
    w k (G.mem i) ⟨(⟨i, rfl⟩ : G.X (G.mem i)), h⟩

end Cb.GlJ3
