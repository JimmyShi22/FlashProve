-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfToy.lean: parts of the data (`LdWfF`, Cb/Ld/LdWfFull.lean) of the reduction from the claim
that the encoded index is well-formed, at small numbers over the field with 101 elements.
This is a toy of weights-formedness.

Definitions. Lemmas on them:
Cb/Ld/LdWfToyProofs.lean, Cb/Ld/LdWfToyMasks.lean. No parameter of a
protocol.

The claim. Over the field with 101 elements, at the proper index set
(Cb/Obj/LdObjectToyConf7.lean: `ToyMo.two`; the relation pair: `ToyMd`,
Cb/Obj/LdObjectToyConf7M.lean, see below): the message of an encoded index has two
rows with one entry each; it holds an index if and only if both entries are 5 or 7.

The parts (Cb/Ld/LdWfFull.lean: `LdWfF`):



  one forest; table (5, 7) (`tab`).
  the lookup's numbers: those of Cb/Ld/LdLkpToy.lean: two keys, two table entries, multiplicities
  below 4 in two bit positions; 8 rows.
  the family sent: Cb/Ld/LdSendToyFam7.lean's: a named member that holds the 4 bits of the
  multiplicities, a mask-only member with 39 entries: the lookup's 35 own masks, the 3 coefficients
  of the batching's hiding polynomial, one idle entry; each with a pad; independent seeds.


  the batching: one claim, so one coefficient (powers, one of them); degree 2.



Notation: `K`: the field with 101 elements (`ZMod 101`, Cb/Ld/LdRelToy.lean).

Limits: the lookup's item "masked messages" is not in this file.

The toy's relation pair is a parameter. Here a model is a value of the class `ToyModel` (below):
a relation pair `Md` with `Md.OK` and countably many instances (`ctb`: instances of the relations,
`Md.Xm`, not Lean's instances). The line `variable [ToyModel]` makes the model an instance argument
of every definition of this file that needs it. The later files of this family
(Cb/Ld/LdWfToyProofs.lean, LdWfToyMasks.lean, LdWfToyItem.lean) each have their
own line `variable [WfToy.ToyModel]`: so every theorem in such a line's reach takes the model in
the same way,
but those under `omit [WfToy.ToyModel] in`, which do not
need it. Lean fills it in, so it is not written out where these names are used. Three things follow:
(1) A statement is one proposition for each model: its text has no "for all" over models.
(2) Its theorem takes the same argument, so it proves the statement for every model: for every
    relation pair Md with `Md.OK` and countably many instances.
(3) Where one of these names is used and no model is in scope (no `[ToyModel]` binder, no `variable`
    line), Lean finds `ToyModel.triv`, the trivial one (an `instance` of low priority: any other
    that is declared as an `instance`, at the usual priority, goes first), and then the
    relation pair is `ToyMd.triv` by definition. So a statement's bare name, read as one
    closed proposition, is its case at the trivial pair alone.
Apart from this: weights-formedness and the test behind it do not read the relation pair, but for
the conditions `sub`, `admits` in `LdCf.OK` (Cb/Obj/LdObjectConf.lean), which `ToyModel.ok` meets,
and `inst` in `PWf.CtbW` (Cb/Obj/LdObjectCtbSplit.lean: countably many instances), which
`ToyModel.ctb` meets.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfFull
import Cb.Ld.LdWfMasksStd
import Cb.Ld.LdLkpToy
import Cb.Ld.LdSendToyFam7
import Cb.Ld.LdSendToyFamLay
import Cb.Obj.LdObjectToyConf7
import Cb.Obj.LdObjectToyConf7M

set_option autoImplicit false

namespace Cb
namespace WfToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy LdToy7 Cb.LdLkp Cb.Lkp

noncomputable section

/-- The relation pair of the toy: a parameter, as an instance argument, so that the texts below need
not name it. Weights-formedness does not read it (but for the conditions named in the head, under
"Limits:"). -/
class ToyModel where
  Md : ToyMd ToyMo.two.I
  ok : Md.OK
  ctb : Countable Md.Xm

/-- the trivial relation pair: found where no other is declared; with it `Md` is `ToyMd.triv`,
by definition -/
instance (priority := low) ToyModel.triv : ToyModel :=
  ⟨ToyMd.triv _, ⟨fun _ _ _ h => h, fun _ _ _ h => h⟩, inferInstanceAs (Countable Unit)⟩

variable [ToyModel]

/-- the names of the coefficients of the batching's hiding polynomial -/
abbrev WBt : Type := PIdx (List.replicate 1 (pfCube K 2))
/-- The bits of the multiplicities: (table entry, bit position); the mask entries: the lookup's, the
batching's, an idle one. -/
abbrev Ix : Type := Bool × Bool
abbrev Im : Type := LkpToy.Mk ⊕ (WBt ⊕ Unit)

instance decIm : DecidableEq Im := Classical.decEq _

/-- The family sent. -/
abbrev F : StdFam K := fam7 Ix Im Ix Im (fun i j => decide (j = i)) (fun i j => decide (j = i))

/-- the named entries -/
abbrev Nm : Type := Ix ⊕ Im
def mkAt (i : LkpToy.Mk) : Nm := .inr (.inl i)
def btAt (i : WBt) : Nm := .inr (.inr (.inl i))
def idle : Nm := .inr (.inr (.inr ()))

def tab (u : ℕ) : K := if u = 0 then 5 else 7
/-- bits as the lookup reads them -/
def bitOf (bd : Ix → K) : ℕ → ℕ → K := fun u j => bd (decide (u = 1), decide (j = 1))
end
end WfToy
end Cb
