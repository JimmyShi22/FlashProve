-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfSupp.lean: the rows of the assembled lookup's read-out are 0 outside any set of places
that holds all places that the lookup's data name except the two inner masks of the last level of
the keys' tree: in this form, no row that the assembled lookup files reads the two inner masks of
the last level of the keys' tree.

A record and statements; the proofs are in Cb/Ld/LdBldWfSuppProofs.lean. Generic: any assembled
lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean). Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs. A row (`Row`, Cb/Ld/LdLkpTree.lean: coefficients `cf`, a
target `tg`) is 0 outside G if its coefficients vanish there (`RowsSupp`, Cb/Ld/LdLkpSupp.lean).

Why: Cb/Ld/LdLkpAsm2Pull.lean states (proved in Cb/Ld/LdLkpAsm2PullProofs.lean) that all rows of the
read-out are 0 outside all places that the lookup's data name (`A.PlacesIn G`: the coarse
condition). The plan of the offline linear test is asked to send every message with a place in a
row's support to its fourth whole test, and every message with a place in the support of a claim's
mask form into the instance's group (Cb/Obj/LdObjectPpRows.lean: the clauses plR, plC of
`LdObjRp.HypPl`). With the coarse supports the message that holds these two masks has to stand in
both groups. By reading, this protocol's technical report (lean/CREDITS.md) has it in one. So the
preamble of weights-formedness asks `A.PlacesInR G` of the public support of every row (`P.gR`,
Cb/Ld/LdWf.lean;
Cb/Ld/LdWfBlocks.lean: `K.OK`, clause supR).
The reason: the row of level l of a product tree reads the hiding coefficients of its own level and
what the incoming form reads: the two inner masks of level l - 1 (at level 0 of the keys' tree: one
inner mask of the tie). The inner masks of level l are read by the form that level l hands on. The
keys' tree has the levels 0 .. v'; what level v' hands on is the lookup's last claim on the keys:
where these two are places of nothing else, only the mask form of that claim reads the two inner
masks of the last level.

Main names:
  `A.PlacesInR G`: `A.PlacesIn G` with one clause weaker: the inner masks of the keys' tree are
    asked to lie in G at the levels below the last only (cK l b for l < v').
  `Spec.ldBldWf_placesR`: `A.PlacesIn G` ⇒ `A.PlacesInR G` (`LkAsm2.PlacesIn.toR` proves it here, in
    one line).
  `Spec.ldBldWf_suppRows`: the rows of the read-out, under `A.PlacesInR G`. `Spec.ldBldWf_suppPull`:
    the same in the form of the rows' half of the preamble's clause `lkpS` (Cb/Ld/LdWf.lean).

Limits: this file changes no record. It changes nothing on the other families of places: they are
asked at all levels that the data name, played or not, as in `A.PlacesIn`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2Pull

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

/-- G holds of all places that the rows can read. -/
structure LkAsm2.PlacesInR {E : Type} [Field E] [Fintype E] (A : LkAsm2 E) (G : A.J → Prop) :
    Prop where
  bAt : ∀ u j, G (A.bAt u j)
  wS  : ∀ i, G (A.wS i)
  cS  : ∀ b, G (A.cS b)
  wAt : ∀ l i, G (A.wAt l i)
  cAt : ∀ l b, G (A.cAt l b)
  wK  : ∀ l i, G (A.wK l i)
  /-- below the last level only -/
  cK  : ∀ l, l < A.v' → ∀ b, G (A.cK l b)
  wT  : ∀ l i, G (A.wT l i)
  cT  : ∀ l b, G (A.cT l b)
  wE  : ∀ i, G (A.wE i)
  wB  : ∀ i, G (A.wB i)
  cB  : G A.cB

/-- the coarse condition gives this one -/
theorem LkAsm2.PlacesIn.toR {E : Type} [Field E] [Fintype E] {A : LkAsm2 E}
    {G : A.J → Prop} (h : A.PlacesIn G) : A.PlacesInR G :=
  ⟨h.bAt, h.wS, h.cS, h.wAt, h.cAt, h.wK, fun l _ b => h.cK l b, h.wT, h.cT, h.wE, h.wB, h.cB⟩

end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldBldWf_placesR : Prop := ∀ (A : LkAsm2 E) (G : A.J → Prop), A.PlacesIn G → A.PlacesInR G

/-- States: if `A.PlacesInR G`, at every last explicit part all rows of the read-out (`A.rd`,
Cb/Ld/LdLkpAsm2.lean) are 0 outside G. -/
def ldBldWf_suppRows : Prop :=
  ∀ (A : LkAsm2 E) (G : A.J → Prop), A.PlacesInR G → ∀ o, RowsSupp G (A.rd o).2.2

/-- States the same in the form of the rows' half of the preamble's clause `lkpS` (Cb/Ld/LdWf.lean):
under `A.PlacesInR G`, a row pulled back along ι has the coefficient 0 at every name n with ι n
outside G. -/
def ldBldWf_suppPull : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (G : A.J → Prop), A.PlacesInR G →
    ∀ (o : A.XB) (i : ℕ) (n : N),
      ¬ G (ι n) → (((A.rd o).2.2.map (Row.pull ι)).getD i ⟨fun _ => 0, 0⟩).cf n = 0

end
end Cb.Spec
