-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5SplitA.lean

The seam before the lookup of an attention sub-proof, in the verifier's own list of matrices: the
cells are small, the identities vanish, and every call's keys lie in its table; so link 2 g + 1 is
in order.

"AttOrd S Z" (Lane5AttDef.lean) is the library's relation of an attention segment
(Inst.Model.AttSeg.RFraw) at the integer matrices Z of the verifier's list. The relation has three
clauses: every cell is below 2^18; every looked-up value in a piece of the four calls is an entry of
its table; the three kinds of identities are 0. The second is the lookup's. "linkA_of_ordL"
(Lane5AttLinkL.lean) proves "LinkOK" at link 2 g + 1 from the three.

WHAT THE TWO PARTS WEIGH. In the library's segments every rounded product is checked by a key, and
the product is formed inside the key. At attention the scores (query times key) and the accumulators
(softmax weight times value; denominator times output) stand in "AttKeys". "AttR0" is: the cells are
small; the index's bits are bits; the row maximum is the score at the index; the denominator is the
sum of the row's weights. A bridge must therefore show that a call's key vector is that formula at
the cells: it holds the products, not a renaming of tables. Who gives "small" is not said here: by
the verifier's own words it is what the smallness test is meant to give, not the lookup.

Main definitions and theorems:
* "AttR0": the first and the third clause: the link's meaning WITHOUT its lookup clause.
* "AttKeys": the second clause.
* "attOrd_iff_split": "AttOrd" is the two together.
* "AttBridge": for the letters of a lookup's calls ("CallsAt", Lane5Split.lean): "every call's keys
  lie in its table" gives "AttKeys". NAMED, NOT PROVED HERE. It is an implication and no more.
* "linkOK_of_attSplit": under the public hypotheses of linkA_of_ordL: "AttR0", "InTables" and
  "AttBridge" give "LinkOK" at link 2 g + 1, at the family of segments with the ledger's head and
  the library's matrices "attMx S g Z".
* "splitA_of_att": so, UNDER "AttR0" AS A HYPOTHESIS OF THE THEOREM, "SplitA" (Lane5Split.lean)
  holds there. Its own premise "LinkR0" is not used: nobody shows that "LinkR0" at "attMx S g Z"
  gives "AttR0 S Z". It is "linkOK_of_attSplit" in SplitA's letters.

Not claimed: "AttBridge" for any calls. The tables in "AttKeys" are the library's, at the letters
made from the shape. The matrices hold integers: how a field element is lifted is said nowhere here.
The end is at the reference sizes. All that Lane5AttLink.lean and Lane5Split.lean do not claim.
-/
import Johnson.Road.Lane5AttLinkL
import Johnson.Road.Lane5Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref Instance Mat AcceptancePolicy tbRef)
open Inst.Model.AttSeg (Raw Idn keyVec lut lutSet idnVal castT)

/-- **The meaning of an attention link without its lookup clause.** -/
def AttR0 (S : Attention.Shape) (Z : Zs) : Prop :=
  (∀ c : Raw, c.Valid (dimOf S) → |cellsA S Z c| < 2 ^ 18) ∧
    ∀ j : Idn, j.Valid (dimOf S) →
      idnVal (dimOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) j = 0

/-- **The lookup clause of an attention link.** -/
def AttKeys (S : Attention.Shape) (Z : Zs) : Prop :=
  ∀ (c : Fin 4) (X : ℕ), X < (dimOf S).used c →
    keyVec (scl := sclOf S) (dimOf S) (tbOf S) (castT (cellsA S Z) : Raw → Cb.Gl.F) c X ∈
      lutSet (lut (scl := sclOf S) (dimOf S) (tbOf S) c)

/-- **An attention link is in order if and only if both parts hold.** -/
theorem attOrd_iff_split {S : Attention.Shape} {Z : Zs} :
    AttOrd S Z ↔ AttR0 S Z ∧ AttKeys S Z :=
  ⟨fun H => ⟨⟨H.rel.1, H.rel.2.2⟩, H.rel.2.1⟩, fun H => ⟨H.1.1, H.2, H.1.2⟩⟩

/-- **The bridge from a lookup's calls to the link's key vectors.** -/
def AttBridge (S : Attention.Shape) (Z : Zs) (C : CallsAt) : Prop := C.InTables → AttKeys S Z

/-- **The seam before the lookup of attention of group g.** -/
theorem linkOK_of_attSplit {S : Attention.Shape} {g : ℕ} (hg : g < 12) (hS : AttSized S)
    {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) {Z : Zs} (pol : AcceptancePolicy)
    (Wz : Mat) (x : Instance ppref) {C : CallsAt} (B : AttBridge S Z C) (R : AttR0 S Z)
    (I : C.InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x (2 * g + 1) (attMx S g Z) :=
  linkA_of_ordL hg hS hsh hE (attOrd_iff_split.2 ⟨R, B I⟩) pol Wz x

/-- **So, under AttR0, the seam of Lane5Split.lean holds at the library's matrices of the link.**
SplitA's own premise LinkR0 is not used. -/
theorem splitA_of_att {S : Attention.Shape} {g : ℕ} (hg : g < 12) (hS : AttSized S)
    {s : Cm.Scales} (hsh : (s.kap (4 * g)).sh = S.cf.sh.getD 0 0)
    (hE : ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) {Z : Zs} (pol : AcceptancePolicy)
    (Wz : Mat) (x : Instance ppref) {C : CallsAt} (B : AttBridge S Z C) (R : AttR0 S Z)
    (A : ℕ → Mx) (hA : A (2 * g + 1) = attMx S g Z) :
    SplitA s pol Wz x A g C := by
  intro _ I
  rw [hA]
  exact linkOK_of_attSplit hg hS hsh hE pol Wz x B R I

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attOrd_iff_split
#print axioms OnBytes.Road.L5.linkOK_of_attSplit
#print axioms OnBytes.Road.L5.splitA_of_att
