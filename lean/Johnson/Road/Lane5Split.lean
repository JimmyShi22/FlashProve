-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5Split.lean

"A link is in order" (Lane5.lean) cut in two: what a lookup does not give, and what it gives; and
the seam before a link's lookup, by name: the first part and "every call's keys lie in its table"
give that the link is in order.

"LinkOK" has three clauses: the link's own cells are below 2^18 in absolute value; every identity
of its segment is 0; every key of its segment is an entry of its table. The third is the lookup's.
A lookup speaks by calls: call c has a vector of 2^(n c) keys and a table of 2^(k c) rows. The
library's segment speaks by its list of keys. What ties the two is named here and not proved.

WHAT THE TWO PARTS WEIGH. In the library's segments every rounded product is checked by a key, and
the product is formed inside the key. So the lookup clause holds every product with a weight matrix
(layers, head) and the scores and accumulators (attention); the first part reads of the weights the
embedding alone. A bridge must therefore show that a call's key vector is that formula at the cells
and at the committed weights: it holds the matrix products, not a renaming of tables. Who gives
"small" is not said here: by the verifier's own words it is what the smallness test is meant to
give, not the lookup.

Main definitions and theorems:
* "LinkR0": the first two clauses: the meaning of a link WITHOUT its lookup clause.
* "LinkKeys": the third clause.
* "linkOK_iff_split": "LinkOK" is the two together.
* "CallsAt": the letters of a lookup's calls over the protocol's field: NC, n, k, the key vectors
  K, the tables T. "CallsAt.InTables": every call's keys lie in its table (the library's
  "Cb.Lkp.InTable").
* "KeysBridge": "InTables" gives "LinkKeys": THE ONE STATEMENT WITH CONTENT. It is an implication
  and no more. Two things would suffice for it, and it says neither: that the calls' key vectors
  hold every key of the segment, and that the calls' tables hold no row that the segment's tables
  lack.
* "SplitInAt": "LinkR0" and "InTables" give "LinkOK". "splitInAt_iff_bridge": under "LinkR0" it
  says what "KeysBridge" says.
* "SplitG g", "SplitA g", "SplitH": "SplitInAt" at link 2 g, link 2 g + 1, link 24, at the family
  of segments with the ledger's head.

Not claimed: "KeysBridge" for any calls. The letters K and T are free here: at a call site K is the
site's key vector over the cells that the matrices hold and over the committed weights, T the
site's tables. All that Lane5.lean does not claim.
-/
import Johnson.Road.Lane5Mean
import Cb.Gen.LkpAlg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-! ## 1. A link in order, cut in two -/

/-- **The meaning of a link without its lookup clause**: its own cells are small, and every identity
of its segment is 0. -/
def LinkR0 (h : Cm.Seg.Hd) (seg : Segs) (Wz : Mat) (x : Instance ppref) (k : ℕ) (A : Mx) : Prop :=
  (∀ n : Cm.Seg.Name, n.Valid h → n.place.1 = k → |Cm.Seg.at' A n.place| < 2 ^ 18) ∧
    ∀ f ∈ (seg k).idn, ∀ b < 2 ^ f.v,
      f.val Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A) b = 0

/-- **The lookup clause of a link**: every key of its segment is an entry of its table. -/
def LinkKeys (seg : Segs) (Wz : Mat) (x : Instance ppref) (k : ℕ) (A : Mx) : Prop :=
  ∀ q ∈ (seg k).keys, ∀ b < 2 ^ q.1.v, ∃ u ∈ q.2.set,
    q.1.val Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM A) b =
      algebraMap Cb.Gl.F Cb.Gl.E u

variable {h : Cm.Seg.Hd} {seg : Segs} {Wz : Mat} {x : Instance ppref} {k : ℕ} {A : Mx}

/-- **A link is in order if and only if both parts hold.** -/
theorem linkOK_iff_split : LinkOK h seg Wz x k A ↔ LinkR0 h seg Wz x k A ∧ LinkKeys seg Wz x k A :=
  ⟨fun H => ⟨⟨H.small, H.idn⟩, H.key⟩, fun H => ⟨H.1.1, H.1.2, H.2⟩⟩

/-! ## 2. The calls of a lookup, and the seam before it -/

/-- The letters of a lookup's calls, over the protocol's field. -/
structure CallsAt where
  /-- the number of calls -/
  NC : ℕ
  /-- call c has 2^(n c) keys -/
  n : ℕ → ℕ
  /-- call c's table has 2^(k c) rows -/
  k : ℕ → ℕ
  /-- the key vectors -/
  K : ℕ → ℕ → Cb.Gl.E
  /-- the tables -/
  T : ℕ → ℕ → Cb.Gl.E

/-- Every call's keys lie in its table. -/
def CallsAt.InTables (C : CallsAt) : Prop :=
  ∀ c < C.NC, Cb.Lkp.InTable (C.n c) (C.k c) (C.K c) (C.T c)

/-- **The bridge from calls to the segment's keys.** -/
def KeysBridge (seg : Segs) (Wz : Mat) (x : Instance ppref) (k : ℕ) (A : Mx) (C : CallsAt) : Prop :=
  C.InTables → LinkKeys seg Wz x k A

/-- **The seam before a link's lookup.** -/
def SplitInAt (h : Cm.Seg.Hd) (seg : Segs) (Wz : Mat) (x : Instance ppref) (k : ℕ) (A : Mx)
    (C : CallsAt) : Prop :=
  LinkR0 h seg Wz x k A → C.InTables → LinkOK h seg Wz x k A

theorem splitInAt_of_bridge {C : CallsAt} (B : KeysBridge seg Wz x k A C) :
    SplitInAt h seg Wz x k A C :=
  fun R I => linkOK_iff_split.2 ⟨R, B I⟩

/-- **Under the first part the seam says what the bridge says.** -/
theorem splitInAt_iff_bridge {C : CallsAt} (R : LinkR0 h seg Wz x k A) :
    SplitInAt h seg Wz x k A C ↔ KeysBridge seg Wz x k A C :=
  ⟨fun S I => (linkOK_iff_split.1 (S R I)).2, splitInAt_of_bridge⟩

/-! ## 3. The seams by name -/

/-- **Before the lookup of group g of layers**: link 2 g. -/
def SplitG (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) (g : ℕ)
    (C : CallsAt) : Prop :=
  SplitInAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x (2 * g) (A (2 * g)) C

/-- **Before the lookup of attention of group g**: link 2 g + 1. -/
def SplitA (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) (g : ℕ)
    (C : CallsAt) : Prop :=
  SplitInAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x (2 * g + 1) (A (2 * g + 1)) C

/-- **Before the lookup of the head with the cost ledger**: link 24. -/
def SplitH (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx)
    (C : CallsAt) : Prop :=
  SplitInAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x 24 (A 24) C

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.linkOK_iff_split
#print axioms OnBytes.Road.L5.splitInAt_iff_bridge
