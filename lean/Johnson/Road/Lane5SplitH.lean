-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5SplitH.lean

The seam before the lookup of the head with the cost ledger, in the layouts' numbering: the head's
cells are small, its identities and the ledger's clauses vanish, and every call's keys lie in its
table; so link 24 is in order.

"Hd.HeadOrdLB" (HeadL5BL.lean) has three clauses on the integer matrices behind the head's
sub-proof: small; the library's "Policy.HeadCl"; "y = 0 if e < T". "Policy.HeadCl" is four clauses:
every key of the nine families is an entry of its table; the 17 identities are 0; two clauses of
the ledger at every position are 0; two sums of the ledger are 0. The first is the lookup's.
"Hd.linkOKL_24B" proves "LinkOK" at link 24 from "Hd.HeadOrdLB".

WHAT THE TWO PARTS WEIGH. In the library's segments every rounded product is checked by a key, and
the product is formed inside the key. So the lookup clause holds every product with a weight matrix
(layers, head) and the scores and accumulators (attention); the first part reads of the weights the
embedding alone. A bridge must therefore show that a call's key vector is that formula at the cells
and at the committed weights: it holds the matrix products, not a renaming of tables. Here:
"HeadR0" does not take the weights at all; the logits' margin, and with it the product with the
output matrix, stands in the key of the family HD0, in "HeadKeys". Who gives "small" is not said
here: by the verifier's own words it is what the smallness test is meant to give, not the lookup.

Main definitions and theorems:
* "HeadR0": all of "Hd.HeadOrdLB" but the clause on keys: the head's meaning WITHOUT its lookup
  clause.
* "HeadKeys": the clause on keys.
* "headOrdLB_iff_split": "Hd.HeadOrdLB" is the two together.
* "HeadBridge": for the letters of a lookup's calls ("CallsAt", Lane5Split.lean): "every call's
  keys lie in its table" gives "HeadKeys". NAMED, NOT PROVED HERE. It is an implication and no
  more.
* "linkOK_of_headSplit": under six public hypotheses on shapes and layouts: "HeadR0", "InTables"
  and "HeadBridge" give "LinkOK" at link 24, at the family of segments with the ledger's head and
  the library's matrices "Hd.headMx h y Mh".
* "splitH_of_head": so, under "HeadR0", "SplitH" (Lane5Split.lean) holds there. Its own premise
  "LinkR0" is not used: nobody shows that "LinkR0" at the library's matrices gives "HeadR0" in the
  layouts' numbering.

Not claimed: "HeadBridge" for any calls. "HeadR0" holds the ledger's four clauses and "y = 0 if e <
T": which of them a protocol shows before its lookup, and which only at the lookup's point, is not
said here. At the family HD0 the key is the library's undivided one, in the table of multiples of
2^23 ("Policy.LedgerHead"); a verifier that divides by 2^23 and looks up in the range table of
width 16 needs a step more. The library's tables stand in "HeadKeys", not a verifier's. The
matrices hold integers: how a field element is lifted is said nowhere here. All is at the reference
sizes. All that HeadL5BL.lean and Lane5Split.lean do not claim.
-/
import Johnson.Road.HeadL5BL
import Johnson.Road.Lane5Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (ppref NormPar Instance Mat AcceptancePolicy)
open Inst.Model.All (DF)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)

/-- **The lookup clause of the head**: every key of the nine families is an entry of its table. -/
def HeadKeys (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (pol : AcceptancePolicy) (Wz : Mat)
    (x : Instance ppref) (Mh : Mats ℤ) : Prop :=
  ∀ f a i, a < Inst.Model.Head.len f → i < Inst.Model.Head.nT →
    Inst.Model.Head.InLut (Policy.LedgerHead.tableOf f)
      (Policy.LedgerHead.key np ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
        (Cm.TP.castH Cb.Gl.p Wz) (Inst.Model.Head.Req.of pol x) f a i)

/-- **The meaning of the head without its lookup clause.** -/
def HeadR0 (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (pol : AcceptancePolicy)
    (x : Instance ppref) (Mh : Mats ℤ) : Prop :=
  Hd.SmallH h L (borderOf y) Mh ∧
  ((∀ i < Inst.Model.Head.nT, ∀ k < 17,
      Inst.Model.Head.N.idn np ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F) i k = 0) ∧
    (∀ i < Inst.Model.Head.nT,
      Inst.Model.Head.dB4 ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of pol x) i = 0 ∧
        Inst.Model.Head.dZ ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
          (Inst.Model.Head.Req.of pol x) i = 0) ∧
    (Inst.Model.Head.sB2 ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of pol x) = 0 ∧
      Inst.Model.Head.sB3 ((Hd.cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
        (Inst.Model.Head.Req.of pol x) = 0)) ∧
  (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0)

/-- **The head is in order if and only if both parts hold.** -/
theorem headOrdLB_iff_split {h : Model.Head.Shape} {L : HL} {y : Lay} {np : NormPar} {pol : AcceptancePolicy}
    {Wz : Mat} {x : Instance ppref} {Mh : Mats ℤ} :
    Hd.HeadOrdLB h L y np pol Wz x Mh ↔
      HeadR0 h L y np pol x Mh ∧ HeadKeys h L y np pol Wz x Mh :=
  ⟨fun O => ⟨⟨O.1, O.2.1.2, O.2.2⟩, O.2.1.1⟩, fun H => ⟨H.1.1, ⟨H.2, H.1.2.1⟩, H.1.2.2⟩⟩

/-- **The bridge from a lookup's calls to the head's keys.** -/
def HeadBridge (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (pol : AcceptancePolicy) (Wz : Mat)
    (x : Instance ppref) (Mh : Mats ℤ) (C : CallsAt) : Prop :=
  C.InTables → HeadKeys h L y np pol Wz x Mh

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- **The seam before the lookup of the head with the cost ledger.** -/
theorem linkOK_of_headSplit (hF : Hd.FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF)
    (Z2 : Sized2 hy DF) {s : Cm.Scales} {pol : AcceptancePolicy} {x : Instance ppref} {Wz : Mat}
    {Mh : Mats ℤ} {C : CallsAt} (B : HeadBridge h L y s.nf pol Wz x Mh C)
    (R : HeadR0 h L y s.nf pol x Mh) (I : C.InTables) :
    LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x 24 (Hd.headMx h y Mh) :=
  Hd.linkOKL_24B hF hL hl S Z Z2 (headOrdLB_iff_split.2 ⟨R, B I⟩)

/-- **So, under "HeadR0", the seam of Lane5Split.lean holds at the library's matrices of the
head.** -/
theorem splitH_of_head (hF : Hd.FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF)
    (Z2 : Sized2 hy DF) {s : Cm.Scales} {pol : AcceptancePolicy} {x : Instance ppref} {Wz : Mat}
    {Mh : Mats ℤ} {C : CallsAt} (B : HeadBridge h L y s.nf pol Wz x Mh C)
    (R : HeadR0 h L y s.nf pol x Mh) (A : ℕ → Mx) (hA : A 24 = Hd.headMx h y Mh) :
    SplitH s pol Wz x A C := by
  intro _ I
  rw [hA]
  exact linkOK_of_headSplit hF hL hl S Z Z2 B R I

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.headOrdLB_iff_split
#print axioms OnBytes.Road.L5.linkOK_of_headSplit
#print axioms OnBytes.Road.L5.splitH_of_head
