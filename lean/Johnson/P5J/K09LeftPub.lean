-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftPub.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THE THREE PUBLIC
SENTENCES OF THE NAMED REST OF THE FIELD hLeft (`LeftRest`,
Johnson/Desc/First/Link/Law/LeftOfRest.lean): dig, first AND maskPub: FROM THE HEAD ALONE, at the
letters of what is left of K9: the place xx and the structure tlD that First.Look.digAt (At.X Zp) m
returns. Theorems: a joining, by calls. A law file; no running text imports it.
  `look_of_dig`       digAt X m = some (xx, tlD) ⊢ lookAt X m true = some xx.
  `AtMgA.left_dig`    ∃ set pp, DigOK set xx tlD h.𝔇.sent h.𝔇.l3.rad pp. By
                    AtMgA.k9_dig (Johnson/P5T/DigAtHead.lean).
  `AtMgA.left_first`  ∀ q < 2, ∀ pc ∈ piecesL tlD q, pc.c0 = q * tlD.mz. By row11_at
                    and pieces_of_row (Johnson/Desc/First/Link/Law/K9Row11.lean): the digits' row,
                    which the verifier asks where the value is laid, holds PieceOK at every piece.
  `AtMgA.left_maskPub`   maskB h.𝔇.sent (digList xx h.𝔇.sent h.𝔇.l3.rad) xx.link xx.arrays.ns =
                    true. NOT by the digits' row (it tests the mask row at a lower bound): by
                    k03_masksUpTo (Johnson/P5J/K03MaskBAt.lean: off the planner's
                    own return) and digits_maskB_of_upTo.


Limits. At OnBytes.secondHashFunction. Nothing on soundness or on hiding.

-/
import Johnson.P5T.DigAtHead
import Johnson.Desc.First.Link.Law.K9Row11
import Johnson.P5J.K03MaskBAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- **dig.** -/
theorem AtMgA.left_dig (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} {tlD : HTailF2}
    (hd : Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD)) :
    ∃ set pp, Desc.First.Look.DigOK set xx tlD h.𝔇.sent h.𝔇.l3.rad pp := by
  obtain ⟨y, tl, hy, H⟩ := h.k9_dig m hm h.𝔇.l3.rad
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hd.symm.trans hy))
  exact ⟨_, _, H⟩

/-- **first.** -/
theorem AtMgA.left_first (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} {tlD : HTailF2}
    (hd : Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD)) :
    ∀ q < 2, ∀ pc ∈ OnBytes.DgP.piecesL tlD q, pc.c0 = q * tlD.mz := by
  have hr : Desc.K3Asks.digRow Zp.p.X (Desc.K3Asks.sentOf Zp) = true :=
    (LPFD.asks_rest h.toAtMg.laid.asks h.toAtMg.laid.pub).1
  have hl : m < Desc.K3Asks.linksOf Zp.p.X := by
    rw [linksOf_pub h.toAtMg.scope h.toAtMg.laid.pub]
    exact hm
  obtain ⟨y, tl, hy, ht, hp, -⟩ := Desc.K9Asks.row11_at hr hl
  have hy' : Desc.First.Look.digAt (At.X Zp) m = some (y, tl) := hy
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hd.symm.trans hy'))
  exact fun q hq pc hpc => (Desc.K9Asks.pieces_of_row ht hp q hq pc hpc).c0

/-- The place is the lookup's. -/
theorem look_of_dig {X : Verify.Public} {m : ℕ} {xx : Desc.First.Look.Place} {tlD : HTailF2}
    (hd : Desc.First.Look.digAt X m = some (xx, tlD)) :
    Desc.First.Look.lookAt X m true = some xx := by
  unfold Desc.First.Look.digAt at hd
  obtain ⟨y, hy, h2⟩ := Option.bind_eq_some_iff.1 hd
  obtain ⟨tl, -, h3⟩ := Option.bind_eq_some_iff.1 h2
  obtain ⟨sh, -, h4⟩ := Option.map_eq_some_iff.1 h3
  rw [hy, (Prod.mk.inj h4).1]

/-- **maskPub.** -/
theorem AtMgA.left_maskPub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25)
    {xx : Desc.First.Look.Place} {tlD : HTailF2}
    (hd : Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD)) :
    Desc.First.Look.maskB h.𝔇.sent (Desc.First.Look.digList xx h.𝔇.sent h.𝔇.l3.rad) xx.link
      xx.arrays.ns = true :=
  Desc.First.Look.digits_maskB_of_upTo (k03_masksUpTo h hm (look_of_dig hd)) (Nat.le_refl _)
    h.𝔇.l3.rad

end P5J

#print axioms P5J.look_of_dig
#print axioms P5J.AtMgA.left_maskPub
#print axioms P5J.AtMgA.left_dig
#print axioms P5J.AtMgA.left_first
