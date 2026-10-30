-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CellPub.lean: THE PUBLIC CONDITION `LaidPub`
(CellOkAt.lean beside this file) AS A TEST WITH CODE: TWO ARRAYS A LINK, NOT EVERY READ CELL. A
definition with code and a theorem. A law file; no running text imports it.
  `laidArrB D l i t`   the array number t of link i's list is the link's own; the layout has it; its
                    oracle message's number lies in the list l; and the programs' own test on its
                    layout (laidMatrixOk) accepts at the bits that this message's shape and the
                    codes give.
  `laidPub_of_B`    a yes at the counts' array (ix.BZ) and at the digits' array (ix.ZZ) ⊢ LaidPub.

Limits. Evaluated at no plan here. Nothing on soundness or on
hiding.
-/
import Johnson.Desc.First.Link.Law.CellOkAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)
open VerifiableInference.Desc.First.Look

/-- The test on one array of a link's list. -/
def laidArrB (D : Sent) (l : List (OracleShape × ℕ)) (i t : ℕ) : Bool :=
  ((D.arrayOf.getD i #[])[t]?).any fun bn =>
    (reqArray D.layout bn.1 bn.2).any fun a' =>
      (l[a'.message]?).any fun sh =>
        laidMatrixOk a' (rowBitsOf sh.1 .main) (placeBitsOf D.codes sh.1 .main)

/-- The seat of a cell names its array's oracle message. -/
theorem seat_msg {D : Sent} {i t r c : ℕ} {z : Seat} (hz : seatOf D i (.cell t r c) = some z) :
    ∃ bn a, (D.arrayOf.getD i #[])[t]? = some bn ∧ reqArray D.layout bn.1 bn.2 = some a ∧
      z.msg = a.message := by
  unfold seatOf at hz
  obtain ⟨bn, hbn, hz⟩ := Option.bind_eq_some_iff.1 hz
  by_cases hb : (bn.1 == i) = true
  · rw [if_pos hb] at hz
    obtain ⟨a, ha, hz⟩ := Option.bind_eq_some_iff.1 hz
    obtain ⟨rp, _, rfl⟩ := Option.map_eq_some_iff.1 hz
    have hbi : bn.1 = i := by simpa using hb
    exact ⟨bn, a, hbn, by rw [hbi]; exact ha, rfl⟩
  · rw [if_neg hb] at hz
    exact nomatch hz

/-- **The public condition from two yeses.** -/
theorem laidPub_of_B (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
    (hB : laidArrB D (digList x D rad) x.link tl.ix.BZ = true)
    (hZ : laidArrB D (digList x D rad) x.link tl.ix.ZZ = true) : LaidPub x tl D rad := by
  intro t r c z bn a' had hz hbn ha' hk
  have ht : laidArrB D (digList x D rad) x.link t = true := by
    rcases had with ⟨_, _, _, _, e⟩ | ⟨_, _, _, _, _, _, _, _, e⟩
    · obtain rfl : t = tl.ix.BZ := (Addr.cell.inj e).1
      exact hB
    · obtain rfl : t = tl.ix.ZZ := (Addr.cell.inj e).1
      exact hZ
  obtain ⟨bn2, a2, e1, e2, e3⟩ := seat_msg hz
  obtain rfl : bn2 = bn := Option.some.inj (e1.symm.trans hbn)
  obtain rfl : a2 = a' := Option.some.inj (e2.symm.trans ha')
  unfold laidArrB at ht
  rw [hbn] at ht
  simp only [Option.any_some] at ht
  rw [ha'] at ht
  simp only [Option.any_some] at ht
  rw [← e3, List.getElem?_eq_getElem hk] at ht
  exact ht

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.laidPub_of_B
