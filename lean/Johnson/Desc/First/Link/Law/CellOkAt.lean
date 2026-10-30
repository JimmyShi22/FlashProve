-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CellOkAt.lean: WHO PAYS `CellOkR`
(Johnson/Top/H/Keep/DigitsCell.lean: what the dictionary on the digits' cells asks of the part of
the verifier's state): A LEMMA ON ONE STATE s AND ONE PART a THAT IS READ OFF IT: the like, at the
cells, of maskOk_at (Johnson/Desc/First/Look/K3DigitsMaskOk.lean). Theorems: a
joining. A law file; no running text imports it.
  `LaidPub`         a condition ON PUBLIC DATA: at each read cell, the programs' own test on the
                    layout of the array that holds it (laidMatrixOk) accepts at the bits that the
                    shape of the array's oracle message and the codes give.
  `cellOkR_at`      s.link? = some a.L · a.d.st = s.st · a.d.book = s.book · FrameIs · the layout
                    and the list of arrays are the description's · the statement's codes are the
                    description's · seatsAtB 0 (List.ofFn seatT) own s = true · shapesAtB 0 (the
                    list's shapes) s = true (two tests with code of
                    Johnson/Desc/First/Att/K05DoorB.lean) · every read cell has a seat, which lies
                    in its table (public) · LaidPub ⊢ CellOkR x tl D rad seatT own a.
  `cellOkR_atS`     the same at a part that the lens atS reads.
How: seat: seatOk_of_B (Johnson/Desc/First/Att/K05DoorLaws.lean); laid: whereIs_own
· shapesAtB_at · rowBits_of · placeBits_of.

Limits. AN IMPLICATION ON ONE STATE. Who makes the two tests true at the batching's front is not
said: by report they follow, as at the mask row, from the fold's facts seatsCarried and
msgShapes, the promise's bookAt and tests on the list of rounds: NOT TYPED. NOT TRIED FOR EMPTINESS
AT ANY STATE. Nothing on soundness or on hiding.



-/
import Johnson.Top.H.Keep.DigitsCell
import Johnson.Desc.First.Att.K05DoorLaws
import Johnson.Desc.First.Batch.Ahead
import Johnson.Desc.First.Link.Law.RbRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Road.Rows (Addr)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K9 (atS rowBitsOf placeBitsOf rowBits_of placeBits_of)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs SeatOk seatsAtB shapesAtB seatOk_of_B
  shapesAtB_at oracleOfMsg)

section
variable (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (own : List (ℕ × ℕ))

/-- **On public data**: the layout of each array that holds a read cell passes the programs' own
test at the bits of its oracle message's shape. -/
def LaidPub : Prop :=
  ∀ (t r c : ℕ) (z : Seat) (bn : ℕ × String) (a' : ReqArray), cellAddr tl (.cell t r c) →
    seatOf D x.link (.cell t r c) = some z → (D.arrayOf.getD x.link #[])[t]? = some bn →
    reqArray D.layout bn.1 bn.2 = some a' → ∀ hk : z.msg < (digList x D rad).length,
    laidMatrixOk a' (rowBitsOf ((digList x D rad).get ⟨z.msg, hk⟩).1 .main)
      (placeBitsOf D.codes ((digList x D rad).get ⟨z.msg, hk⟩).1 .main) = true

/-- **WHO PAYS CellOkR: ON ONE STATE.** -/
theorem cellOkR_at {s : S} {a : K9.Part} (hL : s.link? = some a.L) (est : a.d.st = s.st)
    (ebk : a.d.book = s.book) (hfr : FrameIs D x.link a.L.check.frame)
    (hlay : a.L.check.rows.layout = D.layout) (harr : a.L.arrayOf = D.arrayOf.getD x.link #[])
    (hcs : s.st.codes = D.codes) (h1 : seatsAtB 0 (List.ofFn seatT) own s = true)
    (h2 : shapesAtB 0 ((digList x D rad).map (·.1)) s = true)
    (hseat : ∀ ad, cellAddr tl ad → (seatOf D x.link ad).isSome = true)
    (hfit : ∀ ad z, cellAddr tl ad → seatOf D x.link ad = some z →
      z.Fits D.codes (digList x D rad))
    (hP : LaidPub x tl D rad) : CellOkR x tl D rad seatT own a := by
  refine ⟨hfr, hlay, harr, fun ad z had hz => ?_, fun t r c bn a' o had hbn ha' hw => ?_⟩
  · rw [est, ebk]
    exact seatOk_of_B D.codes (digList x D rad) seatT 0 own hL h1 h2 z (hfit ad z had hz)
  · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (hseat _ had)
    obtain ⟨bn2, a2, e1, e2, _, _, e5⟩ := whereIs_own hfr hz
    obtain rfl : bn2 = bn := Option.some.inj (e1.symm.trans hbn)
    obtain rfl : a2 = a' := Option.some.inj (e2.symm.trans ha')
    obtain ⟨hk, _⟩ := hfit _ z had hz
    have e3 : ((digList x D rad).map (·.1))[z.msg]? =
        some ((digList x D rad).get ⟨z.msg, hk⟩).1 := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hk]
      rfl
    obtain ⟨o', y, b1, b2, b3⟩ := shapesAtB_at h2 hL e3
    obtain rfl : o' = o := Option.some.inj (b1.symm.trans (e5.symm.trans hw))
    rw [est, rowBits_of s.st o' y .main b2, placeBits_of s.st o' y .main b2, b3, hcs]
    exact hP t r c z bn2 a2 had hz hbn ha' hk

/-- The same at a part that the lens reads. -/
theorem cellOkR_atS {s : S} {a : K9.Part} (ha : atS.get? s = some a)
    (hfr : FrameIs D x.link a.L.check.frame) (hlay : a.L.check.rows.layout = D.layout)
    (harr : a.L.arrayOf = D.arrayOf.getD x.link #[]) (hcs : s.st.codes = D.codes)
    (h1 : seatsAtB 0 (List.ofFn seatT) own s = true)
    (h2 : shapesAtB 0 ((digList x D rad).map (·.1)) s = true)
    (hseat : ∀ ad, cellAddr tl ad → (seatOf D x.link ad).isSome = true)
    (hfit : ∀ ad z, cellAddr tl ad → seatOf D x.link ad = some z →
      z.Fits D.codes (digList x D rad))
    (hP : LaidPub x tl D rad) : CellOkR x tl D rad seatT own a := by
  have hb : a.d.book = s.book := by
    have hq := ha
    unfold atS at hq
    simp only [Option.bind_eq_bind, Option.pure_def] at hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.1 hq
    rw [← Option.some.inj hq]
  exact cellOkR_at x tl D rad seatT own (part_reads s a ha).1 (part_reads s a ha).2 hb hfr hlay harr
    hcs h1 h2 hseat hfit hP

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.cellOkR_atS
#print axioms VerifiableInference.Desc.LinkJoin.cellOkR_at
