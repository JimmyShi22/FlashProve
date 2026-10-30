-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/TiesOfRest.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: THE THREE TIES
OF THE BUNDLE `FourFactsAt` (FourFactsAt.lean): THE DATA's CELLS OF THE TWO ARRAYS BZ AND ZZ, AND
ITS MASK ROW AT THE FOUR CLAIMS' SLOTS, ARE WHAT THE LOOKUP's CALLER READS OFF THE WITNESS's OWN
MESSAGES: AT μ₀ := digMu, en := enOf, mk := mkOf: FROM WHAT THE LIBRARY's `rest_pays_of` ASKS.
IMPLICATIONS ON PLAIN DATA AND ONE PART OF A STATE; none of the library's goals. It stands over the
library alone.

  `digMsg_of_digVal` DigOK · the lookup reads the address ad (ReadsDig) · digVal x D rad m ad = some
                   v ⊢ digMsg x D rad m (findJ x.arrays ad) = v
  **`ties_of_rest`** DigOK set x tlD D rad pp · two `OneReader` (the witness's messages are what rd
                   reads: at the members that hold the read cells; at the mask row's) · `CellOkR`
                   and `MaskOkR` at the part a · maskB … = true · q.2 = some (pubOf a) · SameDig tlD
                   t · every slot that a form of four8 t g names lies below a.F.ns ⊢ the three ties
                   at t, at y := dataQ own a rd
By: OnPublicFiles.rest_pays_of (Johnson/Top/H/Keep/DigitsRestPays.lean), which ends in "digVal … = some
(unknownOf …)" at tlD, called at L := a.L and c := four8 t g · dig_c0 (DigitsHeardFacts.lean) · the
bridge: Look.msgAt_of (Johnson/Desc/First/Look/K3CallerBase.lean) where the address has an entry:
DigOK's field resolves at reads_bz and reads_zz (K3DigRows.lean) · `entUnit` and `unknownOf` are one
at q.2 = some (pubOf a): by unfolding · from tlD to t: SameDig's ix, bz, pieces.
KIN IN THE LIBRARY, NOT CALLED: `LeftAsks` (Johnson/Desc/First/Link/Law/LeftThree.lean) is what
rest_pays_of asks, as one structure of nine fields, "SHOWN OF NO STATE" by its own head; left_three
ends where rest_pays_of ends. leftAsks_ones (OneReaderClamp.lean) has both `OneReader` at the reader
rdC, from a premise on the table's list of members. cells_have_seats (Johnson/P5J/K09LeftCells.lean)
walks from DigOK to ReadsDig as here.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. NO TACTIC THAT SEARCHES.
Limits. AN IMPLICATION: `OneReader`, `CellOkR`, `MaskOkR` AND maskB ARE PREMISES, SHOWN HERE OF NO
STATE AND NO WITNESS. So is the clause on the slots. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Top.H.Keep.DigitsRestPays
import Johnson.Top.H.Keep.DigitsHeardFacts
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.Look.K3DigRows
import Johnson.Desc.First.Link.Law.EntryUnit
import Johnson.Desc.First.Batch.Law.K8Four

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Params OnBytes.DgP
open OnBytes.Road.Rows (Addr)
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.OnPublicFiles (SameDig CellOkR MaskOkR cellAddr maskAddr digMu)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ msgsOf)
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9L (Pub9 pubOf four8)
open VerifiableInference.Desc.EntryUnit (entUnit)

section
variable {Cells Tok α : Type} {set : Params.Setting} {pp : ℕ} {x : First.Look.Place}
  {tlD : HTailF2} {D : Sent} {rad : OracleShape → ℕ}

/-- Where the lookup reads, what the messages hold at an address is what the caller's reading has at
the address's entry. -/
theorem digMsg_of_digVal (HD : DigOK set x tlD D rad pp) (m : (digSg x D rad).Msg) {ad : Addr}
    {v : Cb.Gl.E} (hR : ReadsDig tlD x.F.next ad) (hv : digVal x D rad m ad = some v) :
    digMsg x D rad m (findJ x.arrays ad) = v := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 (HD.resolves ad hR).1
  have e := msgAt_of D.codes (digList x D rad) (seatOf D x.link) x.arrays hj m
  have hv' : valAt D.codes (digList x D rad) (seatOf D x.link) m ad = some v := hv
  rw [hv'] at e
  exact e

/-- **THE THREE TIES OF THE LETTERS TO THE DATA's CELLS AND MASK ROW**, at the reading of the
witness's own messages, at any data of the test with tlD's six fields. -/
theorem ties_of_rest (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (own : List (ℕ × ℕ)) (HD : DigOK set x tlD D rad pp) (rd : ℕ × ℕ → MsgQ)
    (w : Wit Cells Tok MsgT)
    (hc : OneReader (ReadMsgOf (cellAddr tlD) (seatOf D x.link)) D.codes (digList x D rad) seatT
      (msgsOf D.codes (digList x D rad) seatT arr w) rd)
    (hm : OneReader (ReadMsgOf (maskAddr x.arrays.ns) (seatOf D x.link)) D.codes
      (digList x D rad) seatT (msgsOf D.codes (digList x D rad) seatT arr w) rd)
    (a : Desc.K9.Part) (C : CellOkR x tlD D rad seatT own a) (M : MaskOkR x D rad seatT own a)
    (hB : maskB D (digList x D rad) x.link x.arrays.ns = true)
    (q : α × Option Pub9) (hq : q.2 = some (pubOf a)) {t : HTailF2} (Sd : SameDig tlD t)
    (g : Forest.Heard)
    (hns : ∀ k ∈ four8 t g, ∀ s ∈ k.form.slots.toList, s.1 < a.F.ns) :
    (∀ r < 32, ∀ i < t.bzColumns, entUnit q (dataQ own a rd) t.ix.BZ r i =
      digMu x D rad seatT arr w (enOf x.arrays (t.ix.BZ, r, i))) ∧
    (∀ c < 2, ∀ p ∈ piecesL t c, ∀ r < p.Rp, ∀ i < p.Cp,
      entUnit q (dataQ own a rd) t.ix.ZZ (p.r0 + r) (p.c0 + i) =
        digMu x D rad seatT arr w (enOf x.arrays (t.ix.ZZ, p.r0 + r, p.c0 + i))) ∧
    ∀ k ∈ four8 t g, ∀ s ∈ k.form.slots.toList,
      (dataQ own a rd).mask s.1 = digMu x D rad seatT arr w (mkOf x.arrays s.1) := by
  obtain ⟨-, hT, hP⟩ := DgP.shape2_parts HD.tail
  have c0 := OnPublicFiles.dig_c0 HD
  obtain ⟨R1, R2, R3⟩ := OnPublicFiles.rest_pays_of seatT arr own HD rd w hc hm a C M hB a.L rfl c0
    (four8 t g) (fun k hk => hns k hk)
  have eU : ∀ T r i, entUnit q (dataQ own a rd) T r i =
      First.K8.Four.unknownOf a.L (dataQ own a rd) (Sum.inl (T, r, i)) := by
    intro T r i
    unfold entUnit
    rw [hq]
    rfl
  refine ⟨fun r hr i hi => ?_, fun c hc' p hp r hr i hi => ?_, fun k hk s hs => R3 k hk s hs⟩
  · rw [Sd.bz] at hi
    rw [Sd.ix, eU]
    exact (digMsg_of_digVal HD _ (reads_bz tlD _ hP.full hr hi) (R1 r hr i hi)).symm
  · rw [Sd.pieces] at hp
    rw [Sd.ix, eU]
    exact (digMsg_of_digVal HD _ (reads_zz tlD _ hT hc' hp (c0 c hc' p hp) hr hi)
      (R2 c hc' p hp r hr i hi)).symm

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.digMsg_of_digVal
#print axioms VerifiableInference.Desc.First.K8.Honest.ties_of_rest
