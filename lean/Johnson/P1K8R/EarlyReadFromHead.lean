-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/EarlyReadFromHead.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS:
THE COMPLEMENT OF `CellsIn`, FROM THE HEAD: NO EARLY CELL OF THE TIE IS READ OFF THE TABLE OF ZEROS.
NO SOUNDNESS.

`CellsIn` (Johnson/Desc/First/K8/LawBlockIn.lean), the second half of `K8LeftT`'s field `alike`, is
a conditional on two look-ups; where one fails, or where the array has no message now, the tie's
reader `cellsAt` reads the table of zeros at every witness (`cellsAt_congr_msgs`, its arms "none").
Here all three are shown to succeed, with no closed test left in front:
  a message now: `P1K8S.namedB_of_reach` (Johnson/P1K8R/NamedOfReach.lean) at
    `P5J.namesDoorB_at_head`, then `Named.namedB_at` (Johnson/Desc/First/K8/LawNamed.lean).
    the closed test
    `k8AllNowB` of Johnson/P1K8R/EarlyArraysHaveMessagesAtDraw.lean is not needed;
  a seat of the group, and a member there: `seated_at_draw` (P1K8R/SeatedAtDraw.lean) at
    `K8Q35.seated_at_head` (Johnson/K8Q35R/SeatedAtHead.lean);
  the facts along "reached": `P5J.atMgR_of_head`'s field (Johnson/P5J/StartAtHead.lean).
  THESE ARE "FROM THE HEAD (WITH THE FOURTEEN ENTRY TESTS)".
  Of P1K8R/CondOfRest3.lean two names alone are taken: `FrK` (the first chain's frame at the seated
  row) and `ground_at_head` (the blank ground is made and has its 25 built links).
  `early_read_from_head`: **under the head, at each of the 25 links, at every state in front of the
    draw that the head's own "reached" holds and on which no check has failed, at every early cell's
    array t (a matrix's symbols' array, or a vector of reads): `Named.msgNow L t = some o`; `seatAt`
    gives a seat q of the link's own group in the book at o; `find?` gives a member of the plan's
    list at q.**
Limits. That the head can be met is other files' to show. It says where the reader reads, not what
stands there. Nothing on arrays that are not early. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.SeatedAtDraw
import Johnson.P1K8R.CondOfRest3
import Johnson.P1K8R.NamedOfReach
import Johnson.Desc.First.K8.LawNamed
import Johnson.HB.LLHARD.K8NamesDoorAtHead
import Johnson.K8Q35R.SeatedAtHead

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.K9 (seatAt)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **FROM THE HEAD: AT EVERY EARLY CELL's ARRAY: A MESSAGE NOW, A SEAT OF THE GROUP, A MEMBER.** -/
theorem early_read_from_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l ≤ 24) :
    ∀ (z : ProofFile.InstPub) (a : S × (FrK D).E.Str) (tl : HTailF2) (L : LinkCtx),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      h.rchU (drawAt l) ((z, a.1), a.2) →
      a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
      ∀ t r c, early tl (.cell t r c) = true →
        ∃ o q y, Named.msgNow L t = some o ∧
          seatAt ((P5J.At.N Zp cF).group l) a.1.book o = some q ∧
          ((P5J.At.ms Zp Z.lay).find? fun y => decide (seatOf y = q)) = some y := by
  intro z a tl L ha hr hm ht hL t r c he
  have hU : ∀ k a, h.rchU k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a :=
    fun _ _ u => u.1.1
  obtain ⟨L₀, A⟩ := P5J.atMgR_of_head h h.rchU hU
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G, hG, hB⟩ := ground_at_head h
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨Xl, e3⟩ := hB l hl
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hU _ _ hr
  obtain ⟨tl', L', ht', hL', hN⟩ := P1K8S.namedB_of_reach h.scope h.reads O h.laid.planOk
    (P5J.namesDoorB_at_head h) hx e3 ((z, a.1), a.2) hr'
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  obtain ⟨o, -, ho, -⟩ := Named.namedB_at hN ((early_iff_named tl t r c).1 he)
  obtain ⟨q, y, hq, hy⟩ := seated_at_draw h A.fold hU hG hl e3
    (K8Q35.seated_at_head h A.listed hl Xl) z a tl L ha hr hm ht hL t r c o he ho
  exact ⟨o, q, y, ho, hq, hy⟩

end P1K8T

#print axioms P1K8T.early_read_from_head
