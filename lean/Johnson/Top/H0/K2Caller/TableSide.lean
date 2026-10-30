-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TableSide.lean: the code switch: THE TABLE's SIDE OF
PinKeptJoin.lean's KeptFacts AT A HELD MEMBER, IN ONE PLACE: the five that KeptFactsOf.lean's
keptFacts_of leaves as premises on the table's side.
  tableSide_of   FOUR OF THE FIVE: KeptSeat · the seat is one of the plan's list · its number there
                 is the frame's entry's own · every leaf is shown. Out of KeptSeatOf.lean's
                 keptSeat_of_fold, KeptSeatsB.lean's test, KeptFactsMore.lean's shown_of_promise
  one_number_of  THE FIFTH: arr gives the new copy's seat the old copy's number: from what
                 keptAlign_at concludes (Johnson/P5T/KeptAlign.lean: read, not imported) at the old
                 copy's seat
tableSide_of's PREMISES. TESTS ON THE PLAN ALONE: SeatFits AT THE ONE MEMBER (KeptSeatOf.lean's
SeatFitAt) · keptSeatsB at a list olds.
ON THE VERIFIER's STATE t THAT THE WAY IN LETS IN: the three tests atFirstBook | atFirstSeats |
atFirstFits (what FoldFacts' bookInOrder | seatsCarried | bookFits conclude at a reached state) ·
the entry's number is below the book's places (PlacesOf.lean has it of the border's state) · the
front reads something at some position · the front's statement has a message of the typed shape at
the entry's number. ho: olds HAS THE FRAME's ENTRY's OWN NUMBER AT THE MEMBER's PLACE. ON THE
ORACLES: horc: AT EVERY KEY j BELOW trees THE READING IS Strs.col j: the conclusion
of orcY_of_data | orcY_in_scope (K2Hears/OrcAtFrame.lean: read, not imported),
to the letter · the table's «shown» at a seat at which a member alike to the typed one sits.
one_number_of's: hN: the law's seat of the new copy is the table's, by place; and in hal the old
copy's seat stands for the table's (N.keptOf l)[a].
LIMITS. An assembly. None of the premises is shown at a real value; neither test has been run by us.
pinKept IS NOT PAID. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.KeptSeatsB
import Johnson.Top.H0.K2Caller.KeptFactsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (SeatFits ShownAt Mem Alike SitsAt shownJT numAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First.K2Hands

variable {r : SwRow} {H : r.OK} {Xi : Type} (G : FileDescription Xi) (seat : Fin r.lo.length → ℕ × ℕ)
  (p : K2.P2) (orc : Strs → ℕ → ℕ → List UInt64) (seats : List (ℕ × ℕ)) (L : Laid) (trees : ℕ)

/-- **The table's side of KeptFacts at a held member**, but for «one number». -/
theorem tableSide_of (t : VerifiableInference.Desc.First.S) (fx : _root_.Tw.K2.Front)
    (W₀ : SwitchFrame) (y : Strs) (k : {a // (plainHd r H).cl a})
    (hS : SeatFitAt G r.cs r.lo seat k.1.1) (olds : List ℕ)
    (hB : keptSeatsB G r.cs L seats trees r.lo seat r.kept olds = true)
    (ho : olds[r.kept.idxOf k.1.1.val]? = some (keptK2 r H W₀ k).old)
    (hIn : VerifiableInference.Desc.K12.Door.atFirstBook (K2.par9 p).firstTree t = true)
    (hSe : VerifiableInference.Desc.K12.Door.atFirstSeats L t = true)
    (hFi : VerifiableInference.Desc.K12.Door.atFirstFits t = true)
    (q₀ : ℕ) (h0 : (K2.longFront p t fx (orc y) q₀).isSome = true)
    (hold : (keptK2 r H W₀ k).old < t.book.place.size)
    (xo : OnBytes.Oracle) (hmsg : fx.st.oracles[(keptK2 r H W₀ k).old]? = some xo)
    (hsh : xo.shape = (r.lo.get k.1.1).1)
    (horc : ∀ j, j < trees → ∀ x, orc y j x = y.col j x)
    (ms : List Mem) (q : ℕ × ℕ) (hs : shownJT r.cs G ms q.1 q.2 y) (x : Mem) (hx : x ∈ ms)
    (hq : SitsAt x q.1 q.2) (hA : Alike x ⟨⟨r.lo, seat⟩, k.1.1⟩) :
    KeptSeat G p t fx (orc y) y (keptK2 r H W₀ k).old (r.lo.get k.1.1).1 (seat k.1.1)
        (2 ^ (cMain r.cs (r.lo.get k.1.1).1).a) ∧
      seat k.1.1 ∈ seats ∧ numAt seats ⟨⟨r.lo, seat⟩, k.1.1⟩ = (keptK2 r H W₀ k).old ∧
      ShownAt G r.cs r.lo seat y k.1.1 := by
  have hSh := shown_of_promise G seat ms q y hs x hx hq k.1.1 hA
  obtain ⟨⟨tp, sh0, p1, e1, e2, p2, p3, p4⟩, p5, p6⟩ :=
    keptSeatB_says G r.cs L seats trees (plan_at_kept G L seats trees seat hB k _ ho)
  have hlt : (keptK2 r H W₀ k).old < fx.st.oracles.size := (Array.getElem?_eq_some_iff.1 hmsg).1
  have hxo : (K2.skelOf fx).oracles[(keptK2 r H W₀ k).old]? = some xo := by
    unfold K2.skelOf
    rw [stSent_old _ _ _ hlt]
    exact hmsg
  exact ⟨keptSeat_of_fold G r.cs r.lo seat k.1.1 hS k.2.fst p t fx (orc y) y _ hSh L hIn hSe hFi q₀
    h0 hold tp p1 sh0 p2 xo hxo hsh p3 (fun x _ => by rw [← e1]; exact horc tp e2 x) p4, p5, p6,
    hSh⟩

/-- **«One number»**: arr gives the new copy's seat the old copy's number, from what keptAlign_at
concludes, where the law's two seats are the table's, by place. news: the table's list
of the switch's first sending's seats (N.sent (l + 1) 0). -/
theorem one_number_of (news : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seatN : Fin r.l.length → ℕ × ℕ) (a : ℕ) (i : Fin r.lo.length)
    (hal : ∃ w, news[1 + a]? = some w ∧ arr (seat i).1 (seat i).2 = arr w.1 w.2)
    (hN : ∀ ho : 1 + a < r.l.length, news[1 + a]? = some (seatN ⟨_, ho⟩))
    (ho : 1 + a < r.l.length) :
    arr (seatN ⟨_, ho⟩).1 (seatN ⟨_, ho⟩).2 = arr (seat i).1 (seat i).2 := by
  obtain ⟨w, h1, h2⟩ := hal
  rw [hN ho] at h1
  rw [h2, ← Option.some.inj h1]

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.one_number_of

#print axioms VerifiableInference.Desc.First.K2Caller.tableSide_of
