-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LendsOfPick.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN
ROUNDS (kind K5): THE FRAME's TEST ON THE LENDING (lendsRow, Honest/Small/LendsRow.lean, of other
authors) IS TRUE AT THE KIND's PLACE AND ROW, AT A BOOK THAT THE MAKER RETURNS: UNDER THE HEAD h AND
ONE PREMISE ON THE MAKER, hPW. Two statements with their proofs. No definition.

  k5Row_plain        a part of the kind's row takes nothing and carries nothing
  k5_lends_of_pick   CONDITIONAL: **lendsRow B 0 ‹the seat's place› (k5Row ‹the seat›) = true**

THE PREMISES OF k5_lends_of_pick, ALL OF THEM. h · hg: g is below 12 · hB: bookWhole returns B at
the description of the head and at mergesByName of its first chain · ha: a is the plan of group g ·
hPW: AT EVERY MEMBER OF THE FIRST CHAIN WITHOUT A ROUND NAMED "FOLD epsilon": there are idx and a
with four conjuncts: the index masks' message as an owner is idx; linksWants returns a; wantsFree
accepts; the entries of B that part j of the member spends are the stretches with that spender.
keyOf and G are letters: the test reads of the seat its place and the plan's numbers.

hPW IS THE END OF pick_whole (Honest/BookRowStretch.lean, of other authors); that file is not
imported here: k5_lends_paid_fill (FillFoot.lean in this folder) pays hPW by one call of it. Of the
four conjuncts the second and the fourth are spent.

Called: k5_member (Member.lean) · k5_no_seed · k5_no_fold · k5_stated (StatedK5.lean) ·
no_merge_of_kind (NamedOfWants.lean) · rowNamed_of_pick (RowNamedOfPick.lean) · lendsRow_of_rowNamed
(LendsHalf.lean) · of other files of ours: plain_no_row · plain_all_spent (Honest/BookPlain.lean) ·
of other authors: orderOf_nodup · bookWhole_word · placesOk_of_planOk.

Limits. Conditional. hPW IS PROVED NOWHERE THAT THIS FILE IMPORTS. That bookWhole returns is a
premise. It says whether the lending returns: nothing on what is lent. h is a hypothesis; on whether
it can be met see Member.lean's head. At the library's full size and the format's second hash function
alone. Through its imports the file stands above the library's folder ThirdParty/. No property is
claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.BookPlain
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsHalf
import Johnson.Desc.ProofFile.Honest.K5.Law.RowNamedOfPick
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns
import Johnson.RunOne.Sound.KeyListsAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open P5J (AtMgA TS CellsM)

/-- A part of K5's row at the small input takes no coin of its own and carries none. -/
theorem k5Row_plain (Z : Seat5) : ∀ p ∈ k5Row Z, p.takes = ⟨0, 0⟩ ∧ p.carries = [] := by
  intro p hp
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hp
  rcases s with ⟨k | _ | n, i⟩ <;> exact ⟨rfl, rfl⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
include h

/-- **THE FRAME's TEST ON THE LENDING AT K5's PLACE, AT A BOOK THAT THE MAKER RETURNS.**
CONDITIONAL: the premises stand in the file's head; hPW is proved nowhere that this file imports. -/
theorem k5_lends_of_pick {g : Nat} (hg : g < 12) {B : ProverCoinCounts} {p0 p1 p2 : Johnson.G.ChainSends}
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2
      (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (hPW : ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      (∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") →
      ∃ (idx : MsgAt) (a : List Want × Nat),
        ownerOf indexMaskRun (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        linksWants (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).ends
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
            .ok a ∧
        wantsFree (a.1 ++ (loneWants idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
          (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
            x.place.link.isNone).flatMap planParts) a.2).1) = true ∧
        ∀ j, BookRow.pick ⟨b.place, j⟩ B.ahead =
          ((a.1 ++ (loneWants idx
            (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
            (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
              x.place.link.isNone).flatMap planParts) a.2).1).filter
                fun w => w.spender == ⟨b.place, j⟩).map (·.entry))
    (keyOf : ProofFile.Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)) (G : Ground)
    {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) :
    lendsRow B 0 (seatOf keyOf Zp G cF g a).place (k5Row (seatOf keyOf Zp G cF g a)) = true := by
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨blk, a', hm, Pl, Dc⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  have hb : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  have hs := k5_no_seed blk _ Dc.rounds
  have hf := k5_no_fold blk _ Dc.rounds
  have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  obtain ⟨idx, w, -, hw, -, hpk⟩ := hPW blk hb hf
  have hpl : blk.place = (seatOf keyOf Zp G cF g a').place := Dc.place
  have hk : blk.place.kind = .K5 := by rw [Dc.place]
  have hrow := rowNamed_of_pick hn hb (l := 2 * g + 1) (by rw [Dc.place]; rfl)
    (fun i => no_merge_of_kind _ ⟨blk.place, i⟩ (by rw [hk]; decide) (by rw [hk]; decide))
    ⟨idx, w, hw, hpk⟩ (plain_no_row hB hp hb hs) (plain_all_spent hB hp hb hs hf)
    (k5Row (seatOf keyOf Zp G cF g a')) (k5Row_plain _)
    (k5_stated blk (parAt Zp g a') (seatOf keyOf Zp G cF g a') hpl Dc.rounds rfl Dc.plan)
  rw [hpl] at hrow
  exact lendsRow_of_rowNamed (bookWhole_word hB) hp (List.mem_map.2 ⟨blk, hb, hpl⟩) hrow

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5Row_plain
#print axioms ProofFile.Honest.K5.k5_lends_of_pick
