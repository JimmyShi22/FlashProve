-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClaimAtClosing.lean: the kind "the code switch" (K2): THE CLAIM
AT `leftAt` OF THE WORDS (Johnson/Desc/K2/Honest/Carry/Left.lean) IS THE CLAIM AT WHAT AN HONEST
PROVER's CLOSING OF A SEGMENT RETURNS (`segmentLeft`, Honest/K2/Closing.lean), under named ties.
Statements with their proofs; no definition. A join: laws typed elsewhere, called one behind the
other.

  `keptTrue_list` the kept members' true shapes, in the order of sending, are the sizes' kept
                    shapes: no premise
  `claimTrue_at_frozen` ALL AT LETTERS: `ClaimTrue` at `leftAt S old w` ↔ `ClaimTrue` at `frozenLeft
                    ‹the two codes› ‹the kept shapes› (foldEnd S.codes old.code old.maskCode
                    (membersTrue S old) M fresh γ)`: the form in which `segmentLeft` returns: under
                    `claimTrue_of_foldEnd`'s seven public premises and three on the entries, and
                    `claimTrue_frozen`'s one on the main code's length
  `claimTrue_at_segmentLeft` THE LOCK: the two joined: `ClaimTrue` at `leftAt S old w` ↔ `ClaimTrue`
                    at what `segmentLeft` returned

THE LOCK's TIES, EACH A PREMISE. Public, between the segment's letters and the carried rows: the
codes, the two codes' numbers (hc, hcode, hmask) · the challenges heard at the segment's numbers are
the carried rows' (hγ) · the carried rows' layout names the group's members and flags, as many flags
as members (hm, hk, hs), and has the four read fields of the description's own layout of the group
(l1 to l4) · the main code's length is a power of two (hp). At whatever rows `segmentGroupRows` returns
(hR): its members are the members at their true shapes; and, ENTRY BY ENTRY, its rows' main and mask
entries at real rows, and the entries of the mask sent ahead at every row below 2 ^ h, are the
words'.

By: `claimTrue_of_foldEnd` (Johnson/Desc/K2/Honest/Carry/LayoutSame.lean) · `claimTrue_frozen`
(Law/ClaimFrozen.lean) · `segmentLeft_inv` (Law/SegmentLeftInv.lean): where `segmentLeft` returns,
`segmentGroupRows` returned some R, and what is handed on is what `foldEnd` leaves of R's rows, kept in
arrays, with the kept members' shapes.

Limits. AN "↔" BETWEEN TWO CLAIMS: NEITHER IS HAD HERE. NO TIE IS PAID HERE, at no state and no run.
hR SPEAKS OF ROWS THAT `segmentGroupRows` MAKES OF THE CARRIED STRETCHES k: here k is a letter; whoever
pays hR at a run says which entry of which stretch a word is. One segment's closing: the walk over
all segments (`closingFrom`, `closingFor`) is not treated. Nothing on tails. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Carry.LayoutSame
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimFrozen
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentLeftInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes
open OnBytes.Slice (GE readE)
open OnBytes.Means (Words)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc.K2.Honest (Left Sizes ClaimTrue sizesAt leftAt foldEnd membersTrue
  GroupMember claimTrue_of_foldEnd)

/-- The kept members' true shapes, in the order of sending, are the sizes' kept shapes. -/
theorem keptTrue_list (S : Statement) (old : SingleRows) (T : SwitchTarget) :
    ((membersTrue S old).filter (·.kept)).map (·.shape) = (sizesAt S old T).kept := by
  show (((old.layout.members.zip old.layout.kept).toList.map fun p =>
      (⟨(S.oracles.getD p.1 default).shape, p.2⟩ : GroupMember)).filter (·.kept)).map (·.shape) =
    (((old.layout.members.zip old.layout.kept).filter (·.2)).map (·.1)).toList.map fun o =>
      (S.oracles.getD o default).shape
  rw [List.filter_map, List.map_map, Array.toList_map, Array.toList_filter, List.map_map]
  rfl

/-- **THE CLAIM AT `leftAt` OF THE WORDS IS THE CLAIM AT WHAT `foldEnd` LEAVES OF ROWS IN FULL, KEPT
IN ARRAYS**: in the form in which `segmentLeft` returns it, all at letters. -/
theorem claimTrue_at_frozen (S : Statement) (G : Group) (old : SingleRows) (T : SwitchTarget)
    (w : Words GE) (M : Nat → Rows) (fresh : Rows)
    (hm : old.layout.members = G.members) (hk : old.layout.kept = G.kept)
    (hs : G.kept.size = G.members.size)
    (l1 : old.layout.k = (VerifiableInference.Desc.Own.layoutOf S G).k)
    (l2 : old.layout.h = (VerifiableInference.Desc.Own.layoutOf S G).h)
    (l3 : old.layout.mainFirst = (VerifiableInference.Desc.Own.layoutOf S G).mainFirst)
    (l4 : old.layout.maskFirst = (VerifiableInference.Desc.Own.layoutOf S G).maskFirst)
    (hp : 2 ^ (S.codes.base.getD old.code default).logEll =
      (S.codes.base.getD old.code default).ell)
    (hM : ∀ i b j, i < old.layout.members.size →
      b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows →
      (M i).main
          ((S.oracles.getD (old.layout.members.getD i noId) default).shape.mainDeg == 3) b j =
        w (old.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
          (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows))
    (hZ : ∀ i b j, i < old.layout.members.size →
      b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows →
      (M i).mask b j = w (old.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
        (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows))
    (hF : ∀ b j, b < 2 ^ old.layout.h → fresh.mask b j = w old.fresh .mask
      (b + j * 2 ^ ceilLog2 (S.oracles.getD old.fresh default).shape.maskRows)) :
    ClaimTrue (sizesAt S old T) old (leftAt S old w) ↔
      ClaimTrue (sizesAt S old T) old
        (frozenLeft (S.codes.base.getD old.code default) (S.codes.mask.getD old.maskCode default)
          (((membersTrue S old).filter (·.kept)).map (·.shape))
          (foldEnd S.codes old.code old.maskCode (membersTrue S old) M fresh
            (old.gamma.map readE))) := by
  rw [keptTrue_list S old T]
  exact (claimTrue_of_foldEnd S G old T w M fresh hm hk hs l1 l2 l3 l4 hM hZ hF).trans
    (claimTrue_frozen (sizesAt S old T) old _ hp).symm

/-- **THE LOCK: THE CLAIM AT `leftAt` OF THE WORDS IS THE CLAIM AT WHAT `segmentLeft` RETURNS**,
under named ties between the segment's public letters and the carried rows, and where the entries
of the group's rows, as `segmentGroupRows` makes them, are the words'. -/
theorem claimTrue_at_segmentLeft (S : Statement) (G : Group) (old : SingleRows) (T : SwitchTarget)
    (w : Words GE) {table : FreshTable} {Sg : SegmentPub} {prev : Option Left}
    {prevKept : List OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {base : Nat} {W : Left} {kept : List OracleShape}
    (h : segmentLeft table Sg prev prevKept own heard k base = .ok (W, kept))
    (hc : Sg.sizes.codes = S.codes) (hcode : Sg.sizes.code = old.code)
    (hmask : Sg.sizes.maskCode = old.maskCode)
    (hγ : challengesOr0 heard Sg.gamma = old.gamma.map readE)
    (hm : old.layout.members = G.members) (hk : old.layout.kept = G.kept)
    (hs : G.kept.size = G.members.size)
    (l1 : old.layout.k = (VerifiableInference.Desc.Own.layoutOf S G).k)
    (l2 : old.layout.h = (VerifiableInference.Desc.Own.layoutOf S G).h)
    (l3 : old.layout.mainFirst = (VerifiableInference.Desc.Own.layoutOf S G).mainFirst)
    (l4 : old.layout.maskFirst = (VerifiableInference.Desc.Own.layoutOf S G).maskFirst)
    (hp : 2 ^ (S.codes.base.getD old.code default).logEll =
      (S.codes.base.getD old.code default).ell)
    (hR : ∀ R, segmentGroupRows table Sg prev prevKept own k base true = .ok R →
      R.members = membersTrue S old ∧
      (∀ i b j, i < old.layout.members.size →
        b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows →
        (R.rows.getD i zeroMessage).main
            ((S.oracles.getD (old.layout.members.getD i noId) default).shape.mainDeg == 3) b j =
          w (old.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
            (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows)) ∧
      (∀ i b j, i < old.layout.members.size →
        b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows →
        (R.rows.getD i zeroMessage).mask b j =
          w (old.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
            (S.oracles.getD (old.layout.members.getD i noId) default).shape.maskRows)) ∧
      ∀ b j, b < 2 ^ old.layout.h → (R.fresh.getD zeroMessage).mask b j = w old.fresh .mask
        (b + j * 2 ^ ceilLog2 (S.oracles.getD old.fresh default).shape.maskRows)) :
    ClaimTrue (sizesAt S old T) old (leftAt S old w) ↔ ClaimTrue (sizesAt S old T) old W := by
  obtain ⟨R, eR, rfl, rfl⟩ := segmentLeft_inv h
  obtain ⟨e, hM, hZ, hF⟩ := hR R eR
  rw [e, hc, hcode, hmask, hγ]
  exact claimTrue_at_frozen S G old T w _ _ hm hk hs l1 l2 l3 l4 hp hM hZ hF

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.keptTrue_list
#print axioms ProofFile.Honest.K2.claimTrue_at_frozen
#print axioms ProofFile.Honest.K2.claimTrue_at_segmentLeft
