-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatScope.lean: THEOREMS. **The library's test on a seat finds no fault at the key file's first two sampled messages' seats, FROM SCOPE's EQUATIONS**: seatFaultAt (Key.descriptionFromSource X N P) csKey tag shIdx 0 0 = none and … shMul 1 0 = none, where the source's one-time chain has the written codes, index-mask message and ranges.
OBJECT: seatFaultAt (Johnson/Desc/SeatAt.lean) at the key file's own description. USER: none yet (meant: two premises of member_fk₁, Johnson/RunOne/KeyFillMeet.lean, a theorem on a member at the woven tables' reading). LETTERS: X N P · the tag.
THE PREMISES ARE OTHERS' CONCLUSIONS: that in scope the source's one-time chain has these values is proved elsewhere (five_in_scope, Johnson/RunOne/Law/KeyInScope.lean, which this file does not import): here they stand as equations.
  numsOf         what the test reads of a told tree: the log-length, the words, each tenant's main and mask words
  noFault_of     the converse of seat_of_noFault, on these numbers: so the test reads no tenant's degree, mark or groups
  nums_eq        the sending kind's telling, read by numsOf, hangs on the codes and the messages alone
  told_front     the first chain's blocks tell first what the two sendings tell
  nums_idx | nums_msg   by the kernel, at closed numbers of a place: [(13, 3, [(0, 3)])] · [(22, 77, [(2, 27), (0, 48)])]; nums_idx_no | nums_msg_no: with one numeral turned: refuted
  n0_scope | n1_scope   **the two**
  codes_full | idx_shape_full | msg_shape_full   the two written codes, keyFull.codes and csKey, are one (rfl); the written messages have the written shapes
  n01_scope      the two, from the equations as scope's theorem words them
What is not claimed. The third seat (W's: tree 5). That scope's equations hold. Anything on what is sent. Nothing on soundness.

-/
import Johnson.RunOne.KeyScopeNums
import Johnson.Desc.Key.Desc
import Johnson.Desc.SeatAt

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.Top.H (csKey shIdx shMul)
open Lk6.AtPlan (keyFull)

/-- What the library's test reads of a told tree. -/
def numsOf (o : VerifiableInference.Desc.Oracle) : ℕ × ℕ × List (ℕ × ℕ) := (o.logLength, o.words, o.tenants.map fun n => (n.main, n.mask))

/-- **The converse of seat_of_noFault, on numbers.** -/
theorem noFault_of {XI : Type} (F : FileDescription XI) (cs : Codes) (tag : String) (s : OracleShape) (j t L W a b : ℕ) (l : List (ℕ × ℕ))
    (ho : (F.oracleAt j).map numsOf = some (L, W, l)) (ht : l[t]? = some (a, b))
    (h1 : L = longOf cs s) (h2 : a = s.mainRows * s.mainDeg) (h3 : b = s.maskRows * 3)
    (h4 : (s.mainRows == 0 || (cs.base.getD s.code default).logN == longOf cs s) = true)
    (h5 : (l.map fun x => x.1 + x.2).sum = W) (h6 : (s.mainDeg == 1 || s.mainDeg == 3) = true) :
    seatFaultAt F cs tag s j t = none := by
  obtain ⟨orc, hor, hn⟩ := Option.map_eq_some_iff.1 ho
  obtain ⟨rfl, rfl, rfl⟩ : orc.logLength = L ∧ orc.words = W ∧ (orc.tenants.map fun n => (n.main, n.mask)) = l := by
    have := hn
    simp only [numsOf, Prod.mk.injEq] at this
    exact this
  rw [List.getElem?_map] at ht
  obtain ⟨n, hnt, hab⟩ := Option.map_eq_some_iff.1 ht
  obtain ⟨rfl, rfl⟩ : n.main = a ∧ n.mask = b := by
    simpa only [Prod.mk.injEq] using hab
  have e5 : (orc.tenants.map fun x => x.main + x.mask).sum = orc.words := by
    rw [← h5, List.map_map]
    rfl
  unfold seatFaultAt
  simp only [hor, hnt, h1, h2, h3, h4, e5, h6, beq_self_eq_true, if_true, List.append_nil, List.isEmpty_nil]

/-- **The sending kind's telling, read by numsOf, hangs on the codes and the messages alone.** -/
theorem nums_eq (P Q : K1.Par) (hc : P.codes = Q.codes) (hs : P.sent = Q.sent) :
    ((K1.oracles P).flatMap id).map numsOf = ((K1.oracles Q).flatMap id).map numsOf := by
  unfold K1.oracles K1.Par.trees
  rw [hc, hs]
  simp only [List.flatMap_cons, List.flatMap_nil, id, List.append_nil, List.map_map]
  refine List.map_congr_left ?_
  rintro ⟨t, i⟩ _
  simp only [Function.comp, numsOf, List.map_map]
  rfl

/-- **The first chain's blocks tell first what the two sendings tell.** -/
theorem told_front (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) :
    ∃ (g₀ g₁ : List (List ℕ)) (R : List VerifiableInference.Desc.Oracle), oraclesOf (descriptionFromSource X N P).first.blocksInOrder =
      (K1.oracles (sendingPar X.Y.k.oneTime pieces.idx "the index masks" #[X.Y.k.oneTime.indexMasks] g₀)).flatMap id ++
        ((K1.oracles (sendingPar X.Y.k.oneTime pieces.msg "the lookups' own message and what rides with it" (Wf.messageOf X.Y.k.oneTime.ranges) g₁)).flatMap id ++ R) :=
  ⟨_, _, _, rfl⟩

/-- Closed numbers of a place: the written codes and one part. -/
def parAt (msg : Array OracleNotice) : K1.Par := { place := default, codes := csKey, gp := { samples := 0, firstTree := 0 }, work := 0, parts := [("", msg)] }

theorem nums_idx : ((K1.oracles (parAt #[keyFull.once.input])).flatMap id).map numsOf = [(13, 3, [(0, 3)])] := by decide +kernel
theorem nums_msg : ((K1.oracles (parAt (Wf.messageOf keyFull.ranges.x))).flatMap id).map numsOf = [(22, 77, [(2, 27), (0, 48)])] := by decide +kernel
theorem nums_idx_no : ((K1.oracles (parAt #[keyFull.once.input])).flatMap id).map numsOf ≠ [(13, 3, [(0, 4)])] := by decide +kernel
theorem nums_msg_no : ((K1.oracles (parAt (Wf.messageOf keyFull.ranges.x))).flatMap id).map numsOf ≠ [(22, 77, [(2, 27), (0, 49)])] := by decide +kernel

/-- What the description tells of its first tree, read by numsOf, in scope. -/
theorem nums_front₀ (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hc : X.Y.k.oneTime.codes = csKey)
    (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) : ((descriptionFromSource X N P).oracleAt 0).map numsOf = some (13, 3, [(0, 3)]) := by
  obtain ⟨g₀, g₁, R, hR⟩ := told_front X N P
  have e₀ := (nums_eq (sendingPar X.Y.k.oneTime pieces.idx "the index masks" #[X.Y.k.oneTime.indexMasks] g₀) (parAt #[keyFull.once.input]) hc
    (by rw [hi]; rfl)).trans nums_idx
  unfold FileDescription.oracleAt
  rw [← List.getElem?_map, hR]
  simp only [List.map_append, List.append_assoc, e₀]
  rfl

/-- Of its first two. -/
theorem nums_front (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hc : X.Y.k.oneTime.codes = csKey)
    (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) :
    ((descriptionFromSource X N P).oracleAt 0).map numsOf = some (13, 3, [(0, 3)]) ∧ ((descriptionFromSource X N P).oracleAt 1).map numsOf = some (22, 77, [(2, 27), (0, 48)]) := by
  obtain ⟨g₀, g₁, R, hR⟩ := told_front X N P
  have e₀ := (nums_eq (sendingPar X.Y.k.oneTime pieces.idx "the index masks" #[X.Y.k.oneTime.indexMasks] g₀) (parAt #[keyFull.once.input]) hc
    (by rw [hi]; rfl)).trans nums_idx
  have e₁ := (nums_eq (sendingPar X.Y.k.oneTime pieces.msg "the lookups' own message and what rides with it" (Wf.messageOf X.Y.k.oneTime.ranges) g₁)
    (parAt (Wf.messageOf keyFull.ranges.x)) hc (by rw [hr]; rfl)).trans nums_msg
  have hall : ∀ j, ((descriptionFromSource X N P).oracleAt j).map numsOf =
      ([(13, 3, [(0, 3)])] ++ ([(22, 77, [(2, 27), (0, 48)])] ++ (R.map numsOf ++ ((oraclesOf (descriptionFromSource X N P).shared.blocksInOrder).map numsOf ++ (oraclesOf (descriptionFromSource X N P).second.blocksInOrder).map numsOf))))[j]? := by
    intro j
    unfold FileDescription.oracleAt
    rw [← List.getElem?_map, hR]
    simp only [List.map_append, List.append_assoc, e₀, e₁]
  exact ⟨(hall 0).trans rfl, (hall 1).trans rfl⟩

/-- **The first sampled message's seat, from scope's equations.** -/
theorem n0_scope (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hc : X.Y.k.oneTime.codes = csKey)
    (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) (tag : String) :
    seatFaultAt (descriptionFromSource X N P) csKey tag shIdx 0 0 = none :=
  noFault_of _ csKey tag shIdx 0 0 13 3 0 3 [(0, 3)] (nums_front₀ X N P hc hi) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The second's.** -/
theorem n1_scope (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hc : X.Y.k.oneTime.codes = csKey)
    (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (tag : String) :
    seatFaultAt (descriptionFromSource X N P) csKey tag shMul 1 0 = none :=
  noFault_of _ csKey tag shMul 1 0 22 77 2 27 [(2, 27), (0, 48)] (nums_front X N P hc hi hr).2 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The two written codes, keyFull.codes and csKey, are one. -/
theorem codes_full : keyFull.codes = csKey := rfl

/-- The written messages have the written shapes. -/
theorem idx_shape_full : keyFull.once.input.shape = shIdx := by decide +kernel
theorem msg_shape_full : ((Wf.messageOf keyFull.ranges.x)[0]?).map (·.shape) = some shMul := by decide +kernel

/-- **The two, from the equations as scope's theorem words them** (the one-time chain's index-mask message, codes and ranges are keyFull's). -/
theorem n01_scope (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hi : X.Y.k.oneTime.indexMasks = keyFull.once.input)
    (hc : X.Y.k.oneTime.codes = keyFull.codes) (hr : X.Y.k.oneTime.ranges = keyFull.ranges.x) (t0 t1 : String) :
    seatFaultAt (descriptionFromSource X N P) csKey t0 shIdx 0 0 = none ∧ seatFaultAt (descriptionFromSource X N P) csKey t1 shMul 1 0 = none :=
  ⟨n0_scope X N P (hc.trans codes_full) hi t0, n1_scope X N P (hc.trans codes_full) hi hr t1⟩

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.noFault_of
#print axioms Johnson.RunOne.KeyLetters.nums_eq
#print axioms Johnson.RunOne.KeyLetters.told_front
#print axioms Johnson.RunOne.KeyLetters.nums_idx
#print axioms Johnson.RunOne.KeyLetters.nums_msg
#print axioms Johnson.RunOne.KeyLetters.nums_idx_no
#print axioms Johnson.RunOne.KeyLetters.nums_msg_no
#print axioms Johnson.RunOne.KeyLetters.nums_front₀
#print axioms Johnson.RunOne.KeyLetters.nums_front
#print axioms Johnson.RunOne.KeyLetters.n0_scope
#print axioms Johnson.RunOne.KeyLetters.n1_scope
#print axioms Johnson.RunOne.KeyLetters.codes_full
#print axioms Johnson.RunOne.KeyLetters.idx_shape_full
#print axioms Johnson.RunOne.KeyLetters.msg_shape_full
#print axioms Johnson.RunOne.KeyLetters.n01_scope
