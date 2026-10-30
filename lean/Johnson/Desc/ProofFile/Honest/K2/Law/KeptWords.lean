-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KeptWords.lean: the kind "the code switch" (K2): WHAT AN HONEST
PROVER's CLOSING OF A SEGMENT LEFT OF A KEPT MEMBER IS THE WORDS AT THAT MEMBER, entry by entry; and
so a row that reads that member's main table alone says of `oldWords` what it says of the words.
Statements with their proofs; no definition.

WHICH SLOT IT IS FOR. The field stored of the record `MadeAsks` (ExchangeAtMade.lean of this
folder): that the kept members' stored sample rows say true of `oldWords` at what the closing left.

  `frozen_entryIn`  a kept member's entry is the same in what `frozenLeft` keeps in arrays
  `kept_member`     the kept member number a stands at the layout's place `keptNo`
  `kept_entry_words`   THE LOCK's PREMISES ⊢ at every index of the table, the entry of W at the kept
                    member a is the words' at that message's main table: where the words are 0
                    beyond the real rows
  `says_old_of_words`   a row that reads the message o's main table alone says of `oldWords` what
                    it says of the words: o the kept member a

By: `segmentLeft_inv` (SegmentLeftInv.lean of this folder) · `keptTrue_list` (ClaimAtClosing.lean) ·
`frozen_kept` (ClaimFrozen.lean) · under Johnson/Desc/K2/Honest/: `sizesKept_true`, `pair_at`
(Carry/OfRows.lean), `groupLayout_true`, `foldEnd_eq_at`, `foldEndAt_lay` · `reads_off`
(Inner/SampleHold.lean) · `switchKept_list` (Johnson/Top/H0/K2Hears/KeptNos.lean) · `value_named`
(Honest/K1/AnswersChain.lean).

Limits. THE TIES OF THE LOCK THAT IT SPENDS ARE PREMISES HERE, AS IN `claimTrue_at_segmentLeft`
(ClaimAtClosing.lean): fewer of them: not the challenges, nor the layout's four fields. Padded: a
premise: the words are 0 at the rows beyond the real ones. Whether a stored row says true of the
words is not said here. k, A LETTER HERE, HANDS THE CLOSING ITS COINS; hR READS EVERY ENTRY OF A
MEMBER's MAIN ROWS, ALSO WHERE A PAD LIES: entries that hold coins: equations between two texts'
values: what is WRITTEN where. One run's coins: never quoted for a law.
NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimAtClosing
import Johnson.Desc.ProofFile.Honest.K1.AnswersChain
import Johnson.Desc.K2.Honest.Inner.SampleHold
import Johnson.Top.H0.K2Hears.KeptNos

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (GE readE rdE coefAt)
open OnBytes.Means (Words Says Padded value onTable tableSize)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc.K2.Honest (Left Sizes sizesAt Held ClaimTrue oldWords membersTrue
  groupLayout_true foldEnd_eq_at foldEndAt_lay foldEnd foldEndAt keptNo keptOf shapeOf_true
  sizesKept_true pair_at reads_off)
open VerifiableInference.Desc.First.K2Hands (readsMain)

/-- **A kept member's entry is the same in what is kept in arrays.** -/
theorem frozen_entryIn (Z : Sizes) (W : Left)
    (hp : 2 ^ (Z.codes.base.getD Z.code default).logEll = (Z.codes.base.getD Z.code default).ell)
    (a i : Nat)
    (hi : i < 2 ^ (ceilLog2 (Z.kept.getD a {}).mainRows +
      (Z.codes.base.getD Z.code default).logEll)) :
    ((frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
      W).kept a).entryIn (Z.kept.getD a {}) i = (W.kept a).entryIn (Z.kept.getD a {}) i := by
  unfold Held.entryIn
  split
  · rename_i hb
    have ha : a < Z.kept.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)] at hb
      exact Nat.not_lt_zero _ hb
    have hj : i / 2 ^ ceilLog2 (Z.kept.getD a {}).mainRows <
        (Z.codes.base.getD Z.code default).ell := by
      rw [← hp]
      exact Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hi)
    unfold VerifiableInference.Desc.K2.Honest.Held.entry
    exact frozen_kept _ _ _ _ a _ _ ha hb hj
  · rfl

/-- **The kept member number a stands at the layout's place `keptNo`.** -/
theorem kept_member (S : Statement) (old : SingleRows)
    (hsz : old.layout.kept.size = old.layout.members.size) {a o : Nat}
    (ho : (switchKept old).toList[a]? = some o) :
    keptNo (membersTrue S old) a < old.layout.members.size ∧
      old.layout.members.getD (keptNo (membersTrue S old) a) noId = o := by
  have hn : (membersTrue S old).length = old.layout.members.size := by
    unfold membersTrue
    rw [List.length_map, Array.length_toList, Array.size_zip, hsz, Nat.min_self]
  have hz : (old.layout.members.zip old.layout.kept).toList.length = old.layout.members.size := by
    rw [Array.length_toList, Array.size_zip, hsz, Nat.min_self]
  have hq : (fun w => keptOf (membersTrue S old) w) = fun w => old.layout.kept.getD w false := by
    funext w
    unfold keptOf membersTrue
    rw [List.getElem?_map, Option.map_map, Array.getD_eq_getD_getElem?]
    by_cases hw : w < old.layout.members.size
    · rw [pair_at old hsz w hw, Array.getElem?_eq_getElem (hsz ▸ hw)]
      rfl
    · rw [List.getElem?_eq_none (by rw [hz]; exact Nat.le_of_not_lt hw),
        Array.getElem?_eq_none (by rw [hsz]; exact Nat.le_of_not_lt hw)]
      rfl
  rw [VerifiableInference.Desc.Own.switchKept_list, List.getElem?_map] at ho
  cases hw : (VerifiableInference.Desc.Own.keptNos old.layout)[a]? with
  | none =>
    rw [hw] at ho
    cases ho
  | some w =>
    rw [hw] at ho
    have hlt : w < old.layout.members.size :=
      List.mem_range.1 (List.mem_filter.1 (List.mem_of_getElem? hw)).1
    have e : keptNo (membersTrue S old) a = w := by
      unfold keptNo
      rw [hq, hn, List.getD_eq_getElem?_getD]
      show ((VerifiableInference.Desc.Own.keptNos old.layout)[a]?).getD _ = w
      rw [hw]
      rfl
    rw [e]
    refine ⟨hlt, ?_⟩
    have e2 : old.layout.members.getD w noId = old.layout.members.getD w 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
      rfl
    rw [e2]
    exact Option.some.inj ho

/-- hR AND hP ARE PREMISES. One run's coins: never quoted for a law. **At every index of the table,
the entry of what the closing left at the kept member a is the words' at that message's main
table.** W: what `segmentLeft` returned. ho: o is the kept member a, by place; `says_old_of_words`
says the same by `idxOf?`: `Lists.idxOf_at` goes from the one to the other where no number stands
twice. -/
theorem kept_entry_words (S : Statement) (old : SingleRows) (T : SwitchTarget)
    (w : Words GE) {table : FreshTable} {Sg : SegmentPub} {prev : Option Left}
    {prevKept : List OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {base : Nat} {W : Left} {kept : List OracleShape}
    (h : segmentLeft table Sg prev prevKept own heard k base = .ok (W, kept))
    (hc : Sg.sizes.codes = S.codes) (hcode : Sg.sizes.code = old.code)
    (hmask : Sg.sizes.maskCode = old.maskCode)
    (hsz : old.layout.kept.size = old.layout.members.size)
    (hp : 2 ^ (S.codes.base.getD old.code default).logEll =
      (S.codes.base.getD old.code default).ell)
    (hR : ∀ R, segmentGroupRows table Sg prev prevKept own k base true = .ok R →
      R.members = membersTrue S old ∧
      (∀ i b j, i < old.layout.members.size →
        b < (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows →
        (R.rows.getD i zeroMessage).main
            ((S.oracles.getD (old.layout.members.getD i noId) default).shape.mainDeg == 3) b j =
          w (old.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
            (S.oracles.getD (old.layout.members.getD i noId) default).shape.mainRows)))
    (hP : Padded S w) {a o : Nat} (ho : (switchKept old).toList[a]? = some o) (i : Nat)
    (hi : i < 2 ^ (ceilLog2 (S.oracles.getD o default).shape.mainRows +
      (S.codes.base.getD old.code default).logEll)) :
    (W.kept a).entryIn ((sizesAt S old T).kept.getD a {}) i = w o .main i := by
  obtain ⟨R, eR, rfl, rfl⟩ := segmentLeft_inv h
  obtain ⟨e, hM⟩ := hR R eR
  obtain ⟨t1, t2⟩ := kept_member S old hsz ho
  have es' : VerifiableInference.Desc.K2.Honest.shapeOf (membersTrue S old)
      (keptNo (membersTrue S old) a) =
      (S.oracles.getD o default).shape := by
    have em : old.layout.members.getD (keptNo (membersTrue S old) a) noId =
        old.layout.members[keptNo (membersTrue S old) a] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem t1]
      rfl
    rw [shapeOf_true, pair_at old hsz _ t1, ← t2, em]
    rfl
  have es : (sizesAt S old T).kept.getD a {} = (S.oracles.getD o default).shape :=
    (sizesKept_true S old T a hsz).trans es'
  rw [e, hc, hcode, hmask, keptTrue_list S old T]
  refine (frozen_entryIn (sizesAt S old T) _ hp a i (by
    show i < 2 ^ (ceilLog2 ((sizesAt S old T).kept.getD a {}).mainRows +
      (S.codes.base.getD old.code default).logEll)
    rw [es]
    exact hi)).trans ?_
  unfold Held.entryIn
  split
  · rename_i hb
    rw [es] at hb
    unfold VerifiableInference.Desc.K2.Honest.Held.entry
    show (R.rows.getD (keptNo (membersTrue S old) a) zeroMessage).main
      ((VerifiableInference.Desc.K2.Honest.shapeOf (membersTrue S old)
        (keptNo (membersTrue S old) a)).mainDeg == 3) _ _ = _
    rw [es', es]
    have h1 := hM _ _ (i / 2 ^ ceilLog2 (S.oracles.getD o default).shape.mainRows) t1
      (by rw [t2]; exact hb)
    rw [t2, Nat.mod_add_div'] at h1
    exact h1
  · rename_i hb
    rw [es] at hb
    refine (hP o .main i ?_).symm
    unfold OnBytes.Means.realRows Statement.rowBits
    cases hx : S.oracles[o]? with
    | none => exact Nat.zero_le _
    | some x =>
      have : (S.oracles.getD o default).shape = x.shape := by
        rw [Array.getD_eq_getD_getElem?, hx]
        rfl
      rw [this] at hb
      exact Nat.le_of_not_lt hb

/-- hE AND hs ARE PREMISES. **A ROW THAT READS THE MESSAGE o's MAIN TABLE ALONE SAYS OF `oldWords`
WHAT IT SAYS OF THE WORDS**, o the kept member a, where each entry of W there is the words'. -/
theorem says_old_of_words (S : Statement) (Z : Sizes) (old : SingleRows) (W : Left) (w : Words GE)
    {a o : Nat} (hidx : (switchKept old).toList.idxOf? o = some a) {r : OnBytes.Row}
    (hr : readsMain o r = true)
    (hE : ∀ i, i < tableSize S o .main → (W.kept a).entryIn (Z.kept.getD a {}) i = w o .main i)
    (hs : Says rdE S r w) : Says rdE S r (oldWords Z old W) := by
  have hN : VerifiableInference.Desc.First.Close.NamesOne r o := fun o' hne part e =>
    reads_off o r hr o' part e (fun h => hne h.1)
  have hz : ∀ (m : Words GE), onTable rdE S r m o .mask = 0 := fun m => by
    unfold onTable
    refine Finset.sum_eq_zero fun i _ => ?_
    show readE (r.coefficient o .mask i) * _ = 0
    have := reads_off o r hr o .mask i (fun h => by cases h.2)
    rw [show readE (r.coefficient o .mask i) = 0 from this, zero_mul]
  unfold Says at hs ⊢
  rw [ProofFile.Honest.K1.value_named S r o hN, hz, add_zero] at hs ⊢
  rw [← hs]
  unfold onTable
  refine Finset.sum_congr rfl fun i hi => ?_
  have e : oldWords Z old W o .main i = w o .main i := by
    unfold oldWords
    rw [hidx]
    exact hE i (Finset.mem_range.1 hi)
  rw [e]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.frozen_entryIn
#print axioms ProofFile.Honest.K2.Law.kept_member
#print axioms ProofFile.Honest.K2.Law.kept_entry_words
#print axioms ProofFile.Honest.K2.Law.says_old_of_words
