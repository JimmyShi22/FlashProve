-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/StoredOfAnswers.lean: the kind "the code switch" (K2): THE
KEPT MEMBERS' STORED SAMPLE ROWS SAY TRUE OF `oldWords` AT WHAT THE CLOSING LEFT, WHERE EACH KEPT
MESSAGE HAS THE ANSWERS OF THE SAMPLE THAT THE STATEMENT HOLDS: at letters. One statement with its
proof: a join; no definition.

WHICH SLOT IT IS FOR. The field stored of the record `MadeAsks` (ExchangeAtMade.lean of this
folder), at a letter S: the field stands at the statement behind the joins, and the lock's limbs at
the front's: `says_of_shapes` (Johnson/Desc/Means/Forth/AllMet.lean) goes from the one to the other:
not called here; one of the four fields on values that `k2_exchange_of_values` (MadeValuesLeft.lean)
leaves. The exchange is one of the debts of the frame's `OwesS` at the first chain.

  `table_le`        a kept message's main table, by the group's code
  `stored_of_answers`   the lock's premises, and hAns: at each kept message, the reader of samples
                    returns a sample whose answers the words' message has ⊢ every stored sample row
                    of a kept member says true of `oldWords`

hAns IS THE LEFT SIDE OF `ans_iff_says`, at the statement's own reader of samples and the words. A
pin at the honest side's threads says the like IN OTHER TERMS: `AnsAt` (Honest/Thread/Ans.lean), at
a sending's list, the reading of the sample that the verifier's state holds and the witness's
message, at the item "pinKept", which the switch's joint takes in (Johnson/Desc/First/Borders.lean).
`kept_answers` (KeptAnswers.lean of this folder) goes from the one to the other.

By: `ans_iff_says` (Honest/K1/Law/SaysMeets.lean) · `kept_entry_words`, `says_old_of_words`
(KeptWords.lean of this folder) · `reads_off` (Johnson/Desc/K2/Honest/Inner/SampleHold.lean) ·
`Lists.idxOf_at` (Inner/Words.lean).

Limits. ALL ARE PREMISES: the lock's, Padded, one stored row a kept message (`one_stored_at_switch`,
AtYesRows.lean, has it at a switch of the plan), that such a row reads that message's main table
alone, the two lengths, that a kept message has the group's main code, and hAns. Who has something
toward them: Padded at the words that a witness gives: `padded_first`
(Johnson/Desc/K10/Honest/CarryOf.lean); the rest is public, and StoredAtYes.lean of this folder pays
them at a switch. k, A LETTER HERE, HANDS THE CLOSING ITS COINS; hR READS EVERY ENTRY OF A MEMBER's
MAIN ROWS, ALSO WHERE A PAD LIES: entries that hold coins: equations between two texts' values: what
is WRITTEN where. One run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeptWords
import Johnson.Desc.ProofFile.Honest.K1.Law.SaysMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (GE readE rdE)
open OnBytes.Means (Words Says Padded tableSize)
open Johnson.Pack (portOmZ partZ locZ pMain pMask)
open VerifiableInference.Desc.K1 (smpAt)
open VerifiableInference.Desc.K2.Honest (Left sizesAt oldWords membersTrue reads_off)
open VerifiableInference.Desc.First.K2Hands (readsMain)

/-- **A kept message's main table is no larger than the group's code says**, where the message has
the group's main code. -/
theorem table_le (S : Statement) (old : SingleRows) (o : Nat) (x : Oracle)
    (hx : S.oracles[o]? = some x) (hc : x.shape.code = old.code) :
    tableSize S o .main ≤ 2 ^ (ceilLog2 x.shape.mainRows +
      (S.codes.base.getD old.code default).logEll) := by
  unfold tableSize
  split
  · rename_i hh
    unfold Statement.has at hh
    rw [hx] at hh
    have hpos : 0 < x.shape.rows .main := of_decide_eq_true hh
    have hne : (x.shape.rows .main == 0) = false := by
      cases e : x.shape.rows .main with
      | zero => rw [e] at hpos; exact absurd hpos (Nat.lt_irrefl _)
      | succ n => rfl
    unfold Statement.tableBits Statement.rowBits Statement.placeBits
    rw [hx]
    simp only [hne, Bool.false_eq_true, if_false, hc]
    exact Nat.le_refl _
  · exact Nat.zero_le _

/-- ALL ARE PREMISES. One run's coins: never quoted for a law. **Every stored sample row of a kept
member says true of `oldWords`.** W: what `segmentLeft` returned. -/
theorem stored_of_answers (S : Statement) (old : SingleRows) (T : SwitchTarget)
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
    (hP : Padded S w)
    (once : (switchKept old).toList.Nodup)
    (hlt : ∀ o ∈ (switchKept old).toList, o < S.oracles.size)
    (hone : ∀ o ∈ (switchKept old).toList, (S.oracles.getD o default).sampleRows.size = 1)
    (hread : ∀ o ∈ (switchKept old).toList, ∀ r ∈ (S.oracles.getD o default).sampleRows.toList,
      readsMain o r = true)
    (hcodeK : ∀ o ∈ (switchKept old).toList, (S.oracles.getD o default).shape.code = old.code)
    (hlM : ∀ o ∈ (switchKept old).toList, ∀ x : Oracle, S.oracles[o]? = some x →
      0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : ∀ o ∈ (switchKept old).toList, ∀ x : Oracle, S.oracles[o]? = some x →
      0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (hAns : ∀ o ∈ (switchKept old).toList, ∀ x : Oracle, S.oracles[o]? = some x →
      ∃ (e : Nat) (z : (portOmZ S.codes x.shape e).Smp), smpAt S.codes x.shape e S o = some z ∧
        (portOmZ S.codes x.shape e).Z.val z.1
          (fun j => w o (partZ S.codes x.shape j) (locZ S.codes x.shape j)) = z.2) :
    ∀ o ∈ (switchKept old).toList, ∀ r ∈ (S.oracles.getD o default).sampleRows.toList,
      Says rdE S r (oldWords (sizesAt S old T) old W) := by
  intro o ho r hr
  obtain ⟨a, ha⟩ := List.getElem?_of_mem ho
  have hidx := VerifiableInference.Desc.K2.Honest.Lists.idxOf_at _ a o once ha
  have hx : S.oracles[o]? = some (S.oracles[o]'(hlt o ho)) :=
    Array.getElem?_eq_getElem (hlt o ho)
  have eg : S.oracles.getD o default = S.oracles[o]'(hlt o ho) := by
    rw [Array.getD_eq_getD_getElem?, hx]
    rfl
  have h1 := hone o ho
  have hr' := hr
  rw [eg] at h1 hr'
  have r0 : (S.oracles[o]'(hlt o ho)).sampleRows[0]? = some r := by
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hr'
    have hjl := (List.getElem?_eq_some_iff.1 hj).1
    have hj0 : j = 0 := by
      rw [Array.length_toList, h1] at hjl
      omega
    subst hj0
    rw [← Array.getElem?_toList]
    exact hj
  have hN : VerifiableInference.Desc.First.Close.NamesOne r o := fun o' hne part e =>
    reads_off o r (hread o ho r hr) o' part e (fun h => hne h.1)
  obtain ⟨e, z, hz, hv⟩ := hAns o ho _ hx
  have hsay := (ProofFile.Honest.K1.ans_iff_says S o _ hx r r0 hN (hlM o ho _ hx) (hlZ o ho _ hx) w hP e z
    hz).1 hv
  exact says_old_of_words S (sizesAt S old T) old W w hidx (hread o ho r hr)
    (fun i hi => kept_entry_words S old T w h hc hcode hmask hsz hp hR hP ha i
      (by
        rw [eg]
        have hc' := hcodeK o ho
        rw [eg] at hc'
        exact Nat.lt_of_lt_of_le hi (table_le S old o _ hx hc'))) hsay

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.table_le
#print axioms ProofFile.Honest.K2.Law.stored_of_answers
