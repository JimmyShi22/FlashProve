-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Item/ItemSaysNo.lean: the comparison of the item "request" with the public part can
refuse: negative facts at `Verify.statementHeld` itself.

Main names.
* `agree_of_held`: two strings that the comparison accepts at one public part agree in their length
  and in every word that it reads: the words 2 to 94, 103 to 162 and 172 to 176. So a string that
  parts from an accepted one in one numeral, one word of a table's digest or one word of a digest of
  call lines is refused.
* `gap_item_refused`: at the public part of `VerifierAndGoals.storedPublicFiles` the comparison refuses every item that is
  made of `VerifierAndGoals.zGap`'s files. `full_item_refused`: the like with the two sets of files in each
  other's places. The makers return at both sets: so the comparison tells two parameter files apart
  that differ in the policy's three numbers.

How. `clauses_of_held` and `word_of_names` (Johnson/AtFull/Item/HeldOfParts.lean): word 148 of an
accepted item is the scan's value of the line C. It is 256 at one scan and 25856 at the other.

Limits. Negative tests beside Johnson/AtFull/Item/ItemAtFull.lean and ItemAtGap.lean. The refused
pairs are no files of one set: that the comparison refuses at any public files with their own item
is not shown, and at these two sets it does not. hsz and hX are premises. No soundness is claimed.
-/
import Johnson.AtFull.Item.ItemAtGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Item
open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Verify OnBytes.K
open VerifiableInference.PlanWritten
open OnBytes.Road.K4.Trial.Values (PW)

/-- **Two accepted strings agree in every word that the comparison reads.** -/
theorem agree_of_held {X : Public} {a b : ByteArray} (ha : statementHeld X a = .ok ())
    (hb : statementHeld X b = .ok ()) :
    a.size = b.size ∧ (∀ k, k < 27 → wordsAt a (2 + k) 1 = wordsAt b (2 + k) 1) ∧
      wordsAt a 29 8 = wordsAt b 29 8 ∧
      (∀ k, k < 34 → wordsAt a (37 + k) 1 = wordsAt b (37 + k) 1) ∧
      wordsAt a 71 8 = wordsAt b 71 8 ∧ wordsAt a 79 8 = wordsAt b 79 8 ∧
      wordsAt a 87 8 = wordsAt b 87 8 ∧
      (∀ k, k < 11 → wordsAt a (103 + k) 1 = wordsAt b (103 + k) 1) ∧
      wordsAt a 114 8 = wordsAt b 114 8 ∧ wordsAt a 122 8 = wordsAt b 122 8 ∧
      (∀ k, k < 25 → wordsAt a (130 + k) 1 = wordsAt b (130 + k) 1) ∧
      wordsAt a 155 8 = wordsAt b 155 8 ∧ wordsAt a 172 1 = wordsAt b 172 1 ∧
      wordsAt a 173 1 = wordsAt b 173 1 ∧ wordsAt a 174 1 = wordsAt b 174 1 ∧
      wordsAt a 175 1 = wordsAt b 175 1 ∧ wordsAt a 176 1 = wordsAt b 176 1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ :=
    clauses_of_held ha
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17⟩ :=
    clauses_of_held hb
  exact ⟨a1.trans b1.symm,
    fun k hk => (word_of_names names2_list a2 k hk).trans (word_of_names names2_list b2 k hk).symm,
    a3.trans b3.symm,
    fun k hk =>
      (word_of_names names37_list a4 k hk).trans (word_of_names names37_list b4 k hk).symm,
    Option.some.inj (a5.symm.trans b5), Option.some.inj (a6.symm.trans b6),
    Option.some.inj (a7.symm.trans b7),
    fun k hk =>
      (word_of_names names103_list a8 k hk).trans (word_of_names names103_list b8 k hk).symm,
    Option.some.inj (a9.symm.trans b9), a10.trans b10.symm,
    fun k hk =>
      (word_of_names names130_list a11 k hk).trans (word_of_names names130_list b11 k hk).symm,
    a12.trans b12.symm, a13.trans b13.symm, a14.trans b14.symm, a15.trans b15.symm,
    a16.trans b16.symm, a17.trans b17.symm⟩

/-- Word 148 of an accepted item is the scan's value of the line C. -/
theorem word_C {X : Public} {it : ByteArray} (h : statementHeld X it = .ok ()) :
    wordsAt it 148 1 = word32 (X.P.value "C") :=
  word_of_names names130_list (clauses_of_held h).2.2.2.2.2.2.2.2.2.2.1 18 (by decide)

/-- The two scans' values of the line C, and that their words differ. -/
theorem values_C : PW.value "C" = 256 ∧ (PW.withPol 25856 512 1).value "C" = 25856 ∧
    word32 256 ≠ word32 25856 := by
  decide +kernel

/-- **At the public part of `VerifierAndGoals.storedPublicFiles` every item made of `VerifierAndGoals.zGap`'s files is refused.** -/
theorem gap_item_refused (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) (req it : ByteArray)
    (hit : Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL req = some it) :
    statementHeld X₀ it ≠ .ok () := by
  intro hok
  have hG := LPFPol.gap_of_full hX
  rw [← VerifierAndGoals.lay_zGap] at hG
  obtain ⟨eP', hP, hT⟩ := facts_zGap hsz hG
  have eP : X₀.P = PW :=
    Except.ok.inj ((publicOfO_scan hX).symm.trans OnBytes.Road.K4.Trial.Values.scan_zFull)
  by_cases hs : req.size = 4 * (2 ^ 10 + 2)
  · obtain ⟨it', h1, h2⟩ := item_zGap hsz hG req (by rw [hT]; exact hs)
    obtain rfl := Option.some.inj (h1.symm.trans hit)
    have a := word_C hok
    have b := word_C h2
    rw [eP, values_C.1] at a
    rw [eP', values_C.2.1] at b
    exact values_C.2.2 (a.symm.trans b)
  · rw [← OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq, requestItem_eq_itemWith,
      none_of_length hP hs] at hit
    cases hit

/-- **At the public part of `VerifierAndGoals.zGap` every item made of `VerifierAndGoals.storedPublicFiles`'s files is refused.** -/
theorem full_item_refused (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {X : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL (some VerifierAndGoals.zGap.lay) = .ok X)
    (req it : ByteArray)
    (hit : Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL req = some it) :
    statementHeld X it ≠ .ok () := by
  intro hok
  obtain ⟨X₀, hX₀, -⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  obtain ⟨eP', -, -⟩ := facts_zGap hsz hX
  have eP : X₀.P = PW :=
    Except.ok.inj ((publicOfO_scan hX₀).symm.trans OnBytes.Road.K4.Trial.Values.scan_zFull)
  by_cases hs : req.size = 4 * (2 ^ 10 + 2)
  · obtain ⟨it', h1, h2⟩ := item_zFull hsz hX₀ req (by rw [tokens_zFull hsz hX₀]; exact hs)
    obtain rfl := Option.some.inj (h1.symm.trans hit)
    have a := word_C h2
    have b := word_C hok
    rw [eP, values_C.1] at a
    rw [eP', values_C.2.1] at b
    exact values_C.2.2 (a.symm.trans b)
  · rw [no_item_zFull hsz hs] at hit
    cases hit

end Johnson.AtFull.Item

#print axioms Johnson.AtFull.Item.agree_of_held
#print axioms Johnson.AtFull.Item.word_C
#print axioms Johnson.AtFull.Item.values_C
#print axioms Johnson.AtFull.Item.gap_item_refused
#print axioms Johnson.AtFull.Item.full_item_refused
