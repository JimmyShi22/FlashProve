-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB9/FileRead.lean: SEVEN OF THE NAMED TESTS ON A KEY FILE's SOURCE
(`sourceClauses`, Johnson/Desc/Key/Source.lean; one of `shapeClauses`, Johnson/Desc/Key/FileOk.lean)
AS LAWS, general in the chains; nothing is asked of Lean's kernel. Three follow from one fact alone,
that `KeyChains.read` returned these three chains: "setting", "read" and the tenth of
`shapeClauses`: they read the chains' parameter bytes, the digest and the items' bytes, which no
written value can answer. Two follow from that fact and one equation each: "codes", "shape". Two
follow from plain equations alone, without that fact: "cut", "binding".

  `read_guard`: what `KeyChains.read` (OnBytes/Params/Chains.lean) itself tests before it returns:
    one setting in the three chains; the same items "codes" and "the test on the table" in the first
    two; no entry for a table's own sample in the later two. It is the tenth of `shapeClauses` to
    the letter.
  `setting_ok`: the clause "setting". `codes_ok`, `shape_ok`: the clauses "codes" and "shape", where
    the two chains' values are one.
  `items_self`, `sameGiven_self`, `sameKeyChains_self`: the test `==` finds a thing equal to itself,
    at the items, at a chain's parameters, at three chains.
  `read_ok`: the clause "read": the bytes that the chains hold are the bytes that were read
    (`Given.read_bytes`, OnBytes/Params/Laws.lean), so reading them again returns the same chains.
  `cut_ok`, `binding_ok`: the clauses "cut" and "binding", from plain equations.

Each ends in the clause's own expression, as it stands in the list, "= true".

Limits. That the reader returns is a premise. The equations are premises. Nothing on soundness.

-/
import Johnson.Desc.Key.Source
import OnBytes.Model.ReadBackMade
import OnBytes.Params.ReadBackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB9
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (KeySource sameGiven sameKeyChains readAgainOk)

/-- **What the reader of a key's three chains tests before it returns.** -/
theorem read_guard {b₁ b₂ b₃ : ByteArray} {k : KeyChains}
    (h : KeyChains.read b₁ b₂ b₃ = some k) :
    (sameSetting k.oneTime.given k.shared.given && sameSetting k.oneTime.given k.second.given &&
        sameItem k.oneTime.given k.shared.given "codes" &&
        sameItem k.oneTime.given k.shared.given "the test on the table" &&
      k.shared.given.record.isNone && k.second.given.record.isNone) = true := by
  unfold KeyChains.read at h
  obtain ⟨a, _, h⟩ := opt_bind h
  obtain ⟨b, _, h⟩ := opt_bind h
  obtain ⟨c, _, h⟩ := opt_bind h
  split at h
  · rename_i hg
    cases h
    exact hg
  · cases h

/-- The clause "setting". -/
theorem setting_ok {b₁ b₂ b₃ : ByteArray} {k : KeyChains}
    (h : KeyChains.read b₁ b₂ b₃ = some k) :
    (sameSetting k.oneTime.given k.shared.given && sameSetting k.oneTime.given k.second.given &&
        k.shared.given.record.isNone && k.second.given.record.isNone) = true := by
  have g := read_guard h
  simp only [Bool.and_eq_true] at g ⊢
  exact ⟨⟨⟨g.1.1.1.1.1, g.1.1.1.1.2⟩, g.1.2⟩, g.2⟩

/-- The clause "codes". -/
theorem codes_ok {b₁ b₂ b₃ : ByteArray} {k : KeyChains} (h : KeyChains.read b₁ b₂ b₃ = some k)
    (e : k.oneTime.codes = k.shared.codes) :
    (sameItem k.oneTime.given k.shared.given "codes" && k.oneTime.codes == k.shared.codes) =
      true := by
  have g := read_guard h
  simp only [Bool.and_eq_true] at g ⊢
  exact ⟨g.1.1.1.2, beq_iff_eq.2 e⟩

/-- The clause "shape". -/
theorem shape_ok {b₁ b₂ b₃ : ByteArray} {k : KeyChains} (h : KeyChains.read b₁ b₂ b₃ = some k)
    (e : k.oneTime.lin = k.shared.lin) :
    (sameItem k.oneTime.given k.shared.given "the test on the table" &&
      k.oneTime.lin == k.shared.lin) = true := by
  have g := read_guard h
  simp only [Bool.and_eq_true] at g ⊢
  exact ⟨g.1.1.2, beq_iff_eq.2 e⟩

/-! ## A thing against itself -/

/-- At a list of items. -/
theorem items_self : ∀ l : List (String × ByteArray), (l == l) = true
  | [] => rfl
  | x :: l => by
    have hx : (x == x) = true := by
      show (x.1 == x.1 && x.2 == x.2) = true
      rw [beq_self_eq_true, beq_self_bytes]
      rfl
    show (x == x && l == l) = true
    rw [hx, items_self l]
    rfl

/-- At a chain's parameters as read. -/
theorem sameGiven_self (g : Given) : sameGiven g g = true := by
  unfold sameGiven
  rw [beq_self_bytes, beq_self_bytes, items_self]
  simp

/-- At a key's three chains. -/
theorem sameKeyChains_self (k : KeyChains) : sameKeyChains k k = true := by
  unfold sameKeyChains
  rw [sameGiven_self, sameGiven_self, sameGiven_self]
  simp

/-- **The clause "read".** -/
theorem read_ok {b₁ b₂ b₃ : ByteArray} {k : KeyChains} (h : KeyChains.read b₁ b₂ b₃ = some k) :
    readAgainOk k = true := by
  obtain ⟨r1, r2, r3, -⟩ := KeyChains.read_three h
  have e1 := Given.read_bytes (OneTime.read_given r1)
  have e2 := Given.read_bytes (Shared.read_given r2)
  have e3 := Given.read_bytes (Second.read_given r3)
  unfold readAgainOk
  rw [e1, e2, e3, h]
  exact sameKeyChains_self k

/-! ## From plain equations -/

/-- The clause "cut". -/
theorem cut_ok {Y : KeySource} (h1 : Y.cutShape = Y.k.oneTime.lin)
    (h2 : Y.cutCodes.1 = Y.k.oneTime.codes) (h3 : Y.cutCodes.2.1 = Y.k.oneTime.codes)
    (h4 : Y.cutCodes.2.2 = Y.k.oneTime.codes) (h5 : Y.cutIdx = Y.k.oneTime.indexMasks)
    (h6 : Y.cutRanges = Y.k.oneTime.ranges)
    (h7 : Y.cutSamples = Y.k.oneTime.given.plan.samples) :
    (Y.cutShape == Y.k.oneTime.lin && Y.cutCodes.1 == Y.k.oneTime.codes &&
        Y.cutCodes.2.1 == Y.k.oneTime.codes &&
        Y.cutCodes.2.2 == Y.k.oneTime.codes && Y.cutIdx == Y.k.oneTime.indexMasks &&
        Y.cutRanges == Y.k.oneTime.ranges &&
        Y.cutSamples == Y.k.oneTime.given.plan.samples) = true := by
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨beq_iff_eq.2 h1, beq_iff_eq.2 h2⟩, beq_iff_eq.2 h3⟩, beq_iff_eq.2 h4⟩,
    beq_iff_eq.2 h5⟩, beq_iff_eq.2 h6⟩, beq_iff_eq.2 h7⟩

/-- The clause "binding". -/
theorem binding_ok {k : KeyChains} (h : k.oneTime.binding.logLeaves = 0) :
    (k.oneTime.binding.logLeaves == 0) = true := beq_iff_eq.2 h

end Johnson.KB9

#print axioms Johnson.KB9.read_guard
#print axioms Johnson.KB9.setting_ok
#print axioms Johnson.KB9.codes_ok
#print axioms Johnson.KB9.shape_ok
#print axioms Johnson.KB9.items_self
#print axioms Johnson.KB9.sameGiven_self
#print axioms Johnson.KB9.sameKeyChains_self
#print axioms Johnson.KB9.read_ok
#print axioms Johnson.KB9.cut_ok
#print axioms Johnson.KB9.binding_ok
