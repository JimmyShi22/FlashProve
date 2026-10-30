-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Free15.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE PROMISE's LAST LETTER's STEP: the fact (free) of fwd_of_facts (Johnson/RunOne/Law/K12FwdFacts.lean): free₁ at border 15 in front gives free₁ at border 16 behind, under the strings' staying, at the block's own decide's yes. One statement with its proof.
OBJECT. free₁ (Johnson/RunOne/KeyRows1At.lean), conjunct by conjunct. USER. Whoever fills fwd_of_facts' hdec.
LETTERS. The tables' own. Premises: hl: two lookups · hp: the block's test on the plan · hd: the held block's yes · hrec: THE READING's recOf SAYS THE SAME OF BOTH RECORDS (a premise on the tables' letter B.h₁: the second half of SamePins, Johnson/Desc/Key/KeyFrames.lean) · hcoll: a collision is read off the cells alone (what CellOnly coll, Johnson/RunOne/KeyKeeps23.lean, gives) · hord: the statement stays in order across the test (Means.InOrder): ranges_inOrder (Johnson/RunOne/Law/K12Order.lean) gives it where the codes' lengths are in order and the state before the test is in order.
HOW EACH CONJUNCT GOES. FreeAt: hrec, hcoll at the cells' staying · ArrOk, ReadsPinned: they read no state · Placed: K12's files' OutK.book: each place stands · the three "18 ≤ 16 → …" and "2 ≤ 16 ∧ 16 ≤ 15 → …": empty · SampleIn behind: BY ITS TEXT it is the field samples of Means.InOrder at that message · InOrder: hord · ShownAt: the words' staying · the key fits: the instance is handed on.
Limits. A block that says no to all meets the statement. Three premises are left. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Shape15
import Johnson.RunOne.KeyRowsAtFk
import Johnson.RunOne.Sound.KeyMapAtFK
import Johnson.Desc.Key.KeyQuiet
import Johnson.Desc.Plain.PaidKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

namespace Johnson.RunOne.Law.K12Free15
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt Fk oneAt)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ open₁ free₁)
open Johnson.RunOne.Law.K12Shape15 (out_of_yes)

/-- At two lookups the pins open at border 16 are among those open at 15: by evaluation. (K12FwdFacts.lean's pins_sub, typed again so that this file stands free of the top's files.) -/
theorem pins_sub : ∀ k ∈ pinned (open₁ 2 16), k ∈ pinned (open₁ 2 15) := by decide

variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
  (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- **The promise's last letter's step across the ranges' test.** -/
theorem free_15_16 (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hp : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true)
    (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b)
    (hrec : B.h₁.recOf b = B.h₁.recOf a) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (hord : Means.InOrder a.2.d.st → Means.InOrder b.2.d.st) :
    ∀ y y', StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) y y' → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y →
      free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 b y' := by
  intro y y' Hy hf
  obtain ⟨f1, f2, f3, _, _, _, f7, f8, f9, _, _⟩ := hf
  obtain ⟨e1, hd'⟩ := held_decide _ a rs gs b hd
  have hy : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide a.2 rs gs = .ok b.2 := hd'
  obtain ⟨tE, G, e, _, k1, _, _, _⟩ := out_of_yes hp hy
  have eb : b.2.d.book = tE.book := by rw [e]
  have hI := hord f7
  have hn : n₁ (oneAt X) = 2 := hl
  refine ⟨?_, f2, ?_, fun h => absurd h (by omega), ?_, fun h => absurd h (by omega), hI, ?_, ?_, fun h => absurd h.2 (by omega), fun h => absurd h (by omega)⟩
  · obtain ⟨r, hr, hc⟩ := f1
    exact ⟨r, hrec.trans hr, fun c => hc (hcoll y y' r Hy.cell c)⟩
  · intro k hk
    obtain ⟨o, t, h1, h2, h3⟩ := f3 k (pins_sub k hk)
    refine ⟨o, t, h1, ?_, h3⟩
    show b.2.d.book.place[o]? = some t
    rw [eb]
    exact k1.book.place o t h2
  · intro j _ o _ x hx r hr
    exact hI.samples o x hx r hr
  · intro j hj
    exact shownAt_ride _ at_ j y y' (Hy.word j (by rw [hn]; exact pins_sub j hj)) (f8 j (pins_sub j hj))
  · rw [e1]
    exact f9

end Johnson.RunOne.Law.K12Free15

#print axioms Johnson.RunOne.Law.K12Free15.free_15_16
