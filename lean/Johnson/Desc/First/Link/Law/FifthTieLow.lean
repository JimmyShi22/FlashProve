-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieLow.lean: THE TWO PREMISES OF THE FIFTH TIE AT K9's FOUR PLACES
THAT READ THE PLAN's NUMBERS: `lowItem` ("every tree that a rider's pins name lies below the piece's
first tree": `t5_quiet`, FifthTie.lean; `t5_eq`, FifthTieEq.lean) and `OwnNotIndex` ("no message of
the link's own is the index masks' message": `t5_eq`): EACH EXCHANGED FOR A TEST WITH CODE ON PUBLIC
DATA. Definitions and theorems.

What is said.
  `lowB N base i`, `lowItem_of_B`: `lowItem` with code. `lowAtB N base k`: over the list of riders
at
    place k of the written full list (`ridersAt`, FifthTieRiders.lean). `riders_low`: its yes gives
    `lowItem` of every rider in the rule's own letters.
  `hO_quiet`, `hO_eq`: **the premise hO of `t5_quiet` and of `t5_eq`, whole, to the letter**, at the
75
    quiet places and the 25 places of the one equation: from the kernel's two facts on the table
    (`riders_quiet`, `riders_eq`) and that one test.
  `ownNotIndexB d m t n`: no number of `d.ownAt m t` is n. `ownNotIndex_reached`: **`OwnNotIndex` at
a
    reached state**: from the field frameIs of `FoldFacts`, "the state's number of the index masks'
    message is n" (the promise's public item indexIs says it), and that test.

Limits. The two tests have run at no data. base is a letter: that it is the piece's own first tree,
and what that is by the plan, is not said here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTieRiders
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS messageNow)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Numbers start FoldData FoldFacts momentAt shiftAt)
open Johnson.Desc.First.Walk.Tied

/-- `lowItem` at "below base", with code. -/
def lowB (N : Numbers) (base : ℕ) : Item → Bool
  | .pin m t => (N.sent m t).all fun x => decide (x.1 < base)
  | .pinKept m => (N.keptOf m).all fun x => decide (x.1 < base)
  | .pinI => decide (N.index.1 < base)
  | .pinV => decide (N.w.1 < base)
  | _ => true

theorem lowItem_of_B {N : Numbers} {base : ℕ} {i : Item} (h : lowB N base i = true) :
    lowItem N (fun j => j < base) i := by
  cases i <;>
    first
    | trivial
    | (simp only [lowB, List.all_eq_true, decide_eq_true_eq] at h
       exact h)

/-- Over the riders at place k. -/
def lowAtB (N : Numbers) (base k : ℕ) : Bool := (ridersAt k).all (lowB N base)

theorem riders_low {N : Numbers} {base k : ℕ} (hk : k ≤ plF.length)
    (h : lowAtB N base k = true) {i : Item}
    (ho : openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i)
    (hn : ¬ insQ linksFull plF k i) : lowItem N (fun j => j < base) i :=
  lowItem_of_B (List.all_eq_true.1 h i (rider_mem hk ho hn))

/-- **hO OF `t5_quiet`, WHOLE.** -/
theorem hO_quiet {N : Numbers} {base k : ℕ} (hk : k ∈ quietAt) (h : lowAtB N base k = true) :
    ∀ i, openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i →
      ¬ insQ linksFull plF k i → (i.part = none ∨ ∃ m, i = .wo m) ∧ notOwn ownDigits i ∧
        lowItem N (fun j => j < base) i :=
  fun _ ho hn => ⟨(riders_quiet hk ho hn).1, (riders_quiet hk ho hn).2,
    riders_low (quietAt_le hk) h ho hn⟩

/-- **hO OF `t5_eq`, WHOLE.** -/
theorem hO_eq {N : Numbers} {base k : ℕ} (hk : k ∈ eqAt) (h : lowAtB N base k = true) :
    ∀ i, openAfter (insQ linksFull plF) (outsQ linksFull plF) (· ∈ start linksFull) k i →
      ¬ insQ linksFull plF k i → pushRider i = true ∧ notOwn ownDigits i ∧
        lowItem N (fun j => j < base) i :=
  fun _ ho hn => ⟨(riders_eq hk ho hn).1, (riders_eq hk ho hn).2,
    riders_low (eqAt_le hk) h ho hn⟩

/-- No number of the segment's own messages is n. -/
def ownNotIndexB (d : FoldData) (m t n : ℕ) : Bool := (d.ownAt m t).all fun o => o != n

/-- **`OwnNotIndex` AT A REACHED STATE.** -/
theorem ownNotIndex_reached {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) {k : ℕ} {a : X} {p : Place} {m n : ℕ}
    (hR : Rch k a) (hu : (at_ a).2.failed = none) (hp : ps[k]? = some p) (hl : p.link = some m)
    (hpc : p.piece ≤ 11 + 2 * shiftAt links m) (hIx : (at_ a).2.out.indexMasks = n)
    (T : ownNotIndexB d m (momentAt (shiftAt links m) p.piece) n = true) :
    OwnNotIndex (at_ a).2 := by
  intro pa hpa j o hmn hEq
  have hL := (part_reads _ pa hpa).1
  obtain ⟨-, h2, -, h4⟩ := FF.frameIs k a p m pa.L hR hu hp hl hL
  obtain ⟨-, h6⟩ := h4 hpc
  have e : (ReqNext.laterOrClose != ReqNext.laterOrClose) = false := by decide
  unfold messageNow at hmn
  rw [h6, e] at hmn
  simp only [Bool.false_eq_true, if_false, beq_self_eq_true, if_true] at hmn
  rw [h2] at hmn
  have hmem : o ∈ d.ownAt m (momentAt (shiftAt links m) p.piece) :=
    Array.mem_of_getElem? hmn
  have h1 := Array.all_eq_true'.1 T o hmem
  rw [hEq, hIx] at h1
  simp at h1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.lowItem_of_B
#print axioms VerifiableInference.Desc.LinkJoin.hO_quiet
#print axioms VerifiableInference.Desc.LinkJoin.hO_eq
#print axioms VerifiableInference.Desc.LinkJoin.ownNotIndex_reached
