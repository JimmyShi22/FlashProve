-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TablesAtRchAll.lean: THE INVARIANT `TablesOk` AT ALL FOUR BORDERS OF EACH
SEGMENT's TWO LATER SENDINGS OF KIND K1, ALONG REACHED STATES INSIDE THE PROMISE: IN THE LETTERS
OF THE THIRD CLAUSE OF THE PREMISE hFacts OF KIND K1's FIFTY (`k01_fifty_atBase`,
Johnson/Desc/K1/Law/K01FiftyAtBase.lean). Statements with their proofs. `low_not_head`: the first
  24 segments are no head: by evaluation. `tables_front_reads_low`: in front of the reads' place
  of a segment l < 24: the promise's own test on where the state stands says "in a segment of that
  sort" (`stand_of_promise`, Johnson/Desc/K1/Law/ArmBySort.lean): no head: so no
  tables of a head (`tablesOk_none`). `tablesOk_at_rch`: **all hundred borders**: three of four
  from the scope alone (`tables_three_rchAt`, Johnson/Desc/AtSeats/TablesAtRch.lean); the fourth
  at l < 24 off the promise; ONE PREMISE IS LEFT: h342: the fourth at the output head's segment
  (number 342).
What is not claimed. h342. That the scope can be met. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.AtSeats.TablesAtRch
import Johnson.Desc.K1.Law.ArmBySort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Desc.First.Walk.Tied (RchAt)
open VerifiableInference.Desc (Block Chain FileDescription Strs)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning flatPlacesOf standOf)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open IM (Open k1Ix)
open ProofFile (Cl)

theorem low_not_head : ∀ l < 24, (linksFull[l]?).getD .layers ≠ ModelPart.head := by decide

/-- **In front of the reads' place of a segment that is no head.** -/
theorem tables_front_reads_low {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W} (h : Head.Shape)
    (L : Head.HL) (hp : Head.HPlanH2) (l : ℕ) (hl : l < 24) (x : Pp × S) (y : Strs)
    (hIn : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l false) x y) :
    TablesOk h L hp x.2 := by
  intro a t ha _
  have hs := stand_of_promise l (by omega) x y hIn
  unfold standOf at hs
  rw [ha] at hs
  dsimp only at hs
  split at hs
  · exact absurd (First.Stand.link.inj hs).symm (low_not_head l hl)
  · cases hs

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **All hundred borders.** -/
theorem tablesOk_at_rch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (h342 : ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        342 a → a.1.2.failed = none → TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.1.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        j a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
      TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.1.2 := by
  intro l hl d j hj a hr hon hm
  cases d with
  | true =>
    exact tables_three_rchAt hS hR O l hl j
      (hj.elim (fun e => .inr (.inl e)) fun e => .inr (.inr e)) a hr
  | false =>
    rcases hj with rfl | rfl
    · by_cases h24 : l = 24
      · subst h24
        exact h342 a hr hm
      · exact tables_front_reads_low _ _ _ l (by omega) a.1 _ ⟨hon, hm⟩
    · exact tables_three_rchAt hS hR O l hl _ (.inl rfl) a hr

end

end VerifiableInference.Desc.K1
