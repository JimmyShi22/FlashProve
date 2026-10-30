-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReachAtHead.lean: THE PUBLIC FIELD reach OF THE PREMISE's FORM
`LaysFilling` (LaysFilling.lean in this folder) HOLDS AT THE SEATS THAT LIE TYPED IN THE FRAME's
FILES, WITH "no challenge has been heard": AT THE SEGMENTS 1 TO 23 AT THE SEAT OVER THE SWITCHES'
SENDINGS (`K2.switchSeat`, Johnson/Desc/ProofFile/Honest/K2/OwnData.lean); AT SEGMENT 0 AT THE SEAT
OF THE FIRST SEGMENT's OPENING (`K1.firstSeat`, Johnson/Desc/ProofFile/Honest/K1/FirstData.lean). On
public data alone. CONDITIONAL: under the hypothesis h, the library's head on the public input
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), but for three lemmas. IT PAYS NOTHING OF THE SCRIPT. Five
theorems.

What it is for. The form has two fields: reach, on public data; lays, on the script's text. At these
letters and segments this file pays the first: what is then left of the form is its sentence on the
script.

Main names:
  `reach_switchSeat`: **the sentence above.** G: the maker's own ground: it stands under "there is"
    and is pinned by `blankBy pureRoad.links Zp = some G`. One G for all N and l. The statement
    behind it is the field reach, at seat := `K2.switchSeat Zp G`, heard := fun _ => 0; this file
    does not import the form: that is read off the form's text.
  `reach_firstSeat`: **the like at segment 0**, at seat := `K1.firstSeat h.𝔇.sent.shape 0`, heard :=
    fun _ => 0: the letters of the frame's own filling there (`K1.firstFill`,
    Johnson/Desc/ProofFile/Honest/K1/PlaceFirst.lean). No opening is spent.
  `arrayMoment_zero`: at the library's written shape and layout each array that the values have
    (`cellsVals Sz.ref`) lies in a message of moment 0. `arrayMoment_written`: the same as one test
    with code: A CLOSED FACT, DECIDED BY EVALUATION IN LEAN's KERNEL, behind the library's rewriting
    of `toNat?` (`Johnson.Unfolds.slice_toNat?_eq`, Johnson/Unfolds/SliceFoldl.lean).
  `arrays_there`: that test does not hold of nothing: each segment from 0 to 23 of the written
    layout has an array that the values have: so the field reach is idle at none of them. A SECOND
    CLOSED FACT, decided in the same way.

How. `switchSeat_reaches` (SwitchReach.lean in this folder); `momentSeat_at`, `msgNo_of_moment`
(SeatReach.lean); `IM.Open.blank` (Johnson/IMR/SeatOpen.lean); the head's comparison with the
library's written values: `H2K5.Door.pins_at_head`, `made_row_gives`
(Johnson/Desc/First/Att/Door/Law/: K5CondOfHead.lean, K5Written.lean).

Limits. Two seats: segment 0 at one, the segments 1 to 23 at the other; these are all the segments
at which the form is asked for an attention segment's cells (2 g and 2 g + 1, g below 12). Not the
head's segment. At `Sz.ref`: in the frame's own filling at these seats the sizes are a letter.
`arrayMoment_written` and `arrays_there` have been checked by Lean's own kernel alone; the three
others rest on the first; `reach_switchSeat` and `reach_firstSeat` also on the head's comparison
with written values. Through its imports the file stands above Cb/Bridge/CodeListRSProved.lean, and
so above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier
hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SwitchReach
import Johnson.P5J.MgAtAll
import Johnson.Unfolds.SliceFoldl
import Johnson.G.LayoutLit
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile.Honest.K1 (labelNo cellsVals)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **At the library's written shape and layout each array that the values have lies in a message of
moment 0**, as one test with code. By evaluation in Lean's kernel. -/
theorem arrayMoment_written :
    (Johnson.G.layoutFull.link.zipIdx.all fun x => x.1.all fun A =>
      !((cellsVals Sz.ref).size x.2 A.name).isSome ||
        ((proofSizedFull.request.link.getD x.2 default).messages[A.message]?).any
          fun M => M.moment == 0) = true := by
  simp only [cellsVals, labelNo, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **NOT OF NOTHING: each segment from 0 to 23 of the written layout has an array that the values
have.** So the test above lets something through at every segment at which this file states the
field reach; the head's segment, 24, is left out here as there. By evaluation in Lean's kernel. -/
theorem arrays_there :
    ((List.range 24).all fun l => (Johnson.G.layoutFull.link.getD l []).any fun A =>
      ((cellsVals Sz.ref).size l A.name).isSome) = true := by
  simp only [cellsVals, labelNo, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **`arrayMoment_written`, read off.** Conditional: A is an array of segment l of the written
layout; the values have it. -/
theorem arrayMoment_zero {l : ℕ} {As : List OnBytes.Params.ReqArray} {A : OnBytes.Params.ReqArray}
    (hl : Johnson.G.layoutFull.link[l]? = some As) (hA : A ∈ As)
    (hz : ((cellsVals Sz.ref).size l A.name).isSome = true) :
    ∃ M, (proofSizedFull.request.link.getD l default).messages[A.message]? = some M ∧
      M.moment = 0 := by
  have H := arrayMoment_written
  rw [List.all_eq_true] at H
  have h1 := H (As, l) (List.mem_zipIdx_iff_getElem?.2 hl)
  rw [List.all_eq_true] at h1
  have h2 := h1 A hA
  simp only [hz, Bool.not_true, Bool.false_or] at h2
  cases hq : (proofSizedFull.request.link.getD l default).messages[A.message]? with
  | none =>
    rw [hq] at h2
    exact absurd h2 (by simp)
  | some M =>
    rw [hq] at h2
    exact ⟨M, rfl, beq_iff_eq.1 h2⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE FORM's PUBLIC FIELD AT THE SEAT OVER THE SWITCHES' SENDINGS, AT THE SEGMENTS 1 TO 23.**
CONDITIONAL: under the hypothesis h. -/
theorem reach_switchSeat :
    ∃ G : Ground, blankBy pureRoad.links Zp = some G ∧
      ∀ (N l : ℕ), 1 ≤ l → l < 24 → ∀ (As : List OnBytes.Params.ReqArray)
        (A : OnBytes.Params.ReqArray), h.𝔇.sent.layout.link[l]? = some As → A ∈ As →
        ((cellsVals Sz.ref).size l A.name).isSome = true →
        ∃ Ad : MsgAddr, K2.switchSeat Zp G Ad = some (l, A.message) ∧
          (fun _ : MsgAddr => 0) Ad ≤ N := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨Bs.G₀, IM.Open.blank O, fun N l h1 h24 As A hl hA hz => ?_⟩
  have hm := (H2K5.Door.pins_at_head h.toAtMg).1
  obtain ⟨-, -, f3, -, -, f6⟩ := (H2K5.Door.made_row_gives hm).1
  have el : h.𝔇.sent.layout = Johnson.G.layoutFull := f6
  rw [el] at hl
  obtain ⟨M, hM, h0⟩ := arrayMoment_zero hl hA hz
  rw [← f3] at hM
  obtain ⟨Ad, hAd⟩ := switchSeat_reaches h.scope h.reads O h.laid.planOk h1 h24 hM h0
  exact ⟨Ad, hAd, Nat.zero_le _⟩

/-- **THE FORM's PUBLIC FIELD AT SEGMENT 0, AT THE SEAT OF THE FIRST SEGMENT's OPENING.**
CONDITIONAL: under the hypothesis h; A is an array of segment 0 that the values have. -/
theorem reach_firstSeat (N : ℕ) {As : List OnBytes.Params.ReqArray} {A : OnBytes.Params.ReqArray}
    (hl : h.𝔇.sent.layout.link[0]? = some As) (hA : A ∈ As)
    (hz : ((cellsVals Sz.ref).size 0 A.name).isSome = true) :
    ∃ Ad : MsgAddr, K1.firstSeat h.𝔇.sent.shape 0 Ad = some (0, A.message) ∧
      (fun _ : MsgAddr => 0) Ad ≤ N := by
  have hm := (H2K5.Door.pins_at_head h.toAtMg).1
  obtain ⟨-, -, f3, -, -, f6⟩ := (H2K5.Door.made_row_gives hm).1
  have el : h.𝔇.sent.layout = Johnson.G.layoutFull := f6
  have es : h.𝔇.sent.shape = proofSizedFull.request := f3
  rw [el] at hl
  obtain ⟨M, hM, h0⟩ := arrayMoment_zero hl hA hz
  rw [← es] at hM
  obtain ⟨k, hk⟩ := msgNo_of_moment hM
  rw [h0] at hk
  exact ⟨⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 0 + k⟩, momentSeat_at _ 0 hk, Nat.zero_le _⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.arrayMoment_written
#print axioms ProofFile.Honest.K5.arrays_there
#print axioms ProofFile.Honest.K5.arrayMoment_zero
#print axioms ProofFile.Honest.K5.reach_switchSeat
#print axioms ProofFile.Honest.K5.reach_firstSeat
