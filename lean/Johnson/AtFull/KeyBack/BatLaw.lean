-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BatLaw.lean: GENERAL LAWS ON THE CUT OF A PROXIMITY TEST OUT OF A KEY FILE's
PLAN. General in the plan: no written value stands here.

`H2U.batPlaces es` (Johnson/Desc/K12/Plan/TestCut.lean) walks the whole list of entries and keeps
the numbers of those named "BAT". `Key.rangesNumbers` and `Key.laterPlaces`
(Johnson/Desc/Key/Ranges.lean, Places.lean) read its first element alone.

  `noBat es`: no entry of es is named "BAT". A test with code.
  `noBat_append`: it can be asked piece by piece.
  `bat_head_from`, `batPlaces_head_of_split`: where es = pre ++ b :: post, no entry of pre is named
    "BAT" and b is, the first place of "BAT" is pre.length. post is not read.
  `keyTestCut_eq`: at a chain that is there, `Key.keyTestCut` is `H2U.cutOn`
    (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) at that chain's entries.
  `cutAt_eq`: `cutAt C ch st` (Core.lean) is `H2U.cutOn` at the place i, from two facts: the chain
    is there; the first place of "BAT" on it is i.
  `cutAt_only`: the way back: where `cutAt C ch st` returns, the two facts hold and `H2U.cutOn`
    returns the same.
Limits. That a plan splits so, or that `H2U.cutOn` returns, is shown at no plan.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key

/-- No entry is named "BAT". -/
def noBat (es : List Fmt.Entry) : Bool := es.all fun e => e.name != "BAT"

/-- `noBat` can be asked piece by piece. -/
theorem noBat_append (a b : List Fmt.Entry) : noBat (a ++ b) = (noBat a && noBat b) := by
  unfold noBat
  exact List.all_append

/-- The law below, with the count beginning at any n. -/
theorem bat_head_from (post : List Fmt.Entry) (b : Fmt.Entry) (hb : b.name = "BAT") :
    ∀ (pre : List Fmt.Entry) (n : Nat), noBat pre = true →
      ((((pre ++ b :: post).zipIdx n).filter fun p => p.1.name == "BAT").map (·.2)).head? =
        some (n + pre.length) := by
  intro pre
  induction pre with
  | nil =>
    intro n _
    simp [List.zipIdx_cons, hb]
  | cons a pre ih =>
    intro n h
    unfold noBat at h
    rw [List.all_cons, Bool.and_eq_true] at h
    have ha : (a.name == "BAT") = false := beq_eq_false_iff_ne.2 (bne_iff_ne.1 h.1)
    have hi := ih (n + 1) h.2
    rw [List.cons_append, List.zipIdx_cons, List.filter_cons_of_neg (by simp [ha]), hi,
      List.length_cons]
    congr 1
    omega

/-- **The first place of "BAT"**, where the list splits at it. -/
theorem batPlaces_head_of_split (pre post : List Fmt.Entry) (b : Fmt.Entry)
    (hp : noBat pre = true) (hb : b.name = "BAT") :
    (H2U.batPlaces (pre ++ b :: post)).head? = some pre.length := by
  unfold H2U.batPlaces
  have h := bat_head_from post b hb pre 0 hp
  rw [Nat.zero_add] at h
  exact h

/-- `Key.keyTestCut` at a chain that is there is `H2U.cutOn` at that chain's entries. -/
theorem keyTestCut_eq (C : Configured) (ch i : Nat) (st : List IoppStage) (P : Planned)
    (hP : C.key[ch]? = some P) :
    keyTestCut C ch i st = H2U.cutOn (P.rounds.map (·.entry)) ch i st := by
  unfold keyTestCut H2U.cutOn
  simp only [hP, Option.bind_eq_bind, Option.bind_some]
  split <;> rfl

/-- **The cut at a chain's first "BAT"** is `H2U.cutOn` there, from two facts. -/
theorem cutAt_eq (C : Configured) (ch i : Nat) (st : List IoppStage) (P : Planned)
    (hP : C.key[ch]? = some P)
    (hb : (H2U.batPlaces (P.rounds.map (·.entry))).head? = some i) :
    cutAt C ch st = H2U.cutOn (P.rounds.map (·.entry)) ch i st := by
  rw [List.head?_eq_getElem?] at hb
  rw [← keyTestCut_eq C ch i st P hP]
  simp only [cutAt, keyBatchRounds, hP, Option.map_some, Option.bind_eq_bind, Option.bind_some, hb]

/-- **The way back**: where the cut returns, the two facts hold and `H2U.cutOn` returns the same. -/
theorem cutAt_only (C : Configured) (ch : Nat) (st : List IoppStage) (t : H2U.TestCut)
    (h : cutAt C ch st = some t) :
    ∃ (P : Planned) (i : Nat), C.key[ch]? = some P ∧
      (H2U.batPlaces (P.rounds.map (·.entry))).head? = some i ∧
      H2U.cutOn (P.rounds.map (·.entry)) ch i st = some t := by
  simp only [cutAt, Option.bind_eq_bind] at h
  obtain ⟨l, hl, hq⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨i, hi, hc⟩ := Option.bind_eq_some_iff.1 hq
  unfold keyBatchRounds at hl
  cases hP : C.key[ch]? with
  | none => rw [hP] at hl; exact nomatch hl
  | some P =>
    rw [hP] at hl
    obtain rfl : _ = l := Option.some.inj hl
    refine ⟨P, i, rfl, by rw [List.head?_eq_getElem?]; exact hi, ?_⟩
    rw [← keyTestCut_eq C ch i st P hP]
    exact hc

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.noBat_append
#print axioms Johnson.AtFull.KeyBack.bat_head_from
#print axioms Johnson.AtFull.KeyBack.batPlaces_head_of_split
#print axioms Johnson.AtFull.KeyBack.keyTestCut_eq
#print axioms Johnson.AtFull.KeyBack.cutAt_eq
#print axioms Johnson.AtFull.KeyBack.cutAt_only
