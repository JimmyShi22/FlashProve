-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngSized.lean: AT A KEY FILE's RANGES' TEST, FROM THE BLOCK's OWN YES AND ITS TEST ON THE PLAN, AT ANY STATE: WHAT STANDS IN FRONT OF THE KIND K12's LEMMA IN THE GAME. Statements and proofs.
OBJECT. `rangesTest laid back N` (Johnson/Desc/Key/Ranges.lean): its yes and its test on the plan, at any state.
USER. Johnson/RunOne/Law/RngAnyCl.lean (cond_of_yes_cl, out_of_yes_cl).
LETTERS. The state, the two halves and N are free; the type of claims is Unit here (any: RngAnyCl.lean).

What is said.
  `sizedL_of_spendL`: the kind K12's test on the plan spendOk walks the stages; its clauses at a stage end with the four on that stage's sizes: where the walk from a stage says yes, these four do.
  `sized_first`: where spendOk says yes, the place's first stage is `Sized` (by sized_of_L, Johnson/Desc/K12/Law/ChainSpend.lean).
  `cond_of_yes`: GENERAL IN THE STATE AND IN THE SEAT's TWO HALVES (laid, back): where the block (Johnson/Desc/Key/Ranges.lean: rangesTest) says yes at s on the rounds rs and its test on the plan says yes: (1) enter returned a record t0, the asking returned at it, the
    variant's decide returned tE at t0 on rs, leave returned; (2) THE BATCHING HAS RETURNED AT t0 ON THE FIRST ROUND SHOWN, without a kept form; (3) FOR EVERY e r row L S' on which the batching returns at t0 without a kept form: the plain data D are made (gpOf … = some D: the
    equation that pins D in `FrontK`), the first stage is `Sized`, and for every radius below the distance `Cond` holds at the word of the typed group made of D, at all members' words and radii.
  `out_of_yes`: GENERAL IN THE STATE TOO: between the record t0 that enter made and the record tE that leave was handed stands the kind's row out, whole (`OutK2`: the group under test is marked and holds no open row and is else as it was; every other group, and every message
    that is no member and not the first mask, stands to the letter; the groups and messages that have come, counted and marked; the masks spent): so a seat whose leave writes tE's statement has the invariant of the row behind the test, whichever its state.
What is left as a premise: none on the state, the layout, the members, the shapes or the sizes. In (3): the radius below the stage's distance.
Limits. (2)'s e is bound by "there is": the batching's return does not hang on it but through tests that it passes. A block that says no to all meets the statement. `Cond` is a condition, not what a yes is worth. Cl := Unit, as the kind K12's laws are. Those of RngCond.lean. Nothing on soundness.

-/
import Johnson.RunOne.Law.RngCond
import Johnson.Desc.K12.Law.ChainSpend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngSized
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngAsked Johnson.RunOne.Law.RngHolds Johnson.RunOne.Law.RngCond
open H2K.Pub (spendOk spendAll spendL sizedL writtenOf WR ok ok_tag ok_cons ok_append sized_of_L)
open H2K.First (Good Plain gpG gpOf sg)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.First.Close (bat)

/-- Where the walk from a stage says yes, the four clauses on that stage's sizes do. -/
theorem sizedL_of_spendL (j : Nat) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : List WR)
    (h : ok (spendL j a rest l) = true) : ok (sizedL a) = true := by
  cases rest with
  | nil =>
    unfold spendL at h
    split at h
    · rw [ok_tag, ok_cons, Bool.and_eq_true] at h
      exact h.2
    · simp [ok] at h
  | cons b rest =>
    unfold spendL at h
    split at h
    · split at h
      · rw [ok_append, ok_tag, ok_cons, ok_cons, Bool.and_eq_true, Bool.and_eq_true,
          Bool.and_eq_true] at h
        exact h.1.2.2
      · simp [ok] at h
    · simp [ok] at h

/-- Where the test on the plan says yes, the place's first stage's sizes are in order. -/
theorem sized_first {p : P12} (h : spendOk p = true) {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (hs : p.nums.stages = a :: rest) : (sg a).Sized := by
  unfold spendOk spendAll at h
  cases hw : writtenOf p.nums with
  | none =>
    rw [hs, hw] at h
    simp [ok] at h
  | some l0 =>
    cases l0 with
    | nil =>
      rw [hs, hw] at h
      simp [ok] at h
    | cons w0 l =>
      rw [hs, hw] at h
      exact sized_of_L (sizedL_of_spendL 0 a rest l h)

/-- **FROM THE BLOCK's OWN YES AND ITS TEST ON THE PLAN, AT ANY STATE.** -/
theorem cond_of_yes {σ : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
    {N : H2U.PlaceNums} {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : (rangesTest (Cl := Unit) laid back N).planOk = true)
    (h : (rangesTest (Cl := Unit) laid back N).decide s rs gs = .ok s') :
    ∃ t0 tE, rangesRecord laid s = .ok t0 ∧ asksOnRecord (rangesParams N) t0 = .ok () ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide t0 rs gs = .ok tE ∧ back s tE = .ok s' ∧
      (∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
        rs.head? = some r ∧ bat t0.st t0.g e r = .ok (row, L, S') ∧ row.kept = #[]) ∧
      ∀ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
        bat t0.st t0.g e r = .ok (row, L, S') → row.kept = #[] →
        ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : Plain)
          (hg : Good (rangesParams N).nums.firstTree a row D),
          (rangesParams N).nums.stages = a :: rest ∧
          gpOf (rangesParams N) { t0 with st := S', pass := .claim row L } a L = some D ∧ (sg a).Sized ∧
          ∀ (rd : ℕ), rd < (sg a).d → ∀ (rad : ℕ → ℕ) (yw : (gpG hg rad).Words),
            Cond (sg a) rd t0.st t0.g ((gpG hg rad).word yw) := by
  obtain ⟨_, he, _, _, hsp⟩ := planOk_ok hp
  obtain ⟨t0, tE, h1, ha, hd, hbk⟩ := decide_ok h
  obtain ⟨id, hid⟩ := asksRecord_mask ha
  refine ⟨t0, tE, h1, ha, hd, hbk, bat_of_yes (rangesParams N) he hd, fun e r row L S' hb h0 => ?_⟩
  obtain ⟨a, rest, D, hg, hs, hD, hc⟩ := cond_asked ha hid hb h0
  have hz := sized_first hsp hs
  exact ⟨a, rest, D, hg, hs, hD, hz, fun rd hd' rad yw => hc rd hz hd' rad yw⟩

/-- **WHAT A YES LEAVES, AT ANY STATE**: the kind's own row out, whole, between the record that enter made and the record that leave was handed. -/
theorem out_of_yes {σ : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
    {N : H2U.PlaceNums} {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : (rangesTest (Cl := Unit) laid back N).planOk = true)
    (h : (rangesTest (Cl := Unit) laid back N).decide s rs gs = .ok s') :
    ∃ t0 tE G, rangesRecord laid s = .ok t0 ∧ back s tE = .ok s' ∧
      H2K.Out.OutK2 t0 tE ((rangesParams N).nums.stages.length - 1) G := by
  obtain ⟨_, he, ha, _, _⟩ := planOk_ok hp
  obtain ⟨t0, tE, h1, _, hd, hbk⟩ := decide_ok h
  obtain ⟨G, k⟩ := H2K.Out.k12_out2 (rangesParams N) he ha t0 tE rs gs hd
  exact ⟨t0, tE, G, h1, hbk, k⟩

end Johnson.RunOne.Law.RngSized

#print axioms Johnson.RunOne.Law.RngSized.out_of_yes
#print axioms Johnson.RunOne.Law.RngSized.sized_first
#print axioms Johnson.RunOne.Law.RngSized.cond_of_yes
