-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamMembers.lean: **CoreFacts (Johnson/Desc/Sound/SeamFacts.lean), MEMBER BY MEMBER, AT A GROUP OF TWO.** Definitions, statements and proofs: a regrouping; no new mathematics.
  MemberFacts    what CoreFacts asks of ONE member j of the kind's data, at the member x of the list that sits there and its radius e0: siteL's yes · sampleL's yes · the test's radius against e0 (hfit) · x's entry is the member's shape with e0 · the plan's mem lays x at the
                 member's number · the member's one sample row is Send.form's at a seed, and the reading smp gives a sample that the library's sample map reads alike · the word off the plain strings is the word as sent.
  GroupFacts     what it asks of the group: the data's codes are cs · StageJ · combineAt · the layout's k | h · the layout finds each member at its place · the group's members are the data's.
  **coreFacts_two**   CoreFacts from: at whatever the record fixes: GroupFacts · the data have two members · MemberFacts at the first with (x₀, e₀) and at the second with (x₁, e₁) · x₀ ≠ x₁ · whoever "sits" is x₀ or x₁.
Limits. Every clause is a premise here. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run
open H2K.First (Seat1 Plain)
open H2K.Pub (sgOf)

section
variable (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12) (no : ℕ → ℕ)
  (rad : Sg → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs)

/-- **What is asked of one member.** -/
def MemberFacts (a : Fmt.M1.Stage) (D : Plain) (j : Fin D.mems.length) (x : Mem) (e0 : ℕ) : Prop :=
  ok (siteL cs a (D.mems.get j)) = true ∧
  (∃ o, D.st.oracles[(D.mems.get j).id]? = some o ∧ ok (sampleL cs (D.mems.get j) o) = true) ∧
  rad (sgOf a) < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf cs (D.mems.get j).sh) ∧
  x.1.l.get x.2 = ((D.mems.get j).sh, e0) ∧
  mem (D.mems.get j).id = some x ∧
  (∃ (o : OnBytes.Oracle) (seed : SampleSeed) (row0 : OnBytes.Row) (tt : E) (β : GEˣ),
    D.st.oracles[(D.mems.get j).id]? = some o ∧
    Send.form cs (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
    o.sampleRows.toList = [{ row0 with target := tt }] ∧
    bitsZ cs (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
    ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a0 x.1 x.2 = some z ∧
      HEq (((readP (bitsZ cs (D.mems.get j).sh) seed.z, β), fun _ => readE tt) :
        (portOmZ cs (D.mems.get j).sh e0).Smp) σ' ∧ z.2 = σ'.2 ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1) ∧
  HEq (strOf cs (D.mems.get j).sh e0 (layOf (D.mems.get j))
      (W0 Fr no D.book y (D.mems.get j).t).1 (W0 Fr no D.book y (D.mems.get j).t).2)
    (VerifiableInference.Desc.Sound.wordsOf G cs x.1.l x.1.seat Y x.2)

/-- **What is asked of the group.** -/
def GroupFacts (t : T12) (a : Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain) : Prop :=
  D.st.codes = cs ∧
  (sgOf a).StageJ (rad (sgOf a)) ∧
  combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
  Ly.k = (sgOf a).h + (sgOf a).g ∧ Ly.h = (sgOf a).h ∧
  (∀ j : Fin D.mems.length, D.L.find (D.mems.get j).id = some j.val) ∧
  ∀ o ∈ G0.members.toList, ∃ j : Fin D.mems.length, (D.mems.get j).id = o

/-- **CoreFacts at a group of two.** -/
theorem coreFacts_two (sits : Mem → Prop) (t : T12) (x₀ x₁ : Mem) (e₀ e₁ : ℕ) (hne : x₀ ≠ x₁)
    (hsits : ∀ z, sits z → z = x₀ ∨ z = x₁)
    (H : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
      Fixes π t a rest G0 Ly D →
      GroupFacts cs rad t a G0 Ly D ∧ D.mems.length = 2 ∧
      ∀ j : Fin D.mems.length,
        (j.val = 0 ∧ MemberFacts cs G Fr no rad smp mem y a0 Y a D j x₀ e₀) ∨
        (j.val = 1 ∧ MemberFacts cs G Fr no rad smp mem y a0 Y a D j x₁ e₁)) :
    CoreFacts cs G Fr π no rad smp mem sits t y a0 Y := by
  intro a rest G0 Ly D hf
  obtain ⟨⟨hcs, hJ, ht, hk, hh, hfind, hmembers⟩, h2, hq⟩ := H a rest G0 Ly D hf
  have pick : ∀ j : Fin D.mems.length,
      MemberFacts cs G Fr no rad smp mem y a0 Y a D j (if j.val = 0 then x₀ else x₁)
        (if j.val = 0 then e₀ else e₁) := by
    intro j
    rcases hq j with ⟨e, h⟩ | ⟨e, h⟩
    · rw [if_pos e, if_pos e]; exact h
    · rw [if_neg (by omega), if_neg (by omega)]; exact h
  refine ⟨hcs, hJ, ht, hk, hh, fun j => (pick j).1, fun j => (pick j).2.1, hfind, hmembers,
    fun j => if j.val = 0 then e₀ else e₁, fun j => if j.val = 0 then x₀ else x₁,
    fun j => (pick j).2.2.1, ?_, ?_, fun j => (pick j).2.2.2.1, fun j => (pick j).2.2.2.2.1,
    fun j => (pick j).2.2.2.2.2.1, fun j => (pick j).2.2.2.2.2.2⟩
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    by_cases ei : i.val = 0 <;> by_cases ej : j.val = 0
    · exact Fin.ext (ei.trans ej.symm)
    · simp only [ei, ej, if_true, if_false] at hij
      exact absurd hij hne
    · simp only [ei, ej, if_true, if_false] at hij
      exact absurd hij.symm hne
    · exact Fin.ext (by omega)
  · intro z hz
    rcases hsits z hz with rfl | rfl
    · exact ⟨⟨0, by omega⟩, if_pos rfl⟩
    · exact ⟨⟨1, by omega⟩, if_neg Nat.one_ne_zero⟩

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.coreFacts_two
