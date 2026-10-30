-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamMembersAll.lean: **CoreFacts (Johnson/Desc/Sound/SeamFacts.lean), MEMBER BY MEMBER, AT A GROUP OF ANY NUMBER OF MEMBERS.** One statement; a regrouping; no mathematics. For the key file's K12 (by report: its four groups have 1 | 2 | 2 | 3 members) and for
the last chain's own test (three members).
  **coreFacts_all**   CoreFacts from: at whatever the record fixes: GroupFacts ∧ there are a laying xs of the data's members onto members of the list and radii es with: xs one to one · whoever "sits" is some xs j · MemberFacts at every j with (xs j, es j).
coreFacts_two (SeamMembers.lean) is its case at two.
Limits. Every clause is a premise here. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamMembers

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

theorem coreFacts_all (cs : Codes) {Xi A : Type} (G : FileDescription Xi) (Fr : Frame) (π : P12)
    (no : ℕ → ℕ) (rad : Sg → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (y : Fr.E.Str) (a0 : A) (Y : Strs) (sits : Mem → Prop) (t : T12)
    (H : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
      Fixes π t a rest G0 Ly D →
      GroupFacts cs rad t a G0 Ly D ∧
      ∃ (xs : Fin D.mems.length → Mem) (es : Fin D.mems.length → ℕ), Function.Injective xs ∧
        (∀ z, sits z → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length, MemberFacts cs G Fr no rad smp mem y a0 Y a D j (xs j) (es j)) :
    CoreFacts cs G Fr π no rad smp mem sits t y a0 Y := by
  intro a rest G0 Ly D hf
  obtain ⟨⟨hcs, hJ, ht, hk, hh, hfind, hmembers⟩, xs, es, hinj, hsits, hM⟩ := H a rest G0 Ly D hf
  exact ⟨hcs, hJ, ht, hk, hh, fun j => (hM j).1, fun j => (hM j).2.1, hfind, hmembers, es, xs,
    fun j => (hM j).2.2.1, hinj, hsits, fun j => (hM j).2.2.2.1, fun j => (hM j).2.2.2.2.1,
    fun j => (hM j).2.2.2.2.2.1, fun j => (hM j).2.2.2.2.2.2⟩

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.coreFacts_all
