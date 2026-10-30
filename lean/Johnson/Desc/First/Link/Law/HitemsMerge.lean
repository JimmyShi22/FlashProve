-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HitemsMerge.lean: `TableOwes.hitems` (LinkTable.lean), ONE ITEM's CLAUSE
AT THE MERGE's ENTRY: a run that lays a window of the ledger. At the readers of the link itself
(`K9.readersOfLink`). Theorems, over HitemsStill.lean, LateWindows.lean and K11Run.lean.

What is said.
  `window_of_run`: what a run of hiding slots with (shown 0, factor −1) leaves: its window is laid
    behind, lies below the number of slots, was free in front and is filled behind. `item_merge`:
    **`ItemAt` at an entry of the order whose run stands under the merge's own run**, the table of
    terms there being `plainTm (valsMerge …)` at `entUnit`; from, at the statement: a part is there;
    the state goes on from what is fixed; the reader's second hole says nothing; the table's public
    test says yes; and the merge's law's own two premises on φ and on Ok.

Limits. One item. As in HitemsStill.lean: the hole's silence is a premise; whether the public test
says yes at a real record is a run's to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.LateWindows
import Johnson.Desc.First.Link.Law.K11Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled Sized Same hideRun_ok)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K4Values (InWin LaidAt winOf)
open VerifiableInference.Desc.K11Run (valsMerge get_head)
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {α W : Type} {F : Frame}

/-- What a run of hiding slots with (shown 0, factor −1) leaves. -/
theorem window_of_run {U G : Fork} {first n : ℕ} (hU : Sized U)
    (h : U.hideRun first (Array.replicate n zeroE) (subE zeroE oneE) = some G) :
    LaidAt G (first, n) ∧ ∀ j, InWin (first, n) j →
      j < G.ns ∧ U.gotF.getD j false = false ∧ G.gotF.getD j false = true := by
  obtain ⟨hsame, _, hin, _⟩ := hideRun_ok U G first _ _ hU h
  have hns : G.ns = U.ns := by
    unfold Same at hsame
    rw [hsame]
  have key : ∀ j, InWin (first, n) j → ∃ i, j = first + i ∧ i < n := fun j hj =>
    ⟨j - first, by have := hj.1; simp only at this; omega,
      by have := hj.1; have := hj.2; simp only at *; omega⟩
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨i, rfl, hi⟩ := key j hj
    obtain ⟨_, _, _, h1, h2⟩ := hin i (by simpa using hi)
    refine ⟨h1.trans ?_, h2⟩
    simp [Array.getD_eq_getD_getElem?, hi]
  · obtain ⟨i, rfl, hi⟩ := key j hj
    obtain ⟨h0, h1, h2, _, _⟩ := hin i (by simpa using hi)
    refine ⟨by rw [hns]; exact h0, ?_, h2⟩
    cases e : U.gotF.getD (first + i) false with
    | false => rfl
    | true => exact absurd e h1

/-- **ONE ITEM's CLAUSE AT THE MERGE's ENTRY.** -/
theorem item_merge (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hne : (o.2 == "K8.equations") = false)
    (run : ℕ → S → Except String (List Claim × S)) (hAt : At L o run)
    (hu : Under run headMergeClaim) (π : α → Option WsForkOut)
    (hπ : ∀ s a, s.here = .head a → π (φ s) = a.wo)
    (hOk : ∀ q wo u, Ok q → π q.1 = some wo → q.2 = some u → Sized u.F ∧
      ∀ x ∈ (wo.p.rowForm wo.fvp {}).slots.toList, InWin (winOf wo.p) x.1 ∨ Filled u.F x.1)
    (ht : tmOf o = plainTm (valsMerge Reading.gl π entUnit))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hf : Fx9 φ Ok (fixed9 φ a.1) a.1) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemAt L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt a.1 hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (K9.get_fork a.1 b hb))
  obtain ⟨ah, wo, G, h1, hwo, rfl, rfl, hrunG⟩ := claim_inv (hu 0 a.1 c s' hz)
  obtain ⟨a₁, ha₁, f1, _, _, f4⟩ := get_head a.1 b hb ah h1 G
  obtain rfl : G' = G := by
    have e := K9.get_fork _ a₁ ha₁
    rw [f1] at e
    exact Option.some.inj (hG'.symm.trans e)
  have hq : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hq1 : π (fixed9 φ a.1).1 = some wo := by
    show π (φ a.1) = _
    rw [hπ a.1 ah h1, hwo]
  obtain ⟨hsz, hsl⟩ := hOk _ wo (pubOf b) hf.1 hq1 hq
  have hrun' : b.F.hideRun wo.p.first (Array.replicate wo.p.walk.1.length zeroE)
      (subE zeroE oneE) = some G' := by rw [f4]; exact hrunG
  obtain ⟨hlaid, hwin⟩ := window_of_run (show Sized b.F from hsz) hrun'
  refine ⟨b, _, [(⟨(o.2, run), tmOf o, lenOf o⟩, valsMerge Reading.gl π entUnit)], hb, ?_, hR, hin,
    ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · have he := named_of_formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 b _ hb hR hin
    show valsMerge Reading.gl π entUnit (fixed9 φ a.1) (dataQ own b (rdW w)) ++ [] = _
    rw [List.append_nil]
    simp only [valsMerge, hq1, hq]
    show [_] = [_]
    refine congrArg (fun v => [v]) ?_
    refine value_meets_windows b G' [winOf wo.p] (dataQ own b (rdW w)) (fixed9 φ a.1) hq _
      (he _ (List.mem_singleton.2 rfl)) fun x hx => ?_
    by_cases hw : InWin (winOf wo.p) x.1
    · obtain ⟨k1, k2, k3⟩ := hwin x.1 hw
      exact Or.inl ⟨_, List.mem_singleton.2 rfl, hw, hlaid, k1, k2, k3⟩
    · refine Or.inr ⟨?_, (hsl x hx).resolve_left hw⟩
      rintro ⟨w', hw', hj⟩
      obtain rfl := List.mem_singleton.1 hw'
      exact hw hj

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.window_of_run
#print axioms VerifiableInference.Desc.LinkJoin.item_merge
