-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AfterRests.lean: the runs behind the batching of a link stand in every
relation that the nine known runs keep, from the ties of these runs alone: not through the whole
"Take" of a link's sort and the lookups' runs' share (`run_layers`, `run_attention`, `run_head`,
Johnson/Desc/First/Link/Law/RunRel.lean), of which the half on `orderAfter` uses neither.
So `htin_of` (TotalMoves.lean) at a sort of link keeps one debt
on states. Theorems. It changes no other file.

  `after_rests_layers`, `after_rests_attention`, `after_rests_head`: `RunRests B` · `SegAt l sub L`
  ·
    the ties of "K8.lsTail", "K8.tests" (and, at a layers' link, "free-slot") ⊢ every run of
    L.orderAfter stands in B.
  `htin_layers`, `htin_attention`, `htin_head`: **the field `htin` of `TableOwes`, to the letter,
    from these ties and h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks sh) a.1 ∧
    SeatsThere own sh.length a.1 ∧ SortsAt sh a.1.**
Limits. h1 is shown of no state: on1 must bear «reached», the open link's number and the plan's
structure of the range proof. The ties are premises here (at the proof file's seat they are Johnson/LPFK9R/K8Ties.lean
and K4Ties.lean, which this file does not import). Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.TotalMoves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (blockAtC)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

variable {B : S → S → Prop}

theorem after_rests_layers (R : RunRests B) {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L)
    {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tFree : ∀ run, AtAfter L (2, "free-slot") run →
      ∃ r, (blockAtC p).after.lookup "free-slot" = some r ∧ UnderAfter run r)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  rw [(order_at hL).2, after_layers]
  refine ⟨fun run h => relAfter_under (tLs run h) R.ls, fun run h e e₁ hr => ?_,
    fun run h => relAfter_under (tTests run h) (R.tests nU)⟩
  obtain ⟨r, h0, hu⟩ := tFree run h
  exact R.free p r h0 e e₁ (hu e e₁ hr)

theorem after_rests_attention (R : RunRests B) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) {nU : Array ℕ}
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  rw [(order_at hL).2, after_attention]
  exact ⟨fun run h => relAfter_under (tLs run h) R.ls,
    fun run h => relAfter_under (tTests run h) (R.tests nU)⟩

theorem after_rests_head (R : RunRests B) {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L)
    {nU : Array ℕ} (tLs : ∀ run, AtAfter L (5, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (5, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → B e e₁ := by
  rw [(order_at hL).2, after_head]
  exact ⟨fun run h => relAfter_under (tLs run h) R.ls,
    fun run h => relAfter_under (tTests run h) (R.tests nU)⟩

/-- `htin_of`, from «every relation that the nine known runs keep holds along orderAfter». -/
theorem htin_of_after {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    (L : Link S Claim) (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (after : ∀ (B : S → S → Prop), RunRests B → ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of sh own nU L on1 h1 (after _ rests_good) (after _ (rests_fork (sizedLooks_rests sh)))
    (after _ (runRests_of_rel rests_rs)) pre oT hord hT (after _ (rests_sorts sh))

/-- **htin AT A LAYERS' LINK.** -/
theorem htin_layers {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    {p : OnBytes.Desc.First.K4.Par}
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tFree : ∀ run, AtAfter L (2, "free-slot") run →
      ∃ r, (blockAtC p).after.lookup "free-slot" = some r ∧ UnderAfter run r)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of_after sh own nU L on1 h1 (fun _ R => after_rests_layers R hL tLs tFree tTests)
    [(4, "K8.lsTail"), (2, "free-slot")] (4, "K8.tests") (by rw [(order_at hL).2]; rfl) tTests

/-- **htin AT AN ATTENTION LINK.** -/
theorem htin_attention {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ))
    (nU : Array ℕ) {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L)
    (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of_after sh own nU L on1 h1 (fun _ R => after_rests_attention R hL tLs tTests)
    [(4, "K8.lsTail")] (4, "K8.tests") (by rw [(order_at hL).2]; rfl) tTests

/-- **htin AT THE HEAD's LINK.** -/
theorem htin_head {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (tLs : ∀ run, AtAfter L (5, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (5, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of_after sh own nU L on1 h1 (fun _ R => after_rests_head R hL tLs tTests)
    [(5, "K8.lsTail")] (5, "K8.tests") (by rw [(order_at hL).2]; rfl) tTests

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.after_rests_layers
#print axioms VerifiableInference.Desc.LinkJoin.after_rests_attention
#print axioms VerifiableInference.Desc.LinkJoin.after_rests_head
#print axioms VerifiableInference.Desc.LinkJoin.htin_layers
#print axioms VerifiableInference.Desc.LinkJoin.htin_attention
#print axioms VerifiableInference.Desc.LinkJoin.htin_head
