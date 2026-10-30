-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PartRests.lean: THE FIELD htin OF THE LINK's TABLE WANTS OF «GOOD»
(`good9`) ONLY THAT A PART IS READ: `totalIn_moves` (TotalMoves.lean) spends neither «the draw has
run» nor «a coefficient for each slot» of it (the latter it has from `SizedLooks`). So the debt h1
of `htin_layers` | `htin_attention` | `htin_head` (AfterRests.lean) loses its first share: that a
part is read in front stands in `SeatsThere` already. Theorems. No text already in the library turns.

  `PartThere s`: the batching's lens reads a part at s.
  `rests_part`: **«a part in front gives a part behind» at a yes of each of the nine known runs**
    (after `rests_good`, GoodFull.lean, case for case).
  `totalIn_moves_part`, `htin_of_part`: `totalIn_moves` and `htin_of_after` without `good9`.
  `htin_layers_part`, `htin_attention_part`, `htin_head_part`: **htin, to the letter, from the ties
    and h1 : ∀ a, on1 a → HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
    SortsAt sh a.1.**
Limits. h1 is shown of no state here. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.AfterRests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (blockAtC frontAtC_pays backAtC_pays)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open VerifiableInference.Desc.K9 (atS totalIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.K11Run (get_head)
open VerifiableInference.Desc.Kinds.Head.Law (join_hands)
open VerifiableInference.Desc.JoinAtBlocks

/-- The batching's lens reads a part. -/
def PartThere (s : S) : Prop := ∃ a, atS.get? s = some a

/-- **THE NINE KNOWN RUNS.** -/
theorem rests_part : RunRests fun e e₁ => PartThere e → PartThere e₁ where
  refl _ := id
  front p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, _⟩ := frontAtC_pays h0 hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_wrote e e₁ a9 ha a G hw
    exact ⟨a₁, ha₁⟩
  back p r h0 n e c e₁ hr := by
    obtain ⟨a, _, G, _, hw, _⟩ := backAtC_pays h0 hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_wrote e e₁ a9 ha a G hw
    exact ⟨a₁, ha₁⟩
  free p r h0 e e₁ hr := by
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_wrote e e₁ a9 ha a _ hw
    exact ⟨a₁, ha₁⟩
  merge n e c e₁ hr := by
    obtain ⟨a, wo, G, h1, _, rfl, _, _⟩ := claim_inv hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_head e a9 ha a h1 G
    exact ⟨a₁, ha₁⟩
  join h iU3 p n e c e₁ hr := by
    obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_head e a9 ha a h1 _
    exact ⟨a₁, ha₁⟩
  eq n e c e₁ hr := by
    obtain ⟨F, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok n e e₁ c hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_put e a9 ha tl' F1
    exact ⟨a₁, ha₁⟩
  ls e e₁ hr := by
    obtain ⟨F, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_putTl e a9 ha _
    exact ⟨a₁, ha₁⟩
  tests nU e e₁ hr := by
    obtain ⟨F, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ hr
    rintro ⟨a9, ha⟩
    obtain ⟨a₁, ha₁, _⟩ := get_put e a9 ha tl _
    exact ⟨a₁, ha₁⟩

/-- `totalIn_moves` without «good». -/
theorem totalIn_moves_part (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    (L : Link S Claim)
    (g2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      PartThere e → PartThere e₁)
    (k2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      HasFork (SizedLooks sh) e → HasFork (SizedLooks sh) e₁)
    (r2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → Rs e e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (q2 : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      SortsAt sh e → SortsAt sh e₁)
    (s t : S) (h : L.runBehind s = .ok t) (hl : HasFork (SizedLooks sh) s)
    (hseat : SeatsThere own sh.length s) (hso : SortsAt sh s) : totalIn own t = true := by
  have hp : PartThere s := by
    obtain ⟨a0, h0, _⟩ := hseat
    exact ⟨a0, h0⟩
  obtain ⟨a, ha⟩ := holds_runBehind PartThere L g2 s t h hp
  obtain ⟨G, hG, ⟨hS, hLS⟩, _⟩ := holds_runBehind (HasFork (SizedLooks sh)) L k2 s t h hl
  obtain rfl : G = a.F := Option.some.inj (hG.symm.trans (fork_part t a ha))
  obtain ⟨t2, t3⟩ := seats_ride own sh.length (rs_runBehind L r2 s t h) a ha hseat
  obtain ⟨e, he, ht⟩ := full_runBehind (fun x => HasFork (SizedLooks sh) x ∧ SortsAt sh x) nU L pre
    oT hord hT
    (fun o' ho' run hr x x₁ hx hp =>
      ⟨k2 o' (by rw [hord]; exact List.mem_append_left _ ho') run hr x x₁ hx hp.1,
        q2 o' (by rw [hord]; exact List.mem_append_left _ ho') run hr x x₁ hx hp.2⟩) s t h
    ⟨hl, hso⟩
  obtain ⟨⟨Fe, hFe, _, hle⟩, hse⟩ := he
  exact totalIn_tests sh own nU e t a ht ha ⟨Fe, hFe, hle⟩ hse ⟨hLS, hS.1, hS.2.1⟩ t2 t3

/-- `htin_of_after` without «good». -/
theorem htin_of_part {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    (L : Link S Claim) (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (after : ∀ (B : S → S → Prop), RunRests B → ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true := fun a t ha hy =>
  totalIn_moves_part sh own nU L (after _ rests_part) (after _ (rests_fork (sizedLooks_rests sh)))
    (after _ (runRests_of_rel rests_rs)) pre oT hord hT (after _ (rests_sorts sh)) a.1 t
    (runBehind_of_moves (α := α) L a.1 t [] hy) (h1 a ha).1 (h1 a ha).2.1 (h1 a ha).2.2

theorem htin_layers_part {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ))
    (nU : Array ℕ) {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L)
    (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    {p : OnBytes.Desc.First.K4.Par}
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tFree : ∀ run, AtAfter L (2, "free-slot") run →
      ∃ r, (blockAtC p).after.lookup "free-slot" = some r ∧ UnderAfter run r)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of_part sh own nU L on1 h1 (fun _ R => after_rests_layers R hL tLs tFree tTests)
    [(4, "K8.lsTail"), (2, "free-slot")] (4, "K8.tests") (by rw [(order_at hL).2]; rfl) tTests

theorem htin_attention_part {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ))
    (nU : Array ℕ) {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L)
    (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (tLs : ∀ run, AtAfter L (4, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (4, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of_part sh own nU L on1 h1 (fun _ R => after_rests_attention R hL tLs tTests)
    [(4, "K8.lsTail")] (4, "K8.tests") (by rw [(order_at hL).2]; rfl) tTests

theorem htin_head_part {α : Type} {F : Frame} (sh : List Look) (own : List (ℕ × ℕ))
    (nU : Array ℕ) {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) (on1 : S × F.E.Str → Prop)
    (h1 : ∀ a, on1 a → HasFork (SizedLooks sh) a.1 ∧ SeatsThere own sh.length a.1 ∧
      SortsAt sh a.1)
    (tLs : ∀ run, AtAfter L (5, "K8.lsTail") run → UnderAfter run k8LsTail)
    (tTests : ∀ run, AtAfter L (5, "K8.tests") run → UnderAfter run (k8Tests nU)) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
      K9.totalIn own t = true :=
  htin_of_part sh own nU L on1 h1 (fun _ R => after_rests_head R hL tLs tTests)
    [(5, "K8.lsTail")] (5, "K8.tests") (by rw [(order_at hL).2]; rfl) tTests

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.rests_part
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_moves_part
#print axioms VerifiableInference.Desc.LinkJoin.htin_layers_part
#print axioms VerifiableInference.Desc.LinkJoin.htin_attention_part
#print axioms VerifiableInference.Desc.LinkJoin.htin_head_part
