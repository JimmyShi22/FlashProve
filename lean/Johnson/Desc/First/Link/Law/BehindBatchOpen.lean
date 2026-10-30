-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/BehindBatchOpen.lean: TWO OF THE SHARES OF THE DEBT h1 OF THE LINK's
TABLE's FIELD htin (`htin_layers` | `htin_attention` | `htin_head`, AfterRests.lean), AT THE STATES
THAT ARE REACHED BEHIND A LINK's BATCHING's ENTRY, IN THE LETTERS OF AN OPENED SEAT (`IM.Open`), AT
sh := THE BUILT LINK's PLANNED ARRAYS' LOOKS. A joining. Theorems.

  `link_behind_batch`: a link is open there, with the number x.1
    (`group_all`, Johnson/IMR/GroupHead.lean).
  `looks_behind_batch`: every ledger that is open there has the looks sh.
  `two_of_h1`: **(∀ G, a.1.2.fork? = some G → LooksAre sh G) ∧ SortsAt sh a.1.2**, from
    sortsB sh Xl.tl = true.
Limits. h1 ASKS MORE: good9 (the batching's lens reads a part; its link is handed; the ledger has as
many slots' sums as slots) · Sized (the other half of SizedLooks) · SeatsThere: NONE IS TREATED
HERE. That the table's condition on1 gives «RchAt at this number» is not said. In scope, at secondHashFunction
alone. No member. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.AtBatchOpen
import Johnson.Desc.First.Link.Law.BatchLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_fold)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem link_behind_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    ∃ L, a.1.2.link? = some L ∧ L.link = x.1 := by
  obtain ⟨_, rs, cols, f⟩ := rchAt_fold h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  obtain ⟨L, h1, h2, _⟩ := Meaning.K2.group_all hS hR O hl'
    (k := 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) + 1)
    (by split <;> omega) (by split <;> omega) f
  exact ⟨L, h1, h2⟩

theorem looks_behind_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    ∀ G, a.1.2.fork? = some G → LooksAre (Xl.Fp.trees.toList.map look) G := by
  intro G hG
  obtain ⟨L, h1, h2⟩ := link_behind_batch hS hR O hx a h
  have hk : 14 * x.1 + x.2.1 + 3 + x.2.2 + 1 ≤ 353 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have hl' : l < 25 := List.mem_range.1 hl
    dsimp only
    split <;> omega
  have hlk := looks_at_open hS hR O hk a h G L hG h1
  rw [h2, shOf_at O.blank e3] at hlk
  exact hlk

/-- **TWO OF h1's SHARES.** -/
theorem two_of_h1 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl)
    (hB : sortsB (Xl.Fp.trees.toList.map look) Xl.tl = true)
    {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    (∀ G, a.1.2.fork? = some G → LooksAre (Xl.Fp.trees.toList.map look) G) ∧
      SortsAt (Xl.Fp.trees.toList.map look) a.1.2 :=
  ⟨looks_behind_batch hS hR O hx e3 a h, sorts_behind_batch hS hR O hx e3 hB a h⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.link_behind_batch
#print axioms VerifiableInference.Desc.LinkJoin.looks_behind_batch
#print axioms VerifiableInference.Desc.LinkJoin.two_of_h1
