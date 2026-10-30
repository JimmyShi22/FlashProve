-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HtinAtSeat.lean: THE FIELD htin OF THE LINK's TABLE (`TableOwes`,
LinkTable.lean), TO THE LETTER, AT EACH OF THE 25 LINKS OF THE PROOF FILE's FIRST CHAIN, GENERAL IN
THE CONDITION on1, FROM ONE PREMISE ON on1 AND ONE Bool ON THE PLAN. A joining of laws that lie.
Theorems.

  `looks_open_reach`, `link_behind_reach`: `looks_at_open` and `link_behind_batch` at «reached by
    the sub-protocols' own steps» (`Reach 0 c.blocksInOrder (ProofFile.startS Z)`).
  `h1_at_seat`: the debt h1 of `htin_layers` | `htin_attention` | `htin_head` (AfterRests.lean) at
    one state s, at sh := the built link's planned arrays' looks, from: s is reached behind the
    link's batching's entry · good9 s · ledgerB s = true · SeatsThere own sh.length s ·
    sortsB sh Xl.tl = true. PAID INSIDE: the ledger's looks · `SortsAt` · `Sized` (it is the public
    test ledgerB).
  `htin_at_seat`: **hOn : ∀ a, on1 a → ‹these four of a.1› ⊢ ∀ a t, on1 a → MovesYes atS
    ((moves₂ Lk).map (·.move)) a.1 t [] → K9.totalIn own t = true.** The ties of "K8.lsTail",
    "K8.tests" and "free-slot" and `SegAt` are paid inside, by Johnson/LPFK9R/K8Ties.lean,
    K4Ties.lean, LinkAtSeat.lean.
Limits. good9 AND SeatsThere STAY IN hOn: no payer at a state behind the batching is called here.
sortsB at the release's 25 built links is an evaluation, no theorem. In scope, at
secondHashFunction alone. No member. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.BehindBatchOpen
import Johnson.Desc.First.Link.Law.AfterRests
import Johnson.LPFK9R.K8Ties
import Johnson.LPFK9R.K4Ties
import Johnson.LPFK9R.LinkAtSeat
import Johnson.Desc.First.FillKeeper

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.JoinAtBlocks
open Meaning.K2 (frontOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem looks_open_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (hk : k ≤ 353)
    (a : ProofFile.InstPub × S) (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) :
    LooksInv (shOfBuilt Z.p.built.links) a.2 := by
  obtain ⟨_, rs, cols, f⟩ := Reach.fold h
  have hk' : k ≤ (frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    exact hk
  exact Meaning.K2.open_fold (seatKeeps_looks Z.p.built.links) O rfl
    (fun l Q hQ => okHead_at O.blank hQ) hk' f (looksInv_none _ (start_none O.pub a.1))

theorem link_behind_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) (a : ProofFile.InstPub × S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) a) :
    ∃ L, a.2.link? = some L ∧ L.link = x.1 := by
  obtain ⟨_, rs, cols, f⟩ := Reach.fold h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  obtain ⟨L, h1, h2, _⟩ := Meaning.K2.group_all hS hR O hl'
    (k := 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) + 1)
    (by split <;> omega) (by split <;> omega) f
  exact ⟨L, h1, h2⟩

/-- **THE DEBT h1 AT ONE STATE.** -/
theorem h1_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl)
    (hB : sortsB (Xl.Fp.trees.toList.map look) Xl.tl = true) (own : List (ℕ × ℕ))
    (z : ProofFile.InstPub) (s : S)
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) (z, s))
    (hg : good9 s) (hl : First.ledgerB s = true)
    (hs : SeatsThere own (Xl.Fp.trees.toList.map look).length s) :
    good9 s ∧ HasFork (SizedLooks (Xl.Fp.trees.toList.map look)) s ∧
      SeatsThere own (Xl.Fp.trees.toList.map look).length s ∧
      SortsAt (Xl.Fp.trees.toList.map look) s := by
  obtain ⟨p, hp, _, hLS⟩ := hg
  have hF : s.fork? = some p.F := fork_part s p hp
  obtain ⟨L, h1, h2⟩ := link_behind_reach hS hR O hx (z, s) h
  have hk : 14 * x.1 + x.2.1 + 3 + x.2.2 + 1 ≤ 353 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have hl' : l < 25 := List.mem_range.1 hl
    dsimp only
    split <;> omega
  have hlk := looks_open_reach hS hR O hk (z, s) h p.F L hF h1
  rw [h2, shOf_at O.blank e3] at hlk
  have hsz : OnBytes.PscRun.Sized p.F := by
    unfold First.ledgerB at hl
    rw [hF] at hl
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hl
    exact ⟨hl.1.1, hl.1.2, hl.2⟩
  exact ⟨⟨p, hp, ‹_›, hLS⟩, ⟨p.F, hF, ⟨hsz, hLS⟩, hlk⟩, hs,
    sortsAt_of_five (planned_behind_batch planned_five (fun _ _ => rfl) hS hR O hx e3 (z, s) h)
      hB⟩

/-- **htin, TO THE LETTER, AT A LINK OF THE SEAT.** -/
theorem htin_at_seat {α : Type} {Fr : Frame} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Lk : Link S Cl}
    (eL : c.links[x.1]? = some Lk) {Xl : LinkH} (e3 : Bs.G₀.built[x.1]? = some Xl)
    (hB : sortsB (Xl.Fp.trees.toList.map look) Xl.tl = true) (own : List (ℕ × ℕ))
    (z : ProofFile.InstPub) (on1 : S × Fr.E.Str → Prop)
    (hOn : ∀ a, on1 a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2 + 1) (z, a.1) ∧ good9 a.1 ∧
        First.ledgerB a.1 = true ∧ SeatsThere own (Xl.Fp.trees.toList.map look).length a.1) :
    ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) Lk).map (·.move)) a.1 t [] →
      K9.totalIn own t = true := by
  have h1 : ∀ a, on1 a → good9 a.1 ∧ HasFork (SizedLooks (Xl.Fp.trees.toList.map look)) a.1 ∧
      SeatsThere own (Xl.Fp.trees.toList.map look).length a.1 ∧
      SortsAt (Xl.Fp.trees.toList.map look) a.1 := fun a ha => by
    obtain ⟨r, g, l, s⟩ := hOn a ha
    exact h1_at_seat hS hR O hx e3 hB own z a.1 r g l s
  have hl : x.1 < 25 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.1 hl
  obtain ⟨Lk', _, _, e', _, hSeg, _⟩ := LPFK9.blocks_each hS hR O x.1 hl
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
  have hsub := IM.subs_scope hS hR O x.1 hl
  by_cases h24 : x.1 = 24
  · have es : IM.subAt x.1 = .head := by rw [h24]; rfl
    rw [es] at hSeg hsub
    obtain ⟨Lk', e', X, _, _, tLs, tTests⟩ := LPFK9.k8_ties O.made O.places O.chain x.1 .head hsub
      5 (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl) (by omega)
    obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
    exact htin_head _ own _ hSeg on1 h1 tLs tTests
  · by_cases he : x.1 % 2 = 0
    · have es : IM.subAt x.1 = .layers := by
        unfold IM.subAt
        rw [if_neg h24, if_pos he]
      rw [es] at hSeg hsub
      obtain ⟨Lk', e', X, _, _, tLs, tTests⟩ := LPFK9.k8_ties O.made O.places O.chain x.1 .layers
        hsub 4 (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl) (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
      obtain ⟨Lk', e', p, _, _, _, tFree⟩ := LPFK9.k4_ties O.made O.places O.chain x.1 .layers
        hsub (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
      exact htin_layers _ own _ hSeg on1 h1 tLs tFree tTests
    · have es : IM.subAt x.1 = .attention := by
        unfold IM.subAt
        rw [if_neg h24, if_neg he]
      rw [es] at hSeg hsub
      obtain ⟨Lk', e', X, _, _, tLs, tTests⟩ := LPFK9.k8_ties O.made O.places O.chain x.1
        .attention hsub 4 (by unfold kindsBeforeBatching; cases (x.1 == 0) <;> rfl) (by omega)
      obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans e')
      exact htin_attention _ own _ hSeg on1 h1 tLs tTests

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.looks_open_reach
#print axioms VerifiableInference.Desc.LinkJoin.link_behind_reach
#print axioms VerifiableInference.Desc.LinkJoin.h1_at_seat
#print axioms VerifiableInference.Desc.LinkJoin.htin_at_seat
