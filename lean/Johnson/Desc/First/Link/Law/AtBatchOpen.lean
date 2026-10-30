-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/AtBatchOpen.lean: AT THE STATES THAT ARE REACHED AT A LINK's BATCHING's
ENTRY's NUMBER, IN THE LETTERS OF AN OPENED SEAT (`IM.Open`, Johnson/IMR/SeatOpen.lean): THE
LEDGER's LOOKS AND THE OPEN LINK's NUMBER ARE THE BUILT LINK's. A joining of other files' laws.
Theorems. It changes no other file.

  `looks_at_open`: `LooksInv (shOfBuilt Z.p.built.links)` at every a with RchAt ‹the description› k
  a,
    k ≤ 353: `looks_at_rch` (Johnson/LPFK9R/LooksSeat.lean) AT O's OWN CHAIN c: by
    `open_fold` (Johnson/IMR/OpenWalk.lean) at `seatKeeps_looks`, and
    `front_len` (Johnson/IMR/RootsWhole.lean: in scope 353 sub-protocols stand in front of what
    stands behind the last link).
  `shOf_at`: Bs.G₀.built[l]? = some Xl ⊢ shOfBuilt Z.p.built.links l = Xl.Fp.trees.toList.map look.
  `link_at_batch`: at x ∈ P1K8S.stretches: a link is open at a.1.2, with the number x.1
    (`group_all`, Johnson/IMR/GroupHead.lean).
  `part_at_batch`: **so, of every part p that the batching's lens reads there: p.L.link = x.1, and
    the snapshot's ledger has the built link's planned arrays' looks:
    (pubOf p).F.trees.toList.map look = Xl.Fp.trees.toList.map look.**
Limits. THAT THE LENS READS A PART THERE IS NOT SAID (at the head's link it wants the merge's slot;
a yes of the batching gives it). In scope, at secondHashFunction alone. No member. Nothing on soundness.

-/
import Johnson.LPFK9R.LooksSeat
import Johnson.IMR.OpenWalk
import Johnson.IMR.MsgsPlaces
import Johnson.IMR.GroupHead
import Johnson.Desc.First.Link.Law.PlannedAtRch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open Meaning.K2 (frontOf blank_built)
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_fold)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The looks, at O's own chain.** -/
theorem looks_at_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (hk : k ≤ 353)
    {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) k a) : LooksInv (shOfBuilt Z.p.built.links) a.1.2 := by
  obtain ⟨_, rs, cols, f⟩ := rchAt_fold h
  have hk' : k ≤ (frontOf c).length := by
    rw [Meaning.Carry.front_len hS hR O]
    exact hk
  exact Meaning.K2.open_fold (seatKeeps_looks Z.p.built.links) O rfl
    (fun l Q hQ => okHead_at O.blank hQ) hk' f
    (looksInv_none _ (start_none O.pub a.1.1))

/-- The plan's looks of link l are the built link's planned arrays'. -/
theorem shOf_at {mk : ProofFile.LinksBy} {G : ProofFile.Ground} (h : ProofFile.blankBy mk Z = some G) {l : ℕ}
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    shOfBuilt Z.p.built.links l = Xl.Fp.trees.toList.map look := by
  obtain ⟨links, e⟩ := blank_built h
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact shOfBuilt_at (X := Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

/-- **A link is open there, with the number x.1.** -/
theorem link_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a) :
    ∃ L, a.1.2.link? = some L ∧ L.link = x.1 := by
  obtain ⟨_, rs, cols, f⟩ := rchAt_fold h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hl' : l < 25 := List.mem_range.1 hl
  obtain ⟨L, h1, h2, _⟩ := Meaning.K2.group_all hS hR O hl'
    (k := 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2))
    (by split <;> omega) (by split <;> omega) f
  exact ⟨L, h1, h2⟩

/-- **Of every part that the batching's lens reads there.** -/
theorem part_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ P1K8S.stretches) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * x.1 + x.2.1 + 3 + x.2.2) a) (p : K9.Part)
    (hp : atS.get? a.1.2 = some p) :
    p.L.link = x.1 ∧ (pubOf p).F.trees.toList.map look = Xl.Fp.trees.toList.map look := by
  obtain ⟨L, h1, h2⟩ := link_at_batch hS hR O hx a h
  have e : p.L = L := Option.some.inj ((part_reads a.1.2 p hp).1.symm.trans h1)
  have hn : p.L.link = x.1 := by rw [e]; exact h2
  have hk : 14 * x.1 + x.2.1 + 3 + x.2.2 ≤ 353 := by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have hl' : l < 25 := List.mem_range.1 hl
    dsimp only
    split <;> omega
  have hlk : LooksAre (shOfBuilt Z.p.built.links p.L.link) p.F :=
    looks_at_open hS hR O hk a h p.F p.L (fork_part a.1.2 p hp) (part_reads a.1.2 p hp).1
  refine ⟨hn, ?_⟩
  rw [hn] at hlk
  exact hlk.trans (shOf_at O.blank e3)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.looks_at_open
#print axioms VerifiableInference.Desc.LinkJoin.shOf_at
#print axioms VerifiableInference.Desc.LinkJoin.link_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.part_at_batch
