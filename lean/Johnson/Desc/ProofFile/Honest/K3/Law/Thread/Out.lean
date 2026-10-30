-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/Out.lean: conditional: the lookup's promise behind a
lookup's sub-protocol holds where `hearV` has returned: the Boolean test `k3OnOut`
(Johnson/Desc/First/Look/K3Borders.lean) accepts every state at which the seat reads the
program's structure of what was heard and the ledger behind the hearing, but for the plan's
number of claims. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there promise (the lookup's, behind), hearing, heard structure,
seat, ledger, slot, shape, leaves and public parameters.

What is shown.
  `sameCall_refl`, `sameShapeAll_refl`: the library's two tests "the same" accept a thing and
    itself.
  `calls_size`: the shape that a place's parameters fix numbers as many calls as it lists.
  `seg_length`, `zb_sizes`: the two points at which the planes are read have a coordinate for
    each variable.
  `sizedB_of`, `freeB_of`: the library's two tests on a ledger, from the sentences that the theorems
    on the lookup use.
  `leaves_at`: the leaves' structure names the ledger's slot at which the row's own count has it.
  `onOut_of`: the theorem: `k3OnOut p t = true`.
Helper: `zip_self_same`.

Hypotheses that remain, in `onOut_of`.
  `hp`: the place's parameters fix the shape h.
  `hS`, `hn`, `hroom`, `hfree`: the ledger in front is as the theorems on the lookup ask it: arrays
    of the right size; the count of slots at the place's first; room; free as far as the lookup
    reaches.
  `hh`, `hg`: `hearV` returns from that ledger; `toHeard` returns.
  `ht1`, `ht2`: what the seat reads at the state t: the program's structure of what was heard; the
    ledger behind the hearing, but for the plan's number of claims.
In the helpers: `h`: a segment lies within the rounds (in `seg_length`); `Sized G` (in `sizedB_of`).
`hr`, `hf`: (in `freeB_of`) room; the stretch is free.

Users. Honest/K3/Law/Thread/OutSite.lean and Honest/K3/Law/Thread/OnOutMember.lean call `onOut_of`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
On the verifier's side alone: no honest prover is spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.ProofFile.Honest.K3.Law.CountsOk
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Call)
open OnBytes.Model.Forest (Shape)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG toPsc k3OnOut sizedB freeB
  heardAt sameCall
  sameShapeAll)
open VerifiableInference.Desc.First.Look (P)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 "The same" -/

/-- The library's test on two calls accepts a call and itself. -/
theorem sameCall_refl (c : Call) : sameCall c c = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := c
  simp [sameCall]

/-- The same of a list of calls, one by one. -/
theorem zip_self_same : ∀ l : List Call, (l.zip l).all (fun x => sameCall x.1 x.2) = true
  | [] => rfl
  | c :: l => by
    rw [List.zip_cons_cons, List.all_cons, zip_self_same l, Bool.and_true]
    exact sameCall_refl c

/-- The library's test on two shapes accepts a shape and itself. -/
theorem sameShapeAll_refl (h : Shape) : sameShapeAll h h = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  simp [sameShapeAll, zip_self_same]

/-- The shape that a place's parameters fix numbers as many calls as it lists. Conditional on there
being a shape. -/
theorem calls_size {p : P} {h : Shape} (hp : p.shape = some h) : h.calls.size = h.NC := by
  unfold VerifiableInference.Desc.First.Look.P.shape at hp
  obtain ⟨h0, _, hp⟩ := Option.bind_eq_some_iff.1 hp
  split at hp
  · rename_i hk
    obtain rfl := Option.some.inj hp
    simp only [VerifiableInference.Desc.First.Look.pubOk, Bool.and_eq_true, beq_iff_eq] at hk
    exact hk.1.1.2
  · exact nomatch hp

/-! ## 2 The two points -/

/-- A stretch of challenges has its length. Conditional on there being so many rounds. -/
theorem seg_length (rs : List Fmt.RoundView) (a n : Nat) (h : a + n ≤ rs.length) :
    (seg rs a n).length = n := by
  unfold seg
  rw [List.length_take, List.length_drop, List.length_map]
  omega

/-- The two points at which the planes are read have a coordinate for each variable. Conditional on
the return of `hearV`. -/
theorem zb_sizes (h : Shape) {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hh : hearV (faceOf h) F rs = some (g, G)) :
    g.zb0.size = h.kT + h.cK + 5 ∧ g.zb1.size = h.kT + h.cK + 5 := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  have W := walk (faceOf h) h.v rfl (two_le_planes_of_ok _ hok) hm
  obtain ⟨_, _, _, _, _, c6, c7, c8⟩ := o_chain (faceOf h) h.v
  have hl := W.len
  have hmu : (faceOf h).mu + (faceOf h).d = h.kT + h.cK + 5 := by
    show 5 + (h.kT + h.cK) = _
    omega
  refine ⟨?_, ?_⟩
  · rw [W.zb0, List.size_toArray, seg_length _ _ _ (by omega), hmu]
  · rw [W.zb1, List.size_toArray, seg_length _ _ _ (by omega), hmu]

/-! ## 3 The ledger -/

/-- The library's test on a ledger's arrays. Conditional on `Sized`. -/
theorem sizedB_of {G : Fork} (h : Sized G) : sizedB G = true := by
  unfold sizedB
  rw [h.1, h.2.1, h.2.2]
  simp

/-- The library's test that a stretch of slots is free. Conditional on `Sized`, on room, and on no
slot of the stretch being filled. -/
theorem freeB_of {G : Fork} {first n : Nat} (hS : Sized G) (hr : first + n ≤ G.ns)
    (hf : ∀ j, first ≤ j → j < first + n → ¬ Filled G j) : freeB G first n = true := by
  unfold freeB
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨decide_eq_true hr, fun j hj => ?_⟩
  have hj' := List.mem_range.1 hj
  rw [MaskedSum.free_getD hS.2.2 (by omega) (hf (first + j) (by omega) (by omega))]
  rfl

/-- The leaves' structure names the slot at which the row's own count has the leaves' sumcheck.
Conditional on the return of `hearV` and on the first ledger's arrays having their size. -/
theorem leaves_at (f : LFace) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hh : hearV f F x = some (g, G)) : g.leaves.first = F.next + firstSlot f .leaves := by
  obtain ⟨hok, hm⟩ := hearV_messages hh
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, hn⟩ := leaves_heard f hS hm
  rw [(MaskedSum.heard_lenK h0).1]
  exact leaves_first f (two_le_planes_of_ok f hok) hn

/-! ## 4 The promise behind -/

/-- **The lookup's promise behind a lookup's sub-protocol.** Here t is a state at which the seat
reads g', the program's structure of what `hearV` heard, and the ledger behind the hearing, but
for the plan's number of claims. Conditional on: the place's shape; the ledger in front as the
theorems on the lookup ask it; the return of `hearV`; that of `toHeard`; and these two readings at
t. No instance of these hypotheses is exhibited in this file. -/
theorem onOut_of (p : P) (h : Shape) (hp : p.shape = some h) {F G : Fork} {x : List Fmt.RoundView}
    {g : HeardV}
    {g' : OnBytes.Model.Forest.Heard} (hS : Sized F) (hn : F.next = p.first)
    (hroom : p.first + (faceOf h).slots ≤ F.ns)
    (hfree : ∀ j, F.next ≤ j → j < p.first + (faceOf h).slots → ¬ Filled F j)
    (hh : hearV (faceOf h) F x = some (g, G)) (hg : toHeard h (toHeardG g) = some g') (t : FS)
      (c : Nat)
    (ht1 : heardAt p.digits t = some g') (ht2 : t.fork? = some { G with planClaimsF := c }) :
    k3OnOut p t = true := by
  obtain ⟨pt, form, hk, hsz⟩ := keys_of_hearV h hh
  have hv : h.v = h.dT + h.rK := rfl
  have hcs := calls_size hp
  obtain ⟨z0, z1⟩ := zb_sizes h hh
  have hSG : Sized G := (hearV_later hh).sized hS
  have hnG : G.next = p.first + OnBytes.Model.Forest.elems h := by
    rw [hearV_next _ hS hh, hn, Spec.slots_elems]
  have hns : G.ns = F.ns := (hearV_later hh).ns
  have hlf := leaves_at (faceOf h) hS hh
  have hown : Stage.own (faceOf h) .leaves = 1 + 2 * h.d + 5 := by
    have e : Stage.own (faceOf h) .leaves = 1 + (faceOf h).mu + 2 * (faceOf h).d := slots_leaves _
    rw [e]
    show 1 + 5 + 2 * h.d = _
    omega
  have hsum := firstSlot_leaves (faceOf h) (two_le_planes_of_ok _ (hearV_messages hh).1)
  have hsl : Stage.slots (faceOf h) .leaves = Stage.own (faceOf h) .leaves := rfl
  rw [Spec.slots_elems] at hsum hroom
  have hfr := leaves_free (faceOf h) hS (by rw [hn]; rw [hn] at hfree; exact hfree) hh
  -- the structure
  unfold toHeard at hg
  have hk' : (toHeardG g).keys = [(pt, form)] := hk
  rw [hk'] at hg
  simp only at hg
  split at hg
  · rename_i hc
    obtain rfl := Option.some.inj hg
    rw [Bool.and_eq_true] at hc
    unfold k3OnOut
    rw [hp, ht1, ht2]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sameShapeAll_refl h, hcs⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
      ?_⟩
    · show (pt.extract 0 h.dT).size = h.dT
      simp [hsz, hv]
    · show (pt.extract h.dT pt.size).size = h.rK
      simp [hsz, hv]
    · show ((Array.range h.NC).map _).size = h.NC
      simp
    · rw [hcs]
      exact hc.2
    · show p.first + OnBytes.Model.Forest.elems h ≤ G.next
      omega
    · exact sizedB_of (G := { G with planClaimsF := c }) hSG
    · refine freeB_of (G := { G with planClaimsF := c }) hSG ?_ ?_
      · show g.leaves.first + (1 + 2 * h.d + 5) ≤ G.ns
        omega
      · intro j a b
        exact hfr j (by rw [← hlf]; exact a) (by rw [← hlf, hown]; exact b)
    · show p.first ≤ g.leaves.first
      omega
    · show g.leaves.first + (1 + 2 * h.d + 5) ≤ p.first + OnBytes.Model.Forest.elems h
      omega
    · exact z0
    · exact z1
  · exact nomatch hg

#print axioms ProofFile.Honest.K3.Law.AtThr.sameCall_refl
#print axioms ProofFile.Honest.K3.Law.AtThr.zip_self_same
#print axioms ProofFile.Honest.K3.Law.AtThr.sameShapeAll_refl
#print axioms ProofFile.Honest.K3.Law.AtThr.calls_size
#print axioms ProofFile.Honest.K3.Law.AtThr.seg_length
#print axioms ProofFile.Honest.K3.Law.AtThr.zb_sizes
#print axioms ProofFile.Honest.K3.Law.AtThr.sizedB_of
#print axioms ProofFile.Honest.K3.Law.AtThr.freeB_of
#print axioms ProofFile.Honest.K3.Law.AtThr.leaves_at
#print axioms ProofFile.Honest.K3.Law.AtThr.onOut_of

end ProofFile.Honest.K3.Law.AtThr
