-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/OrderCovered.lean: in the proof file's description, where the tests on
the plan hold, every segment bears the protocol's order of its own kind, and the lists of claims
that its hearing blocks state are that order's entries, each once; likewise for what is done after
the batching. No file of the description imports this one.
  `linkAt_number`      a segment that the driver's `linkAt` makes bears the number it was asked at
  `namesOk_once`, `orderOk_once`, `orderAfterOk_once`   Block.lean's test on an order: what is
                       stated stands in the order just once
  `descPure_covered`   the law, at every segment of the first chain
  `descPure_covered_at`   the law, at the segment number i
  `chainBy_places`, `descPure_places`   the places of the first chain's flat list are the driver's
                       table `flatPlacesOf`
It is `chain_covered` and `linkAt_order` (Johnson/Desc/First/Driver/OrderLaw.lean), which are
general in the blocks, applied through `descPure_firstChain` (OrderStated.lean).
Limits. It says which lists are stated, not what they hold. The batching's block is handed the
function that runs them in the order; how often that block calls the function is not said here.

-/
import Johnson.Desc.ProofFile.Law.OrderStated
import Johnson.Desc.First.Driver.OrderLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain Link FileDescription KindName namesOk orderOk orderAfterOk
  claimsInBy)
open VerifiableInference.Desc.Shape (mem_runs_iff)
open VerifiableInference.Desc.First

theorem linkAt_number {σ Cl' : Type} (H : Blocks σ Cl') (l : Nat) (sub : ModelPart) (L : Link σ Cl')
    (h : linkAt H l sub = some L) : L.number = l := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  rfl

theorem namesOk_once {all order : List (Nat × String)} (h : namesOk all order = true) :
    ∀ r ∈ all, order.count r = 1 := by
  unfold namesOk at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  intro r hr
  have h1 := h.1 r hr
  rw [Bool.and_eq_true] at h1
  exact beq_iff_eq.1 h1.2

theorem orderOk_once {σ Cl' : Type} {bs : List (Block σ Cl')} {order : List (Nat × String)}
    (h : orderOk bs order = true) (r : Nat × String)
    (hr : ∃ b, bs[r.1]? = some b ∧ r.2 ∈ b.claims.map (·.1)) : order.count r = 1 :=
  namesOk_once h r ((mem_runs_iff (·.claims) bs r).2 hr)

theorem orderAfterOk_once {σ Cl' : Type} {bs : List (Block σ Cl')} {order : List (Nat × String)}
    (h : orderAfterOk bs order = true) (r : Nat × String)
    (hr : ∃ b, bs[r.1]? = some b ∧ r.2 ∈ b.after.map (·.1)) : order.count r = 1 :=
  namesOk_once h r ((mem_runs_iff (·.after) bs r).2 hr)

/-- Where `onlineDescription` returns `F` and `F.planOk` holds. Every segment `L` of the first chain comes of
a member `x` of the list of the segments' kinds with their numbers: `L` bears that number, and the
two orders that it bears and runs are the protocol's for that kind. Every entry of these orders is
stated by the hearing block of its number, and whatever a hearing block states is an entry just
once. -/
theorem descPure_covered {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) :
    ∃ (Z : Pub) (A : SharedSeat) (B : SecondSeat) (c : Chain S Cl),
      pureRoad.pub o pol lay KL = .ok Z ∧
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c ∧
      ∀ L ∈ c.links, ∃ x ∈ (subsOf Z).zipIdx,
        L.number = x.2 ∧ L.order = orderOf x.1 ∧ L.orderAfter = orderAfterOf x.1 ∧
        (∀ r ∈ orderOf x.1, ∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.claims.map (·.1)) ∧
        (∀ r ∈ orderAfterOf x.1, ∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.after.map (·.1)) ∧
        (∀ r, (∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.claims.map (·.1)) →
          (orderOf x.1).count r = 1) ∧
        (∀ r, (∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.after.map (·.1)) →
          (orderAfterOf x.1).count r = 1) ∧
        orderOk L.hear (orderOf x.1) = true ∧ orderAfterOk L.hear (orderAfterOf x.1) = true := by
  obtain ⟨Z, A, B, H, several, c, hZ, hf, hF, hb⟩ := descPure_firstChain h
  refine ⟨Z, A, B, c, hZ, hF, fun L hL => ?_⟩
  obtain ⟨x, hx, L0, e0, eL, c1, c2⟩ := chain_covered H (subsOf Z) several c hf (hb hp) L hL
  have ho := linkAt_order H x.2 x.1 L0 e0
  have o1 : L.order = orderOf x.1 := by rw [eL]; exact ho.1
  have o2 : L.orderAfter = orderAfterOf x.1 := by rw [eL]; exact ho.2
  have n1 : L.number = x.2 := by rw [eL]; exact linkAt_number H x.2 x.1 L0 e0
  have hp' : (orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
      L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter) = true :=
    frame_of_blocksOk c (hb hp) L hL
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, o1, o2] at hp'
  exact ⟨x, hx, n1, o1, o2, c1, c2, orderOk_once hp'.1.1.1, orderAfterOk_once hp'.1.1.2,
    hp'.1.1.1, hp'.1.1.2⟩

/-- The same at the segment number `i` of the first chain: its kind is the one that the list of the
segments' kinds has at the number `i`, and it bears the number `i`. -/
theorem descPure_covered_at {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) :
    ∃ (Z : Pub) (A : SharedSeat) (B : SecondSeat) (c : Chain S Cl),
      pureRoad.pub o pol lay KL = .ok Z ∧
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c ∧
      ∀ (i : Nat) (L : Link S Cl), c.links[i]? = some L →
        ∃ sub, (subsOf Z)[i]? = some sub ∧
          L.number = i ∧ L.order = orderOf sub ∧ L.orderAfter = orderAfterOf sub ∧
          (∀ r ∈ orderOf sub, ∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.claims.map (·.1)) ∧
          (∀ r ∈ orderAfterOf sub, ∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.after.map (·.1)) ∧
          (∀ r, (∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.claims.map (·.1)) →
            (orderOf sub).count r = 1) ∧
          (∀ r, (∃ b, L.hear[r.1]? = some b ∧ r.2 ∈ b.after.map (·.1)) →
            (orderAfterOf sub).count r = 1) ∧
          orderOk L.hear (orderOf sub) = true ∧ orderAfterOk L.hear (orderAfterOf sub) = true := by
  obtain ⟨Z, A, B, H, several, c, hZ, hf, hF, hb⟩ := descPure_firstChain h
  refine ⟨Z, A, B, c, hZ, hF, fun i L hL => ?_⟩
  obtain ⟨sub, L0, hs, e0, eL⟩ := chain_links_at H (subsOf Z) several c hf i L hL
  have ho := linkAt_order H i sub L0 e0
  have o1 : L.order = orderOf sub := by rw [eL]; exact ho.1
  have o2 : L.orderAfter = orderAfterOf sub := by rw [eL]; exact ho.2
  have n1 : L.number = i := by rw [eL]; exact linkAt_number H i sub L0 e0
  have hfr := frame_of_blocksOk c (hb hp) L (List.mem_of_getElem? hL)
  obtain ⟨c1, c2, _⟩ := covered_of_orders sub L o1 o2 hfr
  have hp' : (orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
      L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter) = true := hfr
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, o1, o2] at hp'
  exact ⟨sub, hs, n1, o1, o2, c1, c2, orderOk_once hp'.1.1.1, orderAfterOk_once hp'.1.1.2,
    hp'.1.1.1, hp'.1.1.2⟩

/-! ### The places of the first chain -/

/-- The places of the flat list of a chain that `chainBy` returns are the driver's table, at the
kinds of the segments of the public part. It is `flat_places`
(Johnson/Desc/First/Driver/PlacesLaw.lean) through `chainBy_first_at`. -/
theorem chainBy_places {Z : Pub} {base : List (Block S Cl)} {fr : List (FrameRole × Block S Cl)}
    {road : Gather S Cl} {c : Chain S Cl} (h : chainBy Z base fr road = .ok c) :
    c.blocksInOrder.map (·.place) =
      flatPlacesOf (subsOf Z) (base.any fun b => b.place.kind == KindName.K13) := by
  obtain ⟨H, hf⟩ := chainBy_first_at h
  exact flat_places H _ _ c hf

/-- The same for `onlineDescription`. `base`: the blocks at the places of a kind and the last block. -/
theorem descPure_places {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (Bs : PureBase) (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat)
      (B : SecondSeat),
      pureRoad.pub o pol lay KL = .ok Z ∧ baseOf Z (pureSeat o Z) = .ok Bs ∧
      (partsAt (pureSeat o Z) Bs).base = .ok base ∧
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c ∧
      c.blocksInOrder.map (·.place) =
        flatPlacesOf (subsOf Z) (base.any fun b => b.place.kind == KindName.K13) := by
  obtain ⟨Z, Bs, base, c, A, B, hZ, hB, _, _, hb, hc, _, _, hF⟩ := descPure_parts h
  exact ⟨Z, Bs, base, c, A, B, hZ, hB, hb, hF, chainBy_places hc⟩

end ProofFile.Law

#print axioms ProofFile.Law.descPure_covered
#print axioms ProofFile.Law.chainBy_places
#print axioms ProofFile.Law.descPure_places
#print axioms ProofFile.Law.descPure_covered_at
