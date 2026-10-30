-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TestsAtCounts.lean: TEN PREMISES OF THE LAW ON THE SUB-PROTOCOL K1 AT ITS FIFTY
LATER PLACES (k01_fifty_atBase, Johnson/Desc/K1/Law/K01FiftyAtBase.lean): the tests on the table's
numbers N and on the list of seats: hRows hBook hFence hSent hP1 hNd hSeats hidx hAtA hPlan3: each
ends at that premise's own type, at
  N := `P5T.N0Full.atBlocks s links c.blocksInOrder`: the written core of the numbers, closed over the first
       chain's own sub-protocols (Johnson/Desc/First/NumbersAtBlocks.lean), at any s and links;
  seats := `K13.Law.seatsFull`: the written list of seats.
Statements with their proofs; nothing is evaluated here: the closed facts are TestsWritten.lean's
(this folder) and those of Johnson/HB/LLHARD/*.lean.

THE PREMISES THAT STAY, each an equation on public values or the law's own:
  hS hR O      the goals' scope and the opened IOP as written in Lean (the law's own)
  hok | hOk    every sub-protocol of the first chain passes its own test on its parameters (the
               law's own)
  hc hs        the first chain's codes and request's shape are the written ones (the law's own)
  hWr hRoots   the law's own two on the written rounds (for hSeats alone)
  hN · hseats  the two equations above
  **hC : CountsAre (toldOf c.blocksInOrder)**: at the 359 borders, what the sub-protocols in front tell comes
               to the written counts of oracle messages and trees (`countsFull`,
               Johnson/HB/LLHARD/ToldCounts.lean). NO LAW GIVES IT IN SCOPE YET. `countsAre_of_cut`:
               it follows where the cut of the first chain is the written one
               (`PlanWritten.cutOf c.blocksInOrder = cutFirstFull`: a test with code on public values).
  hL hM        the proximity test's data hold the written layout and shapes (for hPlan3 alone)
  hDsh         the composed meaning's shape is the written one (for hAtA alone; the law's own)
WHY hC CANNOT BE LEFT OUT. Seven of the ten read how many trees or oracle messages ALL
sub-protocols in front of a place tell. WHY N's CORE IS NOT A LETTER. The same seven read N.sent,
which `atBlocks` leaves as the core's.
No premise is asked of the chain's two numbers `gpOf Z`: the tests read a place's parameters
through what it sends and its layout alone (`parL_sent`, `parL_lay`, `parL_shapes`).

  `parL_sent`, `parL_lay`, `parL_shapes`   the place (l, d) sends and lays what the written one does
  `toldBy_toldOf`, `atBlocks_written`, `counts_at_blocks`, `fifty_numbers`   the two counts
  `sentAt_of_laterSeats`   the converse of `laterSeatsOfTold` (SentAtProofs.lean, this folder)
  `goesOn_of_plain`, `goesOnB_congr`   two small laws on the test `goesOnB` (PlanThree.lean)
  `baseL_at`   the piece's base is the numbers' count of trees (as in k01_law's own proof)
  `hRows_at` … `hPlan3_at`   **the ten**

What is not claimed. That the composed meaning's N is this N, or its reader of samples' list this
list: `P5T.seats_in_scope` gives the core and the list under its own premises. NO EXAMPLE of hC at a
chain of sub-protocols. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TestsWritten
import Johnson.Desc.K1.Law.K01Law
import Johnson.Desc.K1.Law.PlanThree
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Desc.First.CutAtNumbers
import Johnson.Goal.Numbers.RequestWritten
import Johnson.LPFK9R.SubsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model Johnson.G
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Chain FileDescription Place Oracle)
open VerifiableInference.Desc.Sound (linksFull toldBy MgData MsgT CellsQ base_at_flat WrittenAs)
open VerifiableInference.Desc.First (S ModelPart Item Numbers flatPlacesOf blockPlaces treesTold msgsTold
  tenantsOf sameMembers)
open VerifiableInference.Desc.First.FillSent (secondNos base1At)
open VerifiableInference.Desc.K13.Law (openAt countsFull CountsAre laterFull seatsFull gpFull LFull
  MFull)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Params (Rounds)
open P5T (N0Full)
open ProofFile (Cl)
open IM (Open k1Ix)

/-! ## 1 A place's parameters, through what the tests read -/

/-- The place (l, d) sends what the written place sends. -/
theorem parL_sent (Z : ProofFile.Pub) (G : ProofFile.Ground) (hs : G.first.shape = shapeFull) (l : ℕ)
    (d : Bool) :
    (parL Z G l d).sent = (parLater qFull gpFull l (k1Ix l d + 1) (momL d)).sent := by
  have e : qFull.shape = shapeFull := PlanWritten.request_shape_written
  apply Array.ext'
  cases d with
  | true =>
    show (parLater G.first (gpOf Z) l (k1Ix l true + 1) 2).sent.toList =
      (parLater qFull gpFull l (k1Ix l true + 1) 2).sent.toList
    rw [parLater_sent, parLater_sent, hs, e]
  | false =>
    show (parLater G.first (gpOf Z) l (k1Ix l false + 1) 1).sent.toList =
      (parLater qFull gpFull l (k1Ix l false + 1) 1).sent.toList
    rw [parLater_sent, parLater_sent, hs, e]

theorem parL_codes (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) :
    (parL Z G l d).codes = G.first.codes := by
  cases d <;> rfl

/-- It lays them as the written place does. -/
theorem parL_lay (Z : ProofFile.Pub) (G : ProofFile.Ground) (hc : G.first.codes = codesFull2)
    (hs : G.first.shape = shapeFull) (l : ℕ) (d : Bool) :
    layOf (parL Z G l d) = layOf (parLater qFull gpFull l (k1Ix l d + 1) (momL d)) := by
  unfold layOf
  rw [parL_sent Z G hs l d, parL_codes, hc]
  rfl

theorem parL_shapes (Z : ProofFile.Pub) (G : ProofFile.Ground) (hs : G.first.shape = shapeFull) (l : ℕ)
    (d : Bool) :
    shapesOf (parL Z G l d) = shapesOf (parLater qFull gpFull l (k1Ix l d + 1) (momL d)) := by
  unfold shapesOf
  rw [parL_sent Z G hs l d]

/-! ## 2 The numbers' two counts -/

theorem toldBy_toldOf {T C : Type} (bs : List (Block T C)) : toldBy bs = First.toldOf bs := by
  unfold toldBy First.toldOf
  simp [List.flatMap_id]

/-- Where the sub-protocols' places are the written list, the closed numbers are laid over it. -/
theorem atBlocks_written {T C : Type} (N₀ : Numbers) (s : ReqShape) (links : List ModelPart)
    (bs : List (Block T C)) (hps : blockPlaces bs = flatPlacesOf linksFull true) :
    N₀.atBlocks s links bs =
      (N₀.withRows s (First.possAt bs links.length) links.length).withTold
        (flatPlacesOf linksFull true) (First.toldOf bs) := by
  unfold Numbers.atBlocks
  rw [hps]

/-- The written cut has the written counts. -/
theorem countsAre_of_cut {T C : Type} {bs : List (Block T C)}
    (h : PlanWritten.cutOf bs = PlanWritten.cutFirstFull) : CountsAre (First.toldOf bs) := by
  rw [First.toldOf_cut, h]
  exact K13.Law.countsAre_cut

section
variable {T C : Type} {N : Numbers} {N₀ : Numbers} {s : ReqShape} {links : List ModelPart}
  {bs : List (Block T C)}

/-- **The two counts at each border are the written ones.** -/
theorem counts_at_blocks (hN : N = N₀.atBlocks s links bs)
    (hps : blockPlaces bs = flatPlacesOf linksFull true) (hC : CountsAre (First.toldOf bs)) {k : ℕ}
    (hk : k ≤ 358) :
    countsFull[k]? = some (N.msgsAt (flatPlacesOf linksFull true)[k]?,
      N.treesAt (flatPlacesOf linksFull true)[k]?) := by
  rw [hN, atBlocks_written N₀ s links bs hps]
  exact K13.Law.told_at _ hC hk

/-- **At each of the fifty the place's row, with the numbers' own two counts, stands in the written
list.** -/
theorem fifty_numbers (hN : N = N₀.atBlocks s links bs)
    (hps : blockPlaces bs = flatPlacesOf linksFull true) (hC : CountsAre (First.toldOf bs)) (l : ℕ)
    (hl : l < 25) (d : Bool) :
    (l, k1Ix l d + 1, momL d, N.msgsAt (flatPlacesOf linksFull true)[noL l d]?,
      N.treesAt (flatPlacesOf linksFull true)[noL l d]?) ∈ laterFull := by
  obtain ⟨m, t, hx, hc⟩ := fifty_at l hl d
  have h := counts_at_blocks hN hps hC (k := noL l d)
    (Nat.le_of_lt (Nat.lt_succ_of_lt (noL_lt l hl d)))
  rw [hc] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact hx

end

/-! ## 3 Two joints -/

/-- The converse of `laterSeatsOfTold`: where sub-protocol number k tells a list that is P's layout,
every message of P has a sample and nT trees are told in front. -/
theorem sentAt_of_laterSeats (N : Numbers) (told : List (List Oracle)) (k m t : ℕ) (P : Par)
    (decl : List Oracle) (ht : told[k]? = some decl)
    (D : Declares decl (layOf P) P.sent.size (tenantOf P))
    (hs : ∀ i, i < P.sent.size → (tenantOf P i).sampled = true)
    (hB : laterSeatsB N P m t (treesTold told k) = true) : sentAtB N told k m t = true := by
  unfold sentAtB
  unfold laterSeatsB at hB
  rw [ht]
  have hS := (sameMembers_iff _ _).1 (declaredSeats decl (layOf P) P.sent.size (tenantOf P) D hs)
  have hB' := (sameMembers_iff _ _).1 hB
  refine (sameMembers_iff _ _).2 fun x => ?_
  rw [← hB' x, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ((hS y).1 hy)
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, (hS _).2 (List.mem_map.2 ⟨i, hi, rfl⟩), rfl⟩

/-- The test `goesOnB` of PlanThree.lean (this folder) follows from the test of the same name
(Johnson/HB/LLHARD/PlanAtQFull.lean) at the data's two lists and the numbers' two counts. At
letters: nothing is evaluated. -/
theorem goesOn_of_plain {dk : K12Data} {N : Numbers} {p : Option Place} {P' : Par}
    (h : K13.Law.goesOnB dk.L dk.M (N.msgsAt p) (N.treesAt p) P' = true) :
    goesOnB dk N p P' = true := by
  unfold K13.Law.goesOnB at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  unfold goesOnB
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨beq_iff_eq.2 (of_decide_eq_true h.1.1), beq_iff_eq.2 (of_decide_eq_true h.1.2)⟩,
    beq_iff_eq.2 (of_decide_eq_true h.2)⟩

/-- It reads a place's parameters through what it sends and its layout alone. -/
theorem goesOnB_congr {dk : K12Data} {N : Numbers} {p : Option Place} {P P' : Par}
    (hs : P.sent = P'.sent) (hl : layOf P = layOf P') (hsh : shapesOf P = shapesOf P') :
    goesOnB dk N p P = goesOnB dk N p P' := by
  unfold goesOnB
  rw [hs, hl, hsh]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The piece's base at the place (l, d) is the numbers' count of trees there. -/
theorem baseL_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {e₁ : List (List ByteArray × ByteArray)}
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots) (N : Numbers)
    (hBook : First.bookFit N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true) (l : ℕ)
    (hl : l < 25) (d : Bool) :
    baseL aN R₁ R₂ R₃ c l d = N.treesAt (flatPlacesOf linksFull true)[noL l d]? := by
  obtain ⟨e, _, _, hflat, hu⟩ := k01_flat hS hR O l hl d
  obtain ⟨e7, hflat7, _, hu7⟩ := K13.Law.k13_sits_flat357 hS hR O
  have hk : noL l d < 357 := noL_lt l hl d
  have hroom := K13.Law.room_of_later c.blocksInOrder (noL l d) 357 e e7 hflat hflat7 hk
    (by rw [hu7.1]; exact Nat.zero_lt_one)
  exact base_at_flat aN R₁ R₂ R₃ c hWr hRoots (fun b hb => (hOk b hb).2) N _ hBook (noL l d)
    (Nat.le_of_lt (lt_places l hl d)) (by omega)

/-! ## 4 The ten -/

variable {N : Numbers} {s : ReqShape} {links : List ModelPart}

/-- **hRows.** -/
theorem hRows_at (hN : N = N0Full.atBlocks s links c.blocksInOrder) :
    First.eachOnce ((List.range 26).map fun m => (N.groupAt m, 0)) = true := by
  subst hN
  exact groupsOnce_id

/-- **hBook**, at any core. -/
theorem hBook_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {N₀ : Numbers}
    (hN : N = N₀.atBlocks s links c.blocksInOrder) :
    First.bookFit N (flatPlacesOf linksFull true) (toldBy c.blocksInOrder) = true := by
  rw [hN, atBlocks_written N₀ s links c.blocksInOrder (LPFK9.blockPlaces_full hS hR O), toldBy_toldOf]
  exact Sound.bookFit_withTold _ _ _ K13.Law.places_fit.2

/-- **hFence.** -/
theorem hFence_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder)) :
    First.fenceFit N linksFull (flatPlacesOf linksFull true) = true := by
  unfold First.fenceFit
  rw [List.all_eq_true]
  intro k hk
  have hk' : k ≤ 358 := by
    have := List.mem_range.1 hk
    rw [K13.Law.places_fit.1] at this
    omega
  rw [List.all_eq_true]
  intro u hu
  have hc := counts_at_blocks hN (LPFK9.blockPlaces_full hS hR O) hC hk'
  have e : First.sampledIn N
      ((First.openSets linksFull (flatPlacesOf linksFull true) (First.start linksFull))[k]?.getD
        []) = First.sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) k) := by
    subst hN
    exact K13.Law.sampledIn_core rfl rfl rfl rfl _
  rw [e] at hu
  exact decide_eq_true (fence_at hc u hu)

/-- **hidx.** -/
theorem hidx_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder))
    {seats : List (ℕ × ℕ)} (hseats : seats = seatsFull) :
    ∀ l, l < 25 → ∀ d : Bool,
      ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
        seats.idxOf u < N.msgsAt (flatPlacesOf linksFull true)[noL l d]? := by
  intro l hl d
  rw [hseats, hN, atBlocks_written N0Full s links c.blocksInOrder (LPFK9.blockPlaces_full hS hR O)]
  exact K13.Law.idx_of_counts (N := N0Full.withRows s _ _) rfl rfl rfl rfl hC
    (Nat.le_of_lt (Nat.lt_succ_of_lt (noL_lt l hl d)))

/-- **hNd.** -/
theorem hNd_at {seats : List (ℕ × ℕ)} (hseats : seats = seatsFull) : seats.Nodup := by
  rw [hseats]
  exact seats_nodup

/-- `laterSeatsB` at each of the fifty, at both moments. -/
theorem laterSeats_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder)) (l : ℕ)
    (hl : l < 25) (d : Bool) :
    laterSeatsB N (parL Z Bs.G₀ l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true := by
  have hx := fifty_numbers hN (LPFK9.blockPlaces_full hS hR O) hC l hl d
  have h : laterSeatsB N0Full (parLater qFull gpFull l (k1Ix l d + 1) (momL d)) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true :=
    List.all_eq_true.1 laterSeats_written _ hx
  have e : N.sent = N0Full.sent := by
    subst hN
    rfl
  unfold laterSeatsB at h ⊢
  rw [parL_sent Z Bs.G₀ hs l d, parL_lay Z Bs.G₀ hc hs l d, e]
  exact h

/-- **hP1.** -/
theorem hP1_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder)) :
    ∀ l, l < 25 → laterSeatsB N (parL Z Bs.G₀ l false) l 1
      (N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true :=
  fun l hl => laterSeats_at hS hR O hc hs hN hC l hl false

/-- **hSent.** -/
theorem hSent_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hok : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder)) :
    ∀ l, l < 25 → ∀ d : Bool, sentAtB N (toldBy c.blocksInOrder) (noL l d) l (momL d) = true := by
  intro l hl d
  have hB := laterSeats_at hS hR O hc hs hN hC l hl d
  rw [(First.bookFit_at N _ _ (hBook_at hS hR O hN) (noL l d)
    (Nat.le_of_lt (lt_places l hl d))).1] at hB
  have ht : ∃ decl, (toldBy c.blocksInOrder)[noL l d]? = some decl ∧
      Declares decl (layOf (parL Z Bs.G₀ l d)) (parL Z Bs.G₀ l d).sent.size
        (tenantOf (parL Z Bs.G₀ l d)) := by
    cases d with
    | true => exact tells_digits hS hR O hok l hl
    | false => exact tells_reads hS hR O hok l hl
  obtain ⟨decl, ht, hD⟩ := ht
  exact sentAt_of_laterSeats N _ (noL l d) l (momL d) _ decl ht hD
    (tenant_sampledL Z Bs.G₀ hs l hl d) hB

/-- **hSeats.** -/
theorem hSeats_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {e₁ : List (List ByteArray × ByteArray)}
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder))
    {seats : List (ℕ × ℕ)} (hseats : seats = seatsFull) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? =
        some (seatOfMsg (parL Z Bs.G₀ l d) (baseL aN R₁ R₂ R₃ c l d) j.val) := by
  intro l hl d j
  have hx := fifty_numbers hN (LPFK9.blockPlaces_full hS hR O) hC l hl d
  have h : ((List.range (shapesOf (parLater qFull gpFull l (k1Ix l d + 1) (momL d))).length).all
      fun j => decide (seatsFull[N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j]? =
        some (seatOfMsg (parLater qFull gpFull l (k1Ix l d + 1) (momL d))
          (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) j))) = true :=
    List.all_eq_true.1 seatsAt_written _ hx
  have hj : j.val < (shapesOf (parLater qFull gpFull l (k1Ix l d + 1) (momL d))).length := by
    rw [← parL_shapes Z Bs.G₀ hs l d]
    exact j.isLt
  have h1 := of_decide_eq_true (List.all_eq_true.1 h j.val (List.mem_range.2 hj))
  rw [hseats, baseL_at hS hR O hWr hOk hRoots N (hBook_at hS hR O hN) l hl d, h1]
  unfold seatOfMsg
  rw [parL_lay Z Bs.G₀ hc hs l d]

/-- `aheadAtB` at the 25 digits' places, at plain letters. -/
theorem ahead_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder)) (l : ℕ)
    (hl : l < 25) :
    aheadAtB shapeFull (N.sent l) (parL Z Bs.G₀ l true) l
      (cntAt shapeFull l 0 + cntAt shapeFull l 1)
      (N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true := by
  have hx := fifty_numbers hN (LPFK9.blockPlaces_full hS hR O) hC l hl true
  have h0 : ((2 : ℕ) != 2 || aheadAtB shapeFull (N0Full.sent l)
      (parLater qFull gpFull l (k1Ix l true + 1) (momL true)) l
      (cntAt shapeFull l 0 + cntAt shapeFull l 1)
      (N.treesAt (flatPlacesOf linksFull true)[noL l true]?)) = true :=
    List.all_eq_true.1 ahead_written _ hx
  have h : aheadAtB shapeFull (N0Full.sent l)
      (parLater qFull gpFull l (k1Ix l true + 1) (momL true)) l
      (cntAt shapeFull l 0 + cntAt shapeFull l 1)
      (N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true := h0
  have e : N.sent = N0Full.sent := by
    subst hN
    rfl
  unfold aheadAtB at h ⊢
  rw [parL_sent Z Bs.G₀ hs l true, parL_lay Z Bs.G₀ hc hs l true, parL_shapes Z Bs.G₀ hs l true,
    e]
  exact h

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV)

/-- By the make of the data: a segment's own messages of its first two sendings. -/
theorem dS1_own_size (l : ℕ) :
    (Dm.pubD.dS1.own l).size = cntAt Dm.shape l 0 + cntAt Dm.shape l 1 := by
  show (Dm.pubD.dS.own l ++
    secondNos Dm.shape (base1At Dm.N Dm.links (flatPlacesOf Dm.links true)) l).size = _
  rw [Array.size_append, dS_own_size]
  simp [secondNos, cntAt]

/-- **hAtA.** -/
theorem hAtA_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hDsh : Dm.shape = shapeFull)
    (hN : Dm.N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder)) :
    ∀ l, l < 25 → aheadAtB Dm.shape (Dm.N.sent l) (parL Z Bs.G₀ l true) l
      (Dm.pubD.dS1.own l).size
      (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true := by
  intro l hl
  rw [dS1_own_size, hDsh]
  exact ahead_at hS hR O hc hs hN hC l hl

end

/-- The three lists go on with what the place (l, d) lays. -/
theorem goesOn_at_counts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder))
    {dk : K12Data} (hL : dk.L = LFull) (hM : dk.M = MFull) (l : ℕ) (hl : l < 25) (d : Bool) :
    goesOnB dk N (flatPlacesOf linksFull true)[noL l d]? (parL Z Bs.G₀ l d) = true := by
  have hx := fifty_numbers hN (LPFK9.blockPlaces_full hS hR O) hC l hl d
  rw [goesOnB_congr (parL_sent Z Bs.G₀ hs l d) (parL_lay Z Bs.G₀ hc hs l d)
    (parL_shapes Z Bs.G₀ hs l d)]
  apply goesOn_of_plain
  rw [hL, hM]
  have h := List.all_eq_true.1 K13.Law.later_go_on _ hx
  exact h

/-- **hPlan3.** -/
theorem hPlan3_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder))
    {dk : K12Data} (hL : dk.L = LFull) (hM : dk.M = MFull) :
    planThreeB dk N Z Bs.G₀ = true := by
  unfold planThreeB
  rw [List.all_eq_true]
  intro l hl
  rw [List.all_eq_true]
  intro d _
  exact goesOn_at_counts hS hR O hc hs hN hC hL hM l (List.mem_range.1 hl) d

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.parL_sent
#print axioms VerifiableInference.Desc.K1.parL_lay
#print axioms VerifiableInference.Desc.K1.parL_shapes
#print axioms VerifiableInference.Desc.K1.toldBy_toldOf
#print axioms VerifiableInference.Desc.K1.atBlocks_written
#print axioms VerifiableInference.Desc.K1.countsAre_of_cut
#print axioms VerifiableInference.Desc.K1.counts_at_blocks
#print axioms VerifiableInference.Desc.K1.fifty_numbers
#print axioms VerifiableInference.Desc.K1.sentAt_of_laterSeats
#print axioms VerifiableInference.Desc.K1.baseL_at
#print axioms VerifiableInference.Desc.K1.hRows_at
#print axioms VerifiableInference.Desc.K1.hBook_at
#print axioms VerifiableInference.Desc.K1.hFence_at
#print axioms VerifiableInference.Desc.K1.hidx_at
#print axioms VerifiableInference.Desc.K1.hNd_at
#print axioms VerifiableInference.Desc.K1.laterSeats_at
#print axioms VerifiableInference.Desc.K1.hP1_at
#print axioms VerifiableInference.Desc.K1.hSent_at
#print axioms VerifiableInference.Desc.K1.hSeats_at
#print axioms VerifiableInference.Desc.K1.ahead_at
#print axioms VerifiableInference.Desc.K1.dS1_own_size
#print axioms VerifiableInference.Desc.K1.hAtA_at
#print axioms VerifiableInference.Desc.K1.goesOn_of_plain
#print axioms VerifiableInference.Desc.K1.goesOnB_congr
#print axioms VerifiableInference.Desc.K1.goesOn_at_counts
#print axioms VerifiableInference.Desc.K1.hPlan3_at
