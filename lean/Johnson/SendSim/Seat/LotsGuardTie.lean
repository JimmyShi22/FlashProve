-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotsGuardTie.lean: what the three parts of Johnson/SendSim/Seat/LotsGuard.lean
give. At every owner at which the further test accepts and the guard's premise holds, every job of
the two lists whose sender is that owner has the premises on the book under which the field fresh is
proved.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". For runs, the guard and the two-part
test: the head of Johnson/SendSim/At/GuardTest.lean. Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Z is any public part, G any ground, Bk any book, ord any order and o any
address. The parameters no and D of the jobs are arbitrary.
  spendersClear_of_parts   The main statement. If lotsOwnerFitsB accepts at o, and GuardClearE
                     (Johnson/SendSim/At/GuardTestTie.lean) holds at the guard lotsGuardE Z G o at
                     each address that has a spending entry on o's coins, then for every job J of
                     the two lists whose sender's address is o, SpendersClearAny holds at J's
                     numbers (Johnson/SendSim/At/SpendersAlone.lean). Under that premise the field
                     fresh is proved at a seated side (sendFreshAtSpendersWide,
                     Johnson/SendSim/At/SpendersAloneProofs.lean).
  lotsMine_job       If lotsMine accepts at o, some job of the two lists has the sender's address o.
                     So the main statement is not vacuous at an owner that lotsMine accepts.
  lotsMine_of_fits   If lotsOwnerFitsB accepts at o, so does lotsMine.
  spendersClear_all  If lotsOkB accepts at every owner of a spending entry of the book at which
                     lotsMine accepts, then SpendersClearAny holds at every job of the two lists. At
                     a sender of which nothing is spent it holds vacuously.
  clear_at_jobs      If lotsOkB accepts at o, the book meets BookClearAny at every job of the two
                     lists whose sender's address is o.
  lotsOkB_iff        lotsOkB accepts at the sender's address of every entry of lotPars Z G if and
                     only if lotPlacesApartB Z G and lotsClearB Z G Bk ord accept
                     (Johnson/SendSim/Seat/LotsTest.lean).
  clear_of_lotsOkB   So, with lotsClearB_iff (Johnson/SendSim/Seat/LotsTestTie.lean): if lotsOkB
                     accepts at all these addresses, the book meets BookClearAny at the sender of
                     every job of the two lists. At G = Bs.G₀ that is the premise on the book of
                     hand_of_lots (AtDescLots.lean).
  lotsGuardE_prefix  The guard begins with the spent runs themselves, at every address.

How it fits. LotsGuard.lean gives our premise on the book as a choice of owners, a guard and a
further test. spendersClear_of_parts is what this folder provides for them: it holds at every
address, so also at every address that lotsMine accepts. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Why a lotsMine that is too wide could do no harm. The main statement does not use lotsMine:
lotsOwnerFitsB rejects at every address at which lotAt finds no job, so a lotsMine that is too wide
could not make a book pass. It would not make a proof in this file fail. That lotsMine is not too
wide is lotsMine_job (through lotAt_spec): it accepts only senders' addresses.

The other names. find_of_nodup: in a list without two members of one value under f, find? at x's
value returns x. lotAt_spec: what lotAt returns at o is an entry of lotPars, and o is that entry's
sender's address. lotAt_of_mem: if lotPlacesApartB accepts, lotAt returns each entry of lotPars at
its sender's address. lotAt_of_job: the same for a job. fits_parts: what lotsOwnerFitsB says.
lotsOkB_at: where lotPlacesApartB accepts, lotsOkB at an entry's sender is ownerOkB
(Johnson/SendSim/At/GuardTest.lean) at that entry. lotsMine_of_mem: lotsMine accepts at the sender's
address of every entry of lotPars.

Limits. Every statement here is about the book and the public numbers; none is about a distribution.
No test is evaluated here. lotPlacesApartB accepts at every public part and ground (lotPlacesApart,
LotPlaces.lean), so the premise on it in lotAt_of_mem, lotAt_of_job and lotsOkB_at always holds.
spendersClear_all gives SpendersClearAny, not BookClearAny. A test that is asked only at the owners
of spending entries leaves open whether the carried entries of a sender of which nothing is spent
are within its number of coins. So it does not give the premise of hand_of_lots. It is enough for
the field fresh (sendFreshAtSpendersWide), where that clause is not needed.
-/
import Johnson.SendSim.Seat.LotsGuard
import Johnson.SendSim.Seat.LotsTestTie
import Johnson.SendSim.At.GuardTestTie

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {X Xi : Type}

/-! ## The look-up -/

/-- In a list without two members of one value under f, find? at x's value returns x. -/
theorem find_of_nodup {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) :
    ∀ l : List α, (l.map f).Nodup → ∀ x ∈ l, (l.find? fun y => f y == f x) = some x
  | [], _, _, hx => by cases hx
  | a :: l, h, x, hx => by
    have h' : (f a :: l.map f).Nodup := h
    obtain ⟨ha, hn⟩ := List.nodup_cons.1 h'
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp only [List.find?_cons, beq_self_eq_true]
    · have hne : f a ≠ f x := fun e => ha (e ▸ List.mem_map.2 ⟨x, hx', rfl⟩)
      have hb : (f a == f x) = false := beq_eq_false_iff_ne.2 hne
      simp only [List.find?_cons, hb]
      exact find_of_nodup f l hn x hx'

/-- What lotAt returns at o is an entry of lotPars, and o is that entry's sender's address. -/
theorem lotAt_spec {Z : ProofFile.Pub} {G : ProofFile.Ground} {o : Addr} {x : K1.Par × (Nat → Option Ride)}
    (h : lotAt Z G o = some x) : x ∈ lotPars Z G ∧ o = ⟨x.1.place, 0⟩ := by
  unfold lotAt at h
  split_ifs at h with hp
  have hp1 : o.part = 0 := beq_iff_eq.1 hp
  have hp2 : (x.1.place == o.place) = true :=
    List.find?_some (p := fun y : K1.Par × (Nat → Option Ride) => y.1.place == o.place) h
  have hp3 : x.1.place = o.place := beq_iff_eq.1 hp2
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  obtain ⟨a, n⟩ := o
  simp only at hp1 hp3
  rw [hp1, hp3]

/-- If no two jobs are at one place, lotAt returns each entry of lotPars at its sender's address. -/
theorem lotAt_of_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} (hN : lotPlacesApartB Z G = true)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ lotPars Z G) :
    lotAt Z G ⟨x.1.place, 0⟩ = some x := by
  have e : lotAt Z G ⟨x.1.place, 0⟩ = (lotPars Z G).find? fun y => y.1.place == x.1.place := rfl
  have hn : ((lotPars Z G).map (·.1.place)).Nodup := of_decide_eq_true hN
  rw [e]
  exact find_of_nodup (·.1.place) _ hn x hx

/-- If no two jobs are at one place, lotAt returns each job's numbers at its sender's address. -/
theorem lotAt_of_job {Z : ProofFile.Pub} {G : ProofFile.Ground} (hN : lotPlacesApartB Z G = true)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G) :
    lotAt Z G ⟨J.P.place, 0⟩ = some (J.P, J.ride) :=
  lotAt_of_mem hN (x := (J.P, J.ride)) (by
    rw [lotPars_eq (X := X) no D Z G]
    exact List.mem_map.2 ⟨J, hJ, rfl⟩)

/-- lotsMine accepts at the sender's address of every entry of lotPars. -/
theorem lotsMine_of_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : K1.Par × (Nat → Option Ride)}
    (hx : x ∈ lotPars Z G) : lotsMine Z G ⟨x.1.place, 0⟩ = true := by
  have e : lotAt Z G ⟨x.1.place, 0⟩ = (lotPars Z G).find? fun y => y.1.place == x.1.place := rfl
  unfold lotsMine
  rw [e, List.find?_isSome]
  exact ⟨x, hx, beq_self_eq_true _⟩

/-- If lotsMine accepts at o, some job of the two lists has the sender's address o. -/
theorem lotsMine_job {Z : ProofFile.Pub} {G : ProofFile.Ground} (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {o : Addr} (hm : lotsMine Z G o = true) :
    ∃ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G, (⟨J.P.place, 0⟩ : Addr) = o := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hm
  obtain ⟨hmem, ho⟩ := lotAt_spec hx
  rw [lotPars_eq (X := X) no D Z G] at hmem
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hmem
  exact ⟨J, hJ, ho.symm⟩

/-- What lotsOwnerFitsB says: no two jobs are at one place, lotAt finds an entry, and ownerFitsB
accepts at it. -/
theorem fits_parts {Z : ProofFile.Pub} {G : ProofFile.Ground} {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (hf : lotsOwnerFitsB Z G Bk ord o = true) :
    lotPlacesApartB Z G = true ∧ ∃ x, lotAt Z G o = some x ∧ ownerFitsB x.1 x.2 Bk o = true := by
  unfold lotsOwnerFitsB at hf
  rw [Bool.and_eq_true] at hf
  refine ⟨hf.1, ?_⟩
  cases hx : lotAt Z G o with
  | none =>
    have h2 := hf.2
    rw [hx] at h2
    cases h2
  | some x =>
    have h2 := hf.2
    rw [hx] at h2
    exact ⟨x, rfl, h2⟩

/-- If lotsOwnerFitsB accepts at o, so does lotsMine. -/
theorem lotsMine_of_fits {Z : ProofFile.Pub} {G : ProofFile.Ground} {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (hf : lotsOwnerFitsB Z G Bk ord o = true) : lotsMine Z G o = true := by
  obtain ⟨-, x, hx, -⟩ := fits_parts hf
  unfold lotsMine
  rw [hx]
  rfl

/-- The guard begins with the spent runs themselves, at every address. -/
theorem lotsGuardE_prefix (Z : ProofFile.Pub) (G : ProofFile.Ground) (o : Addr) (e : List (Nat × Nat)) :
    e <+: lotsGuardE Z G o e := by
  unfold lotsGuardE
  cases lotAt Z G o with
  | none => exact List.prefix_refl _
  | some x => exact guard_prefix x.1 x.2 e

/-! ## What the three parts give -/

/-- **If the further test accepts at o, and the guard's premise holds at each address that has a
spending entry on o's coins, then every job of the two lists whose sender's address is o has the
premises on the book at each address that spends (SpendersClearAny).** -/
theorem spendersClear_of_parts {Z : ProofFile.Pub} {G : ProofFile.Ground} (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (hf : lotsOwnerFitsB Z G Bk ord o = true)
    (hg : ∀ p, Bk.spentBy o p ≠ [] → GuardClearE (lotsGuardE Z G o) Bk ord o p) :
    ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G, (⟨J.P.place, 0⟩ : Addr) = o →
      SpendersClearAny J.P J.ride Bk ord o := by
  intro J hJ ho
  obtain ⟨hN, x, hx, hfx⟩ := fits_parts hf
  have hat := lotAt_of_job hN no D hJ
  rw [ho, hx] at hat
  obtain rfl : x = (J.P, J.ride) := Option.some.inj hat
  refine spendersClearAny_of_guard hfx fun p hp => ?_
  have h := hg p hp
  have e : lotsGuardE Z G o = sendGuardE J.P J.ride := by
    funext r
    unfold lotsGuardE
    rw [hx]
  rw [e] at h
  exact h

/-- Where no two jobs are at one place, lotsOkB at an entry's sender is the two-part test ownerOkB
at that entry. -/
theorem lotsOkB_at {Z : ProofFile.Pub} {G : ProofFile.Ground} (hN : lotPlacesApartB Z G = true)
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ lotPars Z G) (Bk : ProverCoinCounts) (ord : List Place) :
    lotsOkB Z G Bk ord ⟨x.1.place, 0⟩ = ownerOkB x.1 x.2 Bk ord ⟨x.1.place, 0⟩ := by
  unfold lotsOkB lotsOwnerFitsB lotsGuardE
  rw [lotAt_of_mem hN hx, hN, Bool.true_and]
  rfl

/-- If lotsOkB accepts at o, the book meets BookClearAny at every job of the two lists whose
sender's address is o. -/
theorem clear_at_jobs {Z : ProofFile.Pub} {G : ProofFile.Ground} (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (h : lotsOkB Z G Bk ord o = true) :
    ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G, (⟨J.P.place, 0⟩ : Addr) = o →
      BookClearAny J.P J.ride Bk ord o := by
  intro J hJ ho
  have hf : lotsOwnerFitsB Z G Bk ord o = true := by
    unfold lotsOkB at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have hN := (fits_parts hf).1
  have hx : (J.P, J.ride) ∈ lotPars Z G := by
    rw [lotPars_eq (X := X) no D Z G]
    exact List.mem_map.2 ⟨J, hJ, rfl⟩
  have e := lotsOkB_at hN hx Bk ord
  subst ho
  rw [e] at h
  exact ownerOkB_iff.1 h

/-- **lotsOkB accepts at all senders exactly if no two jobs are at one place and lotsClearB
accepts.** -/
theorem lotsOkB_iff (Z : ProofFile.Pub) (G : ProofFile.Ground) (Bk : ProverCoinCounts) (ord : List Place) :
    (∀ x ∈ lotPars Z G, lotsOkB Z G Bk ord ⟨x.1.place, 0⟩ = true) ↔
      (lotPlacesApartB Z G = true ∧ lotsClearB Z G Bk ord = true) := by
  have key : lotPlacesApartB Z G = true →
      ((∀ x ∈ lotPars Z G, lotsOkB Z G Bk ord ⟨x.1.place, 0⟩ = true) ↔
        lotsClearB Z G Bk ord = true) := by
    intro hN
    unfold lotsClearB
    rw [List.all_eq_true]
    refine forall₂_congr fun x hx => ?_
    rw [lotsOkB_at hN hx, ownerOkB_iff, bookClearAnyB_iff]
  constructor
  · intro h
    have h0 := h _ (show (K1.firstPar G.first (K1.gpOf Z), rideOf (firstFold G.first)) ∈
      lotPars Z G from List.mem_append_left _ (List.mem_cons_self ..))
    unfold lotsOkB at h0
    rw [Bool.and_eq_true] at h0
    have hN := (fits_parts h0.1).1
    exact ⟨hN, (key hN).1 h⟩
  · rintro ⟨hN, hc⟩
    exact (key hN).2 hc

/-- If lotsOkB accepts at every sender, the book meets BookClearAny at the sender of every job of
the two lists. -/
theorem clear_of_lotsOkB {Z : ProofFile.Pub} {G : ProofFile.Ground} (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (h : ∀ x ∈ lotPars Z G, lotsOkB Z G Bk ord ⟨x.1.place, 0⟩ = true) :
    ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G,
      BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ :=
  (lotsClearB_iff no D Z G Bk ord).1 ((lotsOkB_iff Z G Bk ord).1 h).2

/-- **If lotsOkB accepts at every owner of a spending entry at which lotsMine accepts, every job of
the two lists has the premises on the book at each address that spends.** -/
theorem spendersClear_all {Z : ProofFile.Pub} {G : ProofFile.Ground} (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {Bk : ProverCoinCounts} {ord : List Place}
    (h : ∀ e ∈ Bk.ahead, e.once = true → lotsMine Z G e.owner = true →
      lotsOkB Z G Bk ord e.owner = true) :
    ∀ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G,
      SpendersClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ := by
  intro J hJ
  by_cases hs : ∃ e ∈ Bk.ahead, e.once = true ∧ e.owner = ⟨J.P.place, 0⟩
  · obtain ⟨e, he, h1, h2⟩ := hs
    have hx : (J.P, J.ride) ∈ lotPars Z G := by
      rw [lotPars_eq (X := X) no D Z G]
      exact List.mem_map.2 ⟨J, hJ, rfl⟩
    have hm : lotsMine Z G e.owner = true := by
      rw [h2]
      exact lotsMine_of_mem hx
    have hok := h e he h1 hm
    rw [h2] at hok
    exact spendersClearAny_of_bookClearAny (clear_at_jobs no D hok J hJ rfl)
  · intro p hp
    exact absurd (spentBy_nil_of_no_spending (fun e he h1 h2 => hs ⟨e, he, h1, h2⟩) p) hp

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.find_of_nodup
#print axioms OnBytes.SendSim.Seat.lotAt_spec
#print axioms OnBytes.SendSim.Seat.lotAt_of_mem
#print axioms OnBytes.SendSim.Seat.lotAt_of_job
#print axioms OnBytes.SendSim.Seat.lotsMine_of_mem
#print axioms OnBytes.SendSim.Seat.lotsMine_job
#print axioms OnBytes.SendSim.Seat.fits_parts
#print axioms OnBytes.SendSim.Seat.lotsMine_of_fits
#print axioms OnBytes.SendSim.Seat.lotsGuardE_prefix
#print axioms OnBytes.SendSim.Seat.spendersClear_of_parts
#print axioms OnBytes.SendSim.Seat.lotsOkB_at
#print axioms OnBytes.SendSim.Seat.clear_at_jobs
#print axioms OnBytes.SendSim.Seat.lotsOkB_iff
#print axioms OnBytes.SendSim.Seat.clear_of_lotsOkB
#print axioms OnBytes.SendSim.Seat.spendersClear_all
