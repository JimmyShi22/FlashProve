-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/FirstBookOwn.lean: **THE PROMISE OF THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM, SECOND ARM (the first fold sends its own mask): "THE BOOK IS IN
ORDER" IN THE PLACE OF `FirstOpensOwn`.** Statements and proofs. The first arm: FirstBook.lean.

`FirstOpensOwn` (OwnArm.lean) has three clauses at what the record fixes: the declared openings' numbers over the file are those of the book's places D.ts · the members' trees
were sent in front of the stretch · the mask's tree is the stretch's first. Here D.book is not the record's book: it is the book BEHIND THE RECEIVING of the fold's mask.
  last_of_max      a strictly increasing list ends in its greatest member.
  own_facts        ON RECORDS ALONE: no mask is handed in · BookStep at the record (Johnson/Desc/Sound/BookInOrder.lean) · the front's clauses hold (a yes has them:
                   block_front_holds, Johnson/Desc/K12/SeatLaws.lean): then at what the record fixes: D.book is in order (a receiving keeps it) · each member's tree lies in the
                   record's own book, the mask's behind it: so D.ts ends in the mask's place and no member sits there.
  firstOpensOwn_of_yes   FirstOpensOwn at every statement from which the piece ever puts out: the first clause by first_of_book (FirstBook.lean), the second and third by
                   membersBelow | freshBase (Law/MasksFixed.lean).
  seat_of_bookOwn  AT A SEAT: a law whose whole promise is FirstOpensOwn at the record behind the door in holds with "no mask is handed in · BookStep" in its place.
  oFull_ownLabels | o_ownLabels   the test on the plan at the place of the test on Omega's group, full and small size (the kind's files' closed terms: a run's print made into terms).
Limits. As FirstBook.lean's. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.FirstBook
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.K12.Law.SwUnfold
import Johnson.Desc.Means.Layout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.First (gpOf Plain opensOf made_of tree_of_ts entered)
open H2K.Sw (recvP_ok bookSentP)

/-- A strictly increasing list ends in its greatest member. -/
theorem last_of_max : ∀ (l : List ℕ) (m : ℕ), l.Pairwise (· < ·) → m ∈ l → (∀ x ∈ l, x ≤ m) →
    l.getLast? = some m
  | [], m, _, hm, _ => absurd hm List.not_mem_nil
  | [a], m, _, hm, _ => by
    rw [List.mem_singleton.1 hm]
    rfl
  | a :: b :: t, m, hp, hm, hx => by
    rw [List.getLast?_cons_cons]
    have hp' := List.pairwise_cons.1 hp
    refine last_of_max (b :: t) m hp'.2 ?_ (fun x h => hx x (List.mem_cons_of_mem _ h))
    rcases List.mem_cons.1 hm with rfl | h
    · have h1 := hp'.1 b List.mem_cons_self
      have h2 := hx b (List.mem_cons_of_mem _ List.mem_cons_self)
      omega
    · exact h

/-- **On records alone.** -/
theorem own_facts (π : P12) (t : T12) (hm0 : t.mask = none)
    (hB : BookStep π.nums.firstTree t.book t.roots)
    (hfront : ∀ c ∈ frontL t.st t.book t.g t.mask, c.2 = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) :
    BookOrd π.nums.firstTree D.book ∧ D.ts.getLast? = some D.fresh.t ∧
      ∀ i, (D.mems.get i).t ≠ D.fresh.t ∧ (D.mems.get i).t ∈ D.ts := by
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  obtain ⟨cu, _, he⟩ := hmd.ent
  unfold entered at he
  dsimp only at he
  rw [hm0] at he
  dsimp only at he
  obtain ⟨⟨ids, d1⟩, hr, he⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨id, hid, he⟩ := Option.map_eq_some_iff.1 he
  obtain ⟨lay, _, hstep, hids, rfl⟩ := recvP_ok hr
  have eid : id = D.fresh.id := congrArg (fun q : ℕ × Statement × TreeBook => q.1) he
  have ebk : recvBook π.nums.firstTree t.book #[foldMaskNotice (ioppFoldShape cu Ly)] lay
      (begun t.st t.g G0).oracles.size t.roots = D.book :=
    congrArg (fun q : ℕ × Statement × TreeBook => q.2.2) he
  have hstep' : (begun t.st t.g G0).oracles.size = t.book.place.size := hstep
  have hBD := bookStep_recv π.nums.firstTree t.book #[foldMaskNotice (ioppFoldShape cu Ly)] lay
    (begun t.st t.g G0).oracles.size t.roots hB
  rw [ebk] at hBD
  -- the mask's place
  have hid' : id = t.book.place.size + 0 := by
    rw [hids] at hid
    simp only [Array.getElem?_map, Array.getElem?_range] at hid
    have h0 : (if 0 < (#[foldMaskNotice (ioppFoldShape cu Ly)] : Array OracleNotice).size then
        some 0 else none : Option ℕ) = some 0 := rfl
    rw [h0] at hid
    have := Option.some.inj hid
    rw [← this, ← hstep']
    exact (Nat.zero_add _).trans (Nat.add_zero _).symm
  have hfp := hmd.fresh.place
  rw [← ebk, ← eid, hid', recvBook_place_new π.nums.firstTree t.book
    #[foldMaskNotice (ioppFoldShape cu Ly)] lay _ t.roots 0 Nat.zero_lt_one] at hfp
  have hft : t.book.trees.size ≤ D.fresh.t := by
    have := congrArg Prod.fst (Option.some.inj hfp)
    have e : t.book.trees.size + lay.tree.getD 0 0 = D.fresh.t := this
    omega
  -- the members' places
  have hLy : Ly.members = G0.members := by
    have e := (OnBytes.Means.layout_eq t.st t.g G0 hf.2.1).symm.trans hf.2.2.1
    rw [← Option.some.inj e]
    rfl
  have hmem : ∀ i, (D.mems.get i).t < t.book.trees.size := by
    intro i
    obtain ⟨h1, h2⟩ := hmd.mem i
    have hin : (D.mems.get i).id ∈ G0.members.toList ++ t.mask.toList := by
      refine List.mem_append_left _ ?_
      rw [← hLy, Array.mem_toList_iff]
      exact Array.mem_of_getElem? h1
    obtain ⟨q, T, hq, hT⟩ := Seat.front_trees hfront hf.2.1 _ hin
    have ho : (D.mems.get i).id < t.book.place.size := (Array.getElem?_eq_some_iff.1 hq).1
    have hp := h2.place
    rw [← ebk, recvBook_place_old π.nums.firstTree t.book _ lay _ t.roots _ ho, hq] at hp
    have e : q.1 = (D.mems.get i).t := congrArg Prod.fst (Option.some.inj hp)
    rw [← e]
    exact (Array.getElem?_eq_some_iff.1 hT).1
  refine ⟨hBD.2, ?_, fun i => ⟨by have := hmem i; omega, ?_⟩⟩
  · rw [hmd.ts]
    refine last_of_max _ _ (Fmt.listOf_incr _) ((Fmt.listOf_mem _ _).2 (by simp)) fun x hx => ?_
    rcases List.mem_append.1 ((Fmt.listOf_mem _ _).1 hx) with h | h
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
      obtain ⟨i, rfl⟩ := List.get_of_mem hm
      have := hmem i
      omega
    · rw [List.mem_singleton.1 h]
  · rw [hmd.ts]
    exact (Fmt.listOf_mem _ _).2 (List.mem_append_left _ (List.mem_map.2 ⟨_, List.get_mem _ i, rfl⟩))

/-- **`FirstOpensOwn` at every statement from which the piece ever puts out.** -/
theorem firstOpensOwn_of_yes {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = true)
    (hP : ownLabelsB π = true) (t₁ t₂ c base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (n1 : ∀ n, VerifiableInference.Desc.numAt t₁ t₂ c (.own (π.nums.free + n)) = base + n)
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base)
    (x : T12 × F.E.Str) (hm : x.1.mask = none)
    (hB : BookStep π.nums.firstTree x.1.book x.1.roots)
    (hy : ∃ τ b, (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) :
    FirstOpensOwn π (VerifiableInference.Desc.numAt t₁ t₂ c)
      (fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z)) base x.1 := by
  obtain ⟨τ, b, hb⟩ := hy
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x τ b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) τ)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 τ).opened = .ok (b.1, k) :=
    hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨_, hfront, _⟩ := Seat.block_front_holds π x.1 b.1 _ _ hdec
  intro a rest G0 Ly D hf
  obtain ⟨hO, hlast, hmem⟩ := own_facts π x.1 hm hB hfront a rest G0 Ly D hf
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  have h1 := first_of_book π t₁ t₂ c a rest hf.1 hP D hmd.opens
    (yes_labels F π he hp base dB dt e₀ εt x τ b hb a rest G0 Ly D hf)
    (fun z hz => tree_of_ts π _ a Ly D hmd z hz) hO
  have M := H2K.Made.masksFixed_of_planOk π hp
  refine ⟨h1, fun i => ?_, M.freshBase ho a rest hf.1 _ base n1 D _ hmd.opens h1 hlast⟩
  exact M.membersBelow ho a rest hf.1 _ base n1 n2 n3 D _ hmd.opens h1 hlast
    (fun z _ e => Nat.add_left_cancel e) _ (hmem i).2 (hmem i).1

/-- **AT A SEAT.** law: the kind's law at the block seated by two doors, with `FirstOpensOwn` at the record behind the door in as its whole promise: a letter. -/
theorem seat_of_bookOwn {S W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = true)
    (hP : ownLabelsB π = true) (t₁ t₂ c base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (n1 : ∀ n, VerifiableInference.Desc.numAt t₁ t₂ c (.own (π.nums.free + n)) = base + n)
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (Q : S × F.E.Str → S × F.E.Str → Prop)
    (law : (seated (pieceT F W π base dB dt e₀ εt) enter leave).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π (VerifiableInference.Desc.numAt t₁ t₂ c)
        (fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z)) base t) Q
      (seated (pieceT F W π base dB dt e₀ εt) enter leave).err) :
    (seated (pieceT F W π base dB dt e₀ εt) enter leave).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t →
        t.mask = none ∧ BookStep π.nums.firstTree t.book t.roots) Q
      (seated (pieceT F W π base dB dt e₀ εt) enter leave).err := by
  intro a ha
  by_cases hy : ∃ τ b, (seated (pieceT F W π base dB dt e₀ εt) enter leave).ior.red.out a τ = some b
  · obtain ⟨τ, b, hb⟩ := hy
    obtain ⟨t₀, t', h1, h2, _⟩ := seated_out (pieceT F W π base dB dt e₀ εt) enter leave a τ b hb
    refine law a fun t ht => ?_
    obtain rfl : t₀ = t := Except.ok.inj (h1.symm.trans ht)
    exact firstOpensOwn_of_yes F π he hp ho hP t₁ t₂ c base dB dt e₀ εt n1 n2 n3 (t₀, a.2)
      (ha t₀ h1).1 (ha t₀ h1).2 ⟨τ, _, h2⟩
  · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hy

/-- The test on the plan at the place of the test on Omega's group: the full size. -/
theorem oFull_ownLabels : ownLabelsB H2K.Member.piOFull = true := by decide +kernel

/-- The small size. -/
theorem o_ownLabels : ownLabelsB H2K.Member.piO = true := by decide +kernel

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.own_facts
#print axioms VerifiableInference.Desc.K12.Coin.firstOpensOwn_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.seat_of_bookOwn
#print axioms VerifiableInference.Desc.K12.Coin.oFull_ownLabels
#print axioms VerifiableInference.Desc.K12.Coin.o_ownLabels
