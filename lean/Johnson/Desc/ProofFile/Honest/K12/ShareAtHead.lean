-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ShareAtHead.lean: K12's LOTS AGAINST THE WRITTEN PLAN's SEATS,
UNDER THE HEAD `P5J.AtMgA`. PUBLIC DATA ALONE: seats, sendings' numbers, the witness's numbers,
counts of rows. Two definitions, twelve theorems.

Why. The frame's authors' law that their joined list is fit under the head (`joinFit_head`,
Honest/Thread/JoinAtHead.lean) takes ten
hypotheses. Six of them its authors set apart as on the record of all senders but the shared
sending: hml, hpl, hfarM, hfarP, htn, hdis; of the four that it hands through, hown and htrees read
that record too (K12's share of hown: OwnedAtHead.lean). This file proves, for K12's lots taken by
themselves, five statements of the shapes of the six. It imports none of those authors' files that
are outside the sealed library: the shapes are stated over the booked `MsgLot`, `PadLot`,
`MsgsAgree`, `PadsAgree`.

  `farSeatB`, `farSeat_gives`   a Boolean on a list of `PSeat`: at (j, t) there is a seat, not a
                 kept copy's, whose sending is none of the shared sending's 52; and what it yields
                 as a proposition
  `planShape`   the shape recorded at (j, t) in a list of `PSeat`
  `testPl_seats_nodup`, `testPl_agree`   hpl's shape, at any job and any t₀
  `testTn_nodup`   htn's shape
  `testMsgLots_agree_of`   hml's shape, from "the numbers are pairwise different"
  `tenSeatsW`, `tenFarW`, `tenFarW_bite`, `tenRowsW`   evaluations in Lean's kernel at
                 `seatsAllFull`, the library's closed term for the list of 225 seats, reckoned from
                 the written sendings; the third is a control
  `hml_k12`, `hfarM_k12`, `hfarP_k12`   under the head, at t₀ = 77 and a job of six stages

By what. `pseatsAll_written` (Honest/K1/Law/K1NumAtHead.lean, of other authors) turns
`P5J.At.pseatsAll Zp` into `seatsAllFull` when h holds.

Limits.
- All that binds whoever builds on ScriptLots.lean (its head) binds here.
- FOR K12's LOTS BY THEMSELVES. `joinFit_head` has a single record for every sender but the shared
  sending. Its hml, hpl and htn therefore speak of K12's lots and the code switch's (K2's) in one
  list. That the two kinds' numbers, seats and members' numbers differ from each other is proved in
  neither the sealed library nor a hand-in for it that we have found; the code switch's authors have
  a file on it (Honest/K2/Law/SharesApartAtHead.lean: OwnedAtHead.lean's head, under "Why"). hfarM
  and hfarP are asked lot by lot, so two kinds' proofs simply add.
- hdis IS NOT HERE: it names terms of the frame's authors' files that are outside the sealed
  library.
- THREE THINGS ARE FIXED BY HAND AND TIED TO NOTHING: t₀ is written 77; arr is `P5J.At.arr Zp`; hJ
  assumes six stages. That the test's first switch's tree is number 77 in the chain is `treesTo_354`
  (OffAt354.lean), not called here; that a job's parameters have six stages is other files' matter.
  The test's own number in the chain does not occur.
- `hfarM_k12` and `hfarP_k12` copy the shape of two hypotheses of `joinFit_head`.
- `tenRowsW` IS ON COUNTS OF ROWS ONLY, AND NAMES NO FENCE. It compares the plan's (main rows, mask
  rows) at the ten seats with powers of two written out from the record's stages. Neither `fenceB`
  nor `stageMsg` occurs in it. The other half of a fence, the bound on places (C.l, Z.l), is not
  compared with anything: the plan records only the number of a code, and whether the code with that
  number has the stage's l for its message length is still open.
- `planShape` occurs in no statement. If no seat matches it gives the default shape, silently. It is
  a second candidate for the letters sh and sh₁ beside the library's `switchTargetStage … .shape`;
  that the two give one shape is not shown.
- The control tries two of the Boolean's five conditions (sending 81; no seat at all).
- h is assumed, not shown. Everything here is at the full size and with the earlier of the format's
  two hashes.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.LotsLaid
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open P5T (PSeat seatsAllFull arrOf)
open ProofFile.Honest.FirstThread

variable {Bk : ProverCoinCounts} {W X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **A Boolean on a list of `PSeat`**: at (j, t) there is a seat; its role is not that of a
kept copy; its sending is not 0, not 3 l + 1 or 3 l + 2 for an l under 25, and not 81: the shared
sending's 52. -/
def farSeatB (ps : List PSeat) (j t : ℕ) : Bool :=
  (ps.find? fun p => p.j == j && p.t == t).any fun q =>
    (match q.role with | .kept _ _ => false | _ => true) && q.send != 0 &&
      ((List.range 25).all fun l => q.send != 3 * l + momL false && q.send != 3 * l + momL true) &&
        q.send != 81

/-- The shape recorded at (j, t) in a list of `PSeat`. If no seat matches: the default shape. -/
def planShape (ps : List PSeat) (j t : ℕ) : OnBytes.OracleShape :=
  ((ps.find? fun p => p.j == j && p.t == t).map (·.shape)).getD default

/-- What `farSeatB` yields as a proposition. -/
theorem farSeat_gives {ps : List PSeat} {j t : ℕ} (hf : farSeatB ps j t = true) :
    ∃ q, (ps.find? fun p => p.j == j && p.t == t) = some q ∧ (∀ l' k', q.role ≠ .kept l' k') ∧
      q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  unfold farSeatB at hf
  cases hq : ps.find? (fun p => p.j == j && p.t == t) with
  | none =>
    rw [hq] at hf
    exact absurd hf Bool.false_ne_true
  | some q =>
    rw [hq] at hf
    simp only [Option.any_some, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true,
      List.mem_range] at hf
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hf
    refine ⟨q, rfl, ?_, h2, ?_, h4⟩
    · intro l' k' e
      rw [e] at h1
      exact absurd h1 Bool.false_ne_true
    · intro l hl d
      cases d
      · exact (h3 l hl).1
      · exact (h3 l hl).2

/-- No seat occurs twice among the lots of `testPl`, whatever the job and t₀. -/
theorem testPl_seats_nodup (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ) :
    ((testPl (Bk := Bk) ch J codes sh sh₁ t₀).map fun L => (L.j, L.t)).Nodup := by
  rw [seats_testPl]
  refine List.Nodup.append ?_ ?_ ?_
  · refine List.Nodup.map (fun a b e => ?_) List.nodup_range
    have := congrArg Prod.fst e
    simp only at this
    omega
  · refine List.Nodup.map (fun a b e => ?_) List.nodup_range
    have := congrArg Prod.fst e
    simp only at this
    omega
  · intro s h0 h1
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 h0
    obtain ⟨b, _, e⟩ := List.mem_map.1 h1
    have := congrArg Prod.snd e
    simp at this

/-- **hpl's shape, for K12's lots by themselves.** -/
theorem testPl_agree (ch : ℕ) (J : TestJob W X) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ) :
    PadsAgree (testPl (Bk := Bk) ch J codes sh sh₁ t₀) := by
  intro L hL L' hL' hj ht k w mask row place y y' h1 h2
  have e : L' = L := List.inj_on_of_nodup_map (testPl_seats_nodup ch J codes sh sh₁ t₀) hL' hL
    (Prod.ext hj ht)
  subst e
  exact Option.some.inj (h2.symm.trans h1)

/-- **htn's shape, for K12's lots by themselves.** -/
theorem testTn_nodup (b : ℕ) : (testTn b).Nodup :=
  List.nodup_singleton b

/-- If the numbers are pairwise different, the lots of messages agree. -/
theorem testMsgLots_agree_of (ch : ℕ) (J : TestJob W X) (own₀ : X) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    (hn : ((List.range (J.p.nums.stages.length - 1)).flatMap fun τ =>
      [arr (t₀ + τ) 0, arr (t₀ + τ) 1]).Nodup)
    :
    MsgsAgree (testMsgLots (Bk := Bk) ch J own₀ n₀ t₀ arr ok) := by
  intro L hL L' hL' hn' k w hd mask row place y y' h1 h2
  have e : L' = L := List.inj_on_of_nodup_map
    (by rw [nums_testMsgLots]; exact hn) hL' hL hn'
  subst e
  exact Option.some.inj (h2.symm.trans h1)

/-- **The ten seats in the written plan**: sending, place within the sending, role, and the
witness's number. -/
theorem tenSeatsW :
    ((List.range 5).flatMap fun τ => [0, 1].map fun t =>
      (seatsAllFull.find? fun p => p.j == 77 + τ && p.t == t).map fun q =>
        (q.send, q.idx, q.role, arrOf seatsAllFull (77 + τ) t)) =
      [some (76, 0, P5T.Role.other, 151), some (76, 1, P5T.Role.other, 152), some (77, 0,
        P5T.Role.other, 153), some (77, 1, P5T.Role.other, 154), some (78, 0, P5T.Role.other, 155),
        some (78, 1, P5T.Role.other, 156), some (79, 0, P5T.Role.other, 157), some (79, 1,
        P5T.Role.other, 158), some (80, 0, P5T.Role.other, 159),
        some (80, 1, P5T.Role.other, 160)] := by
  decide +kernel

/-- `farSeatB` accepts at all ten. -/
theorem tenFarW :
    ((List.range 5).all fun τ =>
      farSeatB seatsAllFull (77 + τ) 0 && farSeatB seatsAllFull (77 + τ) 1)
    = true := by
  decide +kernel

/-- A control. Tree 82 is W's, a sending of the shared sending's: `farSeatB` rejects at both
tenants. At (77, 2) the plan has no seat: it rejects. -/
theorem tenFarW_bite :
    farSeatB seatsAllFull 82 0 = false ∧ farSeatB seatsAllFull 82 1 = false ∧ farSeatB seatsAllFull
      77 2 = false := by
  decide +kernel

/-- **Counts of rows at the ten seats.** The plan's (main rows, mask rows); and the same list
written from the record's stages: 2 ^ k and 2 ^ h of the stage behind the switch at the first
tenant; at the second 0 and 2 ^ h, but 1 and 1 at the last switch. Rows only; no fence is named;
nothing on places. -/
theorem tenRowsW :
    ((List.range 5).flatMap fun τ => [0, 1].map fun t =>
      (seatsAllFull.find? fun p => p.j == 77 + τ && p.t == t).map fun q => (q.shape.mainRows,
        q.shape.maskRows)) =
      [some (16, 8), some (0, 8), some (8, 8), some (0, 8), some (8, 8), some (0, 8), some (16, 16),
        some (0, 16), some (1, 1), some (1, 1)] ∧
    ((List.range 5).flatMap fun τ =>
      [some (2 ^ (H2K.Member.piLFull.nums.stages.getD (τ + 1) default).k, 2 ^
        (H2K.Member.piLFull.nums.stages.getD (τ + 1) default).h),
       some (if τ = 4 then 1 else 0, if τ = 4 then 1 else 2 ^ (H2K.Member.piLFull.nums.stages.getD
         (τ + 1) default).h)]) =
      [some (16, 8), some (0, 8), some (8, 8), some (0, 8), some (8, 8), some (0, 8), some (16, 16),
        some (0, 16), some (1, 1), some (1, 1)] := by
  decide +kernel

/-- **hml's shape, for K12's lots by themselves, under the head.** -/
theorem hml_k12 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (ch : ℕ) (J : TestJob W X)
    (hJ : J.p.nums.stages.length = 6) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    MsgsAgree (testMsgLots (Bk := Bk) ch J own₀ n₀ 77 (P5J.At.arr Zp) ok) := by
  refine testMsgLots_agree_of ch J own₀ n₀ 77 _ ok ?_
  rw [hJ]
  unfold P5J.At.arr
  rw [K1.pseatsAll_written h]
  decide +kernel

/-- **hfarM's shape at K12's lots of messages, under the head.** -/
theorem hfarM_k12 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (ch : ℕ) (J : TestJob W X)
    (hJ : J.p.nums.stages.length = 6) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    ∀ L' ∈ testMsgLots (Bk := Bk) ch J own₀ n₀ 77 (P5J.At.arr Zp) ok, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  intro L' hL'
  unfold testMsgLots at hL'
  rw [hJ] at hL'
  obtain ⟨τ, hτ, hL'⟩ := List.mem_flatMap.1 hL'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hL'
  have hb := List.all_eq_true.1 tenFarW τ hτ
  rw [Bool.and_eq_true] at hb
  have hf : farSeatB seatsAllFull (77 + τ) t = true := by
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hb.1
    · rcases List.mem_cons.1 ht with rfl | ht
      · exact hb.2
      · exact absurd ht (List.not_mem_nil)
  obtain ⟨q, hq, hr⟩ := farSeat_gives hf
  exact ⟨77 + τ, t, q, by rw [K1.pseatsAll_written h]; exact hq, rfl, hr⟩

/-- **hfarP's shape at K12's lots of pads, under the head.** -/
theorem hfarP_k12 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (ch : ℕ) (J : TestJob W X)
    (hJ : J.p.nums.stages.length = 6) (codes : OnBytes.Codes) (sh sh₁ : ℕ → OnBytes.OracleShape) :
    ∀ L' ∈ testPl (Bk := Bk) ch J codes sh sh₁ 77, ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t =
      q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  intro L' hL'
  have key : ∀ τ, τ < 5 → ∀ t, (t = 0 ∨ t = 1) → ∃ q ∈ P5J.At.pseatsAll Zp, 77 + τ = q.j ∧ t = q.t ∧
      q.send ≠ 0 ∧ (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
    intro τ hτ t ht
    have hb := List.all_eq_true.1 tenFarW τ (List.mem_range.2 hτ)
    rw [Bool.and_eq_true] at hb
    have hf : farSeatB seatsAllFull (77 + τ) t = true := by
      rcases ht with rfl | rfl
      · exact hb.1
      · exact hb.2
    obtain ⟨q, hq, _, h2, h3, h4⟩ := farSeat_gives hf
    have hp := List.find?_some hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨q, by rw [K1.pseatsAll_written h]; exact List.mem_of_find?_eq_some hq, hp.1.symm,
      hp.2.symm, h2, h3, h4⟩
  unfold testPl testPadLots testPadLotsB at hL'
  rw [hJ] at hL'
  rcases List.mem_append.1 hL' with hL' | hL'
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hL'
    exact key τ (List.mem_range.1 hτ) 0 (Or.inl rfl)
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hL'
    exact key τ (List.mem_range.1 hτ) 1 (Or.inr rfl)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.farSeatB
#print axioms ProofFile.Honest.K12.planShape
#print axioms ProofFile.Honest.K12.farSeat_gives
#print axioms ProofFile.Honest.K12.testPl_seats_nodup
#print axioms ProofFile.Honest.K12.testPl_agree
#print axioms ProofFile.Honest.K12.testTn_nodup
#print axioms ProofFile.Honest.K12.testMsgLots_agree_of
#print axioms ProofFile.Honest.K12.tenSeatsW
#print axioms ProofFile.Honest.K12.tenFarW
#print axioms ProofFile.Honest.K12.tenFarW_bite
#print axioms ProofFile.Honest.K12.tenRowsW
#print axioms ProofFile.Honest.K12.hml_k12
#print axioms ProofFile.Honest.K12.hfarM_k12
#print axioms ProofFile.Honest.K12.hfarP_k12
