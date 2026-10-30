-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CarryShut.lean: the open item `carry m` of the first chain's
invariant passes over the third sub-protocol of a segment's closing ("the segment is shut", kind
K9). No definition.

At `lettersHead` the item's statement is the variable `carryX`. The authors of kind K2 have written
a text for it, `carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean). It reads the verifier's state
through the library's function `doorZ` alone (Johnson/Top/H0/K2Caller/CarryClosed.lean), and it
reads no string. The shutting writes one flag and two marks of the open segment's record. `doorZ`
returns the same value before and after that writing.

  1  `rest_shut`, `doorZ_shut`   the library's `rest` and `doorZ` return the same before and after
     the writing that the clause of `keeps` at the shutting names (`ShutKeeps`,
     Honest/K9/CloseKeeps.lean)
  2  `carry_cell_shut`   the hypothesis `RidesPastAtS` (Honest/Thread/SharesS.lean) at the number of
     segment `l`'s shutting. The invariant's `keeps` is `kpBy fHead`. Hypothesis `hX`: `carryX`
     passes between two states at which `doorZ` returns the same
  3  `carryAt_full`, `carryAt_control`, `carry_k9_number`   a closed test by Lean's kernel on the
     written lists: at a place of the kind K9 before which an item `carry` is open, the number is
     that of a segment's shutting. The negative test: at the number of "the one equation" the test
     fails
  4  `cell_carry_k9`   the cell by the kind of the place, at `kpBy fHeadG`, under `hX`
  5  `carryExact_door`   `carryExact` meets `hX`
  6  `cell_carry_k9_exact`   the cell at `carryX := carryExact Zp (P5J.At.arr Zp)`, without `hX`.
     That this term has the type of the variable `carryX` is checked by the statement itself

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that the item's statement holds at any state of a run. The authors of
    `carryExact` say the same of their text.
  * The item also passes over the frame's sub-protocols and, for `carry 23`, over number 338. This
    file does not treat them.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsByKind
import Johnson.Desc.ProofFile.Honest.Thread.CarryRides
import Johnson.Desc.K2.Honest.Carry.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.First.K2Caller (rest doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The way in, before and after the shutting -/

/-- `rest` returns the same. -/
theorem rest_shut {s : S} {L : OnBytes.Model.LinkCtx} (hL : s.link? = some L) :
    rest (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) = rest s := by
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
  cases here with
  | between => exact nomatch hL
  | fin a => exact nomatch hL
  | mem a => exact nomatch hL
  | lay a =>
    obtain rfl : a.L = L := Option.some.inj hL
    rfl
  | att a =>
    obtain rfl : a.L = L := Option.some.inj hL
    rfl
  | head a =>
    by_cases ho : a.opened = true
    · have e : a.L = L := by simpa [S.link?, ho] using hL
      subst e
      simp [rest, S.inLink, S.fork?, S.putLink, S.live, S.link?, ho,
        VerifiableInference.Desc.K9.closed]
    · simp [S.link?, ho] at hL

/-- `doorZ` returns the same. -/
theorem doorZ_shut (Z : ProofFile.Pub) (m : Nat) {s : S} {L : OnBytes.Model.LinkCtx}
    (hL : s.link? = some L) :
    doorZ Z m (s.putLink (VerifiableInference.Desc.K9.closed L L.check.frame)) = doorZ Z m s := by
  have hr := rest_shut hL
  unfold doorZ
  rw [hr]
  generalize (ProofFile.pAtK2 Z m).stands = σ
  cases σ with
  | link => rfl
  | finish => rfl
  | head =>
    obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
    cases here with
    | between => exact nomatch hL
    | fin a => exact nomatch hL
    | mem a => exact nomatch hL
    | lay a => rfl
    | att a => rfl
    | head a =>
      by_cases ho : a.opened = true
      · simp [S.putLink, ho]
      · simp [S.link?, ho] at hL

/-! ## 3 The closed test -/

set_option maxRecDepth 1000000 in
/-- At a place of the kind K9 before which an item `carry` is open. -/
theorem carryAt_full : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K9) ||
      (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
        match i with
        | .carry _ => (List.range 25).any fun l => b == 14 * l + IM.nAt l + 6
        | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the number of "the one equation" the same test fails. -/
theorem carryAt_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K9) ||
      (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
        match i with
        | .carry _ => (List.range 25).any fun l => b == 14 * l + IM.nAt l + 4
        | _ => true) = false := by
  decide +kernel

/-- The test at a place. -/
theorem carry_k9_number {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) {m : Nat}
    (ho : Item.carry m ∈ IM.openAt P5J.At.links P5J.At.ps b) :
    ∃ l, l < 25 ∧ b = 14 * l + IM.nAt l + 6 := by
  have t := List.all_eq_true.1 carryAt_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · rw [hk] at t0
    exact absurd t0 (by decide)
  · have t2 : ((List.range 25).any fun l => b == 14 * l + IM.nAt l + 6) = true :=
      List.all_eq_true.1 t1 _ ho
    obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t2
    exact ⟨l, List.mem_range.1 hl, eq_of_beq e⟩

/-! ## 2, 4, 5 and 6 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- Over the shutting of segment `l`. -/
theorem carry_cell_shut
    (hX : ∀ (m : Nat) (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF),
      doorZ Zp m s' = doorZ Zp m s → carryX m (z, s) y v → carryX m (z, s') y' v)
    {l : Nat} (hl : l < 25) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread Said
      (14 * l + IM.nAt l + 6) (Item.carry m) :=
  ridesPastAtS_of _ _ (ridesPastAt_carry_of h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w m fun s s' hk z y y' v => by
      obtain ⟨-, -, L, hL, rfl⟩ := head_keeps_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (fHead Zp cF G take P11 p12 P13) w rfl hl s s' hk
      exact hX m z s _ y y' v (doorZ_shut Zp m hL))

/-- The item `carry m` at a place of the kind K9. -/
theorem cell_carry_k9
    (hX : ∀ (m : Nat) (z : ProofFile.InstPub) (s s' : TS) (y y' : Strs) (v : WtF),
      doorZ Zp m s' = doorZ Zp m s → carryX m (z, s) y v → carryX m (z, s') y' v)
    {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) {m : Nat}
    (hi : Item.carry m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.carry m ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.carry m) := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl⟩ := carry_k9_number hb hp hk ho
  exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
    (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (carry_cell_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
      P11 p12 P13 Said hX hl m)

/-- `carryExact` passes between two states at which `doorZ` returns the same. -/
theorem carryExact_door (Zp : ProofFile.Pub) (arr : Nat → Nat → Nat) (m : Nat) (z : ProofFile.InstPub)
    (s s' : TS) (y y' : Strs) (v : WtF) (e : doorZ Zp m s' = doorZ Zp m s)
    (c : carryExact Zp arr m (z, s) y v) : carryExact Zp arr m (z, s') y' v := by
  obtain ⟨t, fx, h1, h2, h3⟩ := c
  exact ⟨t, fx, e.trans h1, h2, h3⟩

/-- The item `carry m` at a place of the kind K9, at the text `carryExact`. -/
theorem cell_carry_k9_exact {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) {m : Nat}
    (hi : Item.carry m ∈ (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.carry m ∉ ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
      Rd (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.carry m) :=
  cell_carry_k9 h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 Said (carryExact_door Zp (P5J.At.arr Zp)) hb hp hk hi h1

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rest_shut
#print axioms ProofFile.Honest.FirstThread.doorZ_shut
#print axioms ProofFile.Honest.FirstThread.carryAt_full
#print axioms ProofFile.Honest.FirstThread.carryAt_control
#print axioms ProofFile.Honest.FirstThread.carry_k9_number
#print axioms ProofFile.Honest.FirstThread.carry_cell_shut
#print axioms ProofFile.Honest.FirstThread.cell_carry_k9
#print axioms ProofFile.Honest.FirstThread.carryExact_door
#print axioms ProofFile.Honest.FirstThread.cell_carry_k9_exact
