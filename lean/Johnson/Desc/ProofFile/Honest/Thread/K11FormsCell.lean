-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K11FormsCell.lean: the hypothesis `RidesPastAtS`
(Honest/Thread/SharesS.lean) for an open item `forms m k r` of the first chain's invariant at a
place of the kind K11 (the output head's merge, number 346), for an item that is open at the border
and is not closed there. The invariant's `keeps` is `kpBy fHeadG` (FHeadG.lean), with the numbers of
K11 that the kind's authors name (`K11.parOf Zp Bs.G₀`). No definition.

The authors of kind K11 show that the six items `forms 24 k r` whose names the library lists
(`MergeLaw.sixNames`, Johnson/Top/H0/MergeLaw/FormsBackAtMerge.lean) pass over number 346, if
`keeps` there gives their clause `K11KeepsYes` (`K11.sixFormsRide_at_head`,
Honest/K11/Plays/SixRide.lean). A closed test by Lean's kernel on the written lists ties the kind to
that statement.

  1  `k11At_full`, `k11At_control`   a place of the kind K11 stands at number 346, and an item
     `forms` that is open on both sides of it is `forms 24 k r` with `(k, r)` one of the six names.
     The negative test: without the first of the six names the test fails
  2  `k11_place`   the test at a place
  3  `cell_forms_k11`   the cell

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The cell is stated at `SaidOk` (SaidOk.lean), as the lemma that it calls, not at every `Said`.
  * That `ProofFile.baseOf` returns `Bs` is a hypothesis (`hB`).
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.K11.Plays.SixRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.MergeLaw (sixNames)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 and 2 The closed test -/

set_option maxRecDepth 1000000 in
/-- Where a place of the kind K11 stands, and which items `forms` are open on both sides of it. -/
theorem k11At_full : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K11) || (b == 346 &&
      ((IM.openAt P5J.At.links P5J.At.ps 346).filter fun i =>
        (IM.openAt P5J.At.links P5J.At.ps 347).contains i).all fun i =>
        match i with
        | .forms m k ρ => m == 24 && sixNames.contains (k, ρ)
        | _ => true)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: without the first of the six names the same test fails. -/
theorem k11At_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K11) || (b == 346 &&
      ((IM.openAt P5J.At.links P5J.At.ps 346).filter fun i =>
        (IM.openAt P5J.At.links P5J.At.ps 347).contains i).all fun i =>
        match i with
        | .forms m k ρ => m == 24 && (sixNames.drop 1).contains (k, ρ)
        | _ => true)) = false := by
  decide +kernel

/-- The test at a place. -/
theorem k11_place {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K11) :
    b = 346 ∧ ∀ m k ρ, Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps 346 →
      Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps 347 →
      m = 24 ∧ (k, ρ) ∈ sixNames := by
  have t := List.all_eq_true.1 k11At_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · rw [hk] at t0
    exact absurd t0 (by decide)
  · simp only [Bool.and_eq_true] at t1
    refine ⟨eq_of_beq t1.1, fun m k ρ ho ho' => ?_⟩
    have t2 : (m == 24 && sixNames.contains (k, ρ)) = true :=
      List.all_eq_true.1 t1.2 _ (List.mem_filter.2 ⟨ho, List.contains_iff_mem.2 ho'⟩)
    simp only [Bool.and_eq_true] at t2
    exact ⟨eq_of_beq t2.1, List.contains_iff_mem.1 t2.2⟩

/-! ## 3 The cell -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-- The item `forms m k r` at a place of the kind K11. -/
theorem cell_forms_k11 {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {b : Nat} {p : Place}
    (hb : b < 358) (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K11) {m k : Nat}
    {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take (_root_.K11.parOf Zp Bs.G₀) p12 P13
        h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take (_root_.K11.parOf Zp Bs.G₀) p12 P13
        h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take (_root_.K11.parOf Zp Bs.G₀) p12 P13
        h.𝔇.pubD)) w).thread SaidOk
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take (_root_.K11.parOf Zp Bs.G₀) p12 P13
        h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨rfl, hf⟩ := k11_place hb hp hk
  obtain ⟨rfl, hy⟩ := hf m k ρ ho ho'
  exact ProofFile.Honest.K11.sixFormsRide_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX
    item n₁ n₂ b₀ Vd Rd _ w Bs hB
    (fun s s' hK => (((kpBy_at _ hk s s').1
      ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take (_root_.K11.parOf Zp Bs.G₀) p12 P13
        h.𝔇.pubD)) w hp s s').1 hK)).1.1).2)
    (k, ρ) hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k11At_full
#print axioms ProofFile.Honest.FirstThread.k11At_control
#print axioms ProofFile.Honest.FirstThread.k11_place
#print axioms ProofFile.Honest.FirstThread.cell_forms_k11
