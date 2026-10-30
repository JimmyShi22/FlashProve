-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K8FormsCell.lean: the open item `forms m k r` of the first
chain's invariant passes over the draw of the smallness test (kind K8) of each of the 25 segments,
at the invariant whose `keeps` is `kpBy fHeadG` (FHeadG.lean). No definition.

The clause of `keeps` at K8 gives the library's relation `K8.Drawn`: the state after the step is the
state before it with the drawn matrix written into the range proof's state (`k8Keeps_drawn`,
WoKinds.lean). The authors of kind K8 show, under `AtMgA`, that what a segment's readers answer
before such a writing they answer after it, at every item `forms` that is open before the draw
(`K8.Honest.k8_draw_readers_head`, Johnson/Desc/K8/Honest/DrawReaders.lean, a joining of lemmas of
the library). So the clause `readersStayAt` (FHeadG.lean) follows from the clause of `keeps` at K8
as it stands.

  1  `k8_numbers`, `k8_numbers_control`, `k8_number`   a closed test by Lean's kernel: a place of
     the kind K8 in the written list stands at the number of its segment's draw. The negative test:
     at the kind K1 the test fails
  2  `k8_readersStayAt`   the clause `readersStayAt` from `Drawn`
  3  `forms_cell_k8`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the item, at
     every place of the kind K8

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The item has to be open on both sides of the sub-protocol (`ho`, `ho'`).
  * Where `r` is "weights", that the letter `wt` passes forward is a hypothesis (`hwt`). It is shown
    nowhere.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormsCells
import Johnson.Desc.ProofFile.Honest.Thread.WoKinds
import Johnson.Desc.K8.Honest.DrawReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.K8 (Drawn drawAt)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The places of the kind K8 -/

set_option maxRecDepth 1000000 in
/-- A place of the kind K8 stands at the number of its segment's draw. -/
theorem k8_numbers : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K8) ||
      (decide (p.link.getD 25 < 25) && b == drawAt (p.link.getD 25))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the kind K1 the same test fails. -/
theorem k8_numbers_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K1) ||
      (decide (p.link.getD 25 < 25) && b == drawAt (p.link.getD 25))) = false := by
  decide +kernel

/-- The test at a place. -/
theorem k8_number {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K8) : p.link.getD 25 < 25 ∧ b = drawAt (p.link.getD 25) := by
  have t := List.all_eq_true.1 k8_numbers b (List.mem_range.2 hb)
  rw [hp] at t
  have t' : (!(p.kind == KindName.K8) ||
      (decide (p.link.getD 25 < 25) && b == drawAt (p.link.getD 25))) = true := t
  rw [hk] at t'
  simpa using t'

/-! ## 2 and 3 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The readers' answers stay over the draw's writing, at every item `forms` that is open on both
sides of the draw of segment `l`. -/
theorem k8_readersStayAt {l : Nat} (hl : l < 25) {p : Place}
    (hp : P5J.At.ps[drawAt l]? = some p) {s s' : TS} (hD : Drawn s s') :
    readersStayAt h.𝔇.pubD p s s' := by
  intro mm kk ρ ho _
  rw [border_at hp] at ho
  exact VerifiableInference.Desc.First.K8.Honest.k8_draw_readers_head h hl hD mm kk ρ
    (by rw [P5J.linksW_at, P5J.placesW_at]; exact ho)

variable (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-- The item passes over the draw of the smallness test, at every place of the kind K8. -/
theorem forms_cell_k8 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hκ : p.kind = KindName.K8) (m k : Nat) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b)
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (b + 1))
    (hwt : ρ = "weights" → ∀ (s s' : TS) z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread
      b (Item.forms m k ρ) :=
  forms_cell_later h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp m k ρ ho ho'
    fun s s' a => by
      obtain ⟨hl, e⟩ := k8_number hb hp hκ
      have a' : fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD KindName.K8 p s s' :=
        (kpBy_at _ hκ s s').1 a
      have hD : Drawn s s' := k8Keeps_drawn a'.1.1.1
      exact ⟨drawn_part hD, k8_readersStayAt h hl (by rw [← e]; exact hp) hD, a'.1.2,
        fun e' => hwt e' s s'⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k8_numbers
#print axioms ProofFile.Honest.FirstThread.k8_numbers_control
#print axioms ProofFile.Honest.FirstThread.k8_number
#print axioms ProofFile.Honest.FirstThread.k8_readersStayAt
#print axioms ProofFile.Honest.FirstThread.forms_cell_k8
