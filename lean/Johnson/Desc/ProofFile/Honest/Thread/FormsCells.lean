-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormsCells.lean: the open item `forms m k r` of the first
chain's invariant passes over the lookup on a segment's digits (kind K3) and over the sending of a
segment's digits (kind K1), at the invariant whose `keeps` is `kpBy fHeadG` (FHeadG.lean). The
lemmas join what FormsLater.lean and FormsKinds.lean ask of `keeps` with the parts of that clause.
No definition.

What each part of the clause gives.
  * `fHead` at K3: the clause of the authors of kind K3, by the place. At the lookup on the digits
    it gives `K3KeepsDigits` or, in the output head's segment, `K3KeepsHead` (`fHead_h3`,
    `fHead_h3H`, FHeadStaysAll.lean; their hypothesis is `rngWritten_holds` of the same authors).
    From these: the open segment's part after the step differs from the part before it in a later
    ledger alone (`k3Digits_part`, `k3Head_part`, FormsKinds.lean).
  * `fHead` at K1: the clause of the authors of kind K1, by the place. At the sending of the digits
    it gives `K1CommitKeeps`, whose first part is `K1Rest`.
  * `formsBehind` (FHeadF.lean): the public tests that the table ties to the item hold after the
    step (`formsBehind_tests`).
  * `relsHead` (FHeadG.lean): the readers' answers stay; at K1 also `RecRides` and `AheadMeets`.

  1  `formsBehind_tests`   the two tests on a run, out of `formsBehind`
  2  `forms_cell_later`, `forms_cell_rec`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean)
     for the item at `lettersHead`, general in the letter `Kp`, at a place of the written list
  3  `forms_cell_k3`, `forms_cell_k1`   the same at `kpBy fHeadG`, at the numbers `k3K l true` and
     `noL l true`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The item has to be open on both sides of the sub-protocol (`ho`, `ho'`).
  * Where `r` is "weights", that the letter `wt` passes forward is a hypothesis (`hwt`). It is shown
    nowhere.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadGKeeps
import Johnson.Desc.ProofFile.Honest.Thread.FHeadStaysAll
import Johnson.Desc.ProofFile.Honest.Thread.FormsKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item Pub PubData borderOf)
open VerifiableInference.Desc.K9 (segAt? formsIn formsInA)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (noL)
open VerifiableInference.OnPublicFiles (k3K)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt rngWritten_holds)
open OnBytes.PscRun (Later)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The tests after the step -/

/-- The two public tests at the runs of an item `forms` that is open after the place `p`. -/
theorem formsBehind_tests {D : PubData} {p : Place} {s' : TS} (hB : formsBehind D p s')
    {m k : Nat} {ρ : String}
    (ho' : Item.forms m k ρ ∈
      IM.openAt P5J.At.links P5J.At.ps (borderOf P5J.At.ps (some p) + 1)) :
    (∀ q ∈ D.runs m k ρ, D.ah q.1 q.2 = true →
      formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s' = true) ∧
    (∀ q ∈ D.runs m k ρ, ¬ D.ah q.1 q.2 = true →
      formsIn (D.Rd m) (D.N.group m) q.1 q.2 s' = true) := by
  have t : ((D.runs m k ρ).all fun q =>
      if D.ah q.1 q.2 then formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s'
      else formsIn (D.Rd m) (D.N.group m) q.1 q.2 s') = true :=
    hB (Pub.formsIn m k ρ)
      (List.mem_flatMap.2 ⟨Item.forms m k ρ, ho', List.mem_singleton.2 rfl⟩)
  refine ⟨fun q hq ha => ?_, fun q hq ha => ?_⟩
  · have u : (if D.ah q.1 q.2 = true then
        formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s'
        else formsIn (D.Rd m) (D.N.group m) q.1 q.2 s') = true := List.all_eq_true.1 t q hq
    rw [if_pos ha] at u
    exact u
  · have u : (if D.ah q.1 q.2 = true then
        formsInA (D.Rd m) (D.N.sent m) (D.N.group m) q.1 q.2 s'
        else formsIn (D.Rd m) (D.N.group m) q.1 q.2 s') = true := List.all_eq_true.1 t q hq
    rw [if_neg ha] at u
    exact u

/-! ## 2 General in the letter `Kp` -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item passes over the sub-protocol at the place `p`, if `Kp p` gives: the open segment's part
differs in a later ledger alone; `readersStayAt`; `formsBehind`; the letter `wt` at "weights". -/
theorem forms_cell_later {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) (m k : Nat)
    (ρ : String) (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b)
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (b + 1))
    (hK : ∀ s s', Kp p s s' →
      (∀ a, segAt? s = some a → ∃ b', segAt? s' = some b' ∧ b'.L = a.L ∧ b'.d.st = a.d.st ∧
        b'.d.book = a.d.book ∧ Later a.F b'.F) ∧
      readersStayAt h.𝔇.pubD p s s' ∧ formsBehind h.𝔇.pubD p s' ∧
      (ρ = "weights" → ∀ z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.forms m k ρ) :=
  ridesPastAt_forms_later h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m k ρ
    fun s s' hk => by
      obtain ⟨k1, k2, k3, k4⟩ := hK s s' (hk p hp)
      have hbo := border_at hp
      have t := formsBehind_tests k3 (m := m) (k := k) (ρ := ρ) (by rw [hbo]; exact ho')
      exact ⟨k1, k2 m k ρ (by rw [hbo]; exact ho) (by rw [hbo]; exact ho'), t.1, t.2, k4⟩

/-- The item passes over the sub-protocol at the place `p`, if `Kp p` gives: `K1Rest`; `k1RelsAt`;
`formsBehind`; the letter `wt` at "weights". -/
theorem forms_cell_rec {b l : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) (m k : Nat)
    (ρ : String) (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b)
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (b + 1))
    (hK : ∀ s s', Kp p s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ k1RelsAt h.𝔇.pubD l p s s' ∧ formsBehind h.𝔇.pubD p s' ∧
      (ρ = "weights" → ∀ z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.forms m k ρ) :=
  ridesPastAt_forms_rec_test h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m k ρ
    fun s s' hk => by
      obtain ⟨k1, ⟨new, r1, r2, r3⟩, k3, k4⟩ := hK s s' (hk p hp)
      have hbo := border_at hp
      obtain ⟨e, r4⟩ := r3 m k ρ (by rw [hbo]; exact ho)
      have t := formsBehind_tests k3 (m := m) (k := k) (ρ := ρ) (by rw [hbo]; exact ho')
      rw [← e] at r2
      exact ⟨k1, new, r1, r4, fun q hq ha => ⟨t.1 q hq ha, r2⟩, k4⟩

/-! ## 3 At `kpBy fHeadG` -/

variable (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-- The item passes over the lookup on the digits of segment `l`. -/
theorem forms_cell_k3 {l : Nat} (hl : l < 25) (m k : Nat) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true + 1))
    (hwt : ρ = "weights" → ∀ (s s' : TS) z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread
      (k3K l true) (Item.forms m k ρ) := by
  have t := List.all_eq_true.1 rels_none_missed l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at t
  have hp : P5J.At.ps[k3K l true]? = some (IM.k3Place l true) := eq_of_beq t.1.2
  have hc : (IM.k3Place l true).piece = 7 ∨ (IM.k3Place l true).piece = 8 := by
    simpa using t.2
  have hparts : ∀ s s', k3KeepsAt Zp (IM.k3Place l true) s s' →
      (∀ a, segAt? s = some a → ∃ b', segAt? s' = some b' ∧ b'.L = a.L ∧ b'.d.st = a.d.st ∧
        b'.d.book = a.d.book ∧ Later a.F b'.F) := by
    by_cases e : l = 24
    · subst e
      obtain ⟨sh, hh⟩ := fHead_h3H h rngWritten_holds
      exact fun s s' a => k3Head_part (hh s s' a)
    · obtain ⟨sh, claims, hh⟩ := fHead_h3 h rngWritten_holds (l := l) (by omega)
      have ep : IM.k3Place l true =
          { chain := 1, link := some l, piece := 7, kind := KindName.K3 } := by
        show (⟨1, some l, (6 + if l = 24 then 1 else 0) + 1, KindName.K3⟩ : Place) = _
        rw [if_neg e]
      rw [ep]
      exact fun s s' a => k3Digits_part (hh s s' a)
  exact forms_cell_later h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp m k ρ ho ho'
    fun s s' a => ⟨hparts s s' a.1.1, a.2 hc, a.1.2, fun e => hwt e s s'⟩

/-- The item passes over the sending of the digits of segment `l`. -/
theorem forms_cell_k1 {l : Nat} (hl : l < 25) (m k : Nat) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (noL l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (noL l true + 1))
    (hwt : ρ = "weights" → ∀ (s s' : TS) z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread
      (noL l true) (Item.forms m k ρ) := by
  have t := List.all_eq_true.1 rels_none_missed l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at t
  have hp : P5J.At.ps[noL l true]? = some (IM.k1PlaceL l true) := eq_of_beq t.1.1.1
  have hc : (IM.k1PlaceL l true).piece = 6 ∨ (IM.k1PlaceL l true).piece = 7 := by
    simpa using t.1.1.2
  have hrest : ∀ s s', ProofFile.Honest.K1.K1KeepsAt (IM.k1PlaceL l true) s s' →
      ProofFile.Honest.K1.K1Rest s s' := by
    by_cases e : l = 24
    · subst e
      exact fun s s' a => (show ProofFile.Honest.K1.K1CommitKeepsM s s' from a).1.1
    · have ep : IM.k1PlaceL l true =
          { chain := 1, link := some l, piece := 6, kind := KindName.K1 } := by
        show (⟨1, some l, (5 + if l = 24 then 1 else 0) + 1, KindName.K1⟩ : Place) = _
        rw [if_neg e]
      rw [ep]
      exact fun s s' a => (show ProofFile.Honest.K1.K1CommitKeepsM s s' from a).1.1
  have h1 : (IM.k1PlaceL l true).piece ≠ 1 := by
    rcases hc with hc | hc <;> rw [hc] <;> decide
  exact forms_cell_rec h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w (l := l) hp m k ρ ho ho'
    fun s s' a => ⟨hrest s s' ((fHead_K1_later Zp cF G take P11 p12 P13
        (p := IM.k1PlaceL l true) (l := l) rfl h1 s s').1 a.1.1).1,
      a.2 l rfl hc, a.1.2, fun e => hwt e s s'⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.formsBehind_tests
#print axioms ProofFile.Honest.FirstThread.forms_cell_later
#print axioms ProofFile.Honest.FirstThread.forms_cell_rec
#print axioms ProofFile.Honest.FirstThread.forms_cell_k3
#print axioms ProofFile.Honest.FirstThread.forms_cell_k1
