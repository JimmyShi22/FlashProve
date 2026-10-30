-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/CellsByKind.lean: the hypothesis `RidesPastAtS`
(Honest/Thread/SharesS.lean) for the open items `forms m k r` and `wo m` of the first chain's
invariant, stated by the kind of the place: at a place `p` of the written list with a given kind,
for an item that is open at the border and is not closed there. The invariant's `keeps` is
`kpBy fHeadG` (FHeadG.lean). This is the form in which the gathering takes a cell. No definition.

FormsCells.lean, K8FormsCell.lean and WoCells.lean state these cells at numbers (`noL l d`,
`k3K l true`, `14 * l + IM.nAt l + j`). Two closed tests by Lean's kernel on the written lists tie
the kinds to these numbers.

  1  `frontAt_full`, `frontAt_control`   at a place of the kind K1 or K3: if an item `forms` is open
     before it, the place is the sending of a segment's digits (K1) or the lookup on a segment's
     digits (K3); if an item `wo` is open before it, the place is the sending of a segment's reads
     or of its digits (K1) or the lookup on a segment's digits (K3). The negative test: with the
     sending of the reads in the place of the sending of the digits, at `forms`, the test fails
  2  `k10At_full`, `k10At_control`   a place of the kind K10 stands at a segment's closing. The
     negative test: at the number before it the test fails. (Where the places of the kind K9 stand:
     `k9_number_of`, PinKeptCells.lean.)
  3  `forms_k1_number`, `forms_k3_number`, `wo_k1_number`, `wo_k3_number`, `k10_number`   the tests
     at a place
  4  `cell_forms_k1`, `cell_forms_k3`, `cell_forms_k8`   the item `forms m k r`
  5  `cell_wo_k1`, `cell_wo_k3`, `cell_wo_k8`, `cell_wo_k9`, `cell_wo_k10`   the item `wo m`

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Where `r` is "weights", that the letter `wt` passes forward is a hypothesis (`hwt`). It is shown
    nowhere.
  * The item `forms` at the kind K11 is not treated.
  * Nothing here shows that an item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K8FormsCell
import Johnson.Desc.ProofFile.Honest.Thread.WoCells
import Johnson.Desc.ProofFile.Honest.Thread.OpenNext
import Johnson.Desc.ProofFile.Honest.Thread.KeepsMono
import Johnson.Desc.ProofFile.Honest.Thread.PinKeptCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (noL)
open VerifiableInference.OnPublicFiles (k3K)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 and 2 The closed tests -/

set_option maxRecDepth 1000000 in
/-- Which places of the kinds K1 and K3 have an item `forms` or `wo` open before them. -/
theorem frontAt_full : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K1 || p.kind == KindName.K3) ||
      (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
        match i with
        | .forms _ _ _ =>
          if p.kind == KindName.K1 then (List.range 25).any fun l => b == noL l true
          else (List.range 25).any fun l => b == k3K l true
        | .wo _ =>
          if p.kind == KindName.K1 then
            (List.range 25).any fun l => b == noL l false || b == noL l true
          else (List.range 25).any fun l => b == k3K l true
        | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with the sending of the reads for the item `forms` the same test fails. -/
theorem frontAt_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K1 || p.kind == KindName.K3) ||
      (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
        match i with
        | .forms _ _ _ =>
          if p.kind == KindName.K1 then (List.range 25).any fun l => b == noL l false
          else (List.range 25).any fun l => b == k3K l true
        | .wo _ =>
          if p.kind == KindName.K1 then
            (List.range 25).any fun l => b == noL l false || b == noL l true
          else (List.range 25).any fun l => b == k3K l true
        | _ => true) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Where the places of the kind K10 stand. -/
theorem k10At_full : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K10) ||
      (List.range 25).any fun l => b == 14 * l + IM.nAt l + 5) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the number before it the same test fails. -/
theorem k10At_control : ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
    !(p.kind == KindName.K10) ||
      (List.range 25).any fun l => b == 14 * l + IM.nAt l + 4) = false := by
  decide +kernel

/-! ## 3 The tests at a place -/

theorem forms_k1_number {b : Nat} {p : Place} {m k : Nat} {ρ : String} (hb : b < 358)
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K1)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b) :
    ∃ l, l < 25 ∧ b = noL l true := by
  have t := List.all_eq_true.1 frontAt_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · exact absurd t0 (by decide)
  · have t2 : ((List.range 25).any fun l => b == noL l true) = true :=
      List.all_eq_true.1 t1 _ ho
    obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t2
    exact ⟨l, List.mem_range.1 hl, eq_of_beq e⟩

theorem forms_k3_number {b : Nat} {p : Place} {m k : Nat} {ρ : String} (hb : b < 358)
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K3)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b) :
    ∃ l, l < 25 ∧ b = k3K l true := by
  have t := List.all_eq_true.1 frontAt_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · exact absurd t0 (by decide)
  · have t2 : ((List.range 25).any fun l => b == k3K l true) = true :=
      List.all_eq_true.1 t1 _ ho
    obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t2
    exact ⟨l, List.mem_range.1 hl, eq_of_beq e⟩

theorem wo_k1_number {b : Nat} {p : Place} {m : Nat} (hb : b < 358)
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K1)
    (ho : Item.wo m ∈ IM.openAt P5J.At.links P5J.At.ps b) :
    ∃ l d, l < 25 ∧ b = noL l d := by
  have t := List.all_eq_true.1 frontAt_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · exact absurd t0 (by decide)
  · have t2 : ((List.range 25).any fun l => b == noL l false || b == noL l true) = true :=
      List.all_eq_true.1 t1 _ ho
    obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t2
    rcases (Bool.or_eq_true _ _).mp e with e | e
    · exact ⟨l, false, List.mem_range.1 hl, eq_of_beq e⟩
    · exact ⟨l, true, List.mem_range.1 hl, eq_of_beq e⟩

theorem wo_k3_number {b : Nat} {p : Place} {m : Nat} (hb : b < 358)
    (hp : P5J.At.ps[b]? = some p) (hk : p.kind = KindName.K3)
    (ho : Item.wo m ∈ IM.openAt P5J.At.links P5J.At.ps b) :
    ∃ l, l < 25 ∧ b = k3K l true := by
  have t := List.all_eq_true.1 frontAt_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · exact absurd t0 (by decide)
  · have t2 : ((List.range 25).any fun l => b == k3K l true) = true :=
      List.all_eq_true.1 t1 _ ho
    obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t2
    exact ⟨l, List.mem_range.1 hl, eq_of_beq e⟩

theorem k10_number {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K10) : ∃ l, l < 25 ∧ b = 14 * l + IM.nAt l + 5 := by
  have t := List.all_eq_true.1 k10At_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  rcases (Bool.or_eq_true _ _).mp t with t0 | t1
  · exact absurd t0 (by decide)
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 t1
    exact ⟨l, List.mem_range.1 hl, eq_of_beq e⟩

/-! ## 4 and 5 The cells -/

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

/-- The item `forms m k r` at a place of the kind K1. -/
theorem cell_forms_k1 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) {m k : Nat} {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts)
    (hwt : ρ = "weights" → ∀ (s s' : TS) z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl⟩ := forms_k1_number hb hp hk ho
  exact ridesPastAtS_of _ _ (forms_cell_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 hl m k ρ ho ho' hwt)

/-- The item `forms m k r` at a place of the kind K3. -/
theorem cell_forms_k3 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3) {m k : Nat} {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts)
    (hwt : ρ = "weights" → ∀ (s s' : TS) z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl⟩ := forms_k3_number hb hp hk ho
  exact ridesPastAtS_of _ _ (forms_cell_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 hl m k ρ ho ho' hwt)

/-- The item `forms m k r` at a place of the kind K8. -/
theorem cell_forms_k8 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K8) {m k : Nat} {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts)
    (hwt : ρ = "weights" → ∀ (s s' : TS) z y y' v, h.𝔇.wt m (z, s) y v → h.𝔇.wt m (z, s') y' v) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  exact ridesPastAtS_of _ _ (forms_cell_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 hb hp hk m k ρ ho ho' hwt)

/-- The item `wo m` at a place of the kind K1. -/
theorem cell_wo_k1 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) {m : Nat}
    (hi : Item.wo m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.wo m ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.wo m) := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, d, hl, rfl⟩ := wo_k1_number hb hp hk ho
  exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ (wo_cell_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
      P11 p12 P13 hl d m))

/-- The item `wo m` at a place of the kind K3. -/
theorem cell_wo_k3 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3) {m : Nat}
    (hi : Item.wo m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.wo m ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.wo m) := by
  obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl⟩ := wo_k3_number hb hp hk ho
  exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (wo_cell_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hl m)

/-- The item `wo m` at a place of the kind K8. -/
theorem cell_wo_k8 {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K8) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.wo m) :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (wo_cell_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp hk m)

/-- The item `wo m` at a place of the kind K9. -/
theorem cell_wo_k9 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K9) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.wo m) := by
  obtain ⟨l, hl, e⟩ := k9_number_of hb hp hk
  rcases e with rfl | rfl | rfl
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (wo_cell_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hl m)
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (ridesPastAtS_of _ _ (wo_cell_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
        P11 p12 P13 hl m))
  · exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
      (wo_cell_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hl m)

/-- The item `wo m` at a place of the kind K10. -/
theorem cell_wo_k10 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K10) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.wo m) := by
  obtain ⟨l, hl, rfl⟩ := k10_number hb hp hk
  exact head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
      (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
    (ridesPastAtS_of _ _ (wo_cell_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
      P11 p12 P13 hl m))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.frontAt_full
#print axioms ProofFile.Honest.FirstThread.frontAt_control
#print axioms ProofFile.Honest.FirstThread.k10At_full
#print axioms ProofFile.Honest.FirstThread.k10At_control
#print axioms ProofFile.Honest.FirstThread.forms_k1_number
#print axioms ProofFile.Honest.FirstThread.forms_k3_number
#print axioms ProofFile.Honest.FirstThread.wo_k1_number
#print axioms ProofFile.Honest.FirstThread.wo_k3_number
#print axioms ProofFile.Honest.FirstThread.k10_number
#print axioms ProofFile.Honest.FirstThread.cell_forms_k1
#print axioms ProofFile.Honest.FirstThread.cell_forms_k3
#print axioms ProofFile.Honest.FirstThread.cell_forms_k8
#print axioms ProofFile.Honest.FirstThread.cell_wo_k1
#print axioms ProofFile.Honest.FirstThread.cell_wo_k3
#print axioms ProofFile.Honest.FirstThread.cell_wo_k8
#print axioms ProofFile.Honest.FirstThread.cell_wo_k9
#print axioms ProofFile.Honest.FirstThread.cell_wo_k10
