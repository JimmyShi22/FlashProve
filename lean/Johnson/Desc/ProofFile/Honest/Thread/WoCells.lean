-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/WoCells.lean: the open item `wo m` of the first chain's
invariant passes over the sub-protocols of the kinds K1, K3, K8, K9 and K10 that it is open across,
at the invariant whose `keeps` is `kpBy fHead` (FHead.lean). No hypothesis on `keeps` is left. The
lemmas join the lemmas on the item with what the clause gives at each number. No definition.

Where the sub-protocol leaves the statement, the list of commitment trees, `out` and what is left
for the row, the lemma is that of the authors of kind K4 (`K4.k4_ridesPastAtS_wo_at`,
`K4.k4_ridesPastAtS_wo_head`, Honest/K4/Law/). Where it turns the statement or the list of trees,
the lemmas are those of WoKinds.lean, WoClose.lean and WoEqAt.lean.

  1  `rest9_four`, `k1Reads_rest`   two small facts on clauses
  2  `wo_cell_bat`, `wo_cell_eq`, `wo_cell_k10`, `wo_cell_shut`   from a segment's batching to its
     shutting. What `keeps` gives at these numbers: `head_keeps_bat`, `head_keeps_eq`,
     `head_keeps_k10`, `head_keeps_shut` (Law/NoHouse/BackStays.lean)
  3  `wo_cell_k8`   at every place of the kind K8
  4  `wo_cell_k3`   at the lookup on the digits of segment `l`
  5  `wo_cell_k1`   at the sending of the reads (`d` false) or of the digits (`d` true) of segment
     `l`

The frame's own step after the batching is in Law/NoHouse/FrameCells.lean (`rides_behind`).

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas hold at every `m`. Whether the item is open at a number is not said here.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FormsCells
import Johnson.Desc.ProofFile.Honest.Thread.WoKinds
import Johnson.Desc.ProofFile.Honest.Thread.WoClose
import Johnson.Desc.ProofFile.Honest.Thread.WoEqAt
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BackStays
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FrameCells
import Johnson.Desc.ProofFile.Honest.K4.Law.WoRidesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.LinkJoin (rest9)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (noL)
open VerifiableInference.OnPublicFiles (k3K)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt rngWritten_holds)
open Johnson.Desc.First.Walk.Law (leftOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 Two small facts -/

/-- Where `rest9` is the same at every blank, the four are the same. -/
theorem rest9_four {s s' : TS}
    (h9 : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s := by
  have e := h9 { check := s.check } {} {}
  have e1 := congrArg (fun z : TS => z.st) e
  have e2 := congrArg (fun z : TS => z.book) e
  have e3 := congrArg (fun z : TS => z.out) e
  exact ⟨e1, e2, e3, rest9_leftOf e⟩

/-- The clause of the sending of the reads gives `K1Rest`. -/
theorem k1Reads_rest {s s' : TS} (k : ProofFile.Honest.K1.K1ReadsKeeps s s') :
    ProofFile.Honest.K1.K1Rest s s' := by
  obtain ⟨m, ⟨⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩, -⟩, q1, q2, q3, q4, q5, -, q7, q8, -⟩ := k
  unfold ProofFile.Honest.K1.K1Rest
  rw [q1, q2, q3]
  exact ⟨q5.trans r1, q7.trans r2, q8.trans r3, q4.trans r4, r5, r6, r7, r8, r9⟩

/-! ## 2 to 5 At the invariant -/

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

/-- Over the batching of segment `l`. -/
theorem wo_cell_bat {l : Nat} (hl : l < 25) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread Said
      (14 * l + IM.nAt l + 2) (Item.wo m) :=
  ProofFile.Honest.K4.k4_ridesPastAtS_wo_at h _ Q _ _ test carryX item n₁ n₂ _ _ _ Said _ m
    fun _ s _ _ s' _ hk => rest9_four (head_keeps_bat h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (fHead Zp cF G take P11 p12 P13) w rfl hl s s' hk)

/-- Over the shutting of segment `l`. -/
theorem wo_cell_shut {l : Nat} (hl : l < 25) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread Said
      (14 * l + IM.nAt l + 6) (Item.wo m) :=
  ProofFile.Honest.K4.k4_ridesPastAtS_wo_at h _ Q _ _ test carryX item n₁ n₂ _ _ _ Said _ m
    fun _ s _ _ s' _ hk => shutKeeps_four (head_keeps_shut h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (fHead Zp cF G take P11 p12 P13) w rfl hl s s' hk)

/-- Over "the one equation" of segment `l`. -/
theorem wo_cell_eq {l : Nat} (hl : l < 25) (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread
      (14 * l + IM.nAt l + 4) (Item.wo m) := by
  have h9 : IM.nAt l ≤ 9 := by
    unfold IM.nAt
    split <;> omega
  exact ridesPastAt_wo_eq_at h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w hl
    (by rw [head_len h]; omega) m
    (head_keeps_eq h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (fHead Zp cF G take P11 p12 P13) w rfl hl)

/-- Over the closing (kind K10) of segment `l`. -/
theorem wo_cell_k10 {l : Nat} (hl : l < 25) (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread
      (14 * l + IM.nAt l + 5) (Item.wo m) := by
  have h9 : IM.nAt l ≤ 9 := by
    unfold IM.nAt
    split <;> omega
  exact ridesPastAt_wo_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w
    (by rw [head_len h]; omega) (by omega) (by omega) m
    (head_keeps_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (fHead Zp cF G take P11 p12 P13) w (fun _ => rfl) hl)

/-- Over the draw of the smallness test, at every place of the kind K8. -/
theorem wo_cell_k8 {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p)
    (hκ : p.kind = KindName.K8) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread Said
      b (Item.wo m) :=
  ProofFile.Honest.K4.k4_ridesPastAtS_wo_head h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w Said b m hp
    fun _ s _ _ s' _ a => by
      have a' : VerifiableInference.Desc.First.K8.Honest.K8KeepsM s s' :=
        (kpBy_at _ hκ s s').1 a
      exact ⟨a'.1.rest.1, a'.1.rest.2.1, a'.1.rest.2.2.2.2.2.2.1,
        VerifiableInference.Desc.First.K8.blind_leftOf s s' (k8Keeps_drawn a'.1)⟩

/-- Over the lookup on the digits of segment `l`. -/
theorem wo_cell_k3 {l : Nat} (hl : l < 25) (m : Nat) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread Said
      (k3K l true) (Item.wo m) := by
  have t := List.all_eq_true.1 rels_none_missed l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at t
  have hp : P5J.At.ps[k3K l true]? = some (IM.k3Place l true) := eq_of_beq t.1.2
  have hfour : ∀ s s', k3KeepsAt Zp (IM.k3Place l true) s s' →
      s'.st = s.st ∧ s'.book = s.book ∧ s'.out = s.out ∧ leftOf s' = leftOf s := by
    by_cases e : l = 24
    · subst e
      obtain ⟨sh, hh⟩ := fHead_h3H h rngWritten_holds
      exact fun s s' a => k3Head_four (hh s s' a)
    · obtain ⟨sh, claims, hh⟩ := fHead_h3 h rngWritten_holds (l := l) (by omega)
      have ep : IM.k3Place l true =
          { chain := 1, link := some l, piece := 7, kind := KindName.K3 } := by
        show (⟨1, some l, (6 + if l = 24 then 1 else 0) + 1, KindName.K3⟩ : Place) = _
        rw [if_neg e]
      rw [ep]
      intro s s' a
      obtain ⟨-, tl, F, H', G', -, -, hA, -⟩ := hh s s' a
      exact digitsArms_four hA
  exact ProofFile.Honest.K4.k4_ridesPastAtS_wo_head h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w Said _ m hp
    fun _ s _ _ s' _ a => hfour s s' a

/-- Over a sending at a later moment of segment `l`. -/
theorem wo_cell_k1 {l : Nat} (hl : l < 25) (d : Bool) (m : Nat) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHead Zp cF G take P11 p12 P13)) w).thread
      (noL l d) (Item.wo m) := by
  have hp : P5J.At.ps[noL l d]? = some (IM.k1PlaceL l d) :=
    VerifiableInference.Desc.K1.place_fifty l hl d
  have hn : noL l d = 14 * l + IM.k1Ix l d + 2 := rfl
  have hx : IM.k1Ix l d ≤ 6 ∧ 3 ≤ IM.k1Ix l d := by
    cases d <;> by_cases e : l = 24 <;> simp [IM.k1Ix, e]
  have harm : ∀ s s', ProofFile.Honest.K1.K1KeepsAt (IM.k1PlaceL l d) s s' →
      ProofFile.Honest.K1.K1Rest s s' ∧ leftOf s' = leftOf s := by
    have hc : ∀ s s', ProofFile.Honest.K1.K1CommitKeepsM s s' →
        ProofFile.Honest.K1.K1Rest s s' ∧ leftOf s' = leftOf s :=
      fun s s' a => ⟨a.1.1, k1Commit_left a.1⟩
    have hr : ∀ s s', ProofFile.Honest.K1.K1ReadsKeepsM s s' →
        ProofFile.Honest.K1.K1Rest s s' ∧ leftOf s' = leftOf s :=
      fun s s' a => ⟨k1Reads_rest a.1, k1Reads_left a.1⟩
    by_cases e : l = 24
    · subst e
      cases d
      · exact hr
      · exact hc
    · have ep : IM.k1PlaceL l d = ⟨1, some l, (if d then 5 else 3) + 1, KindName.K1⟩ := by
        show (⟨1, some l, ((if d then 5 else 3) + if l = 24 then 1 else 0) + 1, KindName.K1⟩ :
          Place) = _
        rw [if_neg e]
      rw [ep]
      cases d
      · exact hr
      · exact hc
  have h1 : (IM.k1PlaceL l d).piece ≠ 1 := by
    show IM.k1Ix l d + 1 ≠ 1
    omega
  exact ridesPastAt_wo_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w
    (by rw [head_len h, hn]; omega) m
    (fun s s' hk => by
      have a := (fHead_K1_later Zp cF G take P11 p12 P13 (p := IM.k1PlaceL l d) (l := l) rfl h1
        s s').1 ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w hp s s').1 hk)
      exact ⟨(harm s s' a.1).1, (harm s s' a.1).2, a.2.2.2.2.1⟩)
    (fun _ _ _ _ hA => head_index h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHead Zp cF G take P11 p12 P13)) w hA
      (open_pinI (by rw [hn]; omega) (by rw [hn]; omega)))

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rest9_four
#print axioms ProofFile.Honest.FirstThread.k1Reads_rest
#print axioms ProofFile.Honest.FirstThread.wo_cell_bat
#print axioms ProofFile.Honest.FirstThread.wo_cell_shut
#print axioms ProofFile.Honest.FirstThread.wo_cell_eq
#print axioms ProofFile.Honest.FirstThread.wo_cell_k10
#print axioms ProofFile.Honest.FirstThread.wo_cell_k8
#print axioms ProofFile.Honest.FirstThread.wo_cell_k3
#print axioms ProofFile.Honest.FirstThread.wo_cell_k1
