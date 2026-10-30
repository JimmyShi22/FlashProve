-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BatAtHead.lean: THE GATHERING THEOREM `accepted_of_records` (Honest/K9/RunFrame.lean) AT THE FIRST CHAIN's
THREAD UNDER THE LIBRARY's HYPOTHESIS `AtMgA` (`lettersHead`, Honest/Thread/FirstHead.lean), with the premises paid that the
hypothesis pays: the segment's seat, the block at the batching's number, "no mark of failure at a stand", "every reading
that rests under the four writings is kept by every run of the order", and "so is the ledger's core"
(Honest/K9/RunCores.lean).

  **`rests_at_head`**    at each of the 25 segments: for every reading g with `FieldRests g`, every run that the order names
                       keeps g, at every yes: the three theorems of Honest/K9/KeepsAtHead.lean, joined at the seated link
  `block_at_head`       the thread's block at 14 l + `IM.nAt l` + 2 is the seated link's batching
  **`accepted_bat_at_head`**   `AcceptedS` at that number, from what is left. The test `front` of the stand is fixed here: it is
                       the smallness test's `K8.k8Front` (Honest/K8/Share.lean): no column of a drawn matrix has the
                       weight 0 at the drawn element

Limits. What is left, as premises: `hno`, `hfall`, `ready`, `sized`, `plan`, `fit`, and `records`: at each entry of the order a run f that
is tied to the entry (Honest/K9/RunSeats.lean names it, kind by kind) with its record. The full size and the hash function
`secondHashFunction` alone: the hypothesis's. It is not proved that the invariant holds at any run. This file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.RunFrame
import Johnson.Desc.ProofFile.Honest.K9.RunCores
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.ProofFile.Honest.K8.Share
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (FieldRests)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every reading that rests is kept by every run of the order, at each of the 25 segments.** -/
theorem rests_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l k : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hl : l < 25)
    (Sd : SeatedFree cF Zp l k Lk p w) {γ : Type} (g : S → γ) (R : FieldRests g) :
    ∀ (j : ℕ) (o : ℕ × String) (f : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some f →
      ∀ m e z, f m e = .ok z → g z.2 = g e := by
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hl Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro j o f ho hf m e z hz
  have hmem : o ∈ Lk.order := List.mem_of_getElem? ho
  by_cases h24 : l = 24
  · subst h24
    exact fieldRun_head_at h O rfl Lk p hlk seg drawB kp {} R o hmem f hf m e z.1 z.2 hz
  · by_cases hev : l % 2 = 0
    · have hs : IM.subAt l = .layers := by
        unfold IM.subAt
        rw [if_neg h24, if_pos hev]
      exact fieldRun_lay_at h O l hl hs Lk p hlk seg drawB kp {} R o hmem f hf m e z.1 z.2 hz
    · obtain ⟨q, rfl⟩ : ∃ q, l = 2 * q + 1 := ⟨l / 2, by omega⟩
      exact fieldRun_att_at h O (g := q) (by omega) (sub_odd q (by omega)) Lk p hlk seg drawB kp {} R o hmem f hf
        m e z.1 z.2 hz

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

/-- The thread's block at the batching's number. -/
theorem block_at_head {l : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l (IM.nAt l) Lk p w) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread.bs[14 * l + IM.nAt l + 2]? =
      some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := Sd.batching

/-- **`AcceptedS` at the batching of segment l, at the thread under the hypothesis.** -/
theorem accepted_bat_at_head {l : ℕ} (hl : l < 25) {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp l (IM.nAt l) Lk p w)
    {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hno : ∀ g ∈ H.first, g.place.kind ≠ KindName.K9)
    (fall : ℕ → S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall (14 * l + IM.nAt l + 2) s ds = none → K8.k8Front s ds = none)
    (ready : ∀ κ s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said (14 * l + IM.nAt l + 2) κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (sized : ∀ s tr a, StandAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said
      (14 * l + IM.nAt l + 2) K8.k8Front s tr a → ∀ F, s.fork? = some F → PscRun.Sized F)
    (n : ℕ → S → ℕ) (own owe : ℕ → S → ℕ → Prop) (tails : ℕ → Prop) (Ws Ds : ℕ → S → ℕ → Prop) (whole : ℕ → Prop)
    (lo hi : ℕ → S → ℕ)
    (plan : ∀ s tr a, StandAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said
      (14 * l + IM.nAt l + 2) K8.k8Front s tr a → sumTo (fun j => n j s) Lk.order.length ≤ a.F.planClaimsF)
    (fit : ∀ s tr a, StandAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said
      (14 * l + IM.nAt l + 2) K8.k8Front s tr a → Fitted Lk.order.length (fun j => own j s) (fun j => owe j s) tails
        (fun j => Ws j s) (fun j => Ds j s) whole)
    (records : ∀ j, j < Lk.order.length → ∃ f, Tied Lk j f ∧
      RunRecord (StandAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said
        (14 * l + IM.nAt l + 2) K8.k8Front) Lk p j (n j) f (own j) (owe j) (tails j) (Ws j) (Ds j) (whole j) (lo j)
        (hi j)) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said fall
      (14 * l + IM.nAt l + 2) := by
  classical
  let f : ℕ → ClaimsRun := fun j =>
    if hj : j < Lk.order.length then (records j hj).choose else LinkJoin.idle0
  have hf : ∀ j (hj : j < Lk.order.length), f j = (records j hj).choose := fun j hj => dif_pos hj
  exact accepted_of_records (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Sd
    (block_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ Sd) hno fall K8.k8Front hfall ready
    (fun _ _ _ _ hT => Option.isNone_iff_eq_none.1 hT.1.2.2.1.1)
    (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd) sized n f
    (fun j hj => by rw [hf j hj]; exact (records j hj).choose_spec.1)
    own owe tails Ws Ds whole lo hi plan fit
    (fun j hj => by rw [hf j hj]; exact (records j hj).choose_spec.2)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rests_at_head
#print axioms ProofFile.Honest.K9.block_at_head
#print axioms ProofFile.Honest.K9.accepted_bat_at_head
