-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/OpenBridge.lean: two tools for the column `hR` of `owesS_head`
(GatherHead.lean). First, the set of items that the invariant holds open at a border
(`Thread.opened`, Thr.lean) is the library's own open set there (`openSets`,
Johnson/Desc/First/Borders.lean), but for the item `wrow`. Lemmas that are stated at the library's
open sets can so be used at the invariant. Second, `head_hR_of_cells` (RideOk.lean) in a form that
hands on that the item is open at the border. No definition.

  1  `opens_get`   entry `b` of the list `opens` (FirstRows.lean) is the forward open set at border
     `b`
  2  `opens_openSets`   at the full size's written lists, `opens` without `wrow` is `openSets`. The
     statement has no free variable. It is decided by the kernel's evaluation (`decide +kernel`), so
     it is counted apart from the other lemmas. FirstRows.lean evaluates the same test in a `#guard`
  3  `opens_openSets_control`   the test can fail: with `wrow` left in, the two lists differ
  4  `head_opened_openSets`   an item other than `wrow` that the invariant holds open at a border is
     in the library's open set there
  5  `head_ok_at`, `head_hR_of_cellsO`   the table's test at an open item that passes over a
     sub-protocol; the column `hR`, with "the item is open" handed on

Limits.
  * Lists of items only: the file says nothing about what an item means.
  * Full size only, and parts 4 and 5 only under the library's hypothesis `AtMgA` at the hash
    function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RideOk
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstRows
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item)

/-- Entry `b` of `opens` is the forward open set at border `b`. -/
theorem opens_get (links : List ModelPart) : ∀ (ps : List Place) (O : List Item) (b : Nat),
    b ≤ ps.length → (opens links ps O)[b]? = some (fwdOpen O (rows links ps) b)
  | [], _, 0, _ => rfl
  | [], _, b + 1, h => absurd h (by simp)
  | _ :: _, _, 0, _ => rfl
  | p :: ps, O, b + 1, h => by
    have e : (opens links (p :: ps) O)[b + 1]? =
        (opens links ps (fwdStep O (rowAt links p)))[b]? := rfl
    rw [e, fwdOpen_cons]
    exact opens_get links ps _ b (Nat.le_of_succ_le_succ h)

end ProofFile.Honest.FirstRows

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item start openSets)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

set_option maxRecDepth 1000000 in
/-- At the written lists, `opens` without `wrow` is the library's `openSets`. -/
theorem opens_openSets :
    ((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).map
        (·.filter (· != Item.wrow)) ==
      openSets P5J.At.links P5J.At.ps (start P5J.At.links)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with `wrow` left in, the same test fails. -/
theorem opens_openSets_control :
    (FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links) ==
      openSets P5J.At.links P5J.At.ps (start P5J.At.links)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- An item other than `wrow` that the invariant holds open at a border is in the library's open set
there. -/
theorem head_opened_openSets {b : Nat} (hb : b ≤ 358) {i : Item}
    (hi : i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (hw : i ≠ Item.wrow) :
    i ∈ ((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[b]?).getD [] := by
  have e := eq_of_beq opens_openSets
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have hlen : P5J.At.ps.length = 358 := by
    rw [← e']
    exact IM.places_len
  rw [← e, List.getElem?_map,
    FirstRows.opens_get P5J.At.links P5J.At.ps (start P5J.At.links) b (by rw [hlen]; exact hb)]
  show i ∈ (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) b).filter
    (· != Item.wrow)
  exact List.mem_filter.2 ⟨hi, by simpa using hw⟩

/-- The table's test holds at an open item that the row neither closes nor has in `owes`. -/
theorem head_ok_at (ok : Place → Item → Bool)
    (hone : (((FirstRows.opens P5J.At.links P5J.At.ps (start P5J.At.links)).zip P5J.At.ps).all
      fun x => x.1.all fun i => (FirstRows.rowAt P5J.At.links x.2).shuts.contains i ||
        (FirstRows.rowAt P5J.At.links x.2).owes.contains i || ok x.2 i) = true)
    {b : Nat} {p : Place} (hp : P5J.At.ps[b]? = some p) {i : Item}
    (hi : i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b)
    (h1 : i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts)
    (h2 : i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes) :
    ok p i = true := by
  have er := head_row_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp
  rw [er] at h1 h2
  have ht := FirstRows.onePass_at P5J.At.links
    (fun p O => O.all fun i => (FirstRows.rowAt P5J.At.links p).shuts.contains i ||
      (FirstRows.rowAt P5J.At.links p).owes.contains i || ok p i)
    P5J.At.ps (start P5J.At.links) hone b _ hp
  have hi' := List.all_eq_true.1 ht i hi
  simp only [Bool.or_eq_true] at hi'
  rcases hi' with (c1 | c2) | c3
  · exact absurd (List.contains_iff_mem.1 c1) h1
  · exact absurd (List.contains_iff_mem.1 c2) h2
  · exact c3

/-- **The column `hR` from the combinations that the table admits, at open items.** -/
theorem head_hR_of_cellsO (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hok : ∀ b p i, P5J.At.ps[b]? = some p →
      i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b →
      rideOk p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i) :
    ∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
      ∀ i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened b,
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.row b).owes →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b i := by
  intro b hb i hi h1 h2
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (List.getElem?_eq_getElem hb)
  exact hok b _ i hp hi
    (head_ok_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w rideOk rideOk_onePass hp hi h1 h2)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstRows.opens_get
#print axioms ProofFile.Honest.FirstThread.opens_openSets
#print axioms ProofFile.Honest.FirstThread.opens_openSets_control
#print axioms ProofFile.Honest.FirstThread.head_opened_openSets
#print axioms ProofFile.Honest.FirstThread.head_ok_at
#print axioms ProofFile.Honest.FirstThread.head_hR_of_cellsO
