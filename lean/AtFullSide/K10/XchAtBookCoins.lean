-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchAtBookCoins.lean: the closing of a segment (K10): what the fields `stand` of the records on the senders ask of the
book alone, at the book of whatever the maker returns, under the head: the code switch is handed its coins, and a sending of the
shared kind has its cut, at every run's coins.

  `coverLaterB`, `cover_later`, `coverOpenB`, `cover_open`, `cover_bent`   the closed tests: the book's row covers the sender's count
  **`handed_field`**   `K2.handed 0 p k` returns, at each written place
  **`later_cut_field`**, **`open_cut_field`**   `K1.lentCut` returns, at the jobs of the later moments and of the opening

Limits. That the part is handed something; never what. The head and that the maker returns are premises. The full size alone.
-/
import AtFullSide.K10.XchAtBookHead
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (placesW)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2 proofSendsFull)
open OnBytes.Maker (WholeD)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)

/-- The written table's count at a later moment's part covers the sender's. e: a number added to the sender's. -/
def coverLaterB (e l : Nat) (d : Bool) : Bool :=
  decide ((dueS codesFull2 (sentLater l (if d then 2 else 1)) (fun _ => none)
      (sentLater l (if d then 2 else 1)).size).f ≤ (dueAt rawRowsFirstW ⟨⟨1, some l, IM.k1Ix l d + 1, .K1⟩, 0⟩).f) &&
    decide ((dueS codesFull2 (sentLater l (if d then 2 else 1)) (fun _ => none)
      (sentLater l (if d then 2 else 1)).size).e + e ≤ (dueAt rawRowsFirstW ⟨⟨1, some l, IM.k1Ix l d + 1, .K1⟩, 0⟩).e)

/-- The like at the opening. -/
def coverOpenB (e : Nat) : Bool :=
  decide ((dueS codesFull2 sentOpen rideOpen sentOpen.size).f ≤ (dueAt rawRowsFirstW ⟨⟨1, some 0, 1, .K1⟩, 0⟩).f) &&
    decide ((dueS codesFull2 sentOpen rideOpen sentOpen.size).e + e ≤
      (dueAt rawRowsFirstW ⟨⟨1, some 0, 1, .K1⟩, 0⟩).e)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover_later : ((List.range 25).all fun l => coverLaterB 0 l false && coverLaterB 0 l true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cover_open : coverOpenB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The tests can fail: at one coin more they reject at every later moment, and at the opening. -/
theorem cover_bent : ((List.range 25).any fun l => coverLaterB 1 l false || coverLaterB 1 l true) = false ∧
    coverOpenB 1 = false := by
  decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X}
  {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)

include h hA in
/-- **The code switch is handed its coins**, at each written place and every run's coins. -/
theorem handed_field {p : SwitchPlace} (hp : p ∈ placesW) (k : Coins A.B) : ∃ c, K2.handed 0 p k = some c := by
  have t := switch_lends_at_written (book_is_written h hA) hp
  have e : (fun o => (k.look 0 o).1) = lookDue A.B 0 := funext fun o => look_dueIs k 0 o
  obtain ⟨c, hc⟩ := (lendPart_ok_iff A.B (A.B.rowsOf 0) (k.look 0) ⟨p.place, 0⟩
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries)).2 (by rw [e]; exact t)
  refine ⟨c, ?_⟩
  unfold K2.handed
  rw [hc]
  rfl

include h hA in
/-- **A later moment's sender has its cut**, at every run's coins. -/
theorem later_cut_field {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2)
    (gp : _root_.Desc.Plain.GPar) {Xi Xj : Type} {l : Nat} (hl : l < 25) (d : Bool) (first : Nat) (Dt : RowDataOf Xi)
    (k : Coins A.B) :
    ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨(laterJ (X := Xj) q gp l d first Dt).P.place, 0⟩
      (ProofFile.Honest.K1.dueR (laterJ (X := Xj) q gp l d first Dt).P (laterJ (X := Xj) q gp l d first Dt).ride) = some c := by
  have t0 := List.all_eq_true.1 cover_later l (List.mem_range.2 hl)
  have t : coverLaterB 0 l d = true := by
    simp only [Bool.and_eq_true] at t0
    cases d
    · exact t0.1
    · exact t0.2
  have s : (ProofFile.Honest.K1.lentCut k 0 ⟨(laterJ (X := Xj) q gp l d first Dt).P.place, 0⟩
      (ProofFile.Honest.K1.dueR (laterJ (X := Xj) q gp l d first Dt).P (laterJ (X := Xj) q gp l d first Dt).ride)).isSome = true := by
    rw [ProofFile.Honest.K1.lentCut_isSome k 0 (by omega), later_due hs hc]
    unfold ProofFile.Honest.K1.bookCovers
    show decide (_ ≤ (dueAt A.B.first _).f ∧ _ ≤ (dueAt A.B.first _).e) = true
    rw [close_rows (book_is_written h hA)]
    unfold coverLaterB at t
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero] at t
    exact decide_eq_true t
  exact Option.isSome_iff_exists.1 s

include h hA in
/-- **The opening's sender has its cut**, at every run's coins. -/
theorem open_cut_field {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2)
    (gp : _root_.Desc.Plain.GPar) {Xi Xj : Type} (first : Nat) (Dt : RowDataOf Xi) (k : Coins A.B) :
    ∃ c, ProofFile.Honest.K1.lentCut k 0 ⟨(openJ (X := Xj) q gp first Dt).P.place, 0⟩
      (ProofFile.Honest.K1.dueR (openJ (X := Xj) q gp first Dt).P (openJ (X := Xj) q gp first Dt).ride) = some c := by
  have t := cover_open
  have s : (ProofFile.Honest.K1.lentCut k 0 ⟨(openJ (X := Xj) q gp first Dt).P.place, 0⟩
      (ProofFile.Honest.K1.dueR (openJ (X := Xj) q gp first Dt).P (openJ (X := Xj) q gp first Dt).ride)).isSome = true := by
    rw [ProofFile.Honest.K1.lentCut_isSome k 0 (by omega), open_due hs hc]
    unfold ProofFile.Honest.K1.bookCovers
    show decide (_ ≤ (dueAt A.B.first _).f ∧ _ ≤ (dueAt A.B.first _).e) = true
    rw [close_rows (book_is_written h hA)]
    unfold coverOpenB at t
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero] at t
    exact decide_eq_true t
  exact Option.isSome_iff_exists.1 s

end

end AtFullSide.K10

#print axioms AtFullSide.K10.cover_later
#print axioms AtFullSide.K10.cover_open
#print axioms AtFullSide.K10.cover_bent
#print axioms AtFullSide.K10.handed_field
#print axioms AtFullSide.K10.later_cut_field
#print axioms AtFullSide.K10.open_cut_field
