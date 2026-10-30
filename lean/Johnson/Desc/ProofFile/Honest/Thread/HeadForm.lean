-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeadForm.lean: at the first chain's `Thread` under the
library's hypothesis `AtMgA` (`lettersHead`, Honest/Thread/FirstHead.lean): the sub-protocol's
place; the ledger from the public form; the data's list of segments. Lemmas: one call of the
library's `places_paid`, and unfoldings.

  `head_place`   sub-protocol number b is at the written place number b: so the hypothesis of
     `head_keeps` is obtained from the sub-protocol
  `head_keepsAt`   `keeps` at a sub-protocol is the clause of that sub-protocol's own place
  `head_ledgerB`   the public item "ledger m" says `ledgerB` there
  `head_ledger`   where that item is open the invariant gives: a ledger is open, with its three
     sizes
  `head_links`   the data's list of segments is the parameters'

Limits.
  * The full size alone, and the hash function `secondHashFunction` alone (Honest/Thread/FirstAt.lean says which
    that is).
  * A term of the library's hypothesis `AtMgA` exists at the name under four hypotheses on the
    public files (the library's `head_exists_at_name`); this file does not call it, and it proves of
    no such term that the invariant holds at a run.
  * Where "ledger m" is open is the table's matter: an evaluation at written lists: a hypothesis
    here.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (pubSets ledgerB blockPlaces)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- Sub-protocol number b is at the written place number b. By the library's `places_paid`. -/
theorem head_place {b : Nat} {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk) :
    P5J.At.ps[b]? = some blk.place := by
  have e : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have hb' : cF.blocksInOrder[b]? = some blk := hb
  rw [← e]
  unfold blockPlaces
  rw [List.getElem?_map, hb']
  rfl

/-- **`keeps` at a sub-protocol is the clause of that sub-protocol's own place.** -/
theorem head_keepsAt {b : Nat} {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[b]? = some blk)
    (s s' : TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).keeps b s s' ↔ Kp blk.place s s' :=
  head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb) s s'

theorem head_ledgerB (m : Nat) (a : ProofFile.InstPub × TS) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.pub (.ledger m) a =
      ledgerB a.2 := rfl

/-- **Where the public item "ledger m" is open, the invariant gives the ledger with its sizes.** -/
theorem head_ledger {b : Nat} {k : Coins Bk} {s : TS} {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s μ E)
    {m : Nat}
    (hq : VerifiableInference.Desc.First.Pub.ledger m ∈ ((pubSets
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).links
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps)[b]?).getD []) :
    ledgerB s = true := by
  have e := thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq
  rw [head_ledgerB] at e
  exact e

theorem head_links : h.𝔇.links = P5J.At.links := rfl

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_place
#print axioms ProofFile.Honest.FirstThread.head_keepsAt
#print axioms ProofFile.Honest.FirstThread.head_ledgerB
#print axioms ProofFile.Honest.FirstThread.head_ledger
#print axioms ProofFile.Honest.FirstThread.head_links
