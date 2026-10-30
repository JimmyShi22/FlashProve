-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeRow.lean: THE FRAME'S SENTENCE "THE EXCHANGE"
AT A MEMBER OF THE FIRST CHAIN INSIDE A SEGMENT, BROUGHT DOWN TO TWO PREMISES: of the five parts of
Honest/K3/Law/Thread/ExchangeParts.lean three are paid here. No kind is named.

  `asked_of_fit`    general in the thread: where the frame's test on the rows accepts, what a row
                    asks is open in front of it
  `asks_at_link`    at a place inside a segment the first chain's row asks what the table's row
                    closes, then what it reads and leaves
  `exchange_row`    CONDITIONAL, see below: `Exchange L.thread b`

PAID HERE. row: `owes_at_link`. asked: from the frame's test `fwdFit` (a test with code on the
letters). input: the frame's law of every play (`play_mid`, Honest/Law/Along.lean).
WHAT STAYS. hOuts: from the thread in front and the member's step each item that the table's row
opens holds behind: THE DEBT OF THE KIND WHOSE MEMBER IT IS: NOT PAID HERE; for the lookups,
conditional: `allOpenings_digitsLookup`, `all_attention`, `all_layers` (ExchangeAll.lean), `all_head`
(ExchangeHeadAll.lean). hCar: each item that the row reads and leaves says behind, of any witness,
what it says in front: NOT PAID HERE; for the lookups, conditional: `carried_site`
(CarriedSite.lean). Beside these: where the member stands; the test. No instance of these hypotheses
is exhibited in this file.

Limits. `Exchange` is a premise's form of the frame's. Nothing is shown of any item here. Nothing on
soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeParts
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.FirstThread (Letters)

local notation "tableRow" => VerifiableInference.Desc.First.rowOf

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **Where the frame's test on the rows accepts, what a row asks is open in front of it.** -/
theorem asked_of_fit {n b : Nat} (hfit : fwdFit T.start T.row n = true) (hb : b < n) {i : T.ι}
    (hi : i ∈ (T.row b).asks) : i ∈ T.opened b := by
  unfold fwdFit at hfit
  have h1 := List.all_eq_true.1 hfit b (List.mem_range.2 hb)
  have h2 := List.all_eq_true.1 h1 i (List.mem_append_left _ hi)
  exact List.contains_iff_mem.1 h2

end

section
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok M)

/-- **At a place inside a segment the first chain's row asks what the table's row closes, then what
it reads and leaves.** -/
theorem asks_at_link {b i : Nat} {a : Place} (hk : L.ps[b]? = some a) (hl : a.link = some i) :
    (L.thread.row b).asks = (tableRow L.links a).ins ++ (tableRow L.links a).ctx := by
  show (FirstRows.rows L.links L.ps b).asks = _
  unfold FirstRows.rows
  rw [hk]
  show (FirstRows.turn a _).asks = _
  unfold FirstRows.turn
  rw [hl]
  rfl

end

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr Xo Pp Cells Tok M : Type}
  {L : Letters Bk Cl W₀ Rc Xi Tr Xo Pp Cells Tok M}

/-- **CONDITIONAL ON what this file's head lists: THE EXCHANGE at a member of the first chain inside
a segment.** No instance of these hypotheses is exhibited in this file. -/
theorem exchange_row {b : Nat} {a : Place} {i n : Nat} (hk : L.ps[b]? = some a)
    (hl : a.link = some i) (hfit : fwdFit L.thread.start L.thread.row n = true) (hb : b < n)
    (hOuts : ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m E ds y cols st',
      Thr L.thread b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m E ds y cols st' →
      L.thread.Items (tableRow L.links a).outs k st' y.2 (E.add y.1))
    (hCar : ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m E ds y cols st',
      Thr L.thread b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m E ds y cols st' → ∀ x ∈ (tableRow L.links a).ctx, ∀ v,
      L.thread.means m.st.input x (L.thread.seat k m st) (L.thread.strs E) v →
      L.thread.means m.st.input x (L.thread.seat k y.2 st') (L.thread.strs (E.add y.1)) v) :
    Exchange L.thread b :=
  exchange_of_parts
    { row := owes_at_link L hk hl
      asked := fun x hx => asked_of_fit L.thread hfit hb
        (by rw [asks_at_link L hk hl]; exact List.mem_append_right _ hx)
      input := fun _ _ _ _ _ _ _ _ _ _ _ _ hSt => by
        obtain ⟨⟨⟨l, _, hy⟩, _⟩, _⟩ := hSt
        exact (play_mid l _ _ _ _ hy).1
      outs := hOuts
      carried := hCar }

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.asked_of_fit
#print axioms ProofFile.Honest.K3.Law.AtThr.asks_at_link
#print axioms ProofFile.Honest.K3.Law.AtThr.exchange_row
