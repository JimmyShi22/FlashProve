-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/Paid.lean: **THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM, BOTH ARMS, WITH
THE BATCHING's CONVERSE PAID.** Two statements and their proofs: each is one call of the law
(LawY.lean) and one of the payer (Johnson/Desc/K12/Law/Tuple/BatValsPay.lean, the kind's own law's
side).

What is said. In the promise, in the place of the count `BatAtY`, stands `PayK`: at whatever the
record fixes: the facts on codes at the first radius in the form `StageJ`; the test with code
`combineAt` at the statement behind the batching's beginning; four numbers of the layout; and
"the list's bound at the radius times (the number of rows less one) is at most v₀". The piece's
first error is v₀ times the sampler's number w of "BAT"'s round. What is concluded is `NTuple`:
there is one witness within the first radius of the group's word, of whose own words all the batched
rows hold, and whose parts are candidates at each sampled member.

  `k12_lawPaid`: the first arm (the first fold's mask has come earlier).
  `k12_lawPaidO`: the second arm (the first fold sends its own mask).
Limits. NO SOUNDNESS IS CLAIMED. `PayK` IS A PREMISE AND NO MEMBER OF IT IS SHOWN; v₀ is evaluated
nowhere. `NTuple` is not `NearAll` (Sheet.lean): it speaks of the witness's own words, not of each
row carried to the group's tables. `CodesAt`, the bound on the later errors (`bears`), `FirstOpens`
| `FirstOpensOwn` and the public premises of `AtPlace` | `AtPlaceOwn` stay premises; no member of
these is known. "BAT"'s round must draw one element and nothing else, at positions of at most 64
bits: two premises on the stretch's data. That the piece ever says yes is not shown.

-/
import Johnson.Desc.K12.Law.BatValsPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayK batAtY_pay)

/-- **The first arm, the batching's converse paid.** -/
theorem k12_lawPaid (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => FirstOpens π num no base x.1 ∧ PayK π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  Reduction.Leads.conseq
    (k12_lawY F W π num no L mC mS mW rad rd base dB dt _ εt (NTuple F π no rad rd) hA)
    (fun x hx => ⟨hx.1, batAtY_pay F W π no rad rd base dB dt v₀ εt x hx.2 h1 hlog⟩)
    (fun _ _ _ _ _ h => h)

/-- **The second arm, the batching's converse paid.** -/
theorem k12_lawPaidO (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => FirstOpensOwn π num no base x.1 ∧ PayK π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  Reduction.Leads.conseq
    (k12_lawYO F W π num no L mC mS mW rad rd base dB dt _ εt (NTuple F π no rad rd) hA)
    (fun x hx => ⟨hx.1, batAtY_pay F W π no rad rd base dB dt v₀ εt x hx.2 h1 hlog⟩)
    (fun _ _ _ _ _ h => h)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_lawPaid
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawPaidO
