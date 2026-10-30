-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyHonestAt.lean: THEOREMS. **honest_pins_has (KeyHonestStrs.lean) FROM A TEST WITH CODE**: all its premises on the plan follow from «the test on a seat finds no fault»: seatFaultAt F cs tag s j₀ t₀ = none (Johnson/Desc/SeatAt.lean), by seat_of_noFault (Johnson/Desc/Sound/PlanMemProofs.lean). No test of our own is typed: the library has one.
OBJECT: hasSmp | NoColl | PIN at fillG, as in KeyHonestStrs.lean. USER: Johnson/RunOne/KeySeatNumsW.lean | KeySeatNumsW2.lean call honest_pins_at. LETTERS: cs · s · e · F · (j₀, t₀) · tag · o.
  sum_split       the tenants' words, summed tenant by tenant, are the main words' sum and the mask words' sum
  honest_pins_at  **no fault at the seat · Tie · meetsB · Sendable ⊢ at every seed there are a record, strings and a witness with hasSmp · NoColl · PIN, the witness naming the message sent**
What is not claimed. That the test finds no fault at any description: an evaluation's matter. One tenant. The stored table's half. An honest run. Nothing on soundness or on hiding.

-/
import Johnson.RunOne.KeyHonestStrs
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob
open VerifiableInference.Desc VerifiableInference.Desc.K1 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key.Fill

theorem sum_split : ∀ l : List VerifiableInference.Desc.SymbolComponent, (l.map fun t => t.main + t.mask).sum = (l.map (·.main)).sum + (l.map (·.mask)).sum
  | [] => rfl
  | t :: l => by
    simp only [List.map_cons, List.sum_cons, sum_split l]
    omega

variable {cs : Codes} {s : OracleShape} {e : Nat}

theorem honest_pins_at {XI : Type} (F : FileDescription XI) (tag : String) (j₀ t₀ : ℕ) (hfit : seatFaultAt F cs tag s j₀ t₀ = none)
    (hT : Tie cs s) (hme : meetsB cs s e = true) {m : (portCode cs s).J → GE} {r : (portCode cs s).Q → GE} (h : Sendable cs s m r)
    (o : ℕ) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) :
    ∃ (a : Statement) (y : Strs) (w : Wit Unit Unit VerifiableInference.Desc.Key.Fill.Tab),
      hasSmp (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a = true ∧
      NoColl F (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a y ∧
      PIN F (fillG cs s e j₀ t₀ (seedK cs s e (fun St : Statement => St) o) (fun _ _ => 0) (fun _ _ u _ => u) (fun _ (_ : Unit) => (none : Option Unit)) fun _ => none) j₀ t₀ a y w ∧
      w.msg 0 = ofU cs s e m := by
  obtain ⟨oo, n, ho, hn, hlog, hmain, hmask, hm, hsum, hdeg⟩ := seat_of_noFault F cs tag s j₀ t₀ hfit
  exact honest_pins_has F j₀ t₀ oo n ho hn ((sum_split oo.tenants).symm.trans hsum) hmain hmask hdeg hlog hm hT hme h o ρ

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.sum_split
#print axioms Johnson.RunOne.KeyLetters.honest_pins_at
