-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/SeatsAtS.lean: The kind "lookup" (K3): ITS TWO SEATS AT THE RECORD S (the lookup
on a link's calls; the lookup on the smallness test's digits), WITH THE PLAIN MAKER OF CLAIMS (a
form as a claim: no runs of entries, its own number's power), MEET THE TWO PREMISES ON A SEAT OF
Johnson/Top/H/Keep/RunsAtS.lean: AtS2 and SeatFits. Statements and proofs: all by rfl or by the
library's lemmas.

Main names:
  plain: a form as a claim.
  seatCalls_atS2, seatDigits_atS2: AtS2. seatCalls_fitsP, seatDigits_fitsP: SeatFits.
  objects_calls: objects_atS at the seat of the calls, with no premise on the seat left.

Limits. Nothing on whether a record meets the other premises of RunsAtS.lean's theorems.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunsAtS
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun _root_.Fo
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (claimValue worldAt Bound)

/-- A form as a claim. -/
def plain (a : Aff) : Desc.Claim := { form := a }

theorem seatCalls_atS2 : AtS2 (seatCalls plain) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem seatDigits_atS2 : AtS2 (seatDigits plain) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem seatCalls_fitsP : SeatFits (seatCalls plain) (·.form) :=
  seatCalls_fits plain (·.form) fun _ => rfl

theorem seatDigits_fitsP : SeatFits (seatDigits plain) (·.form) :=
  seatDigits_fits plain (·.form) fun _ => rfl

/-- **"objects" at the seat of the calls**: no premise on the seat is left. -/
theorem objects_calls {K : Type} [CommRing K] (ρ : Reading K) (lm : ℕ) {e e₁ : S}
    {a : Desc.K9.Part} {c : List Desc.Claim} {front jLK : ℕ} {g : Heard} {F0 : Fork}
    {rs : Rounds K} (ha : atS.get? e = some a) (hg : e.lookHeard? = some g)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rs)) (hL : _root_.Fo.Later F0 a.F)
    (hok : FoNums.ok g.shape = true) (hS : Sized a.F)
    (hr : objectsRun (seatCalls plain) front e = .ok (c, e₁)) :
    ∃ a₁ G, atS.get? e₁ = some a₁ ∧ Left a a₁ G ∧ e₁ = e.putFork G ∧
      e₁.lookHeard? = some g ∧ OnlyUnder a.F G ∧ _root_.Fo.Later a.F G ∧ Sized G ∧
      (∀ cl ∈ c, cl.eqFirst = none) ∧
      ∀ (L : LinkCtx) (H : Fork) (y : Bound K), _root_.Fo.Later G H →
        c.map (claimValue ρ (worldAt ρ L H y)) =
          (endsOf g.shape lm jLK rs).rows.map (rowRes (muOf y.mask)) :=
  objects_atS ρ (seatCalls plain) seatCalls_atS2 seatCalls_fitsP lm ha hg hI hL hok hS hr

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.seatCalls_atS2
#print axioms VerifiableInference.OnPublicFiles.seatDigits_atS2
#print axioms VerifiableInference.OnPublicFiles.objects_calls
