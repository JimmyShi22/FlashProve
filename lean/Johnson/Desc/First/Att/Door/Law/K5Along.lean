-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5Along.lean: kind K5: WHAT THE KIND's ROAD TO ITS SHARE OF THE CHAIN OF PROMISES SPENDS "FROM REACHED", AS ONE STRUCTURE OF SEVEN NAMED FIELDS, general in the condition Rch beside the promise.
(The bridge at the kind, k5_tiedR, Door/Law/PlusBridge.lean, asks of Rch: Facts5 · hbare · hleft · HandsOn. HERE LEAN HOLDS THE FIRST ALONE: K5Along.facts5. hbare | hleft follow from bare | left by
hbare_of_reached | hleft_of_reached, Door/Law/K5ReachedPlus.lean: not imported. HandsOn is no field: at the meant conditions it is a theorem in other files, kind-free.)

Main names:
  `K5Along Rch L M sent`: seats · shapes · liveShape · liveLayout · codes (in the texts of five fields of FoldFacts, Johnson/Desc/First/FoldFacts.lean: seatsCarried · msgShapes · liveShape · liveLayout · codes) · bare · left (at the twelve borders
    14 (2 g + 1) + 4 in front of the kind's sub-protocol: something is held as received from the lookup argument; its kept rows name no entry; the test leftAtB (Johnson/Desc/First/FillBare.lean) accepts at it and the segment's ledger).
  `K5Along.facts5`: the first five ARE the bridge's Facts5, where the composed data's shape, layout and codes are sent's.
  `K5Along.mono`: at a stronger condition the seven stay.
Is it empty here? A structure and projections. At Rch := never all seven are free. It is shown at no Rch here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.PlusBridge
import Johnson.Desc.First.FillBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes)

/-- **What the kind's road spends "from reached".** General in Rch. -/
structure K5Along {P : Type} {Fr : Frame} (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (L : Laid) (M : List OracleShape)
    (sent : Look.Sent) : Prop where
  seats : ∀ k a, Rch k a → a.1.2.failed = none → atFirstSeats L a.1.2 = true
  shapes : ∀ k a, Rch k a → a.1.2.failed = none → atFirstShapes M a.1.2 = true
  liveShape : ∀ k a, Rch k a → a.1.2.failed = none → a.1.2.live.frame.shape = sent.shape
  liveLayout : ∀ k a, Rch k a → a.1.2.failed = none → a.1.2.live.rows.layout = sent.layout
  codes : ∀ k a, Rch k a → a.1.2.failed = none → a.1.2.st.codes = sent.codes
  bare : ∀ g, g < 12 → ∀ a, Rch (14 * (2 * g + 1) + 4) a → ∃ g₁, a.1.2.lookHeard? = some g₁ ∧ ∀ f ∈ g₁.rows.toList, f.ents = #[]
  left : ∀ g, g < 12 → ∀ a, Rch (14 * (2 * g + 1) + 4) a →
    ∃ g₁ G, a.1.2.lookHeard? = some g₁ ∧ a.1.2.fork? = some G ∧ FillBare.leftAtB g₁ G = true

section
variable {P : Type} {Fr : Frame} {Rch : ℕ → (P × First.S) × Fr.E.Str → Prop} {L : Laid} {M : List OracleShape} {sent : Look.Sent}

/-- **The first five are the bridge's five.** -/
theorem K5Along.facts5 (A : K5Along Rch L M sent) (D : PubData) (cs : Codes) (e1 : D.d3.shape = sent.shape)
    (e2 : D.d3.layout = sent.layout) (e3 : cs = sent.codes) : Facts5 (fun a : P × First.S => a) D L M cs Rch where
  seats := A.seats
  shapes := A.shapes
  liveShape := fun k a hr hm => (A.liveShape k a hr hm).trans e1.symm
  liveLayout := fun k a hr hm => (A.liveLayout k a hr hm).trans e2.symm
  codes := fun k a hr hm => (A.codes k a hr hm).trans e3.symm

/-- At a stronger condition the seven facts stay. -/
theorem K5Along.mono (A : K5Along Rch L M sent) {Rch' : ℕ → (P × First.S) × Fr.E.Str → Prop} (hr : ∀ k a, Rch' k a → Rch k a) :
    K5Along Rch' L M sent where
  seats := fun k a h => A.seats k a (hr k a h)
  shapes := fun k a h => A.shapes k a (hr k a h)
  liveShape := fun k a h => A.liveShape k a (hr k a h)
  liveLayout := fun k a h => A.liveLayout k a (hr k a h)
  codes := fun k a h => A.codes k a (hr k a h)
  bare := fun g hg a h => A.bare g hg a (hr _ a h)
  left := fun g hg a h => A.left g hg a (hr _ a h)

end

end H2K5.Door

#print axioms H2K5.Door.K5Along.facts5
#print axioms H2K5.Door.K5Along.mono
