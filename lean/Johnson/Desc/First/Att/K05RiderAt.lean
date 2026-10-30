-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RiderAt.lean: kind K5: WHAT THE KIND's RELATION IN FRONT SAYS OF THE DENOMINATORS GIVES THE LOOKUP's ITEM worth "rider" (Johnson/Top/H/K3Worth.lean: K3WorthRider): the clause "rider" of K5FillIns (Att/K05Closes.lean).

How. The item says: at ALL rounds rs for which what the verifier has received from the lookup argument stands (HeardIs), the rider's family is met at the key point of rs. The library has (Cb.Rider.den_target_out) that this is
denOut … = 0 at that point. The kind's relation has denOut … = 0 at the typed statement's point x0.2.1.pt, which the lookup's sharp promise (K3LeftOutIs: OutTies.pt) ties to the key point of ITS OWN rounds. HeardIs reads the point's two parts off what was
received: so the key point is one at all rounds for which that stands.

Main names: keyPt_one · rider_of_denOut · k5FillIns_rider (the clause's text).
PREMISES OF k5FillIns_rider: H : AttOK (for AttFits) · leftIs (K5AtMg's own field) · hleftQ · hW : at this segment K3WorthRider … GIVES the meaning's worth m 2 "rider" (an implication at values) · hms : the pin's part is the lookups' tuple of messages.
THE LETTERS UNDER "FOR ALL": hW: s, y, w: free on purpose (a law of the meaning's make) · hms: w: the like · a' in leftIs: fenced by the item's own sentence.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Worth
import Johnson.Desc.First.Att.K05Closes
import Johnson.Desc.First.Att.K05LeftSeats
import Johnson.Desc.First.Att.K05AtCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask attCells attRider attFits_of)
open VerifiableInference.Desc.Sound (Frame strsOf)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart)
open VerifiableInference.OnPublicFiles (K3WorthRider K3OutRider keyPt)

/-- The key point is read off what was received. -/
theorem keyPt_one {g : Forest.Heard} {F' F'' : Fork} {En En' : Fo.Ends Cb.Gl.E} (h : Fo.HeardIs Reading.gl g F' En)
    (h' : Fo.HeardIs Reading.gl g F'' En') : keyPt En = keyPt En' := by
  unfold keyPt
  rw [← h.zx, ← h.zy, ← h'.zx, ← h'.zy]

/-- **The lookup's item worth "rider", from the kind's relation in front.** -/
theorem rider_of_denOut {S₀ W St₀ : Type} {set : Params.Setting} {x : VerifiableInference.Desc.First.Look.Place}
    {S : Attention.Shape} {tl : HTailF2} {D : Sent} {rad : OracleShape → Nat} (H : AttOK set x S tl D rad)
    (Ex' : Iop.ExtSpec) (Wp' : Type) {fork : S₀ → Option Fork} {heard : S₀ → Option Forest.Heard}
    {ι : Fo.Pl → Option (JAtt x.ns tl)} {Q : Fork → Prop} {x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))}
    {g₀ : Forest.Heard} {s : S₀} (hl : K3LeftOutIs fork heard x.fs x.lm x.F.next ι Q x0 g₀ s)
    (ms : W → (attSg x D rad).Msg) (w : W)
    (h : denOut (dimOf S) (callsOf x.fs) x0.2.1.pt (attCells x S tl D rad (ms w)) = 0) :
    K3WorthRider fork heard (attRider x S tl D rad Ex' Wp') x.lm x.F.next (fun _ => ()) ms s w := by
  obtain ⟨F, F₁, rs₀, _, hn, L, e1, _, T⟩ := hl
  intro g F' _ hh rs hI
  obtain rfl : g₀ = g := Option.some.inj (e1.symm.trans hh)
  have hF := attFits_of H.fits
  refine (Cb.Rider.den_target_out hF.e2 hF.nb (fun _ m => attCells x S tl D rad m) () _ (ms w)).2 ?_
  have hI₀ := L.heardIs
  rw [hn] at hI₀
  have hI' : Fo.HeardIs Reading.gl g₀ F' (Fo.endsOf x.fs x.lm x.F.next rs) := hI
  have e : keyPt (Fo.endsOf x.fs x.lm x.F.next rs) = x0.2.1.pt := by
    funext t
    rw [keyPt_one hI' hI₀, T.pt t, hn]
    rfl
  rw [show keyPt (Fo.endsOf (attRider x S tl D rad Ex' Wp').c.h x.lm x.F.next rs) = x0.2.1.pt from e, callsOf_eq]
  exact h

/-- **The clause "rider" of K5FillIns.** -/
theorem k5FillIns_rider {Pp W Cl : Type} {Fr : Frame} {set : Params.Setting} (claim : Aff → Cl) (Mg : Meaning Pp W)
    (N : Numbers) (links : List ModelPart) (π : Pp) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
    (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (H : AttOK set x S tl D rad) (Ex' : Iop.ExtSpec) (Wp' : Type)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (gOf : First.S × Fr.E.Str → Forest.Heard) (ι : Fo.Pl → Option (JAtt x.ns tl)) (Qr : Fork → Prop)
    (part ms : W → (attSg x D rad).Msg) (hms : ∀ w, ms w = part w)
    (leftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        x.fs x.lm x.F.next ι Qr (x0 a') (gOf a') a'.1)
    (hleftQ : Pub.left m ∈ Q)
    (hW : ∀ (s : First.S) y w,
      K3WorthRider (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
        (attRider x S tl D rad Ex' Wp') x.lm x.F.next (fun _ => ()) ms s w → Mg.worth m 2 "rider" (π, s) y w) :
    ∀ a' w, onT N Mg links π Fr pl O Q a' →
      denOut (dimOf S) (callsOf x.fs) (x0 a').2.1.pt (attCells x S tl D rad (part w)) = 0 →
      Mg.worth m 2 "rider" (π, a'.1) (strsOf Fr a'.2) w := fun a' w hon h =>
  hW a'.1 _ w (rider_of_denOut H Ex' Wp' (leftIs a' (onAt_pubP hon.1 hon.2 _ hleftQ)) ms w (by rw [hms]; exact h))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.keyPt_one
#print axioms VerifiableInference.Desc.First.Att.P.rider_of_denOut
#print axioms VerifiableInference.Desc.First.Att.P.k5FillIns_rider
