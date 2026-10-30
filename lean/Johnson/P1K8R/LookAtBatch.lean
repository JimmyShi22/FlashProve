-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/LookAtBatch.lean: AT A LAYERS' SEGMENT WHAT THE LOOKUP ON THE CALLS HAS HEARD BEHIND
ITS OWN BLOCK STANDS IN FRONT OF THE BATCHING; SO THERE IT HAS HEARD SOMETHING, AND ITS ROWS NAME NO
ENTRY. AT STATES THAT THE FIRST CHAIN's OWN BLOCKS REACH; UNDER THE SCOPE, THE FILES READ, IM.Open
AND THE DESCRIPTION's TEST ON ITS PLAN. Lemmas; none of the library's goals. No prover stands in
them; nothing on completeness, soundness or hiding. A joining.

  `look_back_digits`   one block back, at the 24 segments in front of the head's: LinkJoin.back_of
      (Johnson/Desc/First/Link/Law/StretchBack.lean) at the digits' lookup, with
      OnPublicFiles.stated_keeps (Johnson/K11R/LeavesAt346.lean), IM.k3_of (Johnson/IMR/K3Seat.lean),
      OnPublicFiles.k03_const_ok (Johnson/Desc/First/Look/K03PlanOf.lean), K3Lot.k03_place
      (Johnson/P5K3R/SitsRounds.lean)
  **`look_back_layers`**   five blocks back, from 28 g + 9 to 28 g + 4: that one; three by
      OnBytes.Road.K4.InT.ownHeard_back; the layers' own block by kept_reached
      (Johnson/Road/K4/InT/WinsReached.lean), whose KeptAtS holds Rest
      (Johnson/Desc/First/K4/ReadsAtS.lean). The end is OnPublicFiles.KeepsLook: what is heard at the one
      state is heard at the other
  **`callsRows_layers`**   with `callsRows_behind` (Johnson/P1K8R/HeardAtBatch.lean)
The like at the head's segment, from 346 back to 341: MergeLaw.seated_five with back_keeps
(LeavesAt346.lean).
Limits. The attention segments and the head's are not spoken of (Johnson/P1K8R/LookAtBatchAll.lean).
Nothing on the two other forms that a lookup hears; whoever shows something of what is heard at 28 g
+ 4 has it at 28 g + 9, by `look_back_layers`. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.HeardAtBatch
import Johnson.K11R.LeavesAt346
import Johnson.Road.K4.InT.WinsReached
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.Desc.First.Look.K03PlanOf
import Johnson.P5K3R.SitsRounds
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **From the batching's border back over the digits' lookup**, at the 24 segments in front of the
head's: what the lookup on the calls has heard stands behind it (OnPublicFiles.KeepsLook,
Johnson/K11R/LeavesAt346.lean). -/
theorem look_back_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (14 * l + 8) (z, s) ∧ OnPublicFiles.KeepsLook s s' := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l (by omega) true
  obtain ⟨b'', e3', hk⟩ := OnPublicFiles.k03_const_ok hS hR O hOk l (by omega) true
  obtain rfl : b' = b'' := Option.some.inj (e3.symm.trans e3')
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_pos rfl, if_neg (by omega)]
  rw [i3] at e2
  exact LinkJoin.back_of hS hR O (l := l) (i := 6) (by omega) e1 e2 e4 (fun q => nomatch q)
    (fun s rs gs t hd => OnPublicFiles.stated_keeps _ _ _ _ _ _ b' e3 hk l rfl
      (K3Lot.k03_place _ _ _ _ _ l true b' e3).1 s t rs gs hd) h

/-- **AT A LAYERS' SEGMENT: WHAT THE LOOKUP ON THE CALLS HAS HEARD BEHIND ITS OWN BLOCK STANDS IN
FRONT OF THE BATCHING**: five blocks back. -/
theorem look_back_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 4) (z, s) ∧ OnPublicFiles.KeepsLook s s' := by
  have h' : Reach 0 c.blocksInOrder start (14 * (2 * g) + 9) (z, s') := by
    rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact h
  obtain ⟨s8, r8, k8⟩ := look_back_digits hS hR O hOk (l := 2 * g) (by omega) h'
  rw [show 14 * (2 * g) + 8 = 28 * g + 8 by omega] at r8
  obtain ⟨s5, r5, k5⟩ := OnBytes.Road.K4.InT.ownHeard_back hS hR O hg r8
  obtain ⟨p, s4, r4, k4, -⟩ := OnBytes.Road.K4.InT.kept_reached hS hR O hOk hg r5
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hRest, -⟩ := k4
  exact ⟨s4, r4, ((OnPublicFiles.keepsLook_of_eq hRest.lookHeard).trans
    (OnPublicFiles.keepsLook_of_eq k5.2)).trans k8⟩

/-- **So, at a layers' segment, in front of the batching: the lookup on the calls has heard
something, and its rows name no entry.** -/
theorem callsRows_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ ∀ f ∈ k.rows.toList, f.ents = #[] := by
  obtain ⟨s4, r4, e⟩ := look_back_layers hS hR O hOk hg h
  have r4' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 4) (z, s4) := by
    rw [show 14 * (2 * g) + 4 = 28 * g + 4 by omega]
    exact r4
  obtain ⟨k, hk, hb⟩ := callsRows_behind hS hR O hOk (l := 2 * g) (by omega) r4'
  exact ⟨k, e k hk, hb⟩

end

end P1K8

#print axioms P1K8.look_back_digits
#print axioms P1K8.look_back_layers
#print axioms P1K8.callsRows_layers
