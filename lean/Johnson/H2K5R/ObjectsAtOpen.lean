-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/ObjectsAtOpen.lean: KIND K5: WHAT THE READERS OF THE SEATED
ATTENTION LINK ANSWER AT THE LOOKUP's RUNS "objects" AND "guests": a join of theorems that lie.

Why. The clause "objects" of K5's law on what lies behind its sub-protocol (k5FillRel_objects,
Johnson/Desc/First/Att/K05ObjectsBack.lean) has two premises on the readers, hObj and hGst. The
light file Johnson/Desc/First/Att/K05ObjectsReaders.lean pays them at every list of runs in which
find? finds the lookup's run. Johnson/Desc/First/Look/K03StatesRaw.lean shows what
find? finds at the links of the proof file's description (k03_objects_raw, k03_guests_raw), and the
library's objects_answer (Johnson/Top/H/Keep/K3Late.lean) what the run returns. Here they meet, at
the attention links 2 g + 1, hearing block 1.

Main name:
  `K05_objects_guests_of_open`: **in the goals' scope, from an opening at the second hash function,
    for g below 12**: the link Lk at 2 g + 1, and at every filling H of the readers' two holes: hObj
    and hGst at Rd := readersOfLink H Lk.
THE LETTERS UNDER "FOR ALL": H: free on purpose · t: free on purpose (a law of the readers' make) ·
G, h: pinned by two equations at t. Lk: given with its equation; ONE Lk for both sentences.
PREMISES: hS · hR (the goals' scope: k03_objects_raw's own) · the opening O · g < 12. NOT at every
o in the second hash function's place: the payer stands in scope. IDLE wherever onlineDescription refuses.
OVER WHAT IT STANDS: all that the two files named stand on.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Look.K03StatesRaw
import Johnson.Desc.First.Att.K05ObjectsReaders
import Johnson.Top.H.Keep.K3Late

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.Desc.K9 (readersOfLink LinkHoles)
open VerifiableInference.OnPublicFiles (seatOf objects_answer k03_objects_raw k03_guests_raw)

/-- **hObj AND hGst AT THE SEATED LINK, FROM AN OPENING.** -/
theorem K05_objects_guests_of_open {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block First.S Claim)} {c : Chain First.S Claim} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) :
    ∃ Lk : Link First.S Claim, c.links[2 * g + 1]? = some Lk ∧
      (∀ (H : LinkHoles) (t : First.S) (G : Fork) (h : Forest.Heard), t.fork? = some G →
        t.lookHeard? = some h → (∀ f ∈ h.rows.toList, f.ents = #[]) →
        (readersOfLink H Lk).forms 1 "objects" t = some { forms := h.rows.toList, late := [] }) ∧
      ∀ (H : LinkHoles) (t : First.S) (G : Fork), t.fork? = some G →
        (readersOfLink H Lk).forms 1 "guests" t = some { forms := [], late := [] } := by
  have hl : 2 * g + 1 < 25 := by omega
  have hix : IM.k3Ix (2 * g + 1) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g + 1 = 24)]
    rfl
  obtain ⟨Lk, e1, ho⟩ := k03_objects_raw hS hR O (2 * g + 1) hl false
  obtain ⟨Lk', e1', hq⟩ := k03_guests_raw hS hR O (2 * g + 1) hl false
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  rw [hix] at ho hq
  refine ⟨Lk, e1, fun H t G h hF hh hb => ?_, fun H t G hF => ?_⟩
  · exact hRds_of_link H Lk 1 "objects" t _ (by decide)
      (objects_reader K3Lot.ofForm (fun _ => ⟨rfl, rfl, rfl⟩) ho hF
        (objects_answer (seatOf K3Lot.ofForm false) 0 hF hh) hb)
  · exact hRds_of_link H Lk 1 "guests" t _ (by decide) (guests_reader hq hF rfl)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_objects_guests_of_open
