-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigMasks.lean: the lookup on the digits of a link's smallness test: THE
PAYER INTO THE ROW OUT AT A WORLD WITH MASKS OF ITS OWN. Two statements with their proofs. NO
SOUNDNESS IS CLAIMED.

Why. k3Out_of_rows (Johnson/Top/H/K3OutRows.lean) judges the claims at the world whose mask under
slot j is the caller's reading μ₀ (mk j), AT EVERY j. Whoever makes the world has masks of its own.
What a claim is worth reads of the masks those under the slots that its form names, and no other.

Main names.
  valC_masks: two worlds over one ledger and the same entries, whose masks agree at the slots that a
    claim's form names, give the claim one worth.
  k3Out_of_rows_masks: the payer with the claims judged at a world with any masks that, at the slots
    that the claims' forms name, are μ₀ (mk j).
Limits. Those of K3OutRows.lean. That the made world's masks at these slots are what the committed
messages hold is owed by whoever makes the world. The premise on c2 ranges over all its members, as
the payer's own premise hz does; four are spent.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- **What a claim is worth reads of the masks those under the slots that its form names.** -/
theorem valC_masks (H : Fork) {mask mask' : ℕ → K} (entry : ℕ → ℕ → ℕ → K) (k : Desc.Claim)
    (h : ∀ s ∈ k.form.slots.toList, mask s.1 = mask' s.1) :
    valC ρ (H.worldOf ρ mask entry) k = valC ρ (H.worldOf ρ mask' entry) k := by
  have e : k.form.slots.toList.map (slotValue ρ (H.worldOf ρ mask entry)) =
      k.form.slots.toList.map (slotValue ρ (H.worldOf ρ mask' entry)) :=
    List.map_congr_left fun s hs => by
      simp only [slotValue, Fork.worldOf, h s hs]
  have e1 : Ent.value ρ (H.worldOf ρ mask entry) = Ent.value ρ (H.worldOf ρ mask' entry) :=
    funext fun _ => rfl
  have e2 : Run2.value ρ (H.worldOf ρ mask entry) = Run2.value ρ (H.worldOf ρ mask' entry) :=
    funext fun _ => rfl
  unfold valC Aff.value
  rw [e, e1, e2]

variable {J₀ : Type} {front : ℕ}

/-- **The payer into the row out, at a world with masks of its own.** -/
theorem k3Out_of_rows_masks (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tl) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ)
    (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hV : DigRows ρ tl g entry fun e => μ₀ (en e))
    (mask : ℕ → K) (clO : List Desc.Claim)
    (hmO : ∀ k ∈ clO, ∀ s ∈ k.form.slots.toList, mask s.1 = μ₀ (mk s.1))
    (hm2 : ∀ k ∈ c2.toList, ∀ s ∈ k.form.slots.toList, mask s.1 = μ₀ (mk s.1))
    (hO : ∀ rs : Rounds K, HeardIs ρ g F' (endsOf g.shape 5 jLK rs) →
      clO.map (valC ρ (H.worldOf ρ mask entry)) =
        (endsOf g.shape 5 jLK rs).rows.map
          (rowRes fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)))
    (hzO : ∀ k ∈ clO, valC ρ (H.worldOf ρ mask entry) k = 0)
    (hz : ∀ k ∈ c2.toList, valC ρ (H.worldOf ρ mask entry) k = 0) :
    K3Out g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) ρ g F' :=
  k3Out_of_rows ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs jLK F' h0 hok hT hF hfull h5 hn h63 hP hD
    en mk μ₀ entry H hH hV clO
    (fun rs hI => (List.map_congr_left fun k hk =>
      (valC_masks ρ H (mask := mask) (mask' := fun j => μ₀ (mk j)) entry k (hmO k hk)).symm).trans
        (hO rs hI))
    (fun k hk => (valC_masks ρ H (mask := mask) (mask' := fun j => μ₀ (mk j)) entry k
      (hmO k hk)).symm.trans (hzO k hk))
    (fun k hk => (valC_masks ρ H (mask := mask) (mask' := fun j => μ₀ (mk j)) entry k
      (hm2 k hk)).symm.trans (hz k hk))

end

#print axioms valC_masks
#print axioms k3Out_of_rows_masks

end VerifiableInference.OnPublicFiles
