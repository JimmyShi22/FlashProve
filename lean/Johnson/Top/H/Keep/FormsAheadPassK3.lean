-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/FormsAheadPassK3.lean: THE PUBLIC TEST formsInA
(Johnson/Desc/First/Batch/Ahead.lean: the test on a run's forms where these may name what is still
ahead) PASSES A K3Pass (Johnson/Top/H/Keep/FormsPassK3.lean): true in front, true behind: the
sister, at formsInA, of k3_formsIn_fwd. And Fwd at the one name that a link's readers hand to the
link's FIRST hole, "K8.equations" (the run for which the table's name "small" stands), from one
premise on that hole. Statements and proofs: joinings over formsInA_on
(Johnson/Desc/Sound/FormsAheadOn.lean).

OBJECT: K9.formsInA; K9.readersOfLink H l at the name "K8.equations".
Used by Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean, Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean,
  Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean and 2 more.
LETTERS: s, s', F, G, Rd, sent, own, piece, run, H, l, b free.
Compiled with the whole library.

Main names:
  k3_formsInA_fwd: kind-free, under Fwd and hlow, as k3_formsIn_fwd.
  small_fwd: Fwd at "K8.equations" IS "what the first hole answered at s it answers at s'".
  small_formsInA_pass: the two joined.

Limits. THE ONE PREMISE THAT STAYS, hH: WHAT THE LINK's FIRST HOLE (H.small) ANSWERED AT s IT
ANSWERS AT s'. The accept of the digits' decision turns four fields of the approximate range
proof's parameters (foldDrawn, slotA, slotB, heard) and the ledger: whether that hole's term reads
any of them is left to its kind's files to say. hlow (its late slots lie below F.next): likewise.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.FormsPassK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? lateOk Read Readers readersOfLink LinkHoles formsInA)
open VerifiableInference.Desc.Sound (formsInA_on)
open VerifiableInference.Reads.Pass (Fwd)

/-- **THE TEST formsInA GOES FORWARD.** -/
theorem k3_formsInA_fwd {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (Rd : Readers)
    (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (hf : Fwd Rd piece run s s')
    (hlow : ∀ R, Rd.forms piece run s = some R → ∀ x ∈ R.late, x.1 < F.next)
    (hin : formsInA Rd sent own piece run s = true) :
    formsInA Rd sent own piece run s' = true := by
  cases ha : segAt? s with
  | none =>
    unfold formsInA at hin
    rw [ha] at hin
    cases hin
  | some a =>
    cases hR : Rd.forms piece run s with
    | none =>
      unfold formsInA at hin
      rw [ha, hR] at hin
      cases hin
    | some R =>
      obtain ⟨b, hb, _⟩ := P.part ha
      have hlate : lateOk R.late a = true := by
        have h := hin
        unfold formsInA at h
        rw [ha, hR] at h
        exact (Eq.mp (Bool.and_eq_true _ _) h).1
      have M := P.more ha hb (hlow R hR) hlate
      exact formsInA_on sent own Rd piece run s s' a b R ha hb hR (hf R hR) P.merge
        (P.rides own ha hb) ⟨M.ns, M.got, M.vp, M.mf⟩ (P.comes sent own ha hb) M.late hin

/-- **Fwd at the name that the link's first hole reads.** -/
theorem small_fwd (H : LinkHoles) (l : Link S Claim) (b : ℕ) {s s' : S}
    (hH : ∀ R, H.small s = some R → H.small s' = some R) :
    Fwd (readersOfLink H l) b "K8.equations" s s' :=
  fun R hR => hH R hR

/-- **"small".** -/
theorem small_formsInA_pass {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (H : LinkHoles)
    (l : Link S Claim) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (b : ℕ)
    (hH : ∀ R, H.small s = some R → H.small s' = some R)
    (hlow : ∀ R, H.small s = some R → ∀ x ∈ R.late, x.1 < F.next)
    (hin : formsInA (readersOfLink H l) sent own b "K8.equations" s = true) :
    formsInA (readersOfLink H l) sent own b "K8.equations" s' = true :=
  k3_formsInA_fwd P (readersOfLink H l) sent own b "K8.equations" (small_fwd H l b hH)
    (fun R hR => hlow R hR) hin

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_formsInA_fwd
#print axioms VerifiableInference.OnPublicFiles.small_fwd
#print axioms VerifiableInference.OnPublicFiles.small_formsInA_pass
