-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsEntInT.lean: AN ENTRY OF ROW 0 OF THE ARRAY OF THE HEAD's READS, BELOW
THE PLANNED WIDTH, PASSES THE TABLE OF JOINTS' TEST ON ENTRIES IN FRONT OF THE SECOND SENDING
(Johnson/Desc/First/Batch/FormsIn.lean: entInT): the premise hEnt of Law/K6FormsInT.lean's
k6_formsInT. A test with code, statements and proofs.

  entInT_second    GENERAL: where the open segment's list of arrays names the array number t by c,
                   c is of the segment's own second sending (Johnson/Desc/Sound/FormsT.lean:
                   second), and the layout's array of that name has a row and n columns at least.
  readsRoomC W lay arrs   A TEST WITH CODE ON PUBLIC PARAMETERS: the list arrs names the array of
                   the reads, the layout lay has an array of that name, with a row and as many
                   columns at least as the vector of reads is long.
  entInT_reads     MAIN: from that test, at a state whose open segment has that list and layout.

WHAT IT IS NOT. Implications. Nothing on soundness. readsRoomC HAS RUN AT NO PUBLIC PARAMETERS. That
the state's list of arrays and layout are the public ones, and that the reads' array is of the
second sending, are premises (another of K6's and K7's files has them off the table's promise).
LETTERS. No letter stands under "there is" in a conclusion.

-/
import Johnson.Desc.Sound.FormsT
import Johnson.Desc.Kinds.Law.RowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (reqArray)
open OnBytes.Model (Ent)
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.First (S)

/-- **An entry of row 0 of an array of the second sending passes the test on entries**, below n
columns. -/
theorem entInT_second (own : List (Nat × Nat)) (s : S) (aK : K9.Part)
    (hseg : K9.segAt? s = some aK) (t n : Nat) (c : Nat × String)
    (harr : aK.L.arrayOf[t]? = some c) (h2 : Sound.second s c = true)
    (hsz : ∀ A, reqArray aK.L.check.rows.layout c.1 c.2 = some A → 0 < A.sizeI ∧ n ≤ A.sizeC)
    (x : Ent) (h1 : x.tree = t) (hr : x.row = 0) (hi : x.idx < n) :
    K9.entInT own aK x = true := by
  unfold Sound.second at h2
  rw [hseg] at h2
  replace h2 : (match reqArray aK.L.check.rows.layout c.1 c.2 with
    | some A => K9.atMoment1 aK c A
    | none => false) = true := h2
  unfold K9.entInT
  rw [Bool.or_eq_true]
  right
  rw [h1, harr]
  show (match reqArray aK.L.check.rows.layout c.1 c.2 with
    | none => false
    | some A => K9.atMoment1 aK c A &&
      (Decidable.decide (x.row < A.sizeI) && Decidable.decide (x.idx < A.sizeC))) = true
  cases hA : reqArray aK.L.check.rows.layout c.1 c.2 with
  | none =>
    rw [hA] at h2
    cases h2
  | some A =>
    rw [hA] at h2
    obtain ⟨z1, z2⟩ := hsz A hA
    have h2' : K9.atMoment1 aK c A = true := h2
    show (K9.atMoment1 aK c A &&
      (Decidable.decide (x.row < A.sizeI) && Decidable.decide (x.idx < A.sizeC))) = true
    rw [h2', hr, decide_eq_true z1, decide_eq_true (Nat.lt_of_lt_of_le hi z2)]
    rfl

/-- **A TEST WITH CODE ON PUBLIC PARAMETERS**: the list names the array of the reads; the layout has
an array of that name, with a row, and as many columns at least as the vector of reads is long. -/
def readsRoomC (W : OnBytes.Model.Verify.Public) (lay : ReqLayout) (arrs : Array (Nat × String)) :
    Bool :=
  (arrs[readsOf W]?).any fun c =>
    (reqArray lay c.1 c.2).any fun A =>
      Decidable.decide (0 < A.sizeI) && Decidable.decide (W.H.nU.getD 2 0 ≤ A.sizeC)

/-- **THE PREMISE hEnt**, from the test. -/
theorem entInT_reads (W : OnBytes.Model.Verify.Public) (lay : ReqLayout)
    (arrs : Array (Nat × String)) (hC : readsRoomC W lay arrs = true) (own : List (Nat × Nat))
    (s : S) (aK : K9.Part) (hseg : K9.segAt? s = some aK)
    (hlay : aK.L.check.rows.layout = lay) (harrs : aK.L.arrayOf = arrs) (c : Nat × String)
    (harr : aK.L.arrayOf[readsOf W]? = some c) (h2 : Sound.second s c = true) :
    ∀ x : Ent, x.tree = readsOf W → x.row = 0 → x.idx < W.H.nU.getD 2 0 →
      K9.entInT own aK x = true := by
  refine fun x => entInT_second own s aK hseg (readsOf W) _ c harr h2 (fun A hA => ?_) x
  unfold readsRoomC at hC
  rw [← harrs, harr, ← hlay] at hC
  have hC' : ((reqArray aK.L.check.rows.layout c.1 c.2).any fun A =>
      Decidable.decide (0 < A.sizeI) && Decidable.decide (W.H.nU.getD 2 0 ≤ A.sizeC)) = true := hC
  rw [hA] at hC'
  have hC2 : (Decidable.decide (0 < A.sizeI) &&
      Decidable.decide (W.H.nU.getD 2 0 ≤ A.sizeC)) = true := hC'
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hC2
  exact hC2

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.entInT_second
#print axioms VerifiableInference.Desc.Kinds.Head.Law.entInT_reads
