-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SpeaksAtFront.lean: the named premise `Speaks` (RunsAre.lean: at five runs
of claims the stated run's own reader answers) at a state that meets the table's condition in front
of the merge of the claims on the committed table (border 346), at the composed meaning
`mgAll D Mg`: from one fact on the state, `TablesLaid` (SpeaksOfTables.lean). Two theorems with
their proofs.

How. The condition at border 346 holds the public tests "formsIn 24 3 planes", "formsIn 24 4 join"
and "formsIn 24 4 own" (`k11_hIn`, K11PubClosed.lean). At the composed meaning each is a test on the
runs for which it stands (`pubAll_formsIn`, Johnson/Desc/First/PubAllAt.lean), and such a test
accepts only where the segment's readers answer. The readers of segment 24 are `readersOfLink` at
the holes of `holesAt` (Johnson/Desc/First/Batch/ReadersAt.lean), whose second arm, at the output
head's segment, is `k6Silent` at the letters `phAt X 24`. Then `speaks_of_forms`.

Main names.
  `forms_of_test`: a run's test on its forms, in either form, accepts only where the reader
    answers.
  `speaks_at_front`: `Speaks l a.1`.

Premises of the second: D.links = `linksFull`; Mg.more = {}; `headLink X = 24`; the table's
condition at 346; no mark; D.lk 24 = some l; `TablesLaid (phAt X 24) a.1`.

Limits. `TablesLaid` is shown of no state. General in D and Mg. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.K11PubClosed
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Batch.ReadersAt
import Johnson.Top.H0.MergeLaw.SpeaksOfTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (segAt? formsIn formsInA Readers)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_pub keep24 linksFull runsAt CellsQ MsgT
  k11_hIn)

/-- A run's test on its forms, in either form, accepts only where the reader answers. -/
theorem forms_of_test (Rd : Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (ah : Bool)
    (piece : ℕ) (run : String) (s : S)
    (h : (if ah then formsInA Rd sent own piece run s else formsIn Rd own piece run s) = true) :
    (Rd.forms piece run s).isSome = true := by
  cases e2 : Rd.forms piece run s with
  | some R => rfl
  | none =>
    cases ah with
    | true =>
      have h' : formsInA Rd sent own piece run s = true := h
      unfold formsInA at h'
      rw [e2] at h'
      cases e1 : segAt? s <;> rw [e1] at h' <;> cases h'
    | false =>
      have h' : formsIn Rd own piece run s = true := h
      unfold formsIn at h'
      rw [e2] at h'
      cases e1 : segAt? s <;> rw [e1] at h' <;> cases h'

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **`Speaks` at the table's condition in front of the merge**, from `TablesLaid`. -/
theorem speaks_at_front (hl : D.links = linksFull) (hM : Mg.more = {})
    (hH : VerifiableInference.OnPublicFiles.headLink X = 24) (Nn : Numbers) {Fr : Sound.Frame} (z : P)
    (a : S × Fr.E.Str)
    (hon : Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) {l : Link S Claim} (hlk : D.lk 24 = some l)
    (ht : TablesLaid (K9.phAt X 24) a.1) : Speaks l a.1 := by
  unfold Sound.onQ onAt at hon
  obtain ⟨-, hmk | ⟨hb, -⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨-, hpub⟩, -⟩ := hb
    unfold pubHeld at hpub
    have hq : ∀ q ∈ keep24, (mgAll D Mg).pub q (z, a.1) = true := fun q hq =>
      List.all_eq_true.1 hpub q (k11_hIn D Mg hM q (List.mem_append_right _ hq))
    have hRd : D.pubD.Rd 24 =
        K9.readersOfLink (K9.holesAt X (VerifiableInference.OnPublicFiles.headLink X) 24 l) l :=
      K9.readersAt_some D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24 l hlk
    have hsil : (K9.holesAt X (VerifiableInference.OnPublicFiles.headLink X) 24 l).silent =
        Kinds.Head.Law.k6Silent (K9.phAt X 24) (K9.statesOfLink l) := by
      unfold K9.holesAt
      rw [hH]
      rfl
    have key : ∀ (k : ℕ) (r : String) (L : List (ℕ × String)), Pub.formsIn 24 k r ∈ keep24 →
        runsAt linksFull 24 k r = L → ∀ p ∈ L, (p.2 == "K8.equations") = false →
        speaksAt l p.1 p.2 a.1 = true := by
      intro k r L hk hL p hp hne
      have h1 := hq _ hk
      have e : D.pubD.runs 24 k r = L := by
        show runsAt D.links 24 k r = L
        rw [hl]
        exact hL
      rw [mgAll_pub, pubAll_formsIn, e, List.all_eq_true] at h1
      have h2 := forms_of_test _ _ _ _ _ _ _ (h1 p hp)
      rw [hRd] at h2
      exact speaks_of_forms _ l (K9.phAt X 24) p.1 hne hsil ht h2
    exact
      { planes2 := key 3 "planes" [(2, "planes")] (by simp [keep24]) (by decide) (2, "planes")
          (by simp) (by decide)
        join3 := key 4 "join" [(3, "join")] (by simp [keep24]) (by decide) (3, "join") (by simp)
          (by decide)
        norm3 := key 4 "own" [(3, "norm"), (3, "policy"), (3, "logits")] (by simp [keep24])
          (by decide) (3, "norm") (by simp) (by decide)
        policy3 := key 4 "own" [(3, "norm"), (3, "policy"), (3, "logits")] (by simp [keep24])
          (by decide) (3, "policy") (by simp) (by decide)
        logits3 := key 4 "own" [(3, "norm"), (3, "policy"), (3, "logits")] (by simp [keep24])
          (by decide) (3, "logits") (by simp) (by decide) }

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.forms_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.speaks_at_front
