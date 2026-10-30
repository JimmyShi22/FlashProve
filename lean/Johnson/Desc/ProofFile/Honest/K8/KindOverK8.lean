-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/KindOverK8.lean: THE SMALLNESS TEST: ITS TWO RUNS BEHIND THE
BATCHING ("K8.lsTail", "K8.tests"), AS THE KIND's OWN BLOCK LISTS THEM, RETURN WHEREVER THE
LIBRARY's LAW's TEXTS FOR THEM RETURN AND THE LIST OF TABLES IS THERE: the kind's half of the
converse of the library's tie, in the form `KindOver` of
Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean, another house's file of definitions. Lemmas on the
verifier's own text; none of the library's goals.

  `part_at`   where the ledger, the test's data and the list of tables are there, the kind's part of
                   the state is these three
  `lsTail_run`, `tests_run`   WHICH RUNS THE KIND's BLOCK LISTS under the two names: by unfolding
  **`kindOver_lsTail`**   (K8.whole pW).after.lookup "K8.lsTail" = some r → KindOver r K9L.k8LsTail
                   (the list of tables is there)
  **`kindOver_tests`**   (K8.whole pW).after.lookup "K8.tests" = some r → KindOver r (K9L.k8Tests
                   pW.nU) (the same)
Limits. Both are unfoldings: they say nothing on whether either text returns. The seat's half (the
run in the description's list) is not here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Batch.Law.K8Step
import Johnson.Desc.First.Batch.Law.K8Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (K8Part k8PartP testsP)
open ProofFile.Honest.K9 (KindOver)

/-- The kind's part of the state, where its three pieces are there. -/
theorem part_at {e : S} {F : Fork} {tl : HTailF2} {funs : Array HFun} (hF : e.fork? = some F)
    (ht : e.tl? = some tl) (hf : S.funs? e = some funs) :
    k8PartP.get? e = some ⟨tl, funs, F⟩ := by
  show ((tlForkP.get? e).bind fun x => (S.funs? e).map fun fs => (⟨x.1, fs, x.2⟩ : K8Part)) = _
  have e1 : tlForkP.get? e = some (tl, F) := by
    show ((e.tl?).bind fun p => (e.fork?).map fun q => (p, q)) = _
    rw [ht, hF]
    rfl
  rw [e1, hf]
  rfl

/-- The run that the kind's block lists under "K8.lsTail". -/
theorem lsTail_run (pW : K8.ParW) {r : S → Except String S}
    (h : (K8.whole pW).after.lookup "K8.lsTail" = some r) :
    r = fun s => (K8.atRecord (fun q => (TailClaims.k8LsTail.2 q).map fun q' => ((), q')) s).map
      (·.2) := (Option.some.inj h).symm

/-- The run that the kind's block lists under "K8.tests". -/
theorem tests_run (pW : K8.ParW) {r : S → Except String S}
    (h : (K8.whole pW).after.lookup "K8.tests" = some r) :
    r = fun s => (K8.atRecord (fun q => ((TailClaims.k8Tests pW.nU).2 q).map fun q' => ((), q'))
      s).map (·.2) := (Option.some.inj h).symm

/-- **The first run.** -/
theorem kindOver_lsTail (pW : K8.ParW) {r : S → Except String S}
    (h : (K8.whole pW).after.lookup "K8.lsTail" = some r) :
    KindOver r K9L.k8LsTail (fun e => (S.funs? e).isSome = true) := by
  intro e x hx hp
  obtain ⟨F, tl, hF, ht, rfl⟩ := K9L.k8LsTail_ok e x hx
  obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1 hp
  rw [lsTail_run pW h]
  show (K8.atRecord _ e).map (·.2) = _
  unfold K8.atRecord
  rw [part_at hF ht hf]
  show (.ok ((e.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB }).putFork F) :
    Except String S) = _
  have hk : (e.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB }).fork? = some F :=
    (tlP_apart_forkP.get_right e _).trans hF
  rw [show (e.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB }).putFork F =
    e.putTl { tl with lsTail := F.LS.extract tl.slotA tl.slotB } from
      forkP_lawful.set_get _ F hk]

/-- **The second run.** -/
theorem kindOver_tests (pW : K8.ParW) {r : S → Except String S}
    (h : (K8.whole pW).after.lookup "K8.tests" = some r) :
    KindOver r (K9L.k8Tests pW.nU) (fun e => (S.funs? e).isSome = true) := by
  intro e x hx hp
  obtain ⟨funs, hf⟩ := Option.isSome_iff_exists.1 hp
  simp only [K9L.k8Tests] at hx
  obtain ⟨F, hF, hx⟩ := K9L.ok_bind hx
  obtain ⟨tl, ht, hx⟩ := K9L.ok_bind hx
  obtain ⟨G, hG, hx⟩ := K9L.ok_bind hx
  obtain rfl : (e.putTl tl).putFork G = x := Except.ok.inj hx
  rw [tests_run pW h]
  show (K8.atRecord _ e).map (·.2) = _
  unfold K8.atRecord
  rw [part_at (K9L.there_ok hF) (K9L.there_ok ht) hf]
  have hq : (TailClaims.k8Tests pW.nU).2 ⟨tl, funs, F⟩ = .ok ⟨tl, funs, G⟩ := by
    show (testsP pW.nU tl F).map _ = _
    rw [hG]
    rfl
  show ((((TailClaims.k8Tests pW.nU).2 ⟨tl, funs, F⟩).map fun q' => ((), q')).map fun y =>
    (y.1, k8PartP.set e y.2)).map (·.2) = _
  rw [hq]
  rfl

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.part_at
#print axioms ProofFile.Honest.K8.kindOver_lsTail
#print axioms ProofFile.Honest.K8.kindOver_tests
