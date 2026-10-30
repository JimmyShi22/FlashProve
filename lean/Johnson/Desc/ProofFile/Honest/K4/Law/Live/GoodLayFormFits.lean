-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/GoodLayFormFits.lean: CONDITIONAL.

What is here. A TRIAL THAT CAN FAIL: DO `k4_live4_form` AND `k4_un4_form`
(Law/Live/GoodLayForm.lean) FIT THE HYPOTHESES live4 AND un4 OF `goodLayers_of_clauses` AS ITS
WRITERS TYPED THEM? That theorem's file (Honest/K9/GoodLayPaid.lean, of the writers of the
sub-protocol K9) imports two files, Honest/K9/GoodLayShares.lean and
Honest/K3/Good/Live/SharesCover.lean; this file imports neither: the call itself is not made here.
In its stead: the two hypotheses' texts, copied to the letter, stand here as two definitions
(`K4.Live4Text`, `K4.Un4Text`), whose letters are those that the theorem binds in front of them (p4,
a₀, W4; p4, s, a₀, n, at its types), and they are elaborated under that file's own namespace and the
first six of its eight rows of opened names, copied to the letter. Then the two laws give the two
definitions, by a plain call each. It could fail: if a name of the texts meant another thing under
those opened names than under ours, or a letter had another type, Lean would refuse the call. 
`k4_texts_handed` (Honest/K9/K4TextsHanded.lean; no part of the library) states its end in the two
definitions and calls the two laws there.

  `K4.Live4Text`, `K4.Un4Text`   the two hypotheses' texts, as definitions.
  `k4_live4_fits`, `k4_un4_fits`   **the two laws give them.**

Not shown here. All that Law/Live/GoodLayForm.lean's head says is not shown. THAT THE COPIED TEXTS
AND ROWS ARE THAT FILE's IS HELD BY A PROGRAM OUTSIDE LEAN, against the file as it lay with us; Lean
cannot see it, and the trial cannot fail on a slip of the copy that keeps the types. THE LAST TWO
ROWS OF OPENED NAMES OF THAT FILE ARE NOT HERE: they open names of files of the writers of the
sub-protocol K3 (lookups) that are not imported; no name of the two texts is among those that they
open. NEITHER OF THAT FILE's TWO IMPORTS IS HERE: a bare name can also turn through a declaration
that they bring under an enclosing namespace (ProofFile.Honest.K9, ProofFile.Honest, ProofFile). One such name exists:
the frame's Honest/Strat.lean declares `ProofFile.Honest.plainOf`, another thing than the `plainOf` of the
texts; it does not lie beneath this file; whether it lies beneath that file cannot be walked from
here. With it beneath, by Lean's rule for names as we read it (at `plainOf` not tried), `plainOf lf`
would be refused: loudly, never silently. THE CALL OF `goodLayers_of_clauses` ITSELF IS NOT MADE
HERE.

A LAW, NOT A PART: its imports reach modules under Johnson/Bridge/ (through
Johnson/Desc/Ok/FormRules.lean): no file that defines a part of the description may import it.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.GoodLayForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Honest (layersFront layersBack plainOf)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt unnamedAt)

/-- The text of the hypothesis live4 of `goodLayers_of_clauses`. -/
def K4.Live4Text (p4 : OnBytes.Desc.First.K4.Par) (a₀ : LayOwn) (W4 : Nat → Prop) : Prop :=
  ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, W4 j → liveAt (plainOf lf ++ layersBack o) j = true

/-- The text of the hypothesis un4 of `goodLayers_of_clauses`. -/
def K4.Un4Text (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat) : Prop :=
  ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
    unnamedAt (plainOf lf ++ layersBack o) j = true

end ProofFile.Honest.K9

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4 (Par blockAtS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (roundsFit noDigest fieldPrimeWord)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Honest (layersBack plainOf)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt unnamedAt)
open ProofFile.Honest.K9 (Heard4)

/-- CONDITIONAL on every hypothesis. `k4_live4_form` gives live4's text. -/
theorem k4_live4_fits {p4 : Par} {s₀ s₁ : S} {mine : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))}
    (h : (blockAtS p4).decide s₀ (mine.map noDigest) cols = .ok s₁)
    (Qk : K4Pub) (eP : Qk.P = p4.P) (ehp : Qk.hp = p4.hp) (eg : Qk.g = p4.g)
    (hrf : roundsFit ((OnBytes.Desc.First.K4.entries Qk.P Qk.hp Qk.g).map fun e => { entry := e })
      mine = true)
    (hw : ∀ r ∈ mine, ∀ x ∈ r.drawn.elems, x.1 < fieldPrimeWord ∧ x.2.1 < fieldPrimeWord ∧ x.2.2 < fieldPrimeWord)
    {fr : List Fmt.Drawn} (hM : (k4MarkWide Qk).test fr (mine.map (·.drawn)) = none)
    (hC : k4CoinZero Qk (mine.map (·.drawn)) = none)
    {a : LayOwn} {fo : Forest.Heard} (ha : s₀.here = .lay a) (hfo : a.fo = some fo)
    (hF : Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (N : _root_.Fo.Tp.PadNames fo a.F) (hll : p4.P.y.h.ll - 1 = 1) (hLam : p4.P.y.LamM ≤ 2)
    (a₀ : LayOwn) (hcar : ∀ a₁, s₁.here = .lay a₁ → a₀.own = a₁.own) :
    ProofFile.Honest.K9.K4.Live4Text p4 a₀ (k4W4 a.F.next fo a₀) :=
  k4_live4_form h Qk eP ehp eg hrf hw hM hC ha hfo hF hfree N hll hLam a₀ hcar

/-- CONDITIONAL on every hypothesis. `k4_un4_form` gives un4's text. -/
theorem k4_un4_fits {p4 : Par} {s₀ s₁ : S} {rs : List Fmt.RoundView}
    {cols : List (List (Nat × List UInt64))} (h : (blockAtS p4).decide s₀ rs cols = .ok s₁)
    {a : LayOwn} {fo : Forest.Heard} (ha : s₀.here = .lay a) (hfo : a.fo = some fo)
    (hF : Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (N : _root_.Fo.Tp.PadNames fo a.F)
    (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ a.F.next)
    (s : S) (a₀ : LayOwn) (n : Nat) (hs : s.here = .lay a₀)
    (hcar : ∀ a₁, s₁.here = .lay a₁ → a₀.own = a₁.own) :
    ProofFile.Honest.K9.K4.Un4Text p4 s a₀ n :=
  k4_un4_form h ha hfo hF hfree N hlv s a₀ n hs hcar

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K9.K4.Live4Text
#print axioms ProofFile.Honest.K9.K4.Un4Text
#print axioms ProofFile.Honest.K4.Live.k4_live4_fits
#print axioms ProofFile.Honest.K4.Live.k4_un4_fits
