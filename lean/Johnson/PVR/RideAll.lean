-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/RideAll.lean: the run of the verifier on files, as one function of what `VerifierAndGoals.verify`
takes. `Lets`: eight parameters with code, each a function of the three public files: the data of
the key file's and the proof file's rounds, the three decisions, the test in front of them, the
plan's values, the statement's item. `Shares`: a `FlashProve.DescriptionData` has these eight at given public
files. `rideOf`: the five premises of `tie_tenth` (Johnson/Goal/Tie/TieSteps.lean), the three
decoders, then one call of `stepsFullAllAt`. `rideOf_is_verify`: what it returns is
`VerifierAndGoals.verify` at `descriptionOfDataOnBytes L`, evaluated at `hashOf O`. `verdictFrom`,
`verdictFrom_is_verify`: the same for the verdict, with the two rejections in front of the call: out
of the goals' scope, and where the decoders refuse the bytes.
Limits. No soundness: the theorems say that two texts give one answer, not that the answer is right.
At the description's own parser and form alone. At `hashOf O` for a function O on bytes. Where
`verdictFrom` gives `none` nothing is said. This file is a port of a file of the same name (not in
this library), without its print helper `rideRows`, its
placeholder `Lets.filler` with `shares_filler`, and its closing prints; the definitions and proofs
that stay are unchanged. A reference run, over a set of this project's Lean files,
rode that file: that run's print is tied to these theorems by name and statement, not by bytes.

-/
import Johnson.Goal.Tie.TieSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.Ride
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open PV.Head (cThru sevenThru)
open PV.RunPure.Full (stepsFullAllAt)
open LPFD.Full (XF)

/-- The eight parameters of the run, each a function of the three public files alone. -/
structure Lets where
  DK : OnBytes.K.Pub → WholeD
  DP : OnBytes.K.Pub → WholeD
  runK : OnBytes.K.Pub → RecFull → PQ.View → PQ.View → PQ.View → Bool
  runP : OnBytes.K.Pub → XF × RecFull → PQ.View → PQ.View → PQ.View → Bool
  dec : OnBytes.K.Pub → RecFull × RecFull → PQ.View → Bool
  /-- the test of the public files that stands in front of the three decisions -/
  live : OnBytes.K.Pub → Bool
  /-- the plan's values, which `stepsFullAllAt` takes as an argument -/
  G : OnBytes.K.Pub → OnBytes.Flat.FilesParameters XF RecFull
  /-- the statement's item "request" at an instance (`PV.MFull.spI it`) -/
  it : OnBytes.K.Pub → XF → ByteArray

/-- `L` has the eight parameters of `ℓ` at these public files. -/
structure Shares (ℓ : Lets) (L : FlashProve.DescriptionData) (Z : PublicFiles) : Prop where
  DK : L.DK (asDescriptionFiles Z) = ℓ.DK (asDescriptionFiles Z)
  DP : L.DP (asDescriptionFiles Z) = ℓ.DP (asDescriptionFiles Z)
  runK : L.runK (asDescriptionFiles Z) = ℓ.runK (asDescriptionFiles Z)
  runP : L.runP (asDescriptionFiles Z) = ℓ.runP (asDescriptionFiles Z)
  dec : L.dec (asDescriptionFiles Z) = ℓ.dec (asDescriptionFiles Z)
  live : L.live (asDescriptionFiles Z) = ℓ.live (asDescriptionFiles Z)
  plan : L.G (asDescriptionFiles Z) = ℓ.G (asDescriptionFiles Z)
  item : L.it (asDescriptionFiles Z) = ℓ.it (asDescriptionFiles Z)

/-- The run: the five premises of `tie_tenth`, the three decoders, then one call of
`stepsFullAllAt`. -/
def rideOf (ℓ : Lets) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes) (commitment :
            Commitment) (prompt output : List Token) :
    Except String FastSteps :=
  if tiePremB (ℓ.live (asDescriptionFiles Z)) Z O B = true then
    match decodeD (cThru O (asDescriptionFiles Z)) B with
    | none => .error "the decoders refuse"
    | some f =>
      match stepsFullAllAt {} (ℓ.G (asDescriptionFiles Z)) (PV.MFull.spI (ℓ.it (asDescriptionFiles Z))) O (cThru O
                                (asDescriptionFiles Z)) (sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)))
          (ℓ.DK (asDescriptionFiles Z)) (ℓ.DP (asDescriptionFiles Z)) (ℓ.runK (asDescriptionFiles Z)) (ℓ.runP (asDescriptionFiles Z)) (ℓ.dec
                                                          (asDescriptionFiles Z))
          commitment prompt output f.aux f.cm f.rcd f.copy f.fT f.e f.fB with
      | none => .error "the first public answer has not 32 bytes"
      | some s => .ok s
  else .error ("of the tie's five premises these say no: " ++
    toString (((tieRows (ℓ.live (asDescriptionFiles Z)) Z O B).filter fun r => !r.2).map (·.1)))

/-- What the run returns is `VerifierAndGoals.verify` at `descriptionOfDataOnBytes L`, for every `L` that has the
parameters. -/
theorem rideOf_is_verify (ℓ : Lets) (L : FlashProve.DescriptionData) (Z : PublicFiles) (sh : Shares ℓ L Z) (O :
                       ByteArray → ByteArray) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) (s : FastSteps) (h : rideOf ℓ Z O B
        commitment prompt output = .ok s) :
    s.yes = (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output
        B).evaluate (hashOf O) := by
  unfold rideOf at h
  split at h
  · rename_i hp
    split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i s' hs
        cases h
        exact tie_tenth L Z O B (by rw [sh.live]; exact hp) commitment prompt output f hf _
          (by rw [sh.plan, sh.item, sh.DK, sh.DP, sh.runK, sh.runP, sh.dec]; exact hs)
  · cases h

/-- The verdict read off what the run returned: `some true` accept, `some false` reject. `none`: the
theorem below says nothing (a premise on the data fails, or an answer of `O` at a public string has
not 32 bytes). -/
def verdictFrom (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes) (r : Except String FastSteps)
    : Option Bool :=
  if InScope Z = true then
    match r with
    | .ok s => some s.yes
    | .error _ =>
      if (decide ((cThru O (asDescriptionFiles Z)).size = 32) &&
          ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).all fun b => decide (b.size
                                    = 32)) &&
          (decodeD (cThru O (asDescriptionFiles Z)) B).isNone) = true then some false else none
  else some false

/-- Whatever verdict is given is that of `VerifierAndGoals.verify` at `descriptionOfDataOnBytes L`, for every `L` that has
the
parameters. -/
theorem verdictFrom_is_verify (ℓ : Lets) (L : FlashProve.DescriptionData) (Z : PublicFiles) (sh : Shares ℓ L Z) (O :
                       ByteArray → ByteArray) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) (b : Bool)
    (h : verdictFrom Z O B (rideOf ℓ Z O B commitment prompt output) = some b) :
    b = (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output
        B).evaluate (hashOf O) := by
  unfold verdictFrom at h
  split at h
  · rename_i scope
    split at h
    · rename_i s hs
      cases h
      exact rideOf_is_verify ℓ L Z sh O B commitment prompt output s hs
    · split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Option.isNone_iff_eq_none]
            at hc
        exact (verify_descriptionOfDataOnBytes_refused L Z scope O hc.1.1 hc.1.2 commitment prompt output B
            hc.2).symm
      · cases h
  · rename_i scope
    cases h
    exact (verify_out_of_scope L Z (by simpa using scope) (hashOf O) commitment prompt output
        B).symm

end PV.Ride
