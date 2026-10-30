-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/EntersSymbolsAtTheWrittenScript.lean

Nothing on hiding. No property of the protocol is claimed. Two theorems. In the side library: it imports
AtFullSide.K1.LaysAtEveryList and AtFullSide.K1.LaysAtSwitches.

"ScriptSymsRawOn" AT THE FIRST CHAIN's CLOSED SCRIPT "firstScriptAt" (AtFullSide/K1/FirstScript.lean), on all entries, planes and cells,
at an input whose own trace is a trace τ read by "cellOf".

* "laysFilling_at_the_first_script": the senders' sentence at every link below 25 and every bound N: at link 0 by
  "laysFilling_opening_any", at the links 1 to 24 by "laysFilling_switches".
* "rawOn_at_the_first_script": the end.

WHAT IS LEFT AS PREMISES: the head h and the return hA · hLent, hClose, hPub: the three hypotheses of "laysFilling_switches", each at
every place of the code switch, paid nowhere here · planesSizes: ON PUBLIC DATA: the planes' matrices have the filling's sizes · the
input is valid and its trace is τ read by "cellOf".
"The readers read the trace" is by unfolding at "readersB". "The seats' entries read no challenge" is not asked.

Limits. "firstScriptAt" IS THE SCRIPT AT THE BASE PROVER: A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit, returned at the filling
"onlineProverPartsInUse I ...". The honest provers' term (E2E/TheHonestProver.lean) lays that filling READ THROUGH "tableCoins", at the
object's type of randomness: its inputs are of another type. No theorem here crosses from the one to the other.
-/
import Johnson.HonestTrace.Joint.EntersSymbolsAtEveryList
import AtFullSide.K1.LaysAtEveryList
import AtFullSide.K1.LaysAtSwitches

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Meaning (sizesOf)
open P5J (AtMgA TS)
open OnBytes.Maker (WholeD)
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (firstScriptAt readersB LocB laysFilling_opening_any laysFilling_switches)
open ProofFile.Honest.K5 (LaysFilling)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The closed Script lays the filling of the matrices at every link below 25, at every bound.** -/
theorem laysFilling_at_the_first_script (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (valid : LocB W₀ → Prop) (N : ℕ)
    (hLent : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true)
    (hClose : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (hPub : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ w : LocB W₀, valid w →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p ((K2.segmentsOf A.Z A.G).take p.link)
        w.x = true) :
    ∀ link < 25, ∃ seat heard,
      LaysFilling h (firstScriptAt I Sz.ref Op A cF) valid N (readersB I A.Z) seat heard link := by
  intro link below
  by_cases first : link = 0
  · subst first
    exact ⟨_, _, laysFilling_opening_any h hA valid N⟩
  · exact ⟨_, _, laysFilling_switches h hA valid N hLent hClose hPub (Nat.pos_of_ne_zero first) below⟩

/-- **THE END: the closed Script's messages at the layout's seats are the packing of the input's trace.** -/
theorem rawOn_at_the_first_script (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    {valid : LocB W₀ → Prop}
    (hLent : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 p k).isSome = true)
    (hClose : ∀ p ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take p.link) p = true)
    (hPub : ∀ p ∈ K2.switchPlaces A.Z A.G, ∀ w : LocB W₀, valid w →
      K2.publicOk (widerRows Sz.ref A.Z A.G) A.G.first.layout p ((K2.segmentsOf A.Z A.G).take p.link)
        w.x = true)
    (planesSizes : ∀ link < 25, ∀ number segment,
      Sz.ref.matAt link number = some (segment, planeOf segment) →
      (sizesOf (P5J.At.X A.Z) link).m number = (Sz.ref.shapeNo link number).1 ∧
        (sizesOf (P5J.At.X A.Z) link).k number = (Sz.ref.shapeNo link number).2)
    (k : Coins A.B) {v : LocB W₀} (isValid : valid v) {τ : Tr}
    (traceIs : v.trace = ⟨cellOf (P5J.At.X A.Z) τ⟩) :
    ScriptSymsRawOn A.Z (firstScriptAt I Sz.ref Op A cF) k v τ fun _ _ => True :=
  rawOn_at_the_inputs_trace_at_every_list h
    (laysFilling_at_the_first_script h hA valid 0 hLent hClose hPub) planesSizes isValid rfl traceIs

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.laysFilling_at_the_first_script
#print axioms OnBytes.HonestTrace.rawOn_at_the_first_script
