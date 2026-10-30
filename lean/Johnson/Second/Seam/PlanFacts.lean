-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/PlanFacts.lean: THE SEAM's PREMISES THAT READ NO STATE OF A RUN, AT THE RELEASE's OWN VALUES: members for the binders of tupleNine_sh | tupleTen_sh (Johnson/Desc/Sound/SeamAtSh.lean) that speak of the plan's codes and of the linear claim's shape alone. One test with code, its law, and evaluations at what the planner returns at three sets of public files.
  tieB cs s · tie_of_B     K1.Tie cs s (Johnson/Desc/K1/Law/Port2.lean: one answer · the codes' lengths · the shape's test · the pads fit) as a test; its yes gives Tie.
  Facts P sentU layU layO  what the binders ask of P : P14: hU withU P.S = some sentU · hsU sentU.size = 2 · hsO (withOmega P.S).size = 2 · hlU | hlO the two layouts of trees at the plan's codes · hS a split · hm the masks ahead · hTU | hTO | hTS Tie at S.fold.u | S.omega | S.sharedSplit.
  factsB P · facts_of_B    ONE Bool; its yes gives ∃ sentU layU layO, Facts P sentU layU layO.
  atFiles pol lay KL       that Bool at P := p14Of (the planner's chains at the three files) [].
  THE EVALUATIONS (#guard; they run whenever this file is compiled): VerifierAndGoals.storedPublicFiles · VerifierAndGoals.zGap · the library's small example; teeth.
Limits. AN EVALUATION AT ONE VALUE IS NO THEOREM: it pays «is it empty?» alone. beforePoint := []: none of these facts reads it. Nothing on the shared chain's state in a run (sharedX · fitsX · codX · tidY · msgY), on SeatFits, on the members' tests siteL | sampleL. No soundness is claimed.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K1.Law.Port2
import Ladder.Stored
import Johnson.G.PackList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params OnBytes.Model Desc.K14 Desc.Plain
open VerifiableInference.Desc (K1.Tie)

def tieB (cs : Codes) (s : OracleShape) : Bool :=
  decide (s.answers = 1) && cs.lengthsOk && Blk.shapeOk cs s &&
    (VerifiableInference.Desc.K1.Msg.of cs s).padFits

theorem tie_of_B {cs : Codes} {s : OracleShape} (h : tieB cs s = true) :
    VerifiableInference.Desc.K1.Tie cs s := by
  unfold tieB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- What the seam's binders ask of the plan. -/
structure Facts (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) : Prop where
  hU : withU P.S = some sentU
  hsU : sentU.size = 2
  hsO : (withOmega P.S).size = 2
  hlU : layTrees P.codes sentU = some layU
  hlO : layTrees P.codes (withOmega P.S) = some layO
  hS : P.S.sharedSplitNeeded = true
  hm : P.S.masksAhead = true
  hTU : VerifiableInference.Desc.K1.Tie P.codes P.S.fold.u
  hTO : VerifiableInference.Desc.K1.Tie P.codes P.S.omega
  hTS : VerifiableInference.Desc.K1.Tie P.codes P.S.sharedSplit

def factsB (P : P14) : Bool :=
  match withU P.S with
  | none => false
  | some sentU =>
    decide (sentU.size = 2) && decide ((withOmega P.S).size = 2) &&
      (layTrees P.codes sentU).isSome && (layTrees P.codes (withOmega P.S)).isSome &&
      P.S.sharedSplitNeeded && P.S.masksAhead &&
      tieB P.codes P.S.fold.u && tieB P.codes P.S.omega && tieB P.codes P.S.sharedSplit

theorem facts_of_B {P : P14} (h : factsB P = true) : ∃ sentU layU layO, Facts P sentU layU layO := by
  unfold factsB at h
  split at h
  · cases h
  · rename_i sentU hU
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h
    obtain ⟨layU, hlU⟩ := Option.isSome_iff_exists.1 a3
    obtain ⟨layO, hlO⟩ := Option.isSome_iff_exists.1 a4
    exact ⟨sentU, layU, layO, hU, a1, a2, hlU, hlO, a5, a6, tie_of_B a7, tie_of_B a8, tie_of_B a9⟩

/-- The plan's parameters of the kind at three public files. -/
def p14At (pol lay KL : ByteArray) : Option P14 :=
  match Verify.planned pol KL (some lay) with
  | .ok p => some (p14Of p.chains [])
  | .error _ => none

def atFiles (pol lay KL : ByteArray) : Bool := (p14At pol lay KL).any factsB

/-- For the print: the three shapes' rows and codes, and the two layouts' numbers of trees. -/
def look (pol lay KL : ByteArray) : Option (List (Nat × Nat × Nat × Nat × Nat) × Nat × Nat) :=
  (p14At pol lay KL).map fun P =>
    ([P.S.fold.u, P.S.omega, P.S.sharedSplit].map fun s =>
        (s.code, s.mainRows, s.maskRows, s.maskCode, s.answers),
      (((withU P.S).bind (layTrees P.codes)).map (·.shapes.size)).getD 0,
      ((layTrees P.codes (withOmega P.S)).map (·.shapes.size)).getD 0)

-- THE EVALUATIONS
#eval look VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL
#guard atFiles VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL
#guard atFiles VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.lay VerifierAndGoals.zGap.KL
open OnBytes.Model.Verify OnBytes.Params in
#eval look (TestRecordWork.policyOf TestRecordWork.smallHead) SmallFiles.layout
  SmallFiles.scales
open OnBytes.Model.Verify OnBytes.Params in
#guard atFiles (TestRecordWork.policyOf TestRecordWork.smallHead) SmallFiles.layout
  SmallFiles.scales
-- teeth, at the full size's plan: each turn of one number must make the test say no
#guard ((p14At VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL).any fun P =>
  !factsB { P with S := { P.S with masksAhead := false } } &&
  !factsB { P with S := { P.S with omega := { P.S.omega with answers := 2 } } } &&
  !factsB { P with S := { P.S with sharedSplit := { P.S.sharedSplit with maskCode := 999 } } } &&
  !factsB { P with S := { P.S with fold := { P.S.fold with u := { P.S.fold.u with code := 999 } } } } &&
  !factsB { P with codes := {} })

end Second.Seam

#print axioms Second.Seam.tie_of_B
#print axioms Second.Seam.facts_of_B
