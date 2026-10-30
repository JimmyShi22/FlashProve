-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadB1.lean: helper B1 of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: THE SIX CALLS AND THEIR PADDING KEYS. A WORKING FILE.

Three statements, on public data alone, in the goals' scope:
  headCallsAreTheDefaultLines   the output head's layout has the six calls of the default list of lines, each placed by
                                the programs' own rule (OnBytes.Model.place) over its segments' names and lengths
  headLookupHasSixCalls         so the shape of the head's lookup has six calls
  paddingKeyIsTheTablesRow      at each of the six calls the output head's kind's padding key (padKey,
                                Johnson/Desc/Kinds/HeadIn.lean) is, AS A NATURAL NUMBER, the row of the call's table that the
                                library's key vector holds at a padding place (tauN at t0N, OnBytes/Tie/Pv/Lookup/Ends/Joint.lean)
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Goal.Meaning.HeadCallsScope
import Johnson.Goal.Meaning.HeadForInScope
import Johnson.Road.Ends.HeadBack
import Johnson.Road.Ends.HeadForIn
import Johnson.Road.Lane5AttTabsEq
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.HonestTrace.FullPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (place CallD ledNRH)
open OnBytes.Model.Head (Shape HL callsFrom lineSegs segments callsOf keyFloor)
open VerifiableInference.Desc.Kinds.Head (Sizes padKey)
open VerifiableInference.OnPublicFiles

/-- The six calls, as the programs' rule places them, at a shape and a layout's three lengths. -/
def defaultCallsOf (shape : Shape) (layout : HL) : List CallD :=
  [place "R16a" "R16" [("NF", shape.d, false), ("NFH", shape.d, false), ("HD0", layout.JV, false)]
      (keyFloor shape - shape.lt),
   place "R16b" "R16" [("HD1", layout.JV, false)] (keyFloor shape - shape.lt),
   place "R8" "R8" [("ROW", ledNRH shape.XL, false), ("HD2", layout.JV, false)]
      (keyFloor shape - shape.lt),
   place "FEa" "FE" [("HE0", layout.JVa, false)] (keyFloor shape - shape.lt),
   place "FEb" "FE" [("HE1", layout.JV - layout.JVa, false)] (keyFloor shape - shape.lt),
   place "FC" "FC" [("CNF", shape.d, false)] (keyFloor shape - shape.lt)]

/-- The programs' reading of the six default lines, at any shape and layout. -/
theorem callsFromTheDefaultLines (shape : Shape) (layout : HL) :
    callsFrom (segments shape layout) (keyFloor shape - shape.lt)
      [["R16a", "R16", "NF", "NFH", "HD0"], ["R16b", "R16", "HD1"], ["R8", "R8", "ROW", "HD2"],
       ["FEa", "FE", "HE0"], ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]] [] [] =
      some (defaultCallsOf shape layout,
        ["CNF", "HE1", "HE0", "HD2", "ROW", "HD1", "HD0", "NFH", "NF"]) := by
  simp [callsFrom, lineSegs, segments, defaultCallsOf]

section
variable {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
  {publicPart : OnBytes.Model.Verify.Public}

/-- **In scope the output head's calls are the six of the default lines.** -/
theorem headCallsAreTheDefaultLines (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart) :
    publicPart.HLy.calls = (defaultCallsOf publicPart.hS publicPart.HLy).toArray := by
  have core := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  obtain ⟨calls, made, -, areThese⟩ := (OnBytes.Road.Hd.admittedH_of_layout core.head).calls
  have lines := VerifiableInference.Desc.Kinds.Head.Law.InScope.lines_in_scope inScope filesRead
    publicPartMade
  unfold VerifierAndGoals.Lines.callsHRef at lines
  unfold callsOf at made
  rw [lines] at made
  obtain ⟨-, made⟩ := OnBytes.Road.Hd.ok_of_needed made
  dsimp only at made
  rw [callsFromTheDefaultLines] at made
  obtain ⟨-, made⟩ := OnBytes.Road.Hd.ok_of_needed made
  cases made
  exact areThese

/-- In scope the shape of the output head's lookup has six calls. -/
theorem headLookupHasSixCalls (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart) : publicPart.HLy.fs.NC = 6 := by
  have core := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  rw [OnBytes.Road.Hd.fsNC_of_layout core.head,
    headCallsAreTheDefaultLines inScope filesRead publicPartMade]
  rfl

/-- **At each of the six calls the kind's padding key is the table's row at the padding place.** -/
theorem paddingKeyIsTheTablesRow [sizes : Sizes] (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart) {call : Nat} (callIsThere : call < 6) :
    padKey call =
      OnBytes.Ends.tauN publicPart.HLy.fs call (OnBytes.Ends.t0N publicPart.HLy.fs call) := by
  subst sizesAreThePublicParts
  have core := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  have theCalls := headCallsAreTheDefaultLines inScope filesRead publicPartMade
  letI : Sizes := k3SizesAt publicPart
  let run : OnBytes.Model.Head.Run := OnBytes.HonestTrace.runAt publicPart
  have made : OnBytes.Model.Head.layout run.h OnBytes.Road.Hd.tauFCw = .ok run.L := by
    show OnBytes.Model.Head.layout publicPart.hS OnBytes.Road.Hd.tauFCw = .ok publicPart.HLy
    rw [← OnBytes.Road.Hd.tauFC_of_layout core.lay]
    exact core.head
  have exponent : publicPart.hS.famF = 24 := Meaning.HeadS.famF_in_scope inScope filesRead publicPartMade
  have size : run.L.calls.size = 6 := by
    show publicPart.HLy.calls.size = 6
    rw [theCalls]
    rfl
  obtain ⟨record, recordIsThere, isTheTable, -⟩ := OnBytes.Road.Hd.recAt_of_layout (R := run) made
    exponent core.sh core.sT (q := call) (by rw [size]; exact callIsThere)
  obtain ⟨n, word, value⟩ := isTheTable.pad
  have row : OnBytes.Ends.tauN publicPart.HLy.fs call (OnBytes.Ends.t0N publicPart.HLy.fs call) =
      (record.tauAt record.t0).toNat := by
    unfold OnBytes.Ends.tauN OnBytes.Ends.t0N
    rw [show publicPart.HLy.fs.calls[call]? = some record from recordIsThere]
    rfl
  have kind : OnBytes.Road.Hd.tabL run call =
      OnBytes.Road.Hd.lutOfKind ((defaultCallsOf publicPart.hS publicPart.HLy).toArray.getD call
        default).kind := by
    show OnBytes.Road.Hd.lutOfKind (publicPart.HLy.calls.getD call default).kind = _
    rw [theCalls]
  rw [kind] at value
  have exponent' : VerifiableInference.Desc.Kinds.Head.F = 24 := exponent
  rw [row, word]
  interval_cases call
  · rw [show (OnBytes.Road.Hd.lutOfKind _).pad = (0 : ℤ) from by
      show (OnBytes.Road.Hd.lutOfKind "R16").pad = 0
      rw [OnBytes.Road.Hd.lut_R16]; rfl] at value
    rw [OnBytes.Road.L5.toNat_fOfNat (by omega)]
    show 0 = n
    omega
  · rw [show (OnBytes.Road.Hd.lutOfKind _).pad = (0 : ℤ) from by
      show (OnBytes.Road.Hd.lutOfKind "R16").pad = 0
      rw [OnBytes.Road.Hd.lut_R16]; rfl] at value
    rw [OnBytes.Road.L5.toNat_fOfNat (by omega)]
    show 0 = n
    omega
  · rw [show (OnBytes.Road.Hd.lutOfKind _).pad = (0 : ℤ) from by
      show (OnBytes.Road.Hd.lutOfKind "R8").pad = 0
      rw [OnBytes.Road.Hd.lut_R8]; rfl] at value
    rw [OnBytes.Road.L5.toNat_fOfNat (by omega)]
    show 0 = n
    omega
  · rw [show (OnBytes.Road.Hd.lutOfKind _).pad = (2 ^ 40 : ℤ) from by
      show (OnBytes.Road.Hd.lutOfKind "FE").pad = 2 ^ 40
      rw [OnBytes.Road.Hd.lut_FE]; rfl] at value
    have n40 : n = 2 ^ 40 := by exact_mod_cast value
    rw [OnBytes.Road.L5.toNat_fOfNat (by rw [n40]; norm_num), n40]
    show 2 ^ (16 + VerifiableInference.Desc.Kinds.Head.F) = 2 ^ 40
    rw [exponent']
  · rw [show (OnBytes.Road.Hd.lutOfKind _).pad = (2 ^ 40 : ℤ) from by
      show (OnBytes.Road.Hd.lutOfKind "FE").pad = 2 ^ 40
      rw [OnBytes.Road.Hd.lut_FE]; rfl] at value
    have n40 : n = 2 ^ 40 := by exact_mod_cast value
    rw [OnBytes.Road.L5.toNat_fOfNat (by rw [n40]; norm_num), n40]
    show 2 ^ (16 + VerifiableInference.Desc.Kinds.Head.F) = 2 ^ 40
    rw [exponent']
  · rw [show (OnBytes.Road.Hd.lutOfKind _).pad = (2 ^ 15 + 2 ^ 39 : ℤ) from by
      show (OnBytes.Road.Hd.lutOfKind "FC").pad = 2 ^ 15 + 2 ^ 39
      rw [OnBytes.Road.Hd.lut_FC]; rfl] at value
    have nFC : n = 2 ^ 15 + 2 ^ 39 := by exact_mod_cast value
    rw [OnBytes.Road.L5.toNat_fOfNat (by rw [nFC]; norm_num), nFC]
    rfl

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.callsFromTheDefaultLines
#print axioms ProofFile.Honest.K3.Term.headCallsAreTheDefaultLines
#print axioms ProofFile.Honest.K3.Term.headLookupHasSixCalls
#print axioms ProofFile.Honest.K3.Term.paddingKeyIsTheTablesRow
