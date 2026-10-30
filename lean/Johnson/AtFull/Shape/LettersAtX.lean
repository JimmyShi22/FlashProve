-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LettersAtX.lean: UNDER THE HEAD P5J.AtMgA, AT AN OPENING: THE 20 LETTERS THAT
THE TABLE's CELLS READ OF Zp AND Bs.G₀ (lettersOf, TabLetters.lean) ARE ALIKE TO ONE RECORD LW X OF
TERMS IN THE PUBLIC RECORD X := Zp.p.X AND OF WRITTEN VALUES, each in a form that is light to
evaluate. So the run on shapes over the table's own steps is the run of the table's second text at
LW X. A joining of laws; nothing is evaluated here.

What it is for. "The run on shapes returns" at given public files is to be shown by Lean's kernel in
lines of the form atXL (fun X => (shapeL (LW X)).yes a n) = true (AtX.lean). With the letters as the
library's own readers make them such lines ran out of memory; with these they did not, as far as
they have been tried (scratch sheets; no theorem).

  gOf X: a carrier ground: the built records off X (builtOfX, BuiltLinksPlain.lean), the library's
    placeholder for the first chain's parameters (qFull, Johnson/Desc/K1/Law/QFull.lean: the fields
    that no place of the kind K1 reads are empty), X, and a stand-in for the covered positions,
    which none of the letters reads (spent_at_head, LettersSpentAtHead.lean, holds at every such
    ground).
  lookOf X l d: the lookups' letter: at the calls of a layers' link the layout's own record X.y.fo
    (look_layers_at_head); else the place's shape by shapeFree, which runs no test on a table
    (look_free_at_head, LookFreeAtHead.lean).
  **LW X**: the record. The written half: 0; K1's makers at qFull; the written shape of the test on
    the table; k9, close and where13 in numerals (WrittenLiterals.lean); wParW; piLFull. k8 over the
    written table of messages (K8MsgsWritten.lean); k11 at 76. K4's two letters (its two guards that
    read no shape; its hearing on shapes) stand as the library's own terms over X.
  **writtenHalf_LW**: WrittenHalf (LW X), at every X.
  **lw_alike**: the head, an opening ⊢ LettersAlike (lettersOf Zp Bs.G₀) (LW Zp.p.X).
  **shape_at_LW**, **yes_at_LW**: so the two Shapes are equal, and the one Bool is the other.

Limits. IMPLICATIONS UNDER THE HEAD. That the head has a member is shown in scope, where the reader
returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold
together, at two named sets of public files, in a side library. LW X IS NO TEST ON X: lookOf leaves
out the tests on the calls' tables and on the padding, and takes X.y.fo untested; the written half
is the full size's whatever X is: so the run at LW X may return where the table's first text would
refuse; it is the table's run under lw_alike's premises alone. Nothing says that a step returns.
k2n, nums, hpL, k11's other fields and K4's two letters stand as the readers' own terms over X: that
they are light is not said; K4's two were heavy where they were tried (scratch sheets). The full
size alone. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LettersRun
import Johnson.AtFull.Shape.LookFreeAtHead
import Johnson.AtFull.Shape.K8MsgsWritten
import Johnson.AtFull.Shape.BuiltLinksPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K1 (parLater firstPar qFull linkNumbers)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (codesFull2)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc.Lots (esW)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- The carrier ground. -/
def gOf (X : Verify.Public) : ProofFile.Ground := ⟨builtOfX X, qFull, X, default⟩

/-- The lookups' letter off X. -/
def lookOf (X : Verify.Public) (l : Nat) (d : Bool) : Option (Forest.Shape × Nat) :=
  if !d && l % 2 == 0 && decide (l < 24) then (placeAt X l false).map fun p => (X.y.fo, p.first)
  else (placeAt X l d).bind fun p =>
    (shapeFree p.calls p.lid).map fun h0 => ({ h0 with pub := p.pub }, p.first)

/-- **THE RECORD OF LETTERS OFF THE PUBLIC RECORD AND WRITTEN VALUES.** -/
def LW (X : Verify.Public) : TabLetters where
  XZ := X
  XG := X
  links := linksOfX X
  nums := fun l => ((gOf X).built[l]?).bind (linkNumbers (gOf X))
  hpL := P1K2.pureLetters (gOf X)
  k8 := fun l => ((gOf X).built[l]?).map fun Xl => k8ParWC (msgsAt msgsW) (gOf X) Xl l
  k2n := fun a => (P1K2.prepareAt proofSizedFull X qFull codesFull2 proofSizedFull.request
    proofSizedFull.request.answers).bind fun P => P1K2.numsAt P a
  look := lookOf X
  k4pub := k4pubX X
  k4own := k4ownX X
  k11 := parAtC 76 (gOf X)
  ft := 0
  k1 := parLater qFull gpW
  k1First := firstPar qFull gpW
  lin := proofSizedFull.batch.shape
  k9 := fun l => some (k9L l)
  close := fun l => some (closeL l)
  wP := wParW
  where13 := where13L
  p12 := H2K.Member.piLFull

/-- **Its written half holds the written values.** -/
theorem writtenHalf_LW (X : Verify.Public) : WrittenHalf (LW X) where
  ft := rfl
  k1 := fun _ _ _ _ => rfl
  k1First := rfl
  lin := rfl
  k9 := fun l hl => (k9_lit l hl).symm
  close := fun l hl => (close_lit l hl).symm
  wP := fun _ => rfl
  where13 := where13_lit.symm
  p12 := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The lookups' letter under the head. -/
theorem look_at_LW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (l : Nat)
    (hl : l < 25) (d : Bool) : (lettersOf Zp G).look l d = lookOf Zp.p.X l d := by
  unfold lookOf
  split
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨rfl, he⟩, h24⟩ := hc
    exact look_layers_at_head h G l h24 he
  · exact look_free_at_head h G l hl d

/-- **UNDER THE HEAD, AT AN OPENING: THE TABLE's LETTERS ARE ALIKE TO LW AT THE PUBLIC RECORD.** -/
theorem lw_alike (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B) :
    LettersAlike (lettersOf Zp Bs.G₀) (LW Zp.p.X) := by
  obtain ⟨s1, s2, s3, s4, -, s6⟩ := spent_at_head h O (G' := gOf Zp.p.X)
    (ground_eq h.laid.pub O.blank).1 rfl
  refine alike_at_head h O (writtenHalf_LW _) rfl rfl (built_links_eq h.laid.pub)
    (fun l _ => s1 l) (fun l _ _ => s2 l) (fun l _ => ?_) (fun l _ _ => s4 (some l)) (s4 none)
    (fun l hl d => look_at_LW h _ l hl d) (fun _ => rfl) (fun _ => rfl) ?_
  · rw [s3 l, show (fun Xl => k8ParWC (k8MsgsC cutWritten esW) (gOf Zp.p.X) Xl l) =
      fun Xl => k8ParWC (msgsAt msgsW) (gOf Zp.p.X) Xl l from
      funext fun Xl => k8ParWC_lit _ Xl l]
    rfl
  · rw [s6, sent_H8]
    rfl

/-- **So the two Shapes are equal.** -/
theorem shape_at_LW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B) :
    firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀) = shapeL (LW Zp.p.X) :=
  shape_of_alike (lw_alike h O)

/-- **And "the run on shapes returns" at the table is that of the second text at LW.** -/
theorem yes_at_LW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B) (a : ShA) (n : Nat) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a n = (shapeL (LW Zp.p.X)).yes a n :=
  yes_of_alike (lw_alike h O) a n

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.writtenHalf_LW
#print axioms Johnson.AtFull.Shape.look_at_LW
#print axioms Johnson.AtFull.Shape.lw_alike
#print axioms Johnson.AtFull.Shape.shape_at_LW
#print axioms Johnson.AtFull.Shape.yes_at_LW
#print axioms Johnson.AtFull.Shape.gOf
#print axioms Johnson.AtFull.Shape.lookOf
#print axioms Johnson.AtFull.Shape.LW
