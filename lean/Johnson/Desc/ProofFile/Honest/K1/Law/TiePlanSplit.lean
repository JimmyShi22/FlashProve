-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanSplit.lean: THE PREMISE's FORM
TiePlanS (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) CUT INTO ITS TWO FAMILIES. Two
definitions of premise's forms, one statement and its proof. TiePlanS and the laws over it are not
turned.

  TieMatS        (F1) alone: the witness's symbol arrays against the packed cells
  TieReadsS      (F2) alone: the vector of reads against the readings
  tiePlanS_iff   TiePlanS ... ↔ TieMatS ... ∧ TieReadsS ...

WHY THE CUT. The share at the item "tie l" is owed at each of the 25 segments. The array of reads
"U3" of segment l lies in a message of the segment's moment 1: the reads' own sending, a member of
the kind K1: so (F2) can be paid under the kind's record at that member, at every segment. The
matrices' own symbol arrays "M mu" of segment l lie in messages of the segment's moment 0: at l = 0
these are the opening's, a member of the kind K1; from l = 1 on they are sent where the code switch
(the kind K2) hands its sending to K1's text (Johnson/Desc/K1/Law/SitsSwitch.lean): no member of the
kind K1: so (F1) hangs there on another kind's record. The cut draws that border in Lean.

Both are HIDDEN PREMISES ON THE HONEST SIDE's WITNESS, as TiePlanS is: they name the Script's
witness L.Q.wit. What stands of TiePlanS and the law over it (TiePlanShare.lean's head)
holds of these two as of their conjunction. Neither is public:
each names the Script's witness and the input's cells:
a hidden premise of completeness's kind:
NOT IN FRONT OF A LAW OVER COINS.

Limits. Definitions and an equivalence by unfolding: nothing is paid. Nothing on what is sent.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Sz parOfMats packedCells)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf signedOf)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **A HIDDEN PREMISE ON THE HONEST SIDE's WITNESS: THE FIRST FAMILY OF TiePlanS, ALONE**: under
TiePlanS' own binders, to the sign: read through the library's table of cells cellsAt, the thread's
own witness holds, at the matrices' arrays, the packed cells, at the sizes Sz₀, of the input's
reader's own cells. It names no list of matrices and no number of reads. OF COMPLETENESS's KIND:
NOT IN FRONT OF A LAW OVER COINS. A definition: a premise's form. -/
def TieMatS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Sz₀ : Sz) (wit : Local W₀ Rc Xi Tr' → PlaceIn Xi)
    (b m : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl, s'.tl? = some tl → ∀ ds', ∀ A, A = cellsAt cs arr ms L.N m (L.pubOf μ.st.input.x, s')
        (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds'))) →
      ∀ ν, ν < tl.NM → ∀ c, c < (Sz₀.packedShape m ν).2 →
        ∀ i', i' < (Sz₀.packedShape m ν).1 → A (tl.gtTree.getD ν 0) i' c =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz₀ (wit μ.st.input).R.cells.cell m ν i' c)

/-- **A HIDDEN PREMISE ON THE HONEST SIDE's WITNESS: THE SECOND FAMILY OF TiePlanS, ALONE**: under
the same binders: in row 0 of the array of reads the witness holds the vector of reads at the
state's own tables, at the balanced integers of the reader's cells, read through the list mats. It
names no sizes. OF COMPLETENESS's KIND: NOT IN FRONT OF A LAW OVER COINS. A definition: a
premise's form. -/
def TieReadsS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (wit : Local W₀ Rc Xi Tr' → PlaceIn Xi)
    (mats : List (ℕ × String × ℕ)) (b m nR : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl, s'.tl? = some tl → ∀ ds', ∀ A, A = cellsAt cs arr ms L.N m (L.pubOf μ.st.input.x, s')
        (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds'))) →
      ∀ j < nR, A (u3Of tl) 0 j =
        OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf (wit μ.st.input).R.cells mats) j)

/-- **TiePlanS IS ITS TWO FAMILIES.** -/
theorem tiePlanS_iff {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Sz₀ : Sz} {wit : Local W₀ Rc Xi Tr' → PlaceIn Xi}
    {mats : List (ℕ × String × ℕ)} {b m nR : ℕ} :
    TiePlanS L Said cs arr ms Sz₀ wit mats b m nR ↔
      TieMatS L Said cs arr ms Sz₀ wit b m ∧ TieReadsS L Said cs arr ms wit mats b m nR :=
  ⟨fun H => ⟨fun blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe =>
      (H blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe).1,
    fun blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe =>
      (H blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe).2⟩,
   fun H blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe =>
    ⟨H.1 blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe,
      H.2 blk hb k s μ E ds y cols s' hA hd hS tl htl ds' A hAe⟩⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.TieMatS
#print axioms ProofFile.Honest.K1.TieReadsS
#print axioms ProofFile.Honest.K1.tiePlanS_iff
