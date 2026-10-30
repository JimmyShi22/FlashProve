-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean: THE SHARED
"SENDING" (the kind K1): ITS SHARE OF THE THREADS' ExchangeS AT THE ITEM "tie m", AT THE PLAN's OWN
RECORD, AT ANY SIZES, AT THE READER's OWN CELLS. Two definitions of premise's forms, one statement
and its proof.

  TieStateP   TieStateS (Johnson/Desc/ProofFile/Honest/K1/Law/TieShare.lean) WITH ONE SWAP: a letter
              Sz₀ for Sz.ref; AND ONE CONJUNCT MORE: tl.NM ≤ tl.gtTree.size. Public
  TiePlanS    TieRowsS (the same file) WITH THREE SWAPS: Sz₀ for Sz.ref · the thread's reader's own
              cells (wit μ.st.input).R.cells for cellOf X (T μ.st.input) and cellsC X (T μ.st.input)
              · a list mats for matsOf X m. The left sides, the binders of the run and the witness's
              term: not a sign. A HIDDEN PREMISE ON THE HONEST SIDE's WITNESS. MET AT MADE-UP
              LETTERS ALONE
  exchangeAtS_tie_plan   ExchangeAtS L.thread Said b (.tie m), from: hM (the letters' meaning of
              "tie" is the library's, at the table of cells cellsAt) · hmats (public: the list
              names, at each number, what Sz₀'s own list of segment m names there, under m's own
              number) · hSmall (at a valid input the balanced integers of the reader's cells are at
              most 128 in absolute value: IT NAMES THE INPUT) · TieStateP · TiePlanS

AGAINST exchangeAtS_tie: NO public record X, NO trace T, NO NamesFit | MeetsAll (and so no index
under "there is"), NO m < 25. WHAT IS LOST: the sentence on the integer model's trace.

THE FENCE AROUND exchangeAtS_tie_plan, WHICH NO FILE OF THIS LIBRARY CALLS. ONE TERM ON WHATEVER
IS BUILT ON IT: the conjunct on gtTree in TieStateP, or the lack told in both forms' docstrings.
WHAT STAYS SHUT, OF THIS LAW: anything at the letters under the head · (P1) on hSmall.
THE WIDE LAW IS CALLED AT THESE LETTERS, through exchangeAtS_tie_served:
exchangeAtS_tie_base (AtFullSide/K1/TieAtBase.lean), under the head and a returned prover, where
hSt, hF1, hF2, hI and hV are premises.

A RIDER ON hSmall: hSmall is a premise of completeness's kind. What pays it comes from the trace
(hSmall_of_served, TieDebtsAtServed.lean: from hTr and hMA); a premise laid anew pays nothing.
EVERY PREMISE OF exchangeAtS_tie_plan IS ASKED AND NONE IS PROVED HERE.

BY CALLS: tieOf_plan (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlan.lean) · cellsSmall_cells
(Johnson/Desc/ProofFile/Honest/K1/Law/CellsSmallAll.lean); the road is exchangeAtS_tie's own.

Limits. A law under "Stepped": it holds of nothing at a book that does not cover the part's count.
hmats BARS A BORROWED MATRIX. It says what the witness holds; nothing on what is sent. Nothing on
soundness, on completeness or on any other property. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShare
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlan
import Johnson.Desc.ProofFile.Honest.K1.Law.CellsSmallAll
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart Item shift)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Sz ShapesFit TablesLie parOfMats packedCells)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf signedOf)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **PUBLIC: the state behind, at sizes Sz₀.** TieStateS with a letter for Sz.ref, and one conjunct
more: the record's list gtTree has an entry for each of its NM matrices. WHY: the first family of
TiePlanS reads "tl.gtTree.getD ν 0" under ν < tl.NM: with this conjunct that getD never falls to its
default. A definition: a premise's form. -/
def TieStateP (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (Sz₀ : Sz) (b m nR : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∃ tl, s'.tl? = some tl ∧ ShapesFit tl Sz₀ m ∧ TablesLie tl.mats tl.funs nR ∧
      tl.NM ≤ tl.gtTree.size

/-- **A HIDDEN PREMISE ON THE HONEST SIDE's WITNESS. MET AT MADE-UP LETTERS ALONE.** It says
what the witness holds at main rows' cells off the pads; nothing on what is sent. TieRowsS with
three swaps: at every run's coins k, every stand and every continuation ds' of the challenges: read
through the library's table of cells cellsAt, the thread's own witness holds, at the matrices'
arrays, the packed cells, at the sizes Sz₀, of the input's reader's own cells, and in row 0 of the
array of reads the vector of reads at the state's own tables, at the balanced integers of these
cells. A definition: a premise's form. -/
def TiePlanS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Sz₀ : Sz) (wit : Local W₀ Rc Xi Tr' → PlaceIn Xi)
    (mats : List (ℕ × String × ℕ)) (b m nR : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl, s'.tl? = some tl → ∀ ds', ∀ A, A = cellsAt cs arr ms L.N m (L.pubOf μ.st.input.x, s')
        (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds'))) →
      (∀ ν, ν < tl.NM → ∀ c, c < (Sz₀.packedShape m ν).2 →
        ∀ i', i' < (Sz₀.packedShape m ν).1 → A (tl.gtTree.getD ν 0) i' c =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz₀ (wit μ.st.input).R.cells.cell m ν i' c)) ∧
      (∀ j < nR, A (u3Of tl) 0 j =
        OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf (wit μ.st.input).R.cells mats) j))

/-- **THE SHARE AT THE PLAN's OWN RECORD**: ExchangeAtS at the item tie m,
at the member number b. What stays shut: the file's head. The proof does not spend
TieStateP's last conjunct: by it the law's premise is stronger, the law weaker, by one public
sentence. hSmall is a premise of completeness's kind. What pays it comes from the trace
(hSmall_of_served, TieDebtsAtServed.lean: from hTr and hMA); a premise laid anew pays nothing. -/
theorem exchangeAtS_tie_plan {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Sz₀ : Sz} {wit : Local W₀ Rc Xi Tr' → PlaceIn Xi}
    {mats : List (ℕ × String × ℕ)} {b m nR : ℕ}
    (hM : ∀ w, (L.Mg w).tie = First.K8.tieK8Rec (cellsAt cs arr ms L.N))
    (hmats : ∀ mu σ μ, Sz₀.matAt m mu = some (σ, μ) → mats[mu]? = some (m, μ.label, 0))
    (hSmall : ∀ w, L.valid w →
      ∀ k s r c, (signedOf ((wit w).R.cells.cell k s r c)).natAbs ≤ 128)
    (hSt : TieStateP L Said Sz₀ b m nR) (hR : TiePlanS L Said cs arr ms Sz₀ wit mats b m nR) :
    ExchangeAtS L.thread Said b (.tie m) := by
  intro blk hblk k s μ E ds y cols s' hA hd hS ds' i hi'
  obtain rfl := List.mem_singleton.1 hi'
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, -, hval⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  obtain ⟨tl, htl, hSh, hLie, -⟩ := hSt blk hblk k s μ E ds y cols s' hA hd hS
  obtain ⟨hAeq, hSeq⟩ := hR blk hblk k s μ E ds y cols s' hA hd hS tl htl ds' _ rfl
  show (L.Mg y.2.st.input).tie m (L.pubOf y.2.st.input.x, s') (L.thread.strs (E.add y.1))
    (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [ei, eh, List.append_assoc, hM]
  exact ⟨tl, htl, tieOf_plan hSh (wit μ.st.input).R.cells mats hmats
    (cellsSmall_cells _ _ _ (hSmall μ.st.input hval)) hLie _ hAeq hSeq⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.TieStateP
#print axioms ProofFile.Honest.K1.TiePlanS
#print axioms ProofFile.Honest.K1.exchangeAtS_tie_plan
