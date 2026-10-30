-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieShare.lean: THE SHARE OF THE THREADS' ExchangeS AT THE ITEM
"tie m" OF THE TABLE OF JOINTS (K8.TieOf, Johnson/Desc/First/K8/LawItems.lean, at the thread's own
witness), OWED BEHIND A SEGMENT's READS. Three definitions of premises' forms, one statement and its
proof.

  TieStateS        PUBLIC: from the pair and the member's own step: the state behind holds a record
                   tl of the smallness test; its list of matrices has the sizes' shapes; its tables
                   end at or below nR and no entry lies in two of them
  TieRowsS         A PREMISE ON THE HONEST SIDE's WITNESS: see its docstring
  TieSeated        the two in one record, with the equation on the threads' letter "tie", the
                   premise on valid inputs, and A FIELD THAT TIES THE MEMBER's NUMBER b TO THE
                   SEGMENT m
  exchangeAtS_tie  THE SHARE. It takes its premises bare: it is built on no record

THE ROAD. The static half: tieOf_of_reads
(Johnson/HonestTrace/PackedJoins.lean) and tieThird_sent (Johnson/HonestTrace/ReadsTie.lean); the
bound on the integers comes out of MeetsAll. p := parOfMats tl.mats, so ParFits is a theorem
(parFits_parOfMats, Johnson/HonestTrace/Reads.lean). nR, the segment's number of reads, is A LETTER
OF BOTH FORMS: neither p nor n stands under "there is". TablesLie's first clause forces nR to be at
least every table's end: at nR = 0 it holds only where no table has an entry. nR is meant at the
segment's own number of reads; TieStateS is closed upwards in it. ARGUED, TYPED NOWHERE: every p
that fits reads alike (readAt reads of p what ParFits pins); beyond the tables' end both sides of
TieRowsS' second equation are 0.

WHO HAS MET WHAT. TieStateS: s'.tl? and its tables come from the member's own accept by sealed
lemmas (lay_at_reads, att_at_reads: Johnson/Desc/K1/Law/ArmStep.lean; tablesCome_at_reads:
Johnson/Desc/K1/Law/ArmHead.lean); ShapesFit: proved of no state; TablesLie: of the head's and a
group's tables (tablesLie_head: Johnson/HonestTrace/ReadsHead.lean; tablesLie_hear:
Johnson/HonestTrace/ReadsLayers.lean), of an attention segment's by nobody. TieRowsS:
NOBODY. ONE JOIN CAN MAKE IT FALSE: the list tl.funs in the verifier's state against the list that
the filler of "U3" makes of the challenges heard: if these parted, the second equation would fail at
most draws. The premise on valid inputs: the threads' letter valid has no text yet.

Limits. NO MEMBER OF ANY OF THE THREE IS GIVEN, AND NO NEGATIVE TEST. NOTHING IS TO BE BUILT ON
exchangeAtS_tie BEFORE TieRowsS HAS BOTH. The three are definitions: nothing is claimed of them, and
no goal file names them. At a state whose list of tables is empty the tie's third clause holds of
every table. This file stands over files that are in no seal
(PackedJoins, PackedTable, PackedTie, Reads, ReadsTie; the threads'). Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.HonestTrace.PackedJoins
import Johnson.HonestTrace.ReadsTie
import Johnson.Desc.Sound.CellsAt
import Johnson.Desc.First.K8.TieAtSegment
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S ModelPart Item shift)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Sz Tr NamesFit MeetsAll ShapesFit TablesLie parOfMats parFits_parOfMats
  packedCells cellOf cellsC matsOf tieOf_of_reads tieThird_sent)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **PUBLIC: the state behind.** From the pair and the member's own step: the smallness test's
record is there, with the static premises of the laws. A definition: a
premise's form. -/
def TieStateS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (b m nR : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∃ tl, s'.tl? = some tl ∧ ShapesFit tl Sz.ref m ∧ TablesLie tl.mats tl.funs nR

/-- **A HIDDEN PREMISE ON THE HONEST SIDE's WITNESS. MET BY NOBODY. NO MEMBER, NO TOOTH.** It says
what the witness holds at main rows' cells off the pads; nothing on what is sent or shown.
At every run's coins k, every stand and
every continuation ds' of the challenges: read through the library's table of cells cellsAt, the
thread's own witness holds, at the matrices' arrays, the packed cells of the input's trace, and in
row 0 of the array of reads the vector of reads at the state's own tables. A definition: a premise's
form. -/
def TieRowsS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (X : OnBytes.Model.Verify.Public)
    (T : Local W₀ Rc Xi Tr' → Tr) (b m nR : ℕ) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ tl, s'.tl? = some tl → ∀ ds', ∀ A, A = cellsAt cs arr ms L.N m (L.pubOf μ.st.input.x, s')
        (L.Q.wit k μ.st.input (μ.st.heard ++ (ds ++ ds'))) →
      (∀ ν, ν < tl.NM → ∀ c, c < (Sz.ref.packedShape m ν).2 →
        ∀ i', i' < (Sz.ref.packedShape m ν).1 → A (tl.gtTree.getD ν 0) i' c =
          algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (cellOf X (T μ.st.input)) m ν i' c)) ∧
      (∀ j < nR, A (u3Of tl) 0 j =
        OnBytes.Model.Reading.gl.val (First.K8.Honest.readAt (parOfMats tl.mats) tl.funs.toList
          (cellsAtOf (cellsC X (T μ.st.input)) (matsOf X m)) j))

/-- **The share's premises in one record**, at the member number b, the reads of segment m. place:
THE FIELD THAT TIES b TO m. A definition: a premise's form. -/
structure TieSeated (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (cs : OnBytes.Codes)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (X : OnBytes.Model.Verify.Public)
    (T : Local W₀ Rc Xi Tr' → Tr) (b m nR : ℕ) : Prop where
  place : ∃ sub, L.links[m]? = some sub ∧
    L.ps[b]? = some { chain := 1, link := some m, piece := 4 + shift sub, kind := .K1 }
  tieM : ∀ w, (L.Mg w).tie = First.K8.tieK8Rec (cellsAt cs arr ms L.N)
  valid : ∀ w, L.valid w → NamesFit X (T w) ∧ ∃ i x, MeetsAll X i x (T w)
  state : TieStateS L Said b m nR
  rows : TieRowsS L Said cs arr ms X T b m nR

/-- **THE SHARE**: ExchangeAtS at the item tie m, at the member number b. Its premises are taken
bare. NOTHING IS TO BE BUILT ON IT BEFORE TieRowsS HAS A MEMBER AND A NEGATIVE TEST. -/
theorem exchangeAtS_tie {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {X : OnBytes.Model.Verify.Public}
    {T : Local W₀ Rc Xi Tr' → Tr} {b m nR : ℕ} (hm : m < 25)
    (hM : ∀ w, (L.Mg w).tie = First.K8.tieK8Rec (cellsAt cs arr ms L.N))
    (hV : ∀ w, L.valid w → NamesFit X (T w) ∧ ∃ i x, MeetsAll X i x (T w))
    (hSt : TieStateS L Said b m nR) (hR : TieRowsS L Said cs arr ms X T b m nR) :
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
  obtain ⟨tl, htl, hSh, hLie⟩ := hSt blk hblk k s μ E ds y cols s' hA hd hS
  obtain ⟨hAeq, hSeq⟩ := hR blk hblk k s μ E ds y cols s' hA hd hS tl htl ds' _ rfl
  obtain ⟨hN, i₀, x₀, hMe⟩ := hV μ.st.input hval
  show (L.Mg y.2.st.input).tie m (L.pubOf y.2.st.input.x, s') (L.thread.strs (E.add y.1))
    (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [ei, eh, List.append_assoc, hM]
  exact ⟨tl, htl, tieOf_of_reads hN hMe hm hSh _ hAeq
    (tieThird_sent (parFits_parOfMats tl.mats) hLie hSeq)⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.TieStateS
#print axioms ProofFile.Honest.K1.TieRowsS
#print axioms ProofFile.Honest.K1.TieSeated
#print axioms ProofFile.Honest.K1.exchangeAtS_tie
