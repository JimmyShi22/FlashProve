-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReaderReadsOwn.lean: FIVE SMALL LAWS THAT TIE LOOSE ENDS OF
THIS FOLDER's PREMISES' FORMS. THE FIRST: THE PREMISE hQ OF `readerReads_K5_T` (ReaderReadsK5.lean)
FOLLOWS FROM THE FRAME's FORM `OwnMsgs` (Honest/Thread/ScriptLots.lean) AND ONE SENTENCE ON THE
LOT's TEXT: SO hQ CAN BE HAD FROM A LOT. Statements with their proofs; no definition.

  `hQ_of_ownMsgs`         CONDITIONAL: M: `OwnMsgs` Q Vd N n fx txt; ht: under the same three guards
                          the text answers, in the mask table, row 0, at each place ν below ns, the
                          reading of rowOf (ownC k) ν ⊢ hQ's form at the message number n
  `val_any_list`          `cellsVals`' field val (Honest/K1/FirstData.lean) reads no challenge: rfl
  `msg_of_lays_all`       `msg_of_lays` (LaysFilling.lean) AT EVERY LIST hd', where that law ends in
                          "there is a list hd'"
  `msg_of_laysCells_all`  the like for `msg_of_laysCells` (LaysCells.lean)
  `msgNo5_eq_maskNo5`     `msgNo5` (CellsQRaw.lean) and `maskNo5` (ScriptQRaw.lean) are one: by rfl

Why. hQ is typed under the three guards of `OwnMsgs`: `hQ_of_ownMsgs` holds it against that form: a
lot of that form whose text answers as ht says gives it. The two laws on what a script's message
holds end in a list under "there is" that nothing names: since val reads no challenge, they hold at
every list. Two definitions have one body: the rfl says so.

Limits. Conditional: M and ht are proved of no Script and no lot. ht says what a lot's text answers
in the mask table: that is K5's tie between what the book lends and what the sender lays, which
nobody has. The two laws "at every list" have all the premises of the laws that they call. Nothing
here is evaluated. The head h is a hypothesis of every statement that names it.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysCells
import Johnson.Desc.ProofFile.Honest.K5.Law.ScriptQRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName nameNo_isSome nameNo_eq_some_iff matAt_eq_some_iff no?_lt
  parts_in_scope shape_owner owner_owner below_of_mu ref_ok arrayNo_isSome_iff)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (lookAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K1 (labelNo cellsVals firstData)
open P5J (AtMgA TS CellsM)

open OnBytes (E)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.First.Look (sigListCalls)

section
variable {Bk : ProverCoinCounts} {W Cells Tok : Type}

/-- **hQ FROM THE FRAME's FORM.** CONDITIONAL: M: the frame's form at the message number n; ht: what
the text answers, under the form's own three guards. -/
theorem hQ_of_ownMsgs {Q : Script Bk W Cells Tok MsgT} {Vd : W → Prop} {N n fx ns : ℕ}
    {txt : Coins Bk → W → List Fmt.Drawn → Bool → ℕ → ℕ → Option Cb.Gl.E}
    (M : OwnMsgs Q Vd N n fx txt) {d : Due} (rowOf : Cs d → ℕ → E) (ownC : Coins Bk → Cs d)
    (ht : ∀ k v (hd : List Fmt.Drawn) ν, Vd v → N ≤ hd.length → ν < ns →
      txt k v (hd.take fx) true 0 ν = some (Reading.gl.val (rowOf (ownC k) ν))) :
    ∀ k v (hd : List Fmt.Drawn) ν, Vd v → N ≤ hd.length → ν < ns →
      Q.msg n k v (hd.take (Q.fixedMsg n)) true 0 ν = Reading.gl.val (rowOf (ownC k) ν) :=
  fun k v hd ν hv hN hν => M k v hd hv hN true 0 ν _ (ht k v hd ν hv hN hν)

/-- **`cellsVals`' val READS NO CHALLENGE.** No premise. -/
theorem val_any_list (S : Sz) (R : Readers) (hd hd' : List Fmt.Drawn) (l : ℕ) (name : String)
    (i c : ℕ) : (cellsVals S).val R hd l name i c = (cellsVals S).val R hd' l name i c := rfl

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-- **THE TWO NUMBERS ARE ONE.** No premise. -/
theorem msgNo5_eq_maskNo5 (x₁ : VerifiableInference.Desc.First.Look.Place) (kk : ℕ)
    (hk : kk < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) :
    msgNo5 h x₁ kk hk = maskNo5 h x₁ kk hk := rfl

variable {h Q}

/-- **`msg_of_lays` AT EVERY LIST.** CONDITIONAL: as that law. -/
theorem msg_of_lays_all {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : MsgAddr → Option (ℕ × ℕ)}
    {heard : MsgAddr → ℕ} {l : ℕ} (L : LaysFilling h Q Vd N rd seat heard l) {n : String}
    {A : OnBytes.Params.ReqArray}
    (hA : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l n = some A) {i' c : ℕ} {p : ℕ × ℕ}
    (hp : VerifiableInference.Desc.laidAt A i' c = some p) {z : ℕ × ℕ}
    (hz : (cellsVals Sz.ref).size l A.name = some z) (hi : i' < z.1) (hc : c < z.2)
    (k : Coins Bk) {v : Local W₀ Rc ProofFile.Inst Tr} (hv : Vd v) {hd : List Fmt.Drawn}
    (hN : N ≤ hd.length) :
    ∀ hd' : List Fmt.Drawn,
      Q.msg (P5J.At.num Zp l A.message) k v (hd.take (Q.fixedMsg (P5J.At.num Zp l A.message))) false
          p.1 p.2 =
        asE (some ((cellsVals Sz.ref).val (rd v) hd' l A.name i' c)) := by
  intro hd'
  obtain ⟨hd₀, e⟩ := msg_of_lays L hA hp hz hi hc k hv hN
  rw [val_any_list Sz.ref (rd v) hd' hd₀]
  exact e

/-- **`msg_of_laysCells` AT EVERY LIST.** CONDITIONAL: as that law. -/
theorem msg_of_laysCells_all {S : Sz} (hSz : planesAtRef S = Sz.ref)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers} {seat : MsgAddr → Option (ℕ × ℕ)}
    {heard : MsgAddr → ℕ} {l : ℕ} (L : LaysCells h Q S Vd N rd seat heard l) {n : String}
    {A : OnBytes.Params.ReqArray}
    (hA : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout l n = some A)
    (hO : offPlanes l A.name = true) {mu : ℕ} {σ : Seg} {μ : MatName}
    (hn : labelNo A.name = some mu) (hM : Sz.ref.matAt l mu = some (σ, μ)) {i' c : ℕ} {p : ℕ × ℕ}
    (hp : VerifiableInference.Desc.laidAt A i' c = some p) {z : ℕ × ℕ}
    (hz : (cellsVals Sz.ref).size l A.name = some z) (hi : i' < z.1) (hc : c < z.2)
    (k : Coins Bk) {v : Local W₀ Rc ProofFile.Inst Tr} (hv : Vd v) {hd : List Fmt.Drawn}
    (hN : N ≤ hd.length) :
    ∀ hd' : List Fmt.Drawn,
      Q.msg (P5J.At.num Zp l A.message) k v (hd.take (Q.fixedMsg (P5J.At.num Zp l A.message))) false
          p.1 p.2 =
        asE (some ((cellsVals Sz.ref).val (rd v) hd' l A.name i' c)) := by
  intro hd'
  obtain ⟨hd₀, e⟩ := msg_of_laysCells hSz L hA hO hn hM hp hz hi hc k hv hN
  rw [val_any_list Sz.ref (rd v) hd' hd₀]
  exact e

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.hQ_of_ownMsgs
#print axioms ProofFile.Honest.K5.val_any_list
#print axioms ProofFile.Honest.K5.msgNo5_eq_maskNo5
#print axioms ProofFile.Honest.K5.msg_of_lays_all
#print axioms ProofFile.Honest.K5.msg_of_laysCells_all
