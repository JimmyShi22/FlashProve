-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormsReadsPublic.lean: THE KIND K1's SHARES AT THE ITEMS "forms
m piece run", AT THE 25 READS' MEMBERS, AT ProofFile's lettersHead: THE PUBLIC PREMISES OF
exchangeAtS_forms (Honest/K1/Law/FormsShare.lean) THAT WANT NO OTHER HOUSE's FILE. Twelve theorems;
no definition.

THIS LETTER IS FOR THE HONEST RUN's OWN FORMS ALONE: NO STATEMENT ON ANY OTHER PARTY MAY TAKE IT.
(The sentence in FormsShare.lean: it binds what stands at these letters.
The reviewers' other fence, "never on soundness's road", is for laws at L.mgP, the meaning adapted
to the honest side: this file takes L.Mg, the items' meaning at the library's own letters, alone.)

At every sort of segment, by the table's own text (segRow, Johnson/Desc/First/Borders.lean):
  - readsRow_ins, readsRow_outs   the reads' row (piece 4 + shift sub): what it closes: formsT at
                  the runs of earlyRuns sub; what it opens: a pin, a sample row, the tie, and forms
                  at the same runs.
  - forms_out_iff THE PREMISE ho IS "(j, n) ∈ earlyRuns sub".
  - formsT_in_of  and then formsT m j n is among what the row closes.
  - forms_out_no  A NEGATIVE TEST: at a layers' segment "weights" is no run of the row.
At the full size's two written lists (P5J.At.links, P5J.At.ps: lettersHead's links and ps by rfl):
  - links_reads   THE PREMISE hsub: the sort at l is IM.subAt l: the sealed fullLinks_sub.
  - place_reads   ReadsSeated's field place: the place at number K1.noL l false: the sealed
                  place_fifty, with the piece written as 4 + shift (subAt l).
  - row_reads     the thread's forward row there is FwdRow.of of the table's row.
  - formsT_shut, forms_owed   so, at (j, n) ∈ earlyRuns (subAt l): the row shuts formsT l j n and
                  owes forms l j n. WITH A TEST fwdFit AT THESE LISTS  THE FIRST
                  GIVES THE PREMISE hi: NOT HERE.
Under h (the library's head: A HYPOTHESIS), at lettersHead:
  - formsAreLibrarys_head   THE PREMISE FormsAreLibrarys, AT THE LIBRARY's OWN LETTERS OF ITS TWO
                  SENTENCES ON FORMS: h.𝔇's: by unfolding, and the sealed statedIs_of. SO THE LETTER
                  wt, WHICH NO FIELD TIES, IS THE LIBRARY's OWN h.𝔇.wt BY THE CHOICE.
  - formsReader_head   ReadsSeated's THREE EQUATIONS (codes · numbers · members) at these letters
                  and the reads' own plan, and arr: THE FORMS READ THE WITNESS WHERE THE PINS READ
                  IT.

Limits. hi, ReadsStepS, WtFwdS, ArmBehindTieS AND THE SHARE AT "tie m" ARE NOT TOUCHED: NO SHARE IS
HAD HERE. THE FULL SIZE ALONE, from links_reads on. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormsShare
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtHead
import Johnson.LPFK9R.SitsAtConstant
import Johnson.Desc.K1.Law.CallsE
import Johnson.Desc.Sound.StatedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place)
open VerifiableInference.Desc.First (ModelPart Item segRow shift earlyRuns)
open VerifiableInference.Desc.Sound (MsgT uBySort statedIs_of)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- What the reads' row closes. -/
theorem readsRow_ins (sub : ModelPart) (m : ℕ) : (segRow sub m (4 + shift sub)).ins =
    (earlyRuns sub).map fun x => Item.formsT m x.1 x.2 := by
  cases sub <;> rfl

/-- What the reads' row opens. -/
theorem readsRow_outs (sub : ModelPart) (m : ℕ) : (segRow sub m (4 + shift sub)).outs =
    Item.pin m 1 :: Item.row m (.sample 1) :: Item.tie m ::
      (earlyRuns sub).map fun x => Item.forms m x.1 x.2 := by
  cases sub <;> rfl

/-- **THE PREMISE ho, READ OUT.** -/
theorem forms_out_iff (sub : ModelPart) (m j : ℕ) (n : String) :
    Item.forms m j n ∈ (segRow sub m (4 + shift sub)).outs ↔ (j, n) ∈ earlyRuns sub := by
  rw [readsRow_outs]
  constructor
  · intro h
    simp only [List.mem_cons, List.mem_map, reduceCtorEq, false_or, Item.forms.injEq] at h
    obtain ⟨x, hx, -, rfl, rfl⟩ := h
    exact hx
  · intro h
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.2 ⟨(j, n), h, rfl⟩)))

/-- At a run of the row, formsT is among what the row closes. -/
theorem formsT_in_of {sub : ModelPart} {j : ℕ} {n : String} (h : (j, n) ∈ earlyRuns sub) (m : ℕ) :
    Item.formsT m j n ∈ (segRow sub m (4 + shift sub)).ins := by
  rw [readsRow_ins]
  exact List.mem_map.2 ⟨(j, n), h, rfl⟩

/-- A negative test: at a layers' segment "weights" is no run of the row. -/
theorem forms_out_no : Item.forms 0 3 "weights" ∉ (segRow .layers 0 (4 + shift .layers)).outs := by
  decide

/-- **THE PREMISE hsub** at the written list. -/
theorem links_reads {l : ℕ} (hl : l < 25) : P5J.At.links[l]? = some (IM.subAt l) :=
  LPFK9.fullLinks_sub l hl

/-- **ReadsSeated's FIELD place** at the written lists. -/
theorem place_reads {l : ℕ} (hl : l < 25) : P5J.At.ps[K1.noL l false]? =
    some { chain := 1, link := some l, piece := 4 + shift (IM.subAt l), kind := .K1 } := by
  have e : (4 + shift (IM.subAt l) : ℕ) = IM.k1Ix l false + 1 := by
    unfold IM.subAt
    by_cases h24 : l = 24
    · subst h24
      rfl
    · by_cases h2 : l % 2 = 0
      · simp [h24, h2, shift, IM.k1Ix]
      · simp [h24, h2, shift, IM.k1Ix]
  rw [e]
  exact K1.place_fifty l hl false

/-- The thread's forward row at the reads' number is the table's row. -/
theorem row_reads {l : ℕ} (hl : l < 25) :
    FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l false) =
      FwdRow.of (segRow (IM.subAt l) l (4 + shift (IM.subAt l))).ins
        (segRow (IM.subAt l) l (4 + shift (IM.subAt l))).outs
        (segRow (IM.subAt l) l (4 + shift (IM.subAt l))).ctx := by
  unfold FirstRows.rows
  rw [place_reads hl]
  show FirstRows.rowAt P5J.At.links
    { chain := 1, link := some l, piece := 4 + shift (IM.subAt l), kind := .K1 } = _
  unfold FirstRows.rowAt FirstRows.turn First.rowOf
  simp only [links_reads hl, Option.isNone_some, Bool.false_and, Bool.false_eq_true, if_false]

/-- At a run of the row the thread's row shuts formsT. -/
theorem formsT_shut {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (h : (j, n) ∈ earlyRuns (IM.subAt l)) :
    Item.formsT l j n ∈ (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l false)).shuts := by
  rw [row_reads hl]
  exact formsT_in_of h l

/-- At a run of the row the thread's row owes forms. -/
theorem forms_owed {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (h : (j, n) ∈ earlyRuns (IM.subAt l)) :
    Item.forms l j n ∈ (FirstRows.rows P5J.At.links P5J.At.ps (K1.noL l false)).owes := by
  rw [row_reads hl]
  exact List.mem_append_left _ ((forms_out_iff (IM.subAt l) l j n).2 h)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE PREMISE FormsAreLibrarys AT lettersHead**, at the library's own letters. -/
theorem formsAreLibrarys_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) :
    FormsAreLibrarys (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      ⟨h.𝔇.pubD, h.𝔇.ms, h.𝔇.St, uBySort h.𝔇.uL h.𝔇.uA h.𝔇.uH, h.𝔇.after, h.𝔇.wt, h.𝔇.rw⟩
      h.𝔇.arr :=
  ⟨fun _ => rfl, fun _ => rfl, fun s => statedIs_of _ s, fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- **ReadsSeated's THREE EQUATIONS AT THESE LETTERS, AND A FOURTH**: the codes are the reads' own
plan's; the numbers the letters'; the members the table's; and the letter arr, which ReadsSeated and
K1Seated share, is the table's: seatTab reads the witness through cs, arr and ms. -/
theorem formsReader_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block TS ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np)) (l : ℕ) :
    h.𝔇.pubD.cs = (K1.parL Zp Bs.G₀ l false).codes ∧ h.𝔇.pubD.N = P5J.At.N Zp cF ∧
      h.𝔇.ms = P5J.At.ms Zp Z.lay ∧ h.𝔇.arr = P5J.At.arr Zp :=
  ⟨(codes_at_head O).symm, rfl, rfl, rfl⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.readsRow_ins
#print axioms ProofFile.Honest.K1.readsRow_outs
#print axioms ProofFile.Honest.K1.forms_out_iff
#print axioms ProofFile.Honest.K1.formsT_in_of
#print axioms ProofFile.Honest.K1.forms_out_no
#print axioms ProofFile.Honest.K1.links_reads
#print axioms ProofFile.Honest.K1.place_reads
#print axioms ProofFile.Honest.K1.row_reads
#print axioms ProofFile.Honest.K1.formsT_shut
#print axioms ProofFile.Honest.K1.forms_owed
#print axioms ProofFile.Honest.K1.formsAreLibrarys_head
#print axioms ProofFile.Honest.K1.formsReader_head
