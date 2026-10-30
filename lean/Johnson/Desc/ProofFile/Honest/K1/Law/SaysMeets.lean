-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SaysMeets.lean: A SAMPLE ROW SAYS ITS CLAIM OF WORDS JUST IF
THE MESSAGE THAT THE WORDS HOLD MEETS THE ROW, READ AS A LINEAR FORM; AND THAT IS THE EQUATION OF A
PIN AT THE SEED THAT THE LIBRARY's READER OF SAMPLES CHOOSES. Six theorems; no definition. PUBLIC:
rows, words, statements and messages are bound variables: no coin, no run and no state of a run
occurs.

What this file proves. St a statement that holds the message x at the number o; r a row that has no
coefficient on another message than o (NamesOne, Johnson/Desc/First/Close/Law/SampleTie.lean); Wd
words that are 0 on the rows beyond the real ones (Padded, Johnson/Desc/Means/Says.lean); each code
of which x's shape has rows has a message length that is a power of two (hlM, hlZ).
  - value_entries: the row's value on the words is the sum, over the entries j of the library's
    typed message, of formRow St.codes x.shape o r j (Johnson/Desc/K1/Law/GoodSendForms.lean) times
    the words' entry at o, partZ j, locZ j (Johnson/Pack/PortTie.lean).
  - says_iff_meets: so Says rdE St r Wd holds just if that sum is the row's target, read.
  - meets_iff_says: if r is the first sample row that St holds of o: MeetsAt
    (Johnson/Desc/K1/Law/SealTie.lean) of the words' message holds just if r says its claim of Wd.
  - smpAt_spec: what smpAt (GoodSendForms.lean) returns: a seed whose matrix is the row's form, and
    the row's target. ans_iff_meets: so, at every radius e and every message u: the sample map's
    answers of u at THAT seed are the sample's answers just if u meets the row.
  - ans_iff_says: the two together.

How it fits. A pin at the threads (AnsAt, Honest/Thread/Ans.lean) says: the record holds the
member's sample, and the witness's message has that sample's answers at its seed. At the library's
reader smpNamed (Johnson/Desc/Sound/SmpNamed.lean) the record's sample is smpAt's at a member whose
seat stands in the reader's list; at any other member that reader answers nothing. The law on the
prover's side (send_says, Johnson/Prover/Send/Says.lean) ends in Says. ans_iff_says joins the two
ends.

It is a join: value_named (Johnson/Desc/ProofFile/Honest/K1/AnswersChain.lean) and, twice,
onTable_entries (Johnson/Desc/K12/Law/SaysSample.lean), whose six premises are paid as value_sample
(the same file) pays them.

Kin in the library, at more premises. value_sample, says_sample (SaysSample.lean), says_sample_t
(Johnson/Desc/K12/Law/SampleAt.lean), says_sample_ge (Johnson/Desc/K12/Law/FormTake.lean): the same
equivalence AT THE SEED AS READ, for the row that Send.form makes, under: one answer; CaseE ∨ CaseF;
the seed's length; its factor a unit. Here the row is any row that names o alone, and the seed is
the reader's own choice: none of these four is asked. smpAt_of (GoodSendForms.lean), smpAt_like
(Johnson/Top/H0/Tw/K2C/SmpForms.lean): that smpAt returns; smpAt_spec is the converse.

Limits. Nothing says that the seed by choice is the seed that was drawn. Nothing says that any row
says its claim of any words, or that smpAt returns. One answer a message, as in the library's reader
(the first sample row alone). Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.AnswersChain
import Johnson.Desc.K12.Law.SaysSample
import Johnson.Desc.K1.Law.SealTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack
open VerifiableInference.Desc.First.Close (NamesOne)
open VerifiableInference.Desc.K1 (formRow formsAt ansAt smpAt MeetsAt)
open H2K.Pin (onTable_entries)

/-- **A row that names o alone**: its value on padded words is the sum over the message's entries,
where St holds x at o and each code of which x's shape has rows has a message length that is a power
of two (hlM, hlZ). -/
theorem value_entries (St : Statement) (o : ℕ) (x : Oracle) (hx : St.oracles[o]? = some x)
    (r : OnBytes.Row) (hN : NamesOne r o)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain St.codes x.shape).ell = (pMain St.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask St.codes x.shape).ell = (pMask St.codes x.shape).ell)
    (Wd : Words GE) (hP : Padded St Wd) :
    value rdE St r Wd =
      ∑ j : (Fin x.shape.mainRows × Fin (pMain St.codes x.shape).ell) ⊕
        (Fin x.shape.maskRows × Fin (pMask St.codes x.shape).ell),
        formRow St.codes x.shape o r j *
          Wd o (partZ St.codes x.shape j) (locZ St.codes x.shape j) := by
  rw [value_named St r o hN Wd,
    onTable_entries St r Wd o .main x.shape.mainRows (pMain St.codes x.shape).ell
      (by unfold realRows; rw [hx]; rfl) (by unfold Statement.rowBits; rw [hx]; rfl)
      (fun h0 => by
        unfold Statement.placeBits
        rw [hx]
        show (if (x.shape.mainRows == 0) = true then 0 else _) = _
        rw [if_neg (by simpa using Nat.pos_iff_ne_zero.1 h0)]
        rfl)
      (by unfold Statement.has; rw [hx]; rfl) hlM hP,
    onTable_entries St r Wd o .mask x.shape.maskRows (pMask St.codes x.shape).ell
      (by unfold realRows; rw [hx]; rfl) (by unfold Statement.rowBits; rw [hx]; rfl)
      (fun h0 => by
        unfold Statement.placeBits
        rw [hx]
        show (if (x.shape.maskRows == 0) = true then 0 else _) = _
        rw [if_neg (by simpa using Nat.pos_iff_ne_zero.1 h0)]
        rfl)
      (by unfold Statement.has; rw [hx]; rfl) hlZ hP,
    Fintype.sum_sum_type]
  rfl

/-- **It says its claim just if that sum is its target**, under value_entries' premises. -/
theorem says_iff_meets (St : Statement) (o : ℕ) (x : Oracle) (hx : St.oracles[o]? = some x)
    (r : OnBytes.Row) (hN : NamesOne r o)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain St.codes x.shape).ell = (pMain St.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask St.codes x.shape).ell = (pMask St.codes x.shape).ell)
    (Wd : Words GE) (hP : Padded St Wd) :
    Says rdE St r Wd ↔
      ∑ j : (Fin x.shape.mainRows × Fin (pMain St.codes x.shape).ell) ⊕
        (Fin x.shape.maskRows × Fin (pMask St.codes x.shape).ell),
        formRow St.codes x.shape o r j *
          Wd o (partZ St.codes x.shape j) (locZ St.codes x.shape j) = readE r.target := by
  unfold Says
  rw [value_entries St o x hx r hN hlM hlZ Wd hP]
  rfl

/-- **The words' message meets the statement's first sample row of o just if that row says its claim
of the words**, under value_entries' premises: the row names o alone, the words are padded, hlM,
hlZ. -/
theorem meets_iff_says (St : Statement) (o : ℕ) (x : Oracle) (hx : St.oracles[o]? = some x)
    (r : OnBytes.Row) (hr : x.sampleRows[0]? = some r) (hN : NamesOne r o)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain St.codes x.shape).ell = (pMain St.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask St.codes x.shape).ell = (pMask St.codes x.shape).ell)
    (Wd : Words GE) (hP : Padded St Wd) :
    MeetsAt St.codes x.shape St o
        (fun j => Wd o (partZ St.codes x.shape j) (locZ St.codes x.shape j)) ↔
      Says rdE St r Wd := by
  rw [says_iff_meets St o x hx r hN hlM hlZ Wd hP]
  have h1 : formsAt St.codes x.shape St o = some fun _ => formRow St.codes x.shape o r := by
    unfold VerifiableInference.Desc.K1.formsAt
    rw [hx, Option.bind_some, hr]
    rfl
  have h2 : ansAt St o = some fun _ => readE r.target := by
    unfold VerifiableInference.Desc.K1.ansAt
    rw [hx, Option.bind_some, hr]
    rfl
  constructor
  · rintro ⟨φ, v, hφ, hv, q⟩
    obtain rfl := Option.some.inj (h1.symm.trans hφ)
    obtain rfl := Option.some.inj (h2.symm.trans hv)
    exact q
  · intro q
    exact ⟨_, _, h1, h2, q⟩

/-- What the reader of samples returns: a seed whose matrix is the first sample row's form; that
row's target. -/
theorem smpAt_spec (cs : Codes) (s : OracleShape) (e : ℕ) (St : Statement) (o : ℕ)
    (z : (portOmZ cs s e).Smp) (h : smpAt cs s e St o = some z) :
    formsAt cs s St o = some ((portOmZ cs s e).Z.mat z.1) ∧ ansAt St o = some z.2 := by
  unfold smpAt at h
  split at h
  · rename_i g
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨g.choose_spec, hv⟩
  · cases h

/-- **The pin's equation at the reader's seed is "the message meets the row".** -/
theorem ans_iff_meets (cs : Codes) (s : OracleShape) (e : ℕ) (St : Statement) (o : ℕ)
    (z : (portOmZ cs s e).Smp) (h : smpAt cs s e St o = some z) (u : (portCode cs s).J → GE) :
    (portOmZ cs s e).Z.val z.1 u = z.2 ↔ MeetsAt cs s St o u := by
  obtain ⟨h1, h2⟩ := smpAt_spec cs s e St o z h
  constructor
  · intro q
    exact ⟨_, _, h1, h2, congrFun q ()⟩
  · rintro ⟨φ, v, hφ, hv, q⟩
    obtain rfl : (portOmZ cs s e).Z.mat z.1 = φ := Option.some.inj (h1.symm.trans hφ)
    obtain rfl : z.2 = v := Option.some.inj (h2.symm.trans hv)
    funext w
    cases w
    exact q

/-- **THE TWO ENDS JOINED**: where the reader returns a sample of o, the words' message has that
sample's answers at its seed just if the first sample row says its claim of the words: under
value_entries' premises (the row names o alone, the words are padded, hlM, hlZ). -/
theorem ans_iff_says (St : Statement) (o : ℕ) (x : Oracle) (hx : St.oracles[o]? = some x)
    (r : OnBytes.Row) (hr : x.sampleRows[0]? = some r) (hN : NamesOne r o)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain St.codes x.shape).ell = (pMain St.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask St.codes x.shape).ell = (pMask St.codes x.shape).ell)
    (Wd : Words GE) (hP : Padded St Wd) (e : ℕ)
    (z : (portOmZ St.codes x.shape e).Smp) (h : smpAt St.codes x.shape e St o = some z) :
    (portOmZ St.codes x.shape e).Z.val z.1
        (fun j => Wd o (partZ St.codes x.shape j) (locZ St.codes x.shape j)) = z.2 ↔
      Says rdE St r Wd :=
  (ans_iff_meets St.codes x.shape e St o z h _).trans
    (meets_iff_says St o x hx r hr hN hlM hlZ Wd hP)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.value_entries
#print axioms ProofFile.Honest.K1.says_iff_meets
#print axioms ProofFile.Honest.K1.meets_iff_says
#print axioms ProofFile.Honest.K1.smpAt_spec
#print axioms ProofFile.Honest.K1.ans_iff_meets
#print axioms ProofFile.Honest.K1.ans_iff_says
