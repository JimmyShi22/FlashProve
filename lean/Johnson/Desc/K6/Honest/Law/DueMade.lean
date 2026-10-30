-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/DueMade.lean: WHO MAKES THE TWO STRUCTURES OF PREMISES OF
Honest/Law/Due.lean (`K6DueFront`: nine facts on the verifier's state in front of the output head's
own rounds; `K6DuePub`: five facts on public data and letters). CONDITIONAL. Two lemmas, by calls.
No thread of states and no prover's text is read here.

  `dueFront_of_items`   seven of the nine are what the table's promise says at the state
                    (`K6FrontItems`, Honest/Law/FrontItems.lean); the two on every reached state are
                    handed in
  `duePub_at_head`  **the five, under the one hypothesis h that ties the table's letters to the
                    IOP as written in Lean**, at every Lk that is the first chain's link 24 and at
                    the listed seats Lp

What it is not. That a state meets `K6FrontItems`, `FoldAt` or `noTablesB` is shown here of none.
The full size and the format's second hash function alone, as h : `P5J.AtMgA`. (The library has a member of
that hypothesis under four premises on the three public files: `P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) WHO PAYS WHAT. left:
`K6FrontItems.k6Left`; wide: `K6FrontItems.wide` (Honest/Law/FrontMore.lean); sentIs, fresh, book,
lookLeft: fields as they stand; ns: the public test freeAbove says that the open ledger has just the
plan's number of slots. The first lemma's four premises on public parameters and data are paid under
h by: hH: `paid_at_const`'s field on the head's segment; hX: the hypothesis' own field on the public
parameters; hB: `trees_at_const`; hns: `ns_at_const` (both Law/K6BuiltAtConst.lean). states:
`six_of_link_at_head` (Johnson/Desc/Kinds/Law/K6StateAtHead.lean); seats: `seatsC_at_head`
(Johnson/HB/LLHARD/K6SeatsAtHead.lean) with `reads_name_at_const` (Law/K6ReadsNameAtConst.lean);
laid: `paid_at_const` (Law/K06AtConst.lean); named: the hypothesis' own field on the seats' numbers,
at segment 24; stated: `stated_head` (Johnson/Desc/Sound/StatedAll.lean) with `paid_at_const`'s
field on the stated data's arm.
Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.Due
import Johnson.Desc.K6.Honest.Law.FrontMore
import Johnson.Desc.Kinds.Law.K06AtConst
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K6ReadsNameAtConst
import Johnson.HB.LLHARD.K6SeatsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Chain Claim Link Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.Sound (linksFull MgData MsgT CellsQ)

/-- The written list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}

/-- **SEVEN OF THE NINE FACTS IN FRONT ARE WHAT THE TABLE's PROMISE SAYS AT THE STATE**; the two
others, on every reached state, are handed in (F, Z1). hH, hX, hB, hns: facts on public parameters
and data. -/
theorem dueFront_of_items (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (a : P × S) (R : K6FrontItems D Mg a)
    (hH : VerifiableInference.OnPublicFiles.headLink Wp = 24) {pol KL : ByteArray}
    {lay : Option ByteArray} (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hB : First.FillSent.treesAt D.built 24 = First.FillSent.looksOf Wp.H.Fp)
    (hns : D.pubD.nsOf 24 = some Wp.H.ns) (lay6 : ReqLayout) (Lp : K12.Door.Laid)
    (M : List OracleShape) (F : FoldAt Lp M D.cs D.shape lay6 a.2) (Z1 : noTablesB a.2 = true) :
    K6DueFront D.N Wp lay6 D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[]) PS[341]? a.2 :=
  { left := R.k6Left hH
    noTables := Z1
    wide := R.wide hX hB
    fold := F
    sentIs := R.sentIs
    fresh := R.linkFresh
    book := R.book
    lookLeft := R.left
    ns := fun G hG => by
      have h1 := R.freeAbove
      rw [hns] at h1
      have h2 : First.freeAboveB Wp.H.ns a.2 = true := h1
      unfold First.freeAboveB at h2
      rw [hG] at h2
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h2
      exact le_of_eq h2.2 }
end

variable {Z : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **THE FIVE FACTS ON PUBLIC DATA AND LETTERS, UNDER THE ONE HYPOTHESIS h**, at every Lk that is
the first chain's link 24 and at the listed seats Lp. -/
theorem duePub_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x) (Lk : Link S Claim)
    (hlk : cF.links[24]? = some Lk) (Lp : K12.Door.Laid) (hLp : P5J.At.laid? Zp = some Lp) :
    K6DuePub (dAt h).arr (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp) (dAt h).cs
      (dAt h).shape (dAt h).pubD.dS Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      ((dAt h).sent.arrayOf.getD 24 #[]) PS[341]? (dAt h).St Lk :=
  { states := (P4.six_of_link_at_head h hlk).1
    seats := seatsC_at_head h Lp hLp (AtTable.reads_name_at_const h)
    laid := (AtTable.paid_at_const h Lk hlk).laid
    named := fun μ r c hr hc _ => h.plan.hN 24 μ r c hr hc
    stated := fun t ht hno => by
      obtain ⟨o, ho⟩ := ht
      have h1 := Sound.stated_head (dAt h).uL (dAt h).uA (dAt h).uH t o ho
      rw [hno, (AtTable.paid_at_const h Lk hlk).uH] at h1
      exact h1 }

#print axioms dueFront_of_items
#print axioms duePub_at_head

end VerifiableInference.Desc.Kinds.Head.Law.AtFold
