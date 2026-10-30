-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/OwnAtHead.lean: `ownSitsB V` AT THE FIRST CHAIN'S REACHED LAST STATE, AT THE ONE HEAD'S OWN
LETTERS (`P5J.AtMg`, Johnson/P5J/AtMg.lean, with `AtMg.rch`, `AtMg.rc`, `AtMg.typed` of Johnson/P5J/FourAtMg.lean
and `AtMg.mq` of Johnson/P5J/RowsAtMg.lean): the table's numbers, the meaning, the lists, the reader of a
statement, the description, the opening and "reached" are the head's terms. Statements with their proofs.

Main names (namespace `VerifiableInference.Desc.Last`).
  `pubD_N_at`: the composed meaning's public tests read THE TABLE'S OWN NUMBERS: (h.𝔇 𝔇₀).pubD.N = At.N Zp cF.
  `mq_indexIs`: the tower's meaning's test at the item indexIs is `K13.indexIsC (At.N Zp cF).indexNo`.
  `getAt`: how the tower reads a statement's first half: fun a => (a.1, (fun s => s) a.2).
  **`own_at_head_two`**: the end below FROM TWO TESTS ALONE at border 357 (hTwo: `seatsCarriedB L`, `msgShapesB M`, at
    states without a mark reached at a typed instance's public part): no `FoldFacts`; L and M are letters.
  **`own_at_head_of`**: ∀ q y, ocEnd getAt (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps q y → h.rc q →
    (getAt q).2.failed = none → ownSitsB V (getAt q).2 = true: GENERAL IN THE FAMILY OF WHICH THE FACTS ALONG THE
    FOLD ARE STATED (Rf, at_): hRc asks that each state reached along the head's first chain, at a public part
    that is a typed instance's, is read off a member of that family.
  `rch_of_reach`: hRc at the head's own "reached" (`AtMg.rch`) read by `Prod.fst`, beside any string y₀.
  **`own_at_head`**: the same at that family. (Where the field SH₃ is paid, a string is at hand: b.2.)
  At the foot an example hands it to a binder that is typed with `P5J.ocR`.
    SO idx IS (At.N Zp cF).indexNo, N₁ IS At.N Zp cF, the condition on the public part IS h.typed, and the opening
    IS h.laid.opened's: no letter of these is left.

What stays a premise. `First.FoldFacts` (Johnson/Desc/First/FoldFacts.lean as the ground has it) · hsp ·
`PlanSits d.L d.M V (At.N Zp cF).indexNo nW` · hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp.
LETTERS LEFT: V · d · nW · reqW · lk · pl; in `own_at_head_two`: V · L · M · nW.
Limits. At o := `OnBytes.secondHashFunction`. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.OwnOfFacts
import Johnson.Desc.Last.IndexAtEndAll
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub FoldData FoldFacts ModelPart)
open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open Johnson.Desc.First.Walk.Tied (Reach RchAt EndAt₁)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- The composed meaning's public tests read the table's own numbers. -/
theorem pubD_N_at {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp)) :
    (h.𝔇 𝔇₀).pubD.N = P5J.At.N Zp cF := rfl

/-- The tower's meaning's test at the item "indexIs". -/
theorem mq_indexIs {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    (a : ProofFile.InstPub × First.S) :
    (h.mq 𝔇₀).pub .indexIs a = K13.indexIsC (P5J.At.N Zp cF).indexNo a.2 := by
  rw [← P5J.mgAt_is_mq h 𝔇₀]
  exact mgAll_indexIs (h.𝔇 𝔇₀) mgBase a

/-- How the tower reads a statement's first half. -/
abbrev getAt : ProofFile.InstPub × First.S → ProofFile.InstPub × First.S := fun a => (a.1, (fun s => s) a.2)

/-- **At the one head's own letters, from the two tests at border 357 alone.** -/
theorem own_at_head_two (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hTwo : ∀ z s₂, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true)
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits L M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, ocEnd getAt (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps q y → h.rc q →
      (getAt q).2.failed = none → ownSitsB V (getAt q).2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rintro ⟨z, s⟩ y hoc hrc hm
  have he' : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) cF.blocksInOrder.length (z, s) := hrc.1
  rw [flat_358 h.scope h.reads O] at he'
  exact ownSitsB_at_promise_count h.scope h.reads O
    (handsBack_and (ToldDesc.handsBack_below 0 cF.blocksInOrder (ProofFile.startS Zp)) h.typed) getAt
    (fun _ _ => rfl) (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps pinI_open_full
    (mq_indexIs h 𝔇₀) hsp T hNum (fun z s₂ hr hm₂ => hTwo z s₂ hr.1 hr.2 hm₂) (z, s) y hoc
    ⟨hrc.2, he'⟩ hm

/-- **At the one head's own letters, general in the family of which the facts are stated.** -/
theorem own_at_head_of (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {X : Type} {Rf : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × First.S} {V : OwnSeats} {nW : ℕ}
    {d : FoldData} {reqW : ProofFile.InstPub → Array UInt32} {lk : List ModelPart} {pl : List Place}
    (FF : FoldFacts Rf at_ d reqW lk pl)
    (hRc : ∀ k z s, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) k (z, s) →
      ∃ a, Rf k a ∧ at_ a = (z, s))
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits d.L d.M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, ocEnd getAt (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps q y → h.rc q →
      (getAt q).2.failed = none → ownSitsB V (getAt q).2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro q y hoc hrc hm
  exact hOwn_of_facts_at h.scope h.reads O getAt (fun _ _ => rfl) (P5J.At.N Zp cF) (h.mq 𝔇₀)
    P5J.fullLinks P5J.At.ps FF h.typed hRc pinI_open_full (mq_indexIs h 𝔇₀) hsp T hNum Np q y
    ⟨hoc, hrc.2⟩ hrc.1 hm

/-- A reached state at a typed instance's public part is read off a member of the head's "reached". -/
theorem rch_of_reach {o : ProofFile.SecondHashFunctionArgument} (h : P5J.AtMg o Z D r Zp Np cF)
    (y₀ : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (k : ℕ) (z : ProofFile.InstPub)
    (s : First.S) (hk : h.typed z)
    (hr : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) k (z, s)) :
    ∃ a, h.rch k a ∧ Prod.fst a = (z, s) :=
  ⟨((z, s), y₀), ⟨hr, hk⟩, rfl⟩

/-- **At the one head's own letters, the facts stated of the head's own "reached".** -/
theorem own_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    (y₀ : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) {V : OwnSeats} {nW : ℕ}
    {d : FoldData} {reqW : ProofFile.InstPub → Array UInt32} {lk : List ModelPart} {pl : List Place}
    (FF : FoldFacts h.rch Prod.fst d reqW lk pl)
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits d.L d.M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, ocEnd getAt (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps q y → h.rc q →
      (getAt q).2.failed = none → ownSitsB V (getAt q).2 = true :=
  own_at_head_of h 𝔇₀ FF (fun k z s hk hr => rch_of_reach h y₀ k z s hk hr) hsp T hNum

/-- The fit with the two later tables' own condition `P5J.ocR` at the head's letters. -/
example (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    (y₀ : (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) {V : OwnSeats} {nW : ℕ}
    {d : FoldData} {reqW : ProofFile.InstPub → Array UInt32} {lk : List ModelPart} {pl : List Place}
    (FF : FoldFacts h.rch Prod.fst d reqW lk pl)
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits d.L d.M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, P5J.ocR (fun a : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub ×
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ => ((a.1, (fun s => s) a.2) :
                      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × P5J.TS))
        (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps h.rc q y →
      q.2.failed = none → ownSitsB V q.2 = true :=
  fun q y ho hm => own_at_head h 𝔇₀ y₀ FF hsp T hNum q y ho.1 ho.2 hm

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.pubD_N_at
#print axioms VerifiableInference.Desc.Last.mq_indexIs
#print axioms VerifiableInference.Desc.Last.own_at_head_two
#print axioms VerifiableInference.Desc.Last.own_at_head_of
#print axioms VerifiableInference.Desc.Last.rch_of_reach
#print axioms VerifiableInference.Desc.Last.own_at_head
