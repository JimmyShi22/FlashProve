-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TieOfNames.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION: THE CONDITION's TEST tie FROM A TEST THAT READS NO MAP FROM TREES TO ARRAYS' NAMES.** It turns nothing of the condition
(K5CondAt, Door/Law/K5LeftOfCond.lean; K5CellsCond, Door/Law/K5RestCells.lean).
The test tie (linkTieB, Johnson/Goal/Meaning/ReadingsOne.lean) has three conjuncts at each matrix. The first says what the field arrayOf holds at the matrix's tree; the second (symArrB, Johnson/Desc/First/Look/K3CallerAttReads.lean) opens that
same entry and reads nothing else of the field; the third reads none of it. The first is a theorem at the attention segments (names_tie_att_plain, Door/Law/K5NamesTie.lean). So what is left to be tested is the second conjunct with the entry
laid in, and the third.

Main names:
  symEntryB D l i bn R K: symArrB's own text behind its first match, at an entry bn that is handed in. symArr_of_entry: where the field holds bn at tree t, the two are one.
  entryRestB · linkRestB: the second conjunct with the label's entry laid in, and the third; at every matrix. THEY READ NEITHER D.arrayOf NOR tl.gtTree.
  entryTie_of_names · **linkTie_of_names**: over letters: the first conjunct's sentence at every matrix and linkRestB's accept give linkTieB's accept.
  **tie_of_rest**: under the head, at group g < 12, its plan a and the place x₁ of its lookup argument: linkRestB … = true → the condition's field tie, text for text. cellsCond_of_rest: so K5CellsCond from linkRestB's accept and the field one.
IS IT EMPTY HERE? IMPLICATIONS. THAT linkRestB ACCEPTS AT ANY LETTERS IS NOT SHOWN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5NamesTie
import Johnson.Desc.First.Att.Door.Law.K5RestCells
import Johnson.Goal.Meaning.ReadingsOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (arrayOf Chain)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf msgIn symArrB blocksB lookAt)
open VerifiableInference.OnPublicFiles (OneNumber)
open Meaning (labAt ownerK ownerA nameOf entryTieB linkTieB)
open P5J (AtMgA TS)

/-- The test on an array of link i's list, of R rows and K columns, at the entry bn (the link that sent it, its name there). -/
def symEntryB (D : Sent) (l : List (OracleShape × ℕ)) (i : ℕ) (bn : ℕ × String) (R K : ℕ) : Bool :=
  match OnBytes.reqArray D.layout bn.1 bn.2 with
  | some a =>
    match msgIn D i bn.1 a.message with
    | some k =>
      match l[k]? with
      | some o => blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D.codes o.1).ell
      | none => false
    | none => false
  | none => false

/-- Where the field holds bn at tree t, the test on array number t is the test at bn. -/
theorem symArr_of_entry {D : Sent} {l : List (OracleShape × ℕ)} {i t R K : ℕ} {bn : ℕ × String}
    (h : (D.arrayOf.getD i #[])[t]? = some bn) : symArrB D l i t R K = symEntryB D l i bn R K := by
  unfold symArrB symEntryB
  simp only [h]
  rfl

/-- What is left of the ties at one entry: it reads neither D.arrayOf nor tl.gtTree. -/
def entryRestB (X : Model.Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k : ℕ) (tl : HTailF2)
    (μ : ℕ) : Bool :=
  symEntryB D (sigListCalls D rad k) k (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))) (Alg.symRows ((szOf tl).m μ))
      ((szOf tl).k μ) &&
    match arrayOf D.layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) with
    | some A => decide (msgIn D k (ownerK (labAt X k μ)) A.message =
        some (idx (num (ownerK (labAt X k μ)) A.message)))
    | none => false

/-- The same at every entry of the record's list. -/
def linkRestB (X : Model.Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k : ℕ) (tl : HTailF2) :
    Bool :=
  (List.range (szOf tl).NM).all fun μ => entryRestB X D rad num idx k tl μ

section
variable {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}

theorem entryTie_of_names {μ : ℕ}
    (hn : (D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? = some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))))
    (hr : entryRestB X D rad num idx k tl μ = true) : entryTieB X D rad num idx k tl μ = true := by
  unfold entryRestB at hr
  rw [Bool.and_eq_true] at hr
  unfold entryTieB
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true hn, (symArr_of_entry hn).trans hr.1⟩, hr.2⟩

/-- **The names' sentence at every matrix and the rest's accept give the ties' accept.** -/
theorem linkTie_of_names
    (hn : ∀ μ, μ < (szOf tl).NM →
      (D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? = some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))))
    (hr : linkRestB X D rad num idx k tl = true) : linkTieB X D rad num idx k tl = true := by
  unfold linkRestB at hr
  unfold linkTieB
  exact List.all_eq_true.2 fun μ hμ => entryTie_of_names (hn μ (List.mem_range.1 hμ)) (List.all_eq_true.1 hr μ hμ)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE CONDITION's FIELD tie, FROM A TEST THAT READS NO arrayOf.** -/
theorem tie_of_rest {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {idx : ℕ → ℕ}
    (hr : linkRestB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx x₁.link a.seam.tl = true) :
    linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx x₁.link a.seam.tl = true := by
  have e : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  rw [e] at hr ⊢
  have ha' : Zp.p.X.A[g]? = some a := ha
  have etl : Meaning.tlAt Zp.p.X (2 * g + 1) = a.seam.tl := by
    unfold Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha']
    rfl
  refine linkTie_of_names (fun μ hμ => ?_) hr
  have hμ' : μ < (Meaning.sizesOf Zp.p.X (2 * g + 1)).NM := by
    unfold Meaning.sizesOf
    rw [etl]
    exact hμ
  have t := H2K5.Names.names_tie_att_plain h.scope h.reads h.laid.pub hg hμ'
  rw [etl] at t
  exact t

/-- So the two fields of the lookup argument's own ledger, from the rest's accept and the field one. -/
theorem cellsCond_of_rest {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {idx : ℕ → ℕ}
    (hr : linkRestB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx x₁.link a.seam.tl = true)
    (one : OneNumber (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx (_root_.Meaning.tlAt (P5J.At.X Zp)) x₁.link
      (fun j : Fin (sigListCalls h.𝔇.sent h.𝔇.rad3 x₁.link).length => h.𝔇.seat3 x₁.link false j.1) h.𝔇.arr id) :
    K5CellsCond h a x₁ idx :=
  ⟨tie_of_rest h hg ha hx hr, one⟩

end

end H2K5.Door

#print axioms H2K5.Door.symArr_of_entry
#print axioms H2K5.Door.entryTie_of_names
#print axioms H2K5.Door.linkTie_of_names
#print axioms H2K5.Door.tie_of_rest
#print axioms H2K5.Door.cellsCond_of_rest
