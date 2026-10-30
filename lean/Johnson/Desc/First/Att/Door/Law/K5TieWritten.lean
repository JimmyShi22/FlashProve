-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TieWritten.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION: WHERE THE COMPARISON madeRow ACCEPTS, THE CONDITION's TEST tie FOLLOWS FROM A BOOL WHOSE ONLY LETTERS ARE THE GROUP's NUMBER AND THE
INVERSE idx OF THE NUMBERING.** It turns nothing of the condition (K5CondAt, Door/Law/K5LeftOfCond.lean; K5CellsCond, Door/Law/K5RestCells.lean).
The road: tie follows from linkRestB, which reads no map from trees to arrays' names (tie_of_rest, Door/Law/K5TieOfNames.lean). linkRestB reads: the matrices' number, labels, rows and columns (written, by the shape part of madeRow: tail_of_is,
Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean) · the codes, the request's shape and the layout (written: made_row_gives, Door/Law/K5Written.lean) · the shapes of the caller's list (no radius: calls_shapes, Door/Law/K5PairsRead.lean) · the witness's
numbers (written: num_written, Door/Law/K5WrittenAll.lean) · idx.
madeRow's accept IS A PREMISE HERE: the verifier's list of entry tests asks it, from thirteen rows on (GLOSSARY.md, "entry tests").

Main names:
  linkRestBy V D l num idx k: linkRestB's own text, with (the number of matrices, each one's label, rows and columns) and the caller's list as plain parts. getD_view · linkRest_by: the two are one where tl is the plan's record at k.
  symEntry_reads · linkRestBy_reads: they read of what the planner sends the layout, the codes and the request's shape, and of the list its shapes.
  viewW k: the written (number, matrices) of segment k. **tieW g idx**: the test at the written values.
  lookTl_att: the lookups' reader of the plan's record at an attention segment. view_written: the plan's record has the written view.
  **tie_of_written**: the head · madeRow's accept · g < 12 · the plan a · the place x₁ · tieW g idx = true → the condition's field tie at idx.
IS IT EMPTY HERE? AN IMPLICATION. THAT tieW g idx IS true IS NOT SHOWN IN THIS FILE. FOR EACH g BELOW 12, AT ONE idx, THE WRITTEN INVERSE THAT tieWW's TEXT TAKES AT THAT g (Door/Law/K5TieWitness.lean), IT IS THE THEOREM tieWW_true (Door/Law/K5WrittenTrue.lean); OF ANY OTHER idx THAT THEOREM SAYS NOTHING. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5TieOfNames
import Johnson.Desc.First.Att.Door.Law.K5WrittenAll
import Johnson.Desc.First.Att.Door.Law.K5WrittenPlans
import Johnson.Desc.Ok.PlanWritten.XShapeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (arrayOf Chain)
open VerifiableInference.Desc.First.Look (Sent sigListCalls szOf msgIn keptAt bornAt lookAt)
open VerifiableInference.PlanWritten (madeRow tail_of_is tailView)
open Johnson.G (xShapeFull)
open Meaning (labAt ownerK ownerA nameOf linkTieB)
open P5J (AtMgA TS)

/-- **What is left of the ties at a link, over plain parts.** V: the number of matrices; each one's label, rows and columns. -/
def linkRestBy (V : ℕ × List (ℕ × ℕ × ℕ)) (D : Sent) (l : List (OracleShape × ℕ)) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k : ℕ) : Bool :=
  (List.range V.1).all fun μ =>
    symEntryB D l k (ownerK (V.2.getD μ (0, 0, 0)).1, nameOf (ownerA (V.2.getD μ (0, 0, 0)).1)) (Alg.symRows (V.2.getD μ (0, 0, 0)).2.1) (V.2.getD μ (0, 0, 0)).2.2 &&
      match arrayOf D.layout (ownerK (V.2.getD μ (0, 0, 0)).1) (nameOf (ownerA (V.2.getD μ (0, 0, 0)).1)) with
      | some A => decide (msgIn D k (ownerK (V.2.getD μ (0, 0, 0)).1) A.message = some (idx (num (ownerK (V.2.getD μ (0, 0, 0)).1) A.message)))
      | none => false

/-- The list of views meets the array at every number: a matrix's defaults are 0. -/
theorem getD_view (A : Array TMat) (μ : ℕ) :
    (A.toList.map fun x => (x.aId, x.m, x.k)).getD μ (0, 0, 0) = ((A.getD μ {}).aId, (A.getD μ {}).m, (A.getD μ {}).k) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  cases A[μ]? <;> rfl

/-- The two texts are one, where tl is the plan's record at k. -/
theorem linkRest_by {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}
    (hX : Meaning.tlAt X k = tl) :
    linkRestB X D rad num idx k tl =
      linkRestBy (tl.NM, tl.mats.toList.map fun x => (x.aId, x.m, x.k)) D (sigListCalls D rad k) num idx k := by
  subst hX
  have e : ∀ μ, ((Meaning.tlAt X k).mats.toList.map fun x => (x.aId, x.m, x.k)).getD μ (0, 0, 0) =
      (labAt X k μ, (szOf (Meaning.tlAt X k)).m μ, (szOf (Meaning.tlAt X k)).k μ) := fun μ => getD_view _ μ
  unfold linkRestB linkRestBy entryRestB
  simp only [e]
  rfl

theorem msgIn_shape {D D' : Sent} (hs : D.shape = D'.shape) (i b m : ℕ) : msgIn D i b m = msgIn D' i b m := by
  unfold msgIn bornAt
  rw [kept_shape hs, hs]

/-- The test at an entry reads the layout, the codes, the request's shape, and the list's shapes. -/
theorem symEntry_reads {D D' : Sent} (hl : D.layout = D'.layout) (hc : D.codes = D'.codes) (hs : D.shape = D'.shape)
    {l l' : List (OracleShape × ℕ)} (hsh : l.map (·.1) = l'.map (·.1)) (i : ℕ) (bn : ℕ × String) (R K : ℕ) :
    symEntryB D l i bn R K = symEntryB D' l' i bn R K := by
  have e : ∀ k : ℕ, (l[k]?).map (fun x => x.1) = (l'[k]?).map (fun x => x.1) := fun k => by
    rw [← List.getElem?_map, ← List.getElem?_map, hsh]
  unfold symEntryB
  rw [hl, hc]
  cases OnBytes.reqArray D'.layout bn.1 bn.2 with
  | none => rfl
  | some a =>
    show (match msgIn D i bn.1 a.message with
      | some k => (match l[k]? with
        | some o => VerifiableInference.Desc.First.Look.blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D'.codes o.1).ell
        | none => false)
      | none => false) = (match msgIn D' i bn.1 a.message with
      | some k => (match l'[k]? with
        | some o => VerifiableInference.Desc.First.Look.blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D'.codes o.1).ell
        | none => false)
      | none => false)
    rw [msgIn_shape hs]
    cases msgIn D' i bn.1 a.message with
    | none => rfl
    | some k =>
      have ek := e k
      show (match l[k]? with
        | some o => VerifiableInference.Desc.First.Look.blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D'.codes o.1).ell
        | none => false) = (match l'[k]? with
        | some o => VerifiableInference.Desc.First.Look.blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D'.codes o.1).ell
        | none => false)
      cases h1 : l[k]? with
      | none =>
        cases h2 : l'[k]? with
        | none => rfl
        | some o' =>
          rw [h1, h2] at ek
          cases ek
      | some o =>
        cases h2 : l'[k]? with
        | none =>
          rw [h1, h2] at ek
          cases ek
        | some o' =>
          rw [h1, h2] at ek
          have eo : o.1 = o'.1 := Option.some.inj ek
          show VerifiableInference.Desc.First.Look.blocksB a.blocks R K o.1.mainRows (Johnson.Pack.pMain D'.codes o.1).ell =
            VerifiableInference.Desc.First.Look.blocksB a.blocks R K o'.1.mainRows (Johnson.Pack.pMain D'.codes o'.1).ell
          rw [eo]

/-- **What is left of the ties reads no radius and no map of names.** -/
theorem linkRestBy_reads {D D' : Sent} (hl : D.layout = D'.layout) (hc : D.codes = D'.codes) (hs : D.shape = D'.shape)
    {l l' : List (OracleShape × ℕ)} (hsh : l.map (·.1) = l'.map (·.1)) (V : ℕ × List (ℕ × ℕ × ℕ)) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ)
    (k : ℕ) : linkRestBy V D l num idx k = linkRestBy V D' l' num idx k := by
  unfold linkRestBy
  have e1 : ∀ bn R K, symEntryB D l k bn R K = symEntryB D' l' k bn R K := symEntry_reads hl hc hs hsh k
  have e2 : ∀ b m, msgIn D k b m = msgIn D' k b m := msgIn_shape hs k
  simp only [e1, e2, hl]

/-- The written (number of matrices; each one's label, rows and columns) of segment k. -/
def viewW (k : ℕ) : ℕ × List (ℕ × ℕ × ℕ) :=
  match xShapeFull.1[k]? with
  | some (some v) => (v.1, v.2.1)
  | _ => (0, [])

/-- **The test at the written values.** Its letters: the group's number, and the inverse of the numbering. -/
def tieW (g : ℕ) (idx : ℕ → ℕ) : Bool :=
  linkRestBy (viewW (2 * g + 1)) sentW (sigListCalls sentW (fun _ => 0) (2 * g + 1)) (P5T.numOfPlan pseatsAllW) idx (2 * g + 1)

/-- The lookups' reader of the plan's record, at an attention segment. -/
theorem lookTl_att {X : Verify.Public} {g : ℕ} {a : Attention.Plan} (h4 : X.p4 = true) (hN : X.NGr = 12) (hg : g < 12)
    (ha : X.A[g]? = some a) : VerifiableInference.Desc.First.Look.tlAt X (2 * g + 1) = some a.seam.tl := by
  have hst : (if X.p4 then 2 else 1) = 2 := if_pos h4
  unfold VerifiableInference.Desc.First.Look.tlAt
  dsimp only
  rw [hst, hN]
  have h24 : (2 * g + 1 == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have hb : ((2 * g + 1) % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [h24, hb]
  simp only [Bool.false_eq_true, if_false]
  rw [show (2 * g + 1) / 2 = g by omega, ha]
  rfl

/-- **The plan's record at an attention segment has the written view.** -/
theorem view_written {Zp : ProofFile.Pub} (hm : madeRow Zp = true) (h4 : Zp.p.X.p4 = true) (hN : Zp.p.X.NGr = 12) {g : ℕ} (hg : g < 12)
    {a : Attention.Plan} (ha : Zp.p.X.A[g]? = some a) :
    (a.seam.tl.NM, a.seam.tl.mats.toList.map fun x => (x.aId, x.m, x.k)) = viewW (2 * g + 1) := by
  have hx : VerifiableInference.PlanWritten.xShapeIs Zp.p.X = true := by
    unfold madeRow at hm
    rw [Bool.and_eq_true] at hm
    exact hm.2
  have t := tail_of_is hx (k := 2 * g + 1) (by omega)
  rw [lookTl_att h4 hN hg ha] at t
  unfold viewW
  rw [t]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **THE CONDITION's FIELD tie, FROM THE TEST AT THE WRITTEN VALUES.** -/
theorem tie_of_written (hm : madeRow Zp = true) {g : ℕ} (hg : g < 12) {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a)
    {x₁ : VerifiableInference.Desc.First.Look.Place} (hx : lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁) {idx : ℕ → ℕ}
    (hW : tieW g idx = true) :
    linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp) idx x₁.link a.seam.tl = true := by
  refine tie_of_rest h hg ha hx ?_
  have e : x₁.link = 2 * g + 1 := VerifiableInference.OnPublicFiles.lookAt_link hx
  rw [e]
  have ha' : Zp.p.X.A[g]? = some a := ha
  have hpub : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact ProofFile.Law.pub_public h.laid.pub
  obtain ⟨k4, kN, _, _⟩ := Meaning.scope_plans h.scope h.reads hpub
  have etl : Meaning.tlAt Zp.p.X (2 * g + 1) = a.seam.tl := by
    unfold Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha']
    rfl
  obtain ⟨f1, _, f3, _, _, f6⟩ := (made_row_gives hm).1
  have q : linkRestB Zp.p.X (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) (P5J.At.num Zp) idx (2 * g + 1) a.seam.tl = tieW g idx := by
    unfold tieW
    rw [linkRest_by etl, view_written hm k4 kN hg ha', num_written h.toAtMg hm]
    exact linkRestBy_reads (D' := sentW) f6 f1 f3 (calls_shapes (D' := sentW) f3 _ _ _) _ _ _ _
  exact q.trans hW

end

end H2K5.Door

#print axioms H2K5.Door.linkRest_by
#print axioms H2K5.Door.symEntry_reads
#print axioms H2K5.Door.linkRestBy_reads
#print axioms H2K5.Door.lookTl_att
#print axioms H2K5.Door.view_written
#print axioms H2K5.Door.tie_of_written
