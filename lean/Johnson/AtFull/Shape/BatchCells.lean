-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchCells.lean: THE BATCHING MEMBER's STEP ON ShA AND ITS ONE Bool, THEIR ROWS
WRITTEN OUT AS PLAIN FUNCTIONS OF THE PUBLIC RECORD, AT THE TWELVE LAYERS' LINKS AND AT THE HEAD's
LINK OF THE PROOF FILE's OWN FIRST CHAIN; AND "carries" WITH THE VALUES IN HAND, AND Returns, AT
THESE THIRTEEN BATCHING MEMBERS. It joins batch_of_tables (BatchTable.lean) with the slots. Nothing
is evaluated.

  `Row`: a run of claims' three terms: the bare run; the run on shapes; the premise's Bool.
  `Row.idle`, `tabOf rows`: a table out of a list of rows by the order's pairs; elsewhere the idle
    row.
  **`rowsLay W g`**: the seven rows of the layers' link 2 g. **`rowsHead W iU3 lm`**: the eleven of
    the head's link.
  **`cellG`**, **`cellV`**: the member's step on ShA and its one Bool out of a list of rows.
  **`layers_batch`** (g < 12): Bs by baseOf's value · Lk · p · w tied as in batch_named: for every
    ft, G with G (14 (2 g) + Lk.hear.length + 2) = cellG p w.1 (rowsLay Bs.G₀.W g) Lk.order and vals
    with vals ‹number› = cellV p (rowsLay Bs.G₀.W g) Lk.order: CarriesV and Returns at that member.
  **`head_batch`**: the like at link 24, at rowsHead Bs.G₀.W iU3 q.lm, iU3 tied by the plan and q by
    placeAt Bs.G₀.W 24 false.

Limits. THIRTEEN OF THE 25 BATCHING MEMBERS (the twelve attention links': BatchCellsAtt.lean).
Neither end statement says that a member stands at its number; number, step and Bool still hang on
the link Lk (Lk.hear.length, Lk.order), tied by cF.links[l]? alone. CarriesV is the frame's
CarriesU, written out, not Carries. In cellV a clause is true where no ledger is open, where the
draw refuses, and for the runs behind one that refuses (BatchTerms.lean's batchVT). That cellV
accepts at a state of a run, and that cellG returns at a shape that the chain reaches, are not
shown. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the earlier hash. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchSlotsK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere Where)
open VerifiableInference.Desc.K3 (seatCalls planesRun)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun seatOf)
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt parOf asClaim callerKeys seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open ProofFile.Honest.K3.Shape (objectsG guestsG planesShG headReadersG)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA)
open ProofFile.Honest (Returns)

/-- A run of claims' three terms. -/
structure Row where
  run : VerifiableInference.Desc.K9.Shape.Run
  g : Nat → ChainSh → Except String (List ClaimSh × ChainSh)
  pre : Nat → S → Bool

/-- Outside the list of rows: refuses, refuses, rejects. -/
def Row.idle : Row :=
  ⟨fun _ _ => .error "no such run", fun _ _ => .error "no such run", fun _ _ => false⟩

/-- A table out of a list of rows. -/
def tabOf (rows : List ((Nat × String) × Row)) (o : Nat × String) : Row :=
  (rows.lookup o).getD Row.idle

def rowObjects (d : Bool) : Row :=
  ⟨objectsRun (seatOf K3Lot.ofForm d), objectsG d, fun _ _ => true⟩

def rowGuests : Row :=
  ⟨guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest S Claim)), guestsG,
    fun _ _ => true⟩

def rowEq : Row :=
  ⟨eqBare, VerifiableInference.Desc.First.K8.Honest.eqRunG,
    fun _ s => VerifiableInference.Desc.First.K8.Honest.eqPreB s⟩

/-- **The seven rows of the layers' link 2 g.** -/
def rowsLay (W : Verify.Public) (g : Nat) : List ((Nat × String) × Row) :=
  [((1, "objects"), rowObjects false), ((1, "guests"), rowGuests),
   ((2, "front"),
     ⟨fun _ s => OnBytes.Desc.First.K4.Rt.seatRun "K4.claims-front"
        (OnBytes.Desc.First.K4.formsFrontNoRows W.layers g) s,
      fun _ a => OnBytes.Desc.First.K4.Rt.k4RunG (OnBytes.Desc.First.K4.Rt.frontG W.layers g) a,
      fun _ s => OnBytes.Desc.First.K4.Rt.planEnvB W.layers s⟩),
   ((6, "objects"), rowObjects true), ((6, "guests"), rowGuests), ((4, "K8.equations"), rowEq),
   ((2, "back"),
     ⟨fun _ s => OnBytes.Desc.First.K4.Rt.seatRun "K4.claims-back"
        OnBytes.Desc.First.K4.formsBack s,
      fun _ a => OnBytes.Desc.First.K4.Rt.k4RunG
        (OnBytes.Desc.First.K4.Rt.backG W.layers.y W.layers.sc) a,
      fun _ s => OnBytes.Desc.First.K4.Rt.planEnvB W.layers s⟩)]

def rowThree (W : Verify.Public) (iU3 : Nat) (name : String) : Row :=
  ⟨VerifiableInference.Desc.Kinds.Head.Shape.bare W.hS iU3 (parOf W.hS (workAtW W)) 24 4 name,
    VerifiableInference.Desc.Kinds.Head.Shape.threeRunG W.hS iU3 (parOf W.hS (workAtW W)) name,
    fun _ s => endsS (parOf W.hS (workAtW W)) s⟩

/-- **The eleven rows of the head's link.** -/
def rowsHead (W : Verify.Public) (iU3 lm : Nat) : List ((Nat × String) × Row) :=
  [((2, "objects"), rowObjects false), ((2, "guests"), rowGuests),
   ((3, "norm"), rowThree W iU3 "norm"),
   ((3, "join"),
     ⟨VerifiableInference.Desc.K3.joinRun (seatCalls asClaim)
        (callerKeys (parOf W.hS (workAtW W)) (seatAt W.hS iU3)),
      VerifiableInference.Desc.Kinds.Head.Shape.joinRunG W.hS iU3 (parOf W.hS (workAtW W)),
      fun _ s => endsS (parOf W.hS (workAtW W)) s⟩),
   ((3, "policy"), rowThree W iU3 "policy"),
   ((2, "planes"),
     ⟨planesRun (seatCalls K3Lot.ofForm) lm (callerReaders (planesAt iU3)),
      planesShG lm (headReadersG iU3), fun _ _ => true⟩),
   ((7, "objects"), rowObjects true), ((7, "guests"), rowGuests), ((5, "K8.equations"), rowEq),
   ((3, "logits"), rowThree W iU3 "logits"),
   ((8, "the merge"),
     ⟨Johnson.Desc.First.ForkMerge.headMergeClaim,
      Johnson.Desc.First.ForkMerge.ShapeStep.mergeRunG, fun _ _ => true⟩)]

/-- **The member's step on ShA, out of a list of rows.** -/
def cellG (p : Where) (k : SegSort) (rows : List ((Nat × String) × Row))
    (order : List (Nat × String)) : ShA → Except String ShA :=
  liftQ (batchGS p.rows k (fun o => (tabOf rows o).g) order)

/-- **The member's one Bool, out of a list of rows.** -/
def cellV (p : Where) (rows : List ((Nat × String) × Row)) (order : List (Nat × String)) :
    S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool :=
  batchVT p (fun o => guardRun ProofFile.sameReply (tabOf rows o).run) (fun o => (tabOf rows o).pre)
    order

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem layers_batch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.links[2 * g]? = some Lk ∧ IM.k9At Zp (2 * g) = some p ∧
      testsWhere Zp.p.X (2 * g) 0 = some w ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * (2 * g) + Lk.hear.length + 2) = cellG p w.1 (rowsLay Bs.G₀.W g) Lk.order →
        vals (14 * (2 * g) + Lk.hear.length + 2) = cellV p (rowsLay Bs.G₀.W g) Lk.order →
        CarriesV cF.blocksInOrder ft (firstZA G vals) (14 * (2 * g) + Lk.hear.length + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * (2 * g) + Lk.hear.length + 2) := by
  have hl : 2 * g < 25 := by omega
  have h24 : 2 * g ≠ 24 := by omega
  have hsub : subAt (2 * g) = .layers := by
    unfold subAt
    rw [if_neg h24, if_pos (Nat.mul_mod_right 2 g)]
  have i1 : IM.k3Ix (2 * g) false = 1 := by simp [IM.k3Ix, h24]
  have i6 : IM.k3Ix (2 * g) true = 6 := by simp [IM.k3Ix, h24]
  obtain ⟨Lk, p, w, eL, hp, hw, hN⟩ := batch_of_tables h (2 * g) hl
  obtain ⟨L1, _, _, _, e1, _, _, _, hord, _⟩ := batch_named h (2 * g) hl
  obtain rfl : Lk = L1 := Option.some.inj (eL.symm.trans e1)
  obtain ⟨Bs, L4, hB, e4, s4f, s4b⟩ := k4_slotAt h g hg
  obtain rfl : Lk = L4 := Option.some.inj (eL.symm.trans e4)
  obtain ⟨L8, e8, s8⟩ := k8_slotAt h (2 * g) hl
  obtain rfl : Lk = L8 := Option.some.inj (eL.symm.trans e8)
  obtain ⟨La, ea, sao, sag⟩ := k3_two_at h (2 * g) hl false
  obtain rfl : Lk = La := Option.some.inj (eL.symm.trans ea)
  obtain ⟨Lb, eb, sbo, sbg⟩ := k3_two_at h (2 * g) hl true
  obtain rfl : Lk = Lb := Option.some.inj (eL.symm.trans eb)
  rw [hsub] at s8 hord
  rw [i1] at sao sag
  rw [i6] at sbo sbg
  refine ⟨Bs, Lk, p, w, hB, eL, hp, hw, fun ft G vals hG hv =>
    hN (fun o => (tabOf (rowsLay Bs.G₀.W g) o).run) (fun o => (tabOf (rowsLay Bs.G₀.W g) o).g)
      (fun o => (tabOf (rowsLay Bs.G₀.W g) o).pre) ?_ ft G vals hG hv⟩
  rw [hord]
  intro o ho
  simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sao
  · exact sag
  · exact s4f
  · exact sbo
  · exact sbg
  · exact s8
  · exact s4b

theorem head_batch (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere)
        (iU3 : Nat) (q : VerifiableInference.Desc.First.Look.P),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.links[24]? = some Lk ∧ IM.k9At Zp 24 = some p ∧ testsWhere Zp.p.X 24 0 = some w ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some q ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * 24 + Lk.hear.length + 2) = cellG p w.1 (rowsHead Bs.G₀.W iU3 q.lm) Lk.order →
        vals (14 * 24 + Lk.hear.length + 2) = cellV p (rowsHead Bs.G₀.W iU3 q.lm) Lk.order →
        CarriesV cF.blocksInOrder ft (firstZA G vals) (14 * 24 + Lk.hear.length + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * 24 + Lk.hear.length + 2) := by
  have hl : 24 < 25 := by omega
  have hsub : subAt 24 = .head := rfl
  have i2 : IM.k3Ix 24 false = 2 := rfl
  have i7 : IM.k3Ix 24 true = 7 := rfl
  obtain ⟨Lk, p, w, eL, hp, hw, hN⟩ := batch_of_tables h 24 hl
  obtain ⟨L1, _, _, _, e1, _, _, _, hord, _⟩ := batch_named h 24 hl
  obtain rfl : Lk = L1 := Option.some.inj (eL.symm.trans e1)
  obtain ⟨Bs, L6, iU3, hB, e6, hU, s3, s6j⟩ := k6_slotAt h
  obtain rfl : Lk = L6 := Option.some.inj (eL.symm.trans e6)
  obtain ⟨Bp, Lp, iP, q, hBp, ep, hUp, hq, spl⟩ := k3_planes_head h
  obtain rfl : Bs = Bp := Except.ok.inj (hB.symm.trans hBp)
  obtain rfl : Lk = Lp := Option.some.inj (eL.symm.trans ep)
  obtain rfl : iU3 = iP := Option.some.inj (hU.symm.trans hUp)
  obtain ⟨L8, e8, s8⟩ := k8_slotAt h 24 hl
  obtain rfl : Lk = L8 := Option.some.inj (eL.symm.trans e8)
  obtain ⟨L11, e11, s11⟩ := k11_slotAt h
  obtain rfl : Lk = L11 := Option.some.inj (eL.symm.trans e11)
  obtain ⟨La, ea, sao, sag⟩ := k3_two_at h 24 hl false
  obtain rfl : Lk = La := Option.some.inj (eL.symm.trans ea)
  obtain ⟨Lb, eb, sbo, sbg⟩ := k3_two_at h 24 hl true
  obtain rfl : Lk = Lb := Option.some.inj (eL.symm.trans eb)
  rw [hsub] at s8 hord
  rw [i2] at sao sag
  rw [i7] at sbo sbg
  refine ⟨Bs, Lk, p, w, iU3, q, hB, eL, hp, hw, hU, hq, fun ft G vals hG hv =>
    hN (fun o => (tabOf (rowsHead Bs.G₀.W iU3 q.lm) o).run)
      (fun o => (tabOf (rowsHead Bs.G₀.W iU3 q.lm) o).g)
      (fun o => (tabOf (rowsHead Bs.G₀.W iU3 q.lm) o).pre) ?_ ft G vals hG hv⟩
  rw [hord]
  intro o ho
  simp only [VerifiableInference.Desc.First.orderOf, VerifiableInference.Desc.First.orderCuts,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sao
  · exact sag
  · exact s3 "norm" (by simp)
  · exact s6j
  · exact s3 "policy" (by simp)
  · exact spl
  · exact sbo
  · exact sbg
  · exact s8
  · exact s3 "logits" (by simp)
  · exact s11

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.layers_batch
#print axioms Johnson.AtFull.Shape.head_batch
#print axioms Johnson.AtFull.Shape.Row
#print axioms Johnson.AtFull.Shape.Row.idle
#print axioms Johnson.AtFull.Shape.tabOf
#print axioms Johnson.AtFull.Shape.rowObjects
#print axioms Johnson.AtFull.Shape.rowGuests
#print axioms Johnson.AtFull.Shape.rowEq
#print axioms Johnson.AtFull.Shape.rowsLay
#print axioms Johnson.AtFull.Shape.rowThree
#print axioms Johnson.AtFull.Shape.rowsHead
#print axioms Johnson.AtFull.Shape.cellG
#print axioms Johnson.AtFull.Shape.cellV
