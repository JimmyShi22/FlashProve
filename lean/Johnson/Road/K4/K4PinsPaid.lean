-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsPaid.lean: K4's TEST ON THE NEXT ENTRY's NAME AND THE PINS' FIVE TESTS ARE NO
TESTS, UNDER TWO CONDITIONS ON THE PUBLIC FILES: the closed facts of
Johnson/Road/K4/K4PinsWrittenNext.lean, K4PinsWrittenMask.lean and K4PinsWrittenArrays.lean CARRIED
TO THE COMPOSED MEANING's CLOSED PARAMETERS. The ends are two fields of the structure `K4Cond`
(Johnson/Road/K4/K04Cond.lean), to the letter. The bound on the slots is a theorem
(`slots_paid`, Johnson/Road/K4/K4PinsSlots.lean), called. One Lean structure and seven theorems;
nothing is evaluated here.

  `K4PinsAt Dm cF`: three equations more on the composed meaning's parameters: its codes, its
    numbers and its plan of what is sent are the closed letters' (beside `K4PinsFill`,
    Johnson/Road/K4/K4PinsLaterScope.lean). `pinsAt_const`: at the closed constant: by rfl.
  `laid_written`: under `WrittenAt Z` the reader of the listed seats returns something.
  `nextFits_at`, `closed_at`: at every Dm with these equations; `closed_at` takes the bound on the
    slots as a premise.
  **`nextFits_paid`**: the field nextFits. **`pins_paid`**: the field pins, AT THE L THAT THE
    CLOSED PARAMETERS' READER RETURNS (`P5J.At.laid? Zp = some L`: a premise). `cond_with_paid`:
    Lean lays the two into the structure: so the ends are the fields to the letter. IT PAYS NOTHING.

THE CONDITIONS. (1) `WrittenAt Zp`: five parts of the public parameters are the written values. (2)
THE CUT: `cutOf cF.blocksInOrder = cutFirstFull`: the first chain's sub-protocols bear the written names and
places and tell the written trees. BOTH ARE CONDITIONS ON THE THREE PUBLIC FILES ALONE (Zp and cF
are functions of these): nothing that a prover sends is read. (2) is what the tenth row of the
verifier's entry tests compares (`cutRow`, Johnson/Desc/Ok/PlanWritten/CutTest.lean;
`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean: fourteen rows);
THE LIST's FIRST EIGHT ROWS DO NOT ASK IT. (1): the ninth row and the laid value give
its five equations: other files' theorems: not called here. Over the whole list both follow
from the head: Johnson/Road/K4/K4HeadWritten.lean. Of the list's first thirteen rows alone:
EVALUATED: that list's rows on the cut and on the sizes, rounds and sendings
accept at five sets of public files in the goals' scope, at the full size, with negative tests.

Limits. K04_law IS NOT PROVED BY THIS. THE TWO CONDITIONS, AND THE EQUATION ON L, ARE PREMISES; NO
MEMBER IS SHOWN. IT SPEAKS AT THE WIDER MEANING: it counts only when the bridge to the meaning that
counts is paid. The written values rest on prints of Lean's evaluator. The full size alone.

-/
import Johnson.Road.K4.K04Cond
import Johnson.Road.K4.K4PinsClosed
import Johnson.Road.K4.K4PinsWrittenNext
import Johnson.Road.K4.K4PinsWrittenArrays
import Johnson.Road.K4.K4PinsSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (proofSizedFull cutFirstFull)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S flatPlacesOf FillP1.fvsAt FillP1.free0Of)
open VerifiableInference.Desc.First.FillSent (sentDataOf sentDataAt baseAt treesAt)
open VerifiableInference.Desc.First.Look (Sent szOf)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open OnBytes.Road.K4.Rec (RecPlan nextFitsB maskFitsB recPlanOf maskPlanB arrayPlanB arraysPlanB
  maskEllP)
open OnBytes.Road.K4.Riders (fvsFull fvs_at_scope rowsBefore_full)
open Johnson.G (layoutFull)
open Meaning (labAt ownerK ownerA nameOf)
open Inst.Model.Layout (kRef hRef)

/-- the table's own list of places -/
local notation "𝐩𝐬" => (flatPlacesOf linksFull true)

variable {Xi : Type} {nQ : ℕ} {Z : ProofFile.Pub}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Three equations more on the composed meaning's parameters.** -/
structure K4PinsAt (Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ Z.p.X)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) : Prop where
  cs : Dm.cs = P5J.At.cs Z
  N : Dm.N = P5J.At.N Z cF
  dS : Dm.pubD.dS = sentDataAt (P5J.At.shape Z) (P5J.At.N Z cF) linksFull 𝐩𝐬 Z.made.p.built.links

/-- Under the written values the reader of the listed seats returns something. -/
theorem laid_written (W : WrittenAt Z) : ∃ L, P5J.At.laid? Z = some L := by
  rw [laid_at W]
  have h : laidW?.map (fun L => (L.places.length, L.shapes.length)) = some (199, 83) :=
    congrArg Prod.snd sends_counts
  obtain ⟨L, hL, _⟩ := Option.map_eq_some_iff.1 h
  exact ⟨L, hL⟩

section
variable {Dm : MgData Xi ProofFile.InstPub ℕ hRef (2 ^ kRef) nQ Z.p.X} (W : WrittenAt Z)
  (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
  (hfv : FillP1.fvsAt Z = fvsFull) (A : K4PinsAt Dm cF)
  (L : VerifiableInference.Desc.K12.Door.Laid)
include W hc hfv A

/-- **Under `WrittenAt Z`, the written cut and the closed list of flags, the test on the next
entry's name accepts**, at every Dm with the three equations `K4PinsAt`. -/
theorem nextFits_at {g : ℕ} (hg : g < 12) :
    nextFitsB (k4DataWide Dm (eAll Z cF L) mgBase).cs (k4DataWide Dm (eAll Z cF L) mgBase).d12.M
      ((k4DataWide Dm (eAll Z cF L) mgBase).N.msgsAt 𝐩𝐬[28 * g + 4 + 1]?)
      (k4DataWide Dm (eAll Z cF L) mgBase).N.indexNo (k4DataWide Dm (eAll Z cF L) mgBase).free0
      (k4DataWide Dm (eAll Z cF L) mgBase).fvs (2 * g) = true := by
  have B := book_of_cut W hc
  show nextFitsB Dm.cs (P5J.At.d12 Z L).M (Dm.N.msgsAt 𝐩𝐬[28 * g + 4 + 1]?) Dm.N.indexNo
    (FillP1.free0Of (P5J.At.cs Z) (P5J.At.d12 Z L).M (P5J.At.N Z cF).indexNo) (FillP1.fvsAt Z)
    (2 * g) = true
  rw [A.cs, show P5J.At.cs Z = proofSizedFull.codes from W.codes, msgs_at W L, A.N, B.msgsAt,
    B.indexNo, hfv]
  exact List.all_eq_true.1 nextFits_written g (List.mem_range.2 hg)

variable (Pf : K4PinsFill Dm Z) (hL : P5J.At.laid? Z = some L) (H9 : XNine Z.p.X)
  (T : NamesTied Z)
include Pf hL H9 T

/-- **Under `WrittenAt Z`, the written cut, the closed list of flags, `XNine`, the names' tie, and
at the L that the reader of the listed seats returns, the five tests accept**, at every Dm with the
equations `K4PinsAt` and `K4PinsFill`, at a group below 12 with its plan, where the plan's number of
slots is at most 8192. -/
theorem closed_at {par : Par} (hg : par.g < 12) (hG : Z.p.X.G[par.g]? = some par.hp)
    (hns : par.hp.ns ≤ 8192) :
    K4PinsClosed Dm (eAll Z cF L) (28 * par.g + 4) par.g par := by
  have B := book_of_cut W hc
  have hW : laidW? = some L := (laid_at W).symm.trans hL
  have hcs : P5J.At.cs Z = proofSizedFull.codes := W.codes
  have hrow : rowsBefore (FillP1.fvsAt Z) (2 * par.g) = par.g := by
    rw [hfv]
    exact rowsBefore_full (Nat.le_of_lt hg)
  have hmem : par.g ∈ List.range 12 := List.mem_range.2 hg
  -- the letters at the written values
  have d : sentAt Z = ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
      Z.made.p.built.links.map (·.arrayOf)⟩ := by
    unfold sentAt
    rw [show Z.made.p.chains.proof.first.codes = proofSizedFull.codes from W.codes,
      show Z.made.p.chains.proof.first.shape = proofSizedFull.request from
        W.shape.trans shape_one,
      show Z.made.p.chains.proof.first.layout = layoutFull from W.layout]
  have hD : sentOf (k4DataWide Dm (eAll Z cF L) mgBase) =
      ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        Z.made.p.built.links.map (·.arrayOf)⟩ := by
    have h0 : sentOf (k4DataWide Dm (eAll Z cF L) mgBase) =
        ⟨Dm.cs, Dm.sent.shape, Dm.sent.layout, Dm.sent.arrayOf⟩ := rfl
    rw [h0, A.cs, Pf.sent, d]
    exact congrArg (fun c => (⟨c, proofSizedFull.request, layoutFull,
      Z.made.p.built.links.map (·.arrayOf)⟩ : Sent)) hcs
  have hf : (k4DataWide Dm (eAll Z cF L) mgBase).L3.seat (2 * par.g) false =
      P6T.seatCallsT P5T.psFull ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        Z.made.p.built.links.map (·.arrayOf)⟩ (2 * par.g) := by
    funext j
    show Dm.seat3 (2 * par.g) false j = _
    rw [Pf.seat3, seatsAt_written W, d]
  have hbase : baseAt (P5J.At.N Z cF) linksFull 𝐩𝐬 = baseAt nW linksFull 𝐩𝐬 := by
    funext m
    unfold baseAt
    rw [B.msgsAt]
  have hR : recPlanOf (k4DataWide Dm (eAll Z cF L) mgBase)
      (k4DataWide Dm (eAll Z cF L) mgBase).sd =
      ⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        fun m => (Z.made.p.built.links.map (·.arrayOf)).getD m #[], L, mW,
        sentDataOf proofSizedFull.request (baseAt nW linksFull 𝐩𝐬)
          (treesAt Z.made.p.built.links)⟩ := by
    have h0 : recPlanOf (k4DataWide Dm (eAll Z cF L) mgBase)
        (k4DataWide Dm (eAll Z cF L) mgBase).sd =
        ⟨Dm.cs, Dm.sent.shape, Dm.sent.layout, fun m => Dm.sent.arrayOf.getD m #[], L,
          (P5J.At.d12 Z L).M, Dm.pubD.dS⟩ := rfl
    rw [h0, A.cs, hcs, Pf.sent, d, msgs_at W L, A.dS,
      show P5J.At.shape Z = proofSizedFull.request from W.shape.trans shape_one]
    unfold sentDataAt
    rw [hbase]
  have hown : (k4DataWide Dm (eAll Z cF L) mgBase).N.sent (2 * par.g) 0 = ownSentW par.g := by
    show Dm.N.sent (2 * par.g) 0 = nW.sent (2 * par.g) 0
    rw [A.N, B.sent]
  have hn : (k4DataWide Dm (eAll Z cF L) mgBase).N.msgsAt 𝐩𝐬[28 * par.g + 4]? =
      nW.msgsAt 𝐩𝐬[28 * par.g + 4]? := by
    show Dm.N.msgsAt _ = _
    rw [A.N, B.msgsAt]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- maskFits
    have h := maskFits_written
    rw [hW] at h
    have h' := List.all_eq_true.1 (show ((List.range 12).all fun g =>
      maskFitsB proofSizedFull.codes mW L (nW.msgsAt 𝐩𝐬[28 * g + 4 + 1]?)
        (nW.treesAt 𝐩𝐬[28 * g + 4 + 1]?) nW.indexNo g) = true from h) par.g hmem
    show maskFitsB Dm.cs (P5J.At.d12 Z L).M L (Dm.N.msgsAt 𝐩𝐬[28 * par.g + 4 + 1]?)
      (Dm.N.treesAt 𝐩𝐬[28 * par.g + 4 + 1]?) Dm.N.indexNo
      (rowsBefore (FillP1.fvsAt Z) (2 * par.g)) = true
    rw [A.cs, hcs, msgs_at W L, A.N, B.msgsAt, B.treesAt, B.indexNo, hrow]
    exact h'
  · -- indexTie
    have h := indexTie_written
    rw [hW] at h
    have h' := List.all_eq_true.1 (show ((List.range 12).all fun g =>
      indexTieB proofSizedFull.codes mW L.places (msOf listsW) nW (g + 1)) = true from h)
      par.g hmem
    obtain ⟨radM, Q3⟩ := Pf.ms
    have sp : SamePairs (msOf listsW) (P5T.msAtR Z radM) := by
      rw [← lists0At_written W]
      exact samePairs_R _ _ radM _
    show indexTieB Dm.cs (P5J.At.d12 Z L).M L.places Dm.ms Dm.N
      (rowsBefore (FillP1.fvsAt Z) (2 * par.g) + 1) = true
    rw [A.cs, hcs, msgs_at W L, Q3, hrow,
      indexTieB_sameN (N := nW) (N' := Dm.N) (by rw [A.N, B.indexNo]) (by rw [A.N, B.index])]
    exact indexTieB_pairs sp h'
  · -- maskPlan
    have h := maskPlan_written
    rw [hW] at h
    have h' := List.all_eq_true.1 (show ((List.range 12).all fun g =>
      maskPlanB (pin0 sentW (seatW (2 * g)) (2 * g)) (ownSentW g) (recW L)
        (nW.msgsAt 𝐩𝐬[28 * g + 4]?) (2 * g)) = true from h) par.g hmem
    rw [hD, hf, hR, hown, hn]
    exact (maskPlanB_free _ _ _ _ _ _ _ _ #[] _ _ _ _ (fun _ => #[]) _ _ _ _ (fun _ => []) _
      _).trans h'
  · -- arrays
    have h := arrays_written
    rw [hW] at h
    have h' := List.all_eq_true.1 (show ((List.range 12).all fun g => (List.range 9).all fun μ =>
      arrayArm sentW (fun _ => 0) (2 * g) (seatW (2 * g)) (ownSentW g) (recW L)
        (nW.msgsAt 𝐩𝐬[28 * g + 4]?) (2 * g) (Alg.symRows (sizeW μ).1) (sizeW μ).2
        ((ownerW g μ).1, nameOf (ownerW g μ).2)) = true from h) par.g hmem
    have hsz : szOf par.hp.tl = _root_.Meaning.sizesOf Z.p.X (2 * par.g) := size_sizesOf hG hg
    rw [hD, hf, hR, hown, hn]
    unfold arraysPlanB
    refine List.all_eq_true.2 fun μ _ => ?_
    beta_reduce
    have μN : μ.val < (_root_.Meaning.sizesOf Z.p.X (2 * par.g)).NM :=
      Nat.lt_of_lt_of_eq μ.isLt (congrArg (·.NM) hsz)
    have μ9 : μ.val < 9 := Nat.lt_of_lt_of_eq μN (H9.nm par.g hg)
    have o := H9.own par.g hg μ.val μ9
    have sz := H9.size par.g hg μ.val μ9
    have hname : ((Z.made.p.built.links.map (·.arrayOf)).getD (2 * par.g) #[])[
        par.hp.tl.gtTree.getD μ.val 0]? =
        some ((ownerW par.g μ.val).1, nameOf (ownerW par.g μ.val).2) := by
      have t := T par.g hg μ.val μN
      rw [tlAt_even hg hG, show ownerK (labAt Z.p.X (2 * par.g) μ.val) = (ownerW par.g μ.val).1
        from congrArg Prod.fst o, show ownerA (labAt Z.p.X (2 * par.g) μ.val) =
        (ownerW par.g μ.val).2 from congrArg Prod.snd o] at t
      exact t
    have s1 : Alg.symRows ((szOf par.hp.tl).m μ.val) = Alg.symRows (sizeW μ.val).1 :=
      (congrArg (fun z : Cb.Pv.Tail.Size => Alg.symRows (z.m μ.val)) hsz).trans
        (congrArg Prod.fst sz)
    have s2 : (szOf par.hp.tl).k μ.val = (sizeW μ.val).2 :=
      (congrArg (fun z : Cb.Pv.Tail.Size => z.k μ.val) hsz).trans (congrArg Prod.snd sz)
    rw [s1, s2]
    refine Eq.trans (arrayPlanB_named
      (⟨proofSizedFull.codes, proofSizedFull.request, layoutFull,
        Z.made.p.built.links.map (·.arrayOf)⟩ : Sent) (fun _ => 0) (2 * par.g) _
      (fun (e : Empty) _ _ => e.elim) (fun _ => (false, 0, 0)) _ _ _ _ _ _ _ hname) ?_
    exact (arrayArm_free _ _ _ _ _ _ _ _ #[] _ _ _ _ (fun _ => #[]) _ _ _ _ (fun _ => []) _ _ _ _
      _ _).trans (List.all_eq_true.1 h' μ.val (List.mem_range.2 μ9))
  · -- ell
    have h8 := List.all_eq_true.1 ell_written par.g hmem
    have e : maskEllP (pin0 (sentOf (k4DataWide Dm (eAll Z cF L) mgBase))
        ((k4DataWide Dm (eAll Z cF L) mgBase).L3.seat (2 * par.g) false) (2 * par.g)) = 8192 := by
      rw [hD]
      exact (maskEllP_free _ _ _ _ #[] _ _ (seatW (2 * par.g))).trans (eq_of_beq h8)
    rw [e]
    exact hns

end

/-! ## At the closed constant -/

variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- The three equations at the closed constant. -/
theorem pinsAt_const (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r Zp Np cF x₀) :
    K4PinsAt (Z := Zp) hA.𝔇 cF := ⟨rfl, rfl, rfl⟩

/-- **THE FIELD nextFits OF `K4Cond`, from the written values and the written cut.** -/
theorem nextFits_paid (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (W : WrittenAt Zp)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    ∀ g, g < 12 →
      Rec.nextFitsB (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).cs
      (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).d12.M
      ((k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.msgsAt
      (flatPlacesOf linksFull true)[28 * g + 4 + 1]?)
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.indexNo
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).free0
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).fvs (2 * g) = true := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  exact fun g hg =>
    nextFits_at W hc (fvs_at_scope hA.scope hA.reads O) (pinsAt_const hA) L hg

/-- **THE FIELD pins OF `K4Cond`, from the written values and the written cut**, at the L that the
closed parameters' reader returns. -/
theorem pins_paid (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (hL : P5J.At.laid? Zp = some L) (W : WrittenAt Zp)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) :
    ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) →
    ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b → firstFastB Zp g = true →
      K4PinsTests hA.𝔇 (eAll Zp cF L) Zp (28 * g + 4) g (parOf x) := by
  intro Bs base O g hg x b h h1
  have hpub : OnBytes.Model.Verify.publicOf Zl.pol Zl.KL (some Zl.lay) = .ok Zp.p.X :=
    O.W ▸ O.public
  have H9 : XNine Zp.p.X :=
    xNine_of_laid hpub (Hd.core_of_scope hA.scope hA.reads hpub) W.layout hA.plan.laid
  have eg : (parOf x).g = g := h.hg
  subst eg
  have hG : Zp.p.X.G[(parOf x).g]? = some (parOf x).hp := O.W ▸ h.G
  exact tests_of_closed h1
    (closed_at W hc (fvs_at_scope hA.scope hA.reads O) (pinsAt_const hA) L
      (pinsFill_const OnBytes.secondHashFunction Zp Np cF (P5J.At.EAt Zl) hA.plan.shape Zl.lay hA.plan.laid
        hA.plan.hN hA.plan.hG x₀ OnBytes.Flat.numsFull.rows)
      hL H9 (namesTied_of_scope hA.scope hA.reads O) hg hG
      (slots_paid hA.scope hA.reads O W _ hg _ hG))

/-- **The two ends ARE the two fields**: Lean lays them into the structure. -/
theorem cond_with_paid (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid)
    (Pp : ProofFile.InstPub → Prop) (C : K4Cond hA L Pp) (hL : P5J.At.laid? Zp = some L)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) : K4Cond hA L Pp :=
  { C with
    nextFits := nextFits_paid hA L C.written hc
    pins := pins_paid hA L hL C.written hc }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laid_written
#print axioms OnBytes.Road.K4.nextFits_at
#print axioms OnBytes.Road.K4.closed_at
#print axioms OnBytes.Road.K4.pinsAt_const
#print axioms OnBytes.Road.K4.nextFits_paid
#print axioms OnBytes.Road.K4.pins_paid
#print axioms OnBytes.Road.K4.cond_with_paid
