-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/ForTheRule.lean: what the rule that joins the kinds' rows reads of the kind K11, beside
AtFullSide/K11/LendsAtTheTerm.lean.

  k11_ground             at a return of the maker the public part and the ground are the head's
  k11Rows                the kind's rows at the base prover, as one term of the public part and the
                         ground
  k11_sims_public        the row's simulators are made of the plan's numbers alone
  k11Rows_at_base        the sides of the kind at the base prover are those rows' sides, as a list
  k11MaskOwner, k11IndexOwner, k11_owners
                         the two owners of the runs that the kind's second part spends
  K11OwnerFresh          owed beside: the equation of Good.fresh at an owner, at the kind's part
  k11OwnerFresh_of_good  the owner's Good gives that equation
  K11NumberIsBook        owed beside: that the slots the verifier counts hold the coins that the
                         book lends; it is K11ScriptMsg under the name that the rule reads

Limits. K11OwnerFresh and K11NumberIsBook are statements: this file proves neither at any owner or
script. Nothing here adds a premise to the five debts.
-/
import AtFullSide.K11.LendsAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K11
open AtPublicFiles.AtFiles.HonestTerm.K11Term

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **At a return of the maker, at any filling, the public part and the ground are the head's.** -/
theorem k11_ground {W₀ Rc Tr X₀ X : Type} {Pf : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    A.Z = Zp ∧ A.G = Bs.G₀ := by
  obtain ⟨e1, eG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  exact ⟨eZ, Option.some.inj (hG.symm.trans (IM.base_made hB).2.2.1)⟩

/-- **The kind's rows at the base prover, as one term.** No index, randomness, trace or coin is
among its arguments: I is a reader. -/
def k11Rows {W₀ : Type} (I : WiderIn W₀) :
    ProofFile.Pub → ProofFile.Ground → List (Unlettered (Input W₀) (Input W₀) Unit ProofFile.Inst) :=
  fun Zq G => [k11Row (I.weights Zq) Zq G]

/-- The row's simulators are made of the plan's numbers alone. -/
theorem k11_sims_public {W₀ Rc Tr X : Type} (weights : W₀ → Weights) (Zq : ProofFile.Pub)
    (G : ProofFile.Ground) :
    (k11Row (Rc := Rc) (Tr := Tr) (X := X) weights Zq G).row.map (·.2) =
      headMergeSims (_root_.K11.parOf Zq G) :=
  rfl

/-- **The sides of the kind at the base prover are the rows' sides, as a list, at the return's
public part and ground.** -/
theorem k11Rows_at_base {W₀ : Type} {I : WiderIn W₀} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hM : baseMaker I Z = .ok A)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (A.H.first.filter fun g => g.place.kind == KindName.K11) =
      (k11Rows I A.Z A.G).map (·.half) := by
  obtain ⟨eZ, eG⟩ := k11_ground h hM hB
  rw [eZ, eG]
  exact k11_filter_base h hM hB

/-- The owner of the first run that the kind's second part spends: the switch into link 24. -/
def k11MaskOwner : Addr := ⟨⟨1, some 24, 2, KindName.K2⟩, 0⟩

/-- The owner of the second run that the kind's second part spends: the opening's sending. -/
def k11IndexOwner : Addr := ⟨⟨1, some 0, 1, KindName.K1⟩, 0⟩

/-- **At the book of a return, at any filling, the kind's second part spends these two runs.** -/
theorem k11_owners {W₀ Rc Tr X₀ X : Type} {Pf : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL Pf = .ok A) :
    entryRunIs (spentE A.B ⟨IM.k11Place, 1⟩) 0 k11MaskOwner ⟨23217, 3970⟩ ⟨0, 38⟩ = true ∧
      entryRunIs (spentE A.B ⟨IM.k11Place, 1⟩) 1 k11IndexOwner ⟨25848, 8659⟩ ⟨0, 1⟩ = true := by
  obtain ⟨B, -, hW, -, -, hall⟩ := AtFullSide.K14.makers_book_one h
  obtain ⟨eB, -⟩ := hall _ _ _ _ _ Pf A hA
  obtain ⟨t1, t2, -⟩ := tests_at_book h hW
  rw [eB]
  exact ⟨t1, t2⟩

section Owed
variable {S Cl V W X Pb : Type}

/-- Given by hand: among all that this file imports, the search for these runs out of its budget. -/
local instance (priority := high) (d : Due) : Nonempty (Cs d) := ⟨default⟩

local instance (priority := high) (ds : List (String × Due)) (d : Due) :
    Nonempty (CsAll ds × Cs d) := ⟨(default, default)⟩

set_option maxHeartbeats 2000000 in
/-- **Owed beside, by each owner**: the equation of Good.fresh at the owner's part number n, at the
kind's spending part. σ: the owner's side, bud its own. Stated here, proved by the owner's kind. -/
def K11OwnerFresh (Bk : ProverCoinCounts) (ord : List Place) (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (n : Nat) : Prop :=
  ∀ u ∈ σ.members, u.number = n → ∀ (sp : CsAll u.part.spends) (ca : CsAll u.part.carries)
    (m : ProofFile.Honest.Mid W X) (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ ⟨IM.k11Place, 1⟩),
          σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ ⟨IM.k11Place, 1⟩))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ ⟨IM.k11Place, 1⟩).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ ⟨IM.k11Place, 1⟩))

/-- The owner's Good gives that equation. -/
theorem k11OwnerFresh_of_good {Bk : ProverCoinCounts} {ord : List Place} {φ : Face V W Pb}
    {σ : Side S Cl V W X Pb} {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W X → Env → Prop}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) (n : Nat) :
    K11OwnerFresh Bk ord φ σ bud n :=
  fun u hu _ sp ca m ds asks h1 h2 h3 => g.fresh u hu _ sp ca m ds asks h1 h2 h3

end Owed

/-- **Owed beside, for acceptance and for the On behind**: that under the slots which the verifier
counts the segment's mask row holds the first run's coins (maskTie), and that at the entry which the
ledger takes the index-mask message holds the second run's coin (indexTie). It is K11ScriptMsg. -/
abbrev K11NumberIsBook := @K11ScriptMsg

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_ground
#print axioms AtFullSide.K11.k11_sims_public
#print axioms AtFullSide.K11.k11Rows_at_base
#print axioms AtFullSide.K11.k11_owners
#print axioms AtFullSide.K11.k11OwnerFresh_of_good
