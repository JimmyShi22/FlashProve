-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TerminalLaws.lean: laws of the maker of OnBytes/Maker/Terminal.lean, which lays the
protocol of a description with two stored tables (`skeletonOverBothExternalStrings`, Run/PlanQX.lean) out as an interactive
oracle reduction to the trivial statement (`IOR`, Ior/Ior.lean) with an instance.

  `iorX_shape`, `iorX_blinded`, `iorX_extReads`, `iorX_reads`, `iorX_accept`
        the protocol of the reduction (`IOR.toInteractiveOracleProof`) has, at an instance x, the shape, the
        blinding, the reads and the decision of `skeletonOverBothExternalStrings` at the decision `dec x`
  `iorX_toProto_fields`, `iorX_toProto`
        the same as one equation of protocols: at any type of instances; at the one-point instance
  `iorX_isLocal`   the reduction is local (`IOR.IsLocal`), from `psofX_local`
  `iorX_local`     so its protocol is local (`InteractiveOracleProof.IsLocal`)
  `iorX_tied`      nothing is tied (`IOR.Tied`)
  `iorX_point`     every round's oracle is a string (`Shape.IsPoint`)
  `iorX_card`, `iorX_cntPar`, `iorX_cntCh`
        the verifier reads at most as many positions of the stored tables as the description's
        openings count, if the chain's own trees have numbers below 2^16
  `iorS_accept`, `iorS_toProto_fields`, `iorS_isLocal`, `iorS_tied`, `iorS_point`
        the like for a description without stored tables (`PSof`, Run/PlanQS.lean)

Not claimed. Nothing on soundness, and nothing on an honest prover.

-/
import OnBytes.Maker.Terminal
import Run.PlanQXLawsProofs
import Run.PlanQSLaws
import Ior.Batch

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Iop

theorem isSome_ite (b : Bool) : (if b = true then some () else none).isSome = b := by
  cases b <;> rfl

section
variable {Xi : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : Xi → View → Bool)

theorem iorX_shape (x : Xi) :
    (iorX C ds a xs dec).toInteractiveOracleProof.shape = (skeletonOverBothExternalStrings C ds a xs (dec x)).up.loc.shape := rfl

theorem iorX_blinded (x : Xi) :
    (iorX C ds a xs dec).toInteractiveOracleProof.blinded = (skeletonOverBothExternalStrings C ds a xs (dec x)).up.loc.blinded := rfl

theorem iorX_extReads (x : Xi) :
    (iorX C ds a xs dec).toInteractiveOracleProof.extReads x = (skeletonOverBothExternalStrings C ds a xs (dec x)).up.loc.extReads () := rfl

theorem iorX_reads (x : Xi) :
    (iorX C ds a xs dec).toInteractiveOracleProof.reads x = (skeletonOverBothExternalStrings C ds a xs (dec x)).up.loc.reads () := rfl

/-- The decision at the instance x is `skeletonOverBothExternalStrings`'s at the decision `dec x`. -/
theorem iorX_accept (x : Xi) :
    (iorX C ds a xs dec).toInteractiveOracleProof.accept x = (skeletonOverBothExternalStrings C ds a xs (dec x)).up.loc.accept () := by
  funext y τ
  exact isSome_ite _

/-- **The reduction is local.** -/
theorem iorX_isLocal : (iorX C ds a xs dec).IsLocal where
  out := fun x y y' τ τ' hρ hp hE hO => by
    have h := psofX_local C ds a xs (dec x) () y y' τ τ' hρ hp hE hO
    show (if (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ = true then some () else none) =
      if (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y' τ' = true then some () else none
    rw [show (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ = (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y' τ'
      from h]
  imp := fun _ _ _ _ q => q.elim

/-- Its protocol is local. -/
theorem iorX_local : (iorX C ds a xs dec).toInteractiveOracleProof.IsLocal := fun x y y' τ τ' hρ hp hE hO => by
  rw [iorX_accept]
  exact psofX_local C ds a xs (dec x) () y y' τ τ' hρ hp hE hO

/-- Nothing is tied to a position of the prover's oracles. -/
theorem iorX_tied : (iorX C ds a xs dec).Tied := fun _ _ _ => Finset.empty_subset _

/-- The positions read in the stored tables are no more than the openings count. -/
theorem iorX_card (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (ρ : Rho (iorX C ds a xs dec).shape) :
    ((iorX C ds a xs dec).extReads ρ).card ≤ (xs.map (·.count)).sum :=
  (List.toFinset_card_le _).trans
    ((List.length_filterMap_le _ _).trans (xWanted_len a ds xs _ hown))

open Classical in
theorem iorX_cntPar (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (ρ : Rho (iorX C ds a xs dec).shape) :
    (((iorX C ds a xs dec).extReads ρ).filter fun p => p.isLeft).card ≤ (xs.map (·.count)).sum :=
  (Finset.card_filter_le _ _).trans (iorX_card C ds a xs dec hown ρ)

open Classical in
theorem iorX_cntCh (hown : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (ρ : Rho (iorX C ds a xs dec).shape) :
    (((iorX C ds a xs dec).extReads ρ).filter fun p => p.isRight).card ≤ (xs.map (·.count)).sum :=
  (Finset.card_filter_le _ _).trans (iorX_card C ds a xs dec hown ρ)

end

/-- **The protocol of the reduction, written out**: `skeletonOverBothExternalStrings`'s fields, with the instance handed to
the decision. A skeleton with an instance whose fields are these has this protocol by definition. -/
theorem iorX_toProto_fields {Xi : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : Xi → View → Bool) :
    (iorX C ds a xs dec).toInteractiveOracleProof =
      { shape := Twin.up (SOf C ds)
        blinded := fun _ => true
        extReads := fun _ ρ => (skeletonOverBothExternalStrings C ds a xs fun _ => true).extReads () ρ
        reads := fun _ ρ pl => (skeletonOverBothExternalStrings C ds a xs fun _ => true).reads () ρ pl
        accept := fun x y τ => (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ } := by
  have h : (iorX C ds a xs dec).toInteractiveOracleProof.accept =
      fun x y τ => (skeletonOverBothExternalStrings C ds a xs (dec x)).accept () y τ := by
    funext x
    exact iorX_accept C ds a xs dec x
  show (⟨_, _, _, _, (iorX C ds a xs dec).toInteractiveOracleProof.accept⟩ : InteractiveOracleProof Xi (twoExternalStrings (2 ^ a) SgX)) = _
  rw [h]
  rfl

/-- At the one-point instance the protocol of the reduction is `skeletonOverBothExternalStrings`'s own. -/
theorem iorX_toProto (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) (dec : View → Bool) :
    (iorX (Xi := Unit) C ds a xs fun _ => dec).toInteractiveOracleProof = (skeletonOverBothExternalStrings C ds a xs dec).up.loc := by
  have h : (iorX (Xi := Unit) C ds a xs fun _ => dec).toInteractiveOracleProof.accept =
      (skeletonOverBothExternalStrings C ds a xs dec).up.loc.accept := by
    funext x
    exact iorX_accept C ds a xs (fun _ : Unit => dec) x
  show (⟨_, _, _, _, (iorX (Xi := Unit) C ds a xs fun _ => dec).toInteractiveOracleProof.accept⟩ :
    InteractiveOracleProof Unit (twoExternalStrings (2 ^ a) SgX)) = _
  rw [h]
  rfl

/-! ## The same for a description without stored tables -/

section
variable {Xi : Type} (C : CK) (ds : List RD) (dec : Xi → View → Bool)

/-- The decision at the instance x is `PSof`'s at the decision `dec x`. -/
theorem iorS_accept (x : Xi) :
    (iorS C ds dec).toInteractiveOracleProof.accept x = (PSof C ds (dec x)).up.loc.accept () := by
  funext y τ
  exact isSome_ite _

/-- The protocol of the reduction, written out. -/
theorem iorS_toProto_fields :
    (iorS C ds dec).toInteractiveOracleProof =
      { shape := Twin.up (SOf C ds)
        blinded := fun _ => true
        extReads := fun _ _ => ∅
        reads := fun _ ρ pl => (PSof C ds fun _ => true).reads () ρ pl
        accept := fun x y τ => (PSof C ds (dec x)).accept () y τ } := by
  have h : (iorS C ds dec).toInteractiveOracleProof.accept = fun x y τ => (PSof C ds (dec x)).accept () y τ := by
    funext x
    exact iorS_accept C ds dec x
  show (⟨_, _, _, _, (iorS C ds dec).toInteractiveOracleProof.accept⟩ : InteractiveOracleProof Xi E0) = _
  rw [h]
  rfl

/-- **The reduction is local.** -/
theorem iorS_isLocal : (iorS C ds dec).IsLocal where
  out := fun x y y' τ τ' hρ hp hE hO => by
    have h := psof_local C ds (dec x) () y y' τ τ' hρ hp hE hO
    show (if (PSof C ds (dec x)).accept () y τ = true then some () else none) =
      if (PSof C ds (dec x)).accept () y' τ' = true then some () else none
    rw [show (PSof C ds (dec x)).accept () y τ = (PSof C ds (dec x)).accept () y' τ' from h]
  imp := fun _ _ _ _ q => q.elim

theorem iorS_tied : (iorS C ds dec).Tied := fun _ _ _ => Finset.empty_subset _

end

/-- the oracle of a round is a string -/
def pointRound (C : CK) (d : RD) : (roundS C d).up.IsPoint :=
  ⟨inferInstanceAs (Fintype (Fin (posN d.tree))), inferInstanceAs (DecidableEq (Fin (posN d.tree))),
    fun f => f, fun _ _ => rfl, fun _ => rfl, fun _ _ => 0⟩

/-- the oracle of the round in front is a string without a position -/
def pointFront (C : CK) : (s0 C).up.IsPoint :=
  ⟨inferInstanceAs (Fintype Empty), inferInstanceAs (DecidableEq Empty), fun _ => (),
    fun _ p => p.elim, fun _ => rfl, fun p => p.elim⟩

def pointRounds (C : CK) : (ds : List RD) → (uL C ds).IsPoint
  | [] => ()
  | d :: ds => (pointRound C d, pointRounds C ds)

/-- **Every round's oracle is a string.** -/
theorem iorX_point {Xi : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : Xi → View → Bool) : Nonempty (iorX C ds a xs dec).shape.IsPoint :=
  ⟨(pointFront C, pointRounds C ds)⟩

theorem iorS_point {Xi : Type} (C : CK) (ds : List RD) (dec : Xi → View → Bool) :
    Nonempty (iorS C ds dec).shape.IsPoint :=
  ⟨(pointFront C, pointRounds C ds)⟩

end OnBytes.Maker
