-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkPasses.lean: AccLaw AT THE WRITTEN LINK IS NOT EMPTY OF CASES: there is a
transcript that meets its three premises (Johnson/Prover/Law/Defs.lean): all tests of work passed;
the strategy's own run but for nonces; its challenges outside the empty set. Statements and proofs.

  puts_self           a transcript is itself but for nonces
  passSL_some         at every list of written rounds some challenges pass all tests of work: any
                      challenges with the test bits set to 0
  accLaw_link_run     at every next: there are challenges at which THE STRATEGY's OWN RUN meets the
                      three
  accLaw_link_meets   so some transcript does

Limits. ONE transcript is shown, at test bits 0. Nothing on how many challenges pass (that hangs on
the rounds' test bits alone, on no strategy). The strategy sends the nonce 0 and does not search.
Nothing on soundness or any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.LinkFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes TypedOracleCompiler.Iop
open OnBytes.Flat (linkSkeletonOfRoundData linkProtocolOfRoundData)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO)
open TypedOracleCompiler.Run.PQ (RD uL passSL wiresSL)
open OnBytes.Prover (AccLaw Puts)
open Johnson.RunOne.StrictW (wqW)

theorem puts_self {lam K : ℕ} : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s),
    Puts s A W τ τ
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, _, τ) => ⟨rfl, rfl, Or.inl rfl, puts_self s A W τ⟩

theorem passSL_some (C : CK) : ∀ ds : List RD, ∃ ρ : Rho (uL C ds), passSL C ds ρ = true
  | [] => ⟨(), rfl⟩
  | d :: ds => by
      obtain ⟨ρ, h⟩ := passSL_some C ds
      obtain ⟨c, -⟩ := Classical.choice (instNonemptyRho (uL C (d :: ds)))
      refine ⟨(GChal.zero d.entry.work (GChal.old (b := d.entry.work) c), ρ), ?_⟩
      show (GChal.pass (b := d.entry.work) (GChal.zero d.entry.work _) && passSL C ds ρ) = true
      rw [GChal.pass_zero, h]
      rfl

variable (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

theorem accLaw_link_run (next : ℕ → List Fmt.Drawn → MsgV) :
    ∃ ρ : Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape,
      RoundsQueryLayout.pass (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (wqW C ds a xs dec K chal).sh ((stratOf C ds next).run ρ).1.rho = true ∧
      Puts (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (wqW C ds a xs dec K chal).sh
        ((stratOf C ds next).run ((stratOf C ds next).run ρ).1.rho).1
        ((stratOf C ds next).run ρ).1 ∧
      ((stratOf C ds next).run ρ).1.rho ∉
        (∅ : Set (Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)) := by
  obtain ⟨ρ, h⟩ := passSL_some C ds
  obtain ⟨c0, -⟩ := Classical.choice (instNonemptyRho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
  refine ⟨(c0, ρ), ?_, ?_, fun hx => hx⟩
  · rw [Strat.rho_run]
    refine Bool.and_eq_true_iff.2 ⟨rfl, ?_⟩
    exact (pass_wiresSL C K chal ds ρ).trans h
  · rw [Strat.rho_run]
    exact puts_self _ _ _ _

theorem accLaw_link_meets (next : ℕ → List Fmt.Drawn → MsgV) :
    ∃ τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape,
      RoundsQueryLayout.pass (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (wqW C ds a xs dec K chal).sh τ.rho = true ∧
      Puts (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
        (wqW C ds a xs dec K chal).sh ((stratOf C ds next).run τ.rho).1 τ ∧
      τ.rho ∉ (∅ : Set (Rho (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)) := by
  obtain ⟨ρ, h⟩ := accLaw_link_run C ds a xs dec K chal next
  exact ⟨_, h⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.puts_self
#print axioms Johnson.Prover.Link.passSL_some
#print axioms Johnson.Prover.Link.accLaw_link_run
#print axioms Johnson.Prover.Link.accLaw_link_meets
