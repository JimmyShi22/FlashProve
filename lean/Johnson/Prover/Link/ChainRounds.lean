-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainRounds.lean: Block.step's first test, roundsFit (Johnson/Desc/Block.lean),
AT THE ROUNDS OF THE COPY's FILE's FRAME (rvOf, Johnson/Prover/Link/LinkFrame.lean), at every
verifier's randomness; and roundsFit CUT IN TWO: what a round draws, and the items that it shows.
Statements and proofs.

  drawn_rvOf          the frame's rounds show the draws
  fitsDrawn_run       AT EVERY rho: what each round of the protocol draws meets the library's six
                      clauses (H2K.Fit.FitsDrawn, Johnson/Desc/K12/Law/FitWritten.lean)
  roundFits_of_drawn  THE CUT: these six and the items' clause give the library's seven (RoundFits,
                      Johnson/Top/H0/StepLaws/RoundsFit.lean), AT ANY ITEMS
  roundFits_zip, roundFits_run   so, at every rho, round by round: whoever shows the declared items
                      fits
  roundFits_rvOf, roundsFit_rvOf   the frame's rounds fit the declared rounds, at every rho AND
                      EVERY next (what does not fit is sent as typed zeros: layP is total)

By: fitsDrawn_ckP, gots_items, zip_all_of_forall₂ (FitWritten.lean); roundsFit_iff (RoundsFit.lean).

Limits. The tie of the protocol's rounds' data to the declared rounds (IsOf2, round by round) and
"no entry asks more elements other than 0 than elements" are premises: closed facts on public data.
At the library's challenge kit ckP .two alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainDefs
import Johnson.Desc.K12.Law.FitWritten
import Johnson.Top.H0.StepLaws.RoundsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD drawnSL uL)
open _root_.Iop (Rho)

/-- The frame's rounds show the draws. -/
theorem drawn_rvOf (next : ℕ → List Fmt.Drawn → MsgV) : ∀ (ds : List RD) (i : ℕ)
    (hist Ds : List Fmt.Drawn), Ds.length = ds.length →
    (rvOf ds i hist next Ds).map (·.drawn) = Ds
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, h => by cases h
  | _ :: _, _, _, [], h => by cases h
  | d :: ds, i, hist, D :: Ds, h => by
    show D :: (rvOf ds (i + 1) (hist ++ [D]) next Ds).map (·.drawn) = D :: Ds
    rw [drawn_rvOf next ds _ _ Ds (Nat.succ.inj h)]

/-- **At every rho: what each round draws meets the library's six clauses.** -/
theorem fitsDrawn_run : ∀ (ds : List RD) (ρ : Rho (uL (ckP .two) ds)),
    List.Forall₂ (fun (w : RD) (D : Fmt.Drawn) => H2K.Fit.FitsDrawn w.entry w.kind D) ds
      (drawnSL (ckP .two) ds ρ)
  | [], _ => List.Forall₂.nil
  | _ :: ds, (_, ρ) => List.Forall₂.cons (H2K.Fit.fitsDrawn_ckP _ _ _) (fitsDrawn_run ds ρ)

/-- **roundsFit cut in two.** -/
theorem roundFits_of_drawn (d : Fmt.DeclaredRound) (k : Fmt.Kind) (D : Fmt.Drawn) (vals : List Fmt.ItemValue)
    (hk : Fmt.kindOf d.entry.name = some k) (hz : d.entry.drawNZ ≤ d.entry.drawE)
    (F : H2K.Fit.FitsDrawn d.entry k D) (hi : vals.map itemOf = d.items.filter (· != .root)) :
    RoundFits d ⟨vals, D⟩ :=
  { items := hi, elems := F.elems hz, count := F.poss, trits := F.trits, below := F.below
    three := F.signs
    nz := by
      unfold drawsMarkedNonzeroHaveNonzeroWords
      rw [hk]
      exact H2K.Fit.zip_all_of_forall₂ _ _ F.nz }

/-- Round by round, from the two ties. -/
theorem roundFits_zip : ∀ (decls : List Fmt.DeclaredRound) (ds : List RD) (Ds : List Fmt.Drawn),
    List.Forall₂ IsOf2 decls ds → (∀ d ∈ decls, d.entry.drawNZ ≤ d.entry.drawE) →
    List.Forall₂ (fun (w : RD) (D : Fmt.Drawn) => H2K.Fit.FitsDrawn w.entry w.kind D) ds Ds →
    List.Forall₂ (fun (d : Fmt.DeclaredRound) (D : Fmt.Drawn) => ∀ vals : List Fmt.ItemValue,
      vals.map itemOf = d.items.filter (· != .root) → RoundFits d ⟨vals, D⟩) decls Ds
  | [], [], [], _, _, _ => List.Forall₂.nil
  | d :: decls, w :: ds, D :: Ds, h1, hz, h2 => by
    cases h1 with
    | cons a1 b1 =>
      cases h2 with
      | cons a2 b2 =>
        obtain ⟨e1, -, e3⟩ := a1
        rw [e1] at a2
        exact List.Forall₂.cons
          (fun vals hi => roundFits_of_drawn d w.kind D vals e3 (hz d List.mem_cons_self) a2 hi)
          (roundFits_zip decls ds Ds b1 (fun x hx => hz x (List.mem_cons_of_mem _ hx)) b2)

/-- **At every rho, round by round: whoever shows the declared items fits.** -/
theorem roundFits_run (decls : List Fmt.DeclaredRound) (ds : List RD)
    (h : List.Forall₂ IsOf2 decls ds) (hz : ∀ d ∈ decls, d.entry.drawNZ ≤ d.entry.drawE)
    (ρ : Rho (uL (ckP .two) ds)) :
    List.Forall₂ (fun (d : Fmt.DeclaredRound) (D : Fmt.Drawn) => ∀ vals : List Fmt.ItemValue,
      vals.map itemOf = d.items.filter (· != .root) → RoundFits d ⟨vals, D⟩) decls
      (drawnSL (ckP .two) ds ρ) :=
  roundFits_zip decls ds _ h hz (fitsDrawn_run ds ρ)

/-- The frame's rounds, round by round. -/
theorem roundFits_rvOf (next : ℕ → List Fmt.Drawn → MsgV) :
    ∀ (decls : List Fmt.DeclaredRound) (ds : List RD) (Ds : List Fmt.Drawn) (i : ℕ)
      (hist : List Fmt.Drawn), List.Forall₂ IsOf2 decls ds →
    List.Forall₂ (fun (d : Fmt.DeclaredRound) (D : Fmt.Drawn) => ∀ vals : List Fmt.ItemValue,
      vals.map itemOf = d.items.filter (· != .root) → RoundFits d ⟨vals, D⟩) decls Ds →
    List.Forall₂ RoundFits decls (rvOf ds i hist next Ds)
  | [], [], [], _, _, _, _ => List.Forall₂.nil
  | d :: decls, w :: ds, D :: Ds, i, hist, h1, h2 => by
    cases h1 with
    | cons a1 b1 =>
      cases h2 with
      | cons a2 b2 =>
        refine List.Forall₂.cons (a2 _ ?_) (roundFits_rvOf next decls ds Ds _ _ b1 b2)
        rw [H2K.Fit.gots_items, a1.2.1]

/-- **The frame's rounds fit the declared rounds**, at every rho and every next. -/
theorem roundsFit_rvOf (next : ℕ → List Fmt.Drawn → MsgV) (decls : List Fmt.DeclaredRound)
    (ds : List RD) (h : List.Forall₂ IsOf2 decls ds)
    (hz : ∀ d ∈ decls, d.entry.drawNZ ≤ d.entry.drawE) (i : ℕ) (hist : List Fmt.Drawn)
    (ρ : Rho (uL (ckP .two) ds)) :
    roundsFit decls (rvOf ds i hist next (drawnSL (ckP .two) ds ρ)) = true :=
  (roundsFit_iff _ _).2 (roundFits_rvOf next decls ds _ i hist h (roundFits_run decls ds h hz ρ))

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.drawn_rvOf
#print axioms Johnson.Prover.Link.fitsDrawn_run
#print axioms Johnson.Prover.Link.roundFits_of_drawn
#print axioms Johnson.Prover.Link.roundFits_zip
#print axioms Johnson.Prover.Link.roundFits_run
#print axioms Johnson.Prover.Link.roundFits_rvOf
#print axioms Johnson.Prover.Link.roundsFit_rvOf
