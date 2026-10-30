-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormRows.lean.
WHAT IT DOES NOT SHOW. THAT Norm.lean's WHOLE HEARING FALLS APART INTO THE TWO STRETCHES at which
the level and the sumcheck are heard here: each stretch's hearing is a premise, with the ledger in
front of it. That the world is the ledger's; that the three reads are true; that the 26 forms are 0;
that no bad element was drawn: premises: other kinds' laws. That the letters which stand first here
are fixed IN TIME before the draws: the order of the letters alone. TWO OF THE BAD EVENTS (the
bridge's BadG, BadO) READ THE WORLD, at the numbers of the nine hidden sums and of the seven hidden
products: these are sent in the rounds in front of gam and of om; that the world holds the ledger's
values at these numbers too is not asked here: whoever lays the world pays it. The bad events are
counted where they are defined: the two rules' lists by their lengths; the bridge's three sets by
its own counts.
WHAT IT IS. K6's JOINT ON THE PER-POSITION BRIDGE OF A NORM, WHOLE, OVER THE KIND's OWN TEXT: all 26
forms of Norm.forms worth 0 in a world that holds the hidden scalars, three true reads, and none of
five bad events: THE CLAUSE rows OF CellRelN: at every position's corner the row's 17 forms are 0.
The bridge's three premises are paid by Law/NormJoint.lean (Lines, Products) and
Law/NormSquares.lean (Squares); its fourth bad event (the point over the norms' numbers) cannot
happen at one norm.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormSquares

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World Fork)
open Norm (lt ls d lPd T S2)
open Came (val sEndG sEndL)
open D6.Bridge (Data)

variable [Sizes] [Policy] [Request] [Token]

/-- At one norm there is no bad point over the norms' numbers. -/
theorem not_badI (c : NCells) (u : Nat → K) (Wt : Nat → K) (g : K) (rho : Fin 0 → K) :
    ¬ (dataOf c).BadI u Wt g rho := by
  intro hb
  obtain ⟨⟨i, hi, hne⟩, hs⟩ := hb
  have hi' : i < 1 := hi
  obtain rfl : i = 0 := by omega
  have h : (Finset.range 1).sum (fun i => Blocks.eqN 0 0 (Blocks.nat rho) i *
      (dataOf c).dWg u Wt g i) = 0 := hs
  have e1 : Blocks.eqN 0 0 (Blocks.nat rho) 0 = (1 : K) := by simp [Blocks.eqN]
  rw [Finset.sum_range_one, e1, one_mul] at h
  exact hne h

section Whole
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- The three reads that the norm's 26 forms spend, each below the length spent, are true. -/
structure NormReads (W : World K) (c : NCells) : Prop where
  atPV : ∀ j, j < NR → val W (Norm.digit .rowsAtPV 0 j) =
    Blocks.ext lt (fun t => dK c t j) (ptK Norm.pV)
  atProducts : ∀ j, j < NR → val W (Norm.digit .rowsAtProducts 0 j) =
    Blocks.ext lt (fun t => dK c t j) (ptK Norm.products.r)
  atSquares : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtSquares i) =
    rd (readAtN c (.stream, Norm.Read.streams.weights) i)

/-- **K6's JOINT, WHOLE.** FS, FP: the ledgers in front of the level and of the sumcheck; tS, tP:
their stretches of rounds; GS, GP: the ledgers behind. -/
theorem norm_rows (c : NCells) (mask : Nat → E) (FS FP : Fork) (Tt : E) (Cv : K)
    (hWS : WellLaid FS) (hWP : WellLaid FP) (hz : (Norm.pV).size = lt) (hls : ls ≤ lPd)
    (hdS : S2 ∣ d) {GS GP : Fork} {tS tP : List Fmt.RoundView} (W : World K)
    (hsS : ∀ j, FS.next ≤ j → j < sEndL (zS Norm.pV) FS + 2 → W.slot j = rd (hidden GS mask j))
    (hsP : ∀ j, FP.next ≤ j → j < sEndG Norm.pV 4 FP + 4 → W.slot j = rd (hidden GP mask j))
    (hcS : Canonical tS) (hcP : Canonical tP)
    (hlev : level (zS Norm.pV) (Norm.squaresStart Norm.W Norm.gam #[]) FS tS =
      some (Norm.squares, GS, []))
    (hsum : sumcheck Norm.pV 4 FP tP = some (Norm.products, GP, []))
    (hT : FS.publicPart (Norm.squaresStart Norm.W Norm.gam #[]) = some Tt)
    (hC : val W (Norm.squaresStart Norm.W Norm.gam #[]) = Cv)
    (hreads : NormReads W c) (hforms : ∀ f, f ∈ Norm.forms → val W f = 0)
    (hbS : NoBad (squaresRule c mask FS Norm.pV Norm.gam Tt Cv) tS)
    (hbP : NoBad (productsRule c mask FP Norm.pV Norm.om) tP)
    (hP : ¬ (dataOf c).BadP (tupK Norm.pV))
    (hG : ¬ (dataOf c).BadG (Blocks.nat (tupK Norm.pV)) (WtOf W) (rd Norm.gam))
    (hO : ¬ (dataOf c).BadO (Blocks.nat (tupK Norm.pV)) (PtOf W) (rd Norm.om)) :
    ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  have fS : ∀ f, f ∈ Norm.squareForms → val W f = 0 := fun f hf =>
    hforms f (List.mem_append_left _ (List.mem_append_left _ hf))
  have fP : ∀ f, f ∈ Norm.productForms → val W f = 0 := fun f hf =>
    hforms f (List.mem_append_left _ (List.mem_append_right _ hf))
  have fR : ∀ f, f ∈ Norm.rowForms → val W f = 0 := fun f hf =>
    hforms f (List.mem_append_right _ hf)
  exact norm_joint c (tupK Norm.pV) (WtOf W) (rd Norm.gam) (PtOf W) (rd Norm.om)
    (lines_at_tuple c _ _ _ (lines_of_world c W hreads.atPV fR))
    (squares_of_eq c _ _ _ _ ((squares_eq c mask FS Tt Cv hWS hz hls hdS W hsS hcS hlev hT hC
      hreads.atSquares fS hbS).trans (ext_congr_pt lt _ fun t ht => (nat_tupK Norm.pV ht).symm)))
    (products_at_tuple c _ _ _ (products_text c mask FP hWP hz W hsP hcP hsum hreads.atProducts fP
      hbP))
    hP hG (not_badI c _ _ _ _) hO

end Whole

end VerifiableInference.Desc.Kinds.Head.Law
