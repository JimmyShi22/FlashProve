-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SomeAtName.lean: THE TWO TESTS callsSomeB AND digSomeB OF
At.k3SeatsB, AT ALL WRITTEN SEGMENTS, IN THE LETTER OF THE JOIN OF THE NAMED CONDITIONS: under
«laid», from the one named condition on the second reading of the three public files
(P5J.rowsRead, Johnson/Goal/Skeleton/RowsRead.lean) and two named premises. NO BLOCK
IMPORTS THIS FILE.
  rows_at        under «laid»: the rows that the closed letters read (P5T.rowsAt? Zp.pol Z.lay
                 Zp.KL) are the rows that the maker returns at Z's three files (ProofFile.Law.pub_files)
  k3Some_of_rows LaidAt … Zp Np cF · rowsRead Z · hSh · A₁ · A₂ ⟹ ((List.range At.links.length).all
  fun l => At.callsSomeB Zp Z.lay l && At.digSomeB Zp Z.lay l) = true: the premise h2 of
  k3SeatsB_of_two, to the letter
THE PREMISES THAT STAY, BY NAME: rowsRead Z (a test with code on the three public files: the maker
of the rows returns, and one shape has one radius over the first chain's rows: NOT ASKED BY
verify()) · hSh : P1Opts.RowsShaped at whatever rows the maker returns and the plan's seats · A₁ |
A₂ : at each written segment each place of the calls' | the digits' list has a seat of the plan
with a sample, with the list's shape there and the seat that seat3At names: ON Zp ALONE BUT FOR
THE LISTS' RADII, WHICH THEY DO NOT READ.
LIMITS. None of the premises is shown here. No soundness is claimed.
-/
import Johnson.Top.H0.Opts.SomeAtRows
import Johnson.Goal.Skeleton.RowsRead
import Johnson.P5J.LaidOpens
import Johnson.Desc.ProofFile.Law.CarryAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open VerifiableInference.Desc (Chain)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

theorem rows_at (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {R : List Johnson.G.SendRow} (hrows : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) :
    P5T.rowsAt? Zp.pol Z.lay Zp.KL = some R := by
  obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files L.pub
  unfold P5T.rowsAt?
  rw [e1, e2, hrows]
  rfl

theorem k3Some_of_rows (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hrr : P5J.rowsRead Z)
    (hSh : ∀ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R →
      RowsShaped R (P5J.At.pseats Zp))
    (A₁ : ∀ l, l < P5J.At.links.length → ∀ i : Fin (P5J.At.callsListAt Zp Z.lay l).length,
      ∃ p ∈ P5J.At.pseats Zp, p.smpd = true ∧
        p.shape = ((P5J.At.callsListAt Zp Z.lay l).get i).1 ∧
        p.seat = P5J.At.seat3At Zp l false i.1)
    (A₂ : ∀ l, l < P5J.At.links.length → ∀ i : Fin (P5J.At.digListAt Zp Z.lay l).length,
      ∃ p ∈ P5J.At.pseats Zp, p.smpd = true ∧
        p.shape = ((P5J.At.digListAt Zp Z.lay l).get i).1 ∧
        p.seat = P5J.At.seat3At Zp l true i.1) :
    ((List.range P5J.At.links.length).all fun l =>
      P5J.At.callsSomeB Zp Z.lay l && P5J.At.digSomeB Zp Z.lay l) = true := by
  obtain ⟨R, hR, h1⟩ := P5J.rowsRead_iff.1 hrr
  have hr := rows_at L hR
  refine List.all_eq_true.2 fun l hl => ?_
  have hl' := List.mem_range.1 hl
  rw [Bool.and_eq_true]
  exact ⟨callsSome_of Zp Z.lay hr h1 (hSh R hR) l (A₁ l hl'),
    digSome_of Zp Z.lay hr h1 (hSh R hR) l (A₂ l hl')⟩

end P1Opts

#print axioms P1Opts.rows_at
#print axioms P1Opts.k3Some_of_rows
