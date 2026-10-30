-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroK2.lean: THE CODE SWITCH (K2) STEPS IN `KeepsZero`; THE HEAD's LINK's MAKER, UNDER
"THE PLAN's ROWS BEGIN AT COLUMN 0" IN THE PLACE OF THE LIBRARY's EQUATION ON THE LINK's LOOKS (THAT
STATEMENT AND PROOF ARE TURNED BY HAND). MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksK2.lean, WITH THE ROWS' FIRST COLUMNS (`l0s`,
Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE OF
KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under a
new name; the others are called where they lie. None of the library's goals. No prover stands in it;
nothing on completeness, soundness or hiding.

  `k2_kz_decide`, `k2_kz`, **`placeH2_makesZ`**   there: k2_keeps, k2_steps, placeH2_makes
Limits. THE DECISIONS ALONE. The maker's premise, `AllZero` of the plan's ledger, is shown of no
plan here. Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroMakers
import Johnson.Desc.First.Link.Law.LooksK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

theorem k2_kz_decide {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {s' : S}
    (h : decideWith snd p s rs gs = .ok s') : KeepsZero s s' :=
  kzL_same (fork_kept h) (by rw [k2_link_kept h])

/-- **K2: the code switch.** -/
theorem k2_kz (p : P2) :
    (codeSwitchKind p : Block S Unit).Steps KeepsZero := by
  intro s rs gs s' h
  exact k2_kz_decide (show decideWith _ p s rs gs = .ok s' from h)

/-- **THE HEAD's LINK's MAKER: the whole place «H:2».** -/
theorem placeH2_makesZ (p : P2) (n : String) (P : HeadPar)
    (hz : AllZero P.X.Fp) :
    ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).Steps KeepsZero := by
  intro s rs gs s' h
  exact kz_laid { trees := P.X.Fp.trees } P.hp.ns (placeH2_fork h)
    (allZero_trees (F := P.X.Fp) rfl hz)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.k2_kz_decide
#print axioms VerifiableInference.Desc.LinkJoin.k2_kz
#print axioms VerifiableInference.Desc.LinkJoin.placeH2_makesZ
