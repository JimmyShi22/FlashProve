-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeTieMet.lean: THE CLAUSE "tie" OF LastFits
(Johnson/Goal/Conditions/HomeLast.lean) CAN BE MET AT FINITE COINS: shown, at written coins, a
written κOf and a written runs.

Why. A prover's coins (Honest.Coin, Iop/InteractiveOracleProof.lean) are a finite type, and there are infinitely many
byte strings: asked at all of them the tie could hold at no provers. So it is asked at run values of
the kind that occurs (Runs4.Fit, Johnson/Prover/Print/DrawOwes.lean). That this form can be met at
finite coins is the theorem here.

The coins. A string of 32 bytes is kept as a digest of 256 bits (Dig 256 := Fin 256 → Bool, a finite
type): forth by digS (Run/CodingFnThin.lean), back by digToBytes; back after forth gives the string
again at 32 bytes (digToBytes_digS, Run/ChainRow.lean). The key file's prover has the coins C_T ×
(Dig 256 × Dig 256), the link's C_L, the proof file's C_B × (Dig 256 × Dig 256), at any types C_T,
C_L, C_B.

Main names.
  CoinRuns C   the coins C × (Dig 256 × Dig 256). finite_coinRuns: finite, if C is.
  kapToy, runsToy   κOf and runs, written.
  tie_toy   THE STATEMENT: at every k and every fitting r: runsToy (kapToy (k, r)) = r.
  runsToy_T, runsToy_B   the first two values are read off the key file's prover's coin alone, the
    last two off the proof file's: as the laws lawT and lawB of LastFits force.

Limits. TYPES AND TWO MAPS: no prover is defined in this file: nothing on strategies, on acceptance,
on any other clause of LastFits: that LastFits has a member is not shown here (it has an idle one,
where read, scope and live hold, at an α of at least 3, where the bound says nothing: lastFits_idle,
Johnson/Goal/Conditions/HomeIdle.lean). Of Runs4.Fit the four sizes alone are spent. These coins
hold the zero digest too: there runsToy gives 32 zero bytes, which do not fit; the tie asks nothing
there. Finite is shown; a prover's coins bear Fintype and Nonempty.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.DrawOwes
import Run.ChainRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open Johnson.Prover.Print (Runs4)
open _root_.Iop (Dig)

/-- The coins of a prover that holds two run values. -/
abbrev CoinRuns (C : Type) : Type := C × (Dig 256 × Dig 256)

/-- They are finite, if C is. -/
theorem finite_coinRuns (C : Type) [Finite C] : Finite (CoinRuns C) := inferInstance

variable {CT CL CB : Type}

/-- κOf, written: the four run values are laid into the two provers' coins. -/
def kapToy (z : (CT × CL × CB) × Runs4) : CoinRuns CT × CL × CoinRuns CB :=
  ((z.1.1, (_root_.Run.digS z.2.1.1, _root_.Run.digS z.2.1.2)), z.1.2.1,
    (z.1.2.2, (_root_.Run.digS z.2.2.1, _root_.Run.digS z.2.2.2)))

/-- runs, written: they are read back. -/
def runsToy (κ : CoinRuns CT × CL × CoinRuns CB) : Runs4 :=
  ((_root_.Run.digToBytes κ.1.2.1, _root_.Run.digToBytes κ.1.2.2),
    (_root_.Run.digToBytes κ.2.2.2.1, _root_.Run.digToBytes κ.2.2.2.2))

/-- **THE TIE HOLDS.** -/
theorem tie_toy (k : CT × CL × CB) (r : Runs4) (h : Runs4.Fit r) :
    runsToy (kapToy (k, r)) = r := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := r
  show ((_root_.Run.digToBytes (_root_.Run.digS a), _root_.Run.digToBytes (_root_.Run.digS b)),
    (_root_.Run.digToBytes (_root_.Run.digS c), _root_.Run.digToBytes (_root_.Run.digS d))) = _
  rw [_root_.Run.digToBytes_digS a h.sizeT2, _root_.Run.digToBytes_digS b h.sizeT3,
    _root_.Run.digToBytes_digS c h.sizeB2, _root_.Run.digToBytes_digS d h.sizeB3]

/-- The first two values hang on the key file's prover's coin alone. -/
theorem runsToy_T (κ κ' : CoinRuns CT × CL × CoinRuns CB) (h : κ.1 = κ'.1) :
    (runsToy κ).1 = (runsToy κ').1 := by
  unfold runsToy
  rw [h]

/-- The last two hang on the proof file's prover's coin alone. -/
theorem runsToy_B (κ κ' : CoinRuns CT × CL × CoinRuns CB) (h : κ.2.2 = κ'.2.2) :
    (runsToy κ).2 = (runsToy κ').2 := by
  unfold runsToy
  rw [h]

end FlashProve

#print axioms FlashProve.finite_coinRuns
#print axioms FlashProve.tie_toy
#print axioms FlashProve.runsToy_T
#print axioms FlashProve.runsToy_B
