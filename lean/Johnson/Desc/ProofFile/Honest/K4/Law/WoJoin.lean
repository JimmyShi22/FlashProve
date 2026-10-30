-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/WoJoin.lean: CONDITIONAL: the hypothesis `K4WoAsks`
(Law/WoOf.lean: seven clauses on what K4's merge has left and on the witness) from the same seven
said of what K4 has heard, with one matrix and one coin named. Statements with their proofs: by
unfolding.

Not shown here. THAT ONE OF THE SEVEN HOLDS AT AN HONEST RUN. THE READER rw OF THE PILE OF PENDING
ROWS IS TYPED HERE AT d.lay.lk COLUMN BITS; the library's own reader at its full-size structure is
typed at another term for that number, equal to it by a public fact alone: SO THESE STATEMENTS
CANNOT BE CALLED AT THAT READER AS THEY STAND: the forms to call are Law/WoShareK.lean (general in
the number of column bits) and, at the first chain's thread, Law/WoHead.lean and Law/WoTop.lean.
No example is known. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH: as Law/WoOf.lean's.

  `left_of_own`: at a layers' state whose segment holds what K4 has heard (o), what the open
      segment's sub-protocol has left is o.wo.
  `k4WoAsks_of`: K4WoAsks d s' wit, where what is left at s' is wo, and of wo, a matrix M, the
      merge's claims with their coefficients cr and ONE VALUE coin: recs · value (the shown end
      value is the merge's function of M at the merge's point plus coin times the factor) · point ·
      rows · zero · mat · and mask: whichever entry the index masks' ledger gives next at s', the
      witness's mask entry at the index masks' message and that entry is coin.
Who is meant to prove each: as Law/WoOf.lean's head says. coin is meant to be the reading of the
last coin that K4's row spends; M the committed weights as the honest side reads them.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.WoOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E mulE)
open OnBytes.Model (Reading WsClaim WsForkOut wsRowPart wsEpsT)
open OnBytes.Model.Layer (Own)
open OnBytes.Road (Wm fmAt)
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.First (LayOwn)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.K13.Law (lowBits)
open Johnson.Desc.First.Walk (leftLay)
open Johnson.Desc.First.Walk.Law (leftOf ledgerAt)

/-- What is left at a layers' state is what K4 has heard of the merge. -/
theorem left_of_own {s : First.S} {a : LayOwn} {o : Own} (ha : s.here = .lay a)
    (ho : a.own = some o) : leftOf s = some o.wo := by
  unfold leftOf leftLay
  rw [ha]
  simp only [ho, Option.map_some]

/-- **`K4WoAsks`, from the seven at one matrix and one coin.** CONDITIONAL. -/
theorem k4WoAsks_of {d : PubData} {nR : Nat} {s' : First.S} {wit : PileWit nR d.lay.lk}
    {wo : WsForkOut} (hleft : leftOf s' = some wo) (M : Wm Cb.Gl.E) (cr : List (WsClaim × E))
    (coin : Cb.Gl.E)
    (recs : wo.recs = cr.map (fun y => wsRowPart d.lay y.1 (mulE y.2 (wsEpsT d.lay y.1 wo.rm))))
    (value : Reading.gl.val wo.fvp =
      fmAt Reading.gl d.lay M cr wo.rm + coin * Reading.gl.val wo.beta)
    (point : wo.rm.size = d.lay.lk) (rows : nR ≤ 2 ^ d.lin.kRow)
    (zero : ∀ j, nR ≤ j → ∀ C, M j C = 0)
    (mat : ∀ (i : Fin nR) (C : Nat), C < 2 ^ d.lay.lk → wit.mat i (lowBits d.lay.lk C) = M i C)
    (mask : ∀ l c l', ledgerAt s' = some l → takeEntry l = some (c, l') →
      wit.mask ⟨s'.out.indexMasks, c⟩ = coin) : K4WoAsks d s' wit := by
  intro w0 l c l' h1 h2 h3
  obtain rfl : wo = w0 := Option.some.inj (hleft.symm.trans h1)
  exact ⟨M, cr, fun _ => coin, recs, value, point, rows, zero, mat, mask l c l' h2 h3⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.left_of_own
#print axioms ProofFile.Honest.K4.k4WoAsks_of
