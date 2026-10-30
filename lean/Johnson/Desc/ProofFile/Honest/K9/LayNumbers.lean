-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/LayNumbers.lean: THREE PUBLIC FACTS ON NUMBERS AT A FEED-FORWARD SEGMENT, UNDER THE
HEAD: for the premises h0 and hnum of `batFrontLay_handed_nums` (Honest/K9/BatFrontHandedNums.lean). Statements and
proofs; no definition; no state stands in them; no goal is stated.
  `calls_first_lay`   the first slot of the lookup on the calls is 0: `First.Look.place_lay` under
      `H2K5.Door.scope_all` · `digits_end_lay`: the stretch of the lookup on the digits has the plan's shape and ends at
      the plan's number of slots (hp.ns): `digits_lay` · **`filled_le_digits_end`**: the tests'
      number of filled slots is at most that end, WHERE hused: the plan's number of used slots is at most its number of
      slots: by `k4_used_is` (Honest/K9/FallTies.lean)
WHAT IS NOT CLAIMED. hused here: it is paid in Honest/K9/PlanUsed.lean (`ground_used`). All three are called by
Honest/K9/BatFrontHandedFilled.lean (`digits_end_lay` through the third). At the full size and the format's second hash function
alone. Nothing on any property.
GROUND: beneath this file lie 118 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.FallTies
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.WindowsLay
import Johnson.Desc.First.Look.K3PlaceLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- At a feed-forward segment the first slot of the lookup on the calls is 0. -/
theorem calls_first_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {pC : Look.P}
    (hC : Look.placeAt (P5J.At.X Zp) (2 * g) false = some pC) : pC.first = 0 := by
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have e2 : (if (P5J.At.X Zp).p4 then 2 else 1) = 2 := by rw [h4]; rfl
  obtain ⟨-, -, -, -, e, -⟩ := First.Look.place_lay h.pubOne hC (by rw [e2, hN]; omega) (by rw [e2]; omega)
  exact e

/-- At a feed-forward segment the stretch of the lookup on the digits ends at the plan's number of slots. -/
theorem digits_end_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {pD : Look.P}
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g) true = some pD) :
    ∃ hp, (P5J.At.X Zp).G[g]? = some hp ∧ pD.shape = some hp.tl.f9 ∧
      pD.first + Forest.elems hp.tl.f9 = hp.ns := by
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have e2 : (if (P5J.At.X Zp).p4 then 2 else 1) = 2 := by rw [h4]; rfl
  obtain ⟨hp, e, k⟩ := ProofFile.Honest.K3.Good.Live.digits_lay h.pubOne hD (by rw [e2, hN]; omega) (by rw [e2]; omega)
  rw [e2, show 2 * g / 2 = g by omega] at e
  exact ⟨hp, e, k⟩

/-- **The tests' number of filled slots is at most the end of the digits' stretch, where the plan's number of used
slots is at most its number of slots.** -/
theorem filled_le_digits_end (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : ℕ} (hg : g < 12) {pD : Look.P}
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    {u : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (hu : Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u)
    (hused : ∀ hp, Bs.G₀.W.G[g]? = some hp → hp.used ≤ hp.ns) :
    ∀ hsD, pD.shape = some hsD → u.2.2.filled ≤ pD.first + Forest.elems hsD := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans O.made)
  obtain ⟨hp, e, sh, en⟩ := digits_end_lay h hg hD
  have e' : Bs.G₀.W.G[g]? = some hp := by
    rw [O.W]
    exact e
  obtain ⟨-, -, xm, -, -, hx, -, hl, -, -, hG, -⟩ := IM.k4_of h.scope h.reads O g hg
  have hk := LPFK9.k4ParAt_of_mem hx hl
  have hf := k4_used_is h.scope h.reads O hg hk hu
  obtain rfl : xm.2.hp = hp := Option.some.inj (hG.symm.trans e')
  intro hsD sp
  obtain rfl : xm.2.hp.tl.f9 = hsD := Option.some.inj (sh.symm.trans sp)
  rw [en, ← hf]
  exact hused _ e'

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.calls_first_lay
#print axioms ProofFile.Honest.K9.digits_end_lay
#print axioms ProofFile.Honest.K9.filled_le_digits_end
