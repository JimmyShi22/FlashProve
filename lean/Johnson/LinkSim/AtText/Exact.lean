-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Exact.lean: from the level of the algorithms' outputs to "exact at all
verifier messages". It proves Spec.exactOfText (Johnson/LinkSim/AtText/SpecExact.lean).
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves (exactOfText). Suppose that at every valid private input and instance and at
all verifier messages, what the prover's algorithm and the simulator's algorithm disclose (shownOf)
agrees up to a shift of the coins that can be undone. Then the honest prover (linkSide) is exact
against the simulator simLink at all verifier messages: ExactOff at the empty set. The other
premises are those listed in SpecExact.lean.

How. A shift of the coins that can be undone is one to one (UpToShift.injective), so on the finite
type of coins it is a bijection of the coins with themselves. Coin by coin the two algorithms
disclose the same, so the two runs of the protocol as stated in Lean disclose the same
(showsOfShown, Johnson/LinkSim/AtText/SeamGroups.lean). The simulator's algorithm gives the same
output at the honest data and at the data made of the instance and the symbols read (simOfAns,
Johnson/LinkSim/AtText/SeamInput.lean). That is ShiftTo (Johnson/LinkSim/SpecForm.lean).
exactOfShift (Johnson/LinkSim/Bridge.lean) turns ShiftTo at every valid input and verifier message
into ExactOff.

How it fits. exactOfText is used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean), and
linkFieldsHome passes it to roadCloses. Johnson/LinkSim/AtHome/RoadCloses.lean takes the statement
Spec.exactOfText as a premise.

Main names (namespace OnBytes.LinkSim.Seam): exactOfText, above; and bldX_rd: at a position where a
symbol was read, the input oracle that bldX builds holds it.
Limits.
It is an implication, for all parameters.

Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecExact
import Johnson.LinkSim.Bridge

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Seam
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.LinkSim OnBytes.LinkSim.AtText
open OnBytes.Flat (linkProtocolOfRoundData)
open _root_.Desc.K15 (P15 p12Of)
open Johnson.Prover.Link
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK View XO SgX)
open TypedOracleCompiler.Run.PQ (RD SOf drawnSL)

/-- At a position where a symbol was read, the input oracle that bldX builds holds that symbol. -/
theorem bldX_rd (a : ℕ) (f : (twoExternalStrings (2 ^ a) SgX).Pos → Option SgX) (p : (twoExternalStrings (2 ^ a) SgX).Pos)
    (v : SgX) (h : f p = some v) : (twoExternalStrings (2 ^ a) SgX).rd (bldX a f) p = v := by
  rcases p with p | p
  · show (f (.inl p)).getD (0, []) = v
    rw [h]
    rfl
  · show (f (.inr p)).getD (0, []) = v
    rw [h]
    rfl

/-- Proves Spec.exactOfText: from agreement up to a shift of the coins to exactness at all verifier
messages. -/
theorem exactOfText : Spec.exactOfText := by
  intro K ds a xs Xi dec P S t Kc _ _ lay addK keysOf Wt ext inW valid first rest hs hW hSt hc hk
    hy hU
  refine exactOfShift Xi (twoExternalStrings (2 ^ a) SgX) (linkProtocolOfRoundData K ds a xs dec) Wt
    (linkSide K ds a xs dec P S t Kc lay ext inW) valid Kc (bldX a) _ ∅ (bldX_rd a) ?_
  intro w x hv ρ _ _
  obtain ⟨s, s', hss⟩ := hU w x hv ρ
  have hb : Function.Bijective fun k : Kc => addK k (s k) :=
    Finite.injective_iff_bijective.1 (UpToShift.injective
      (f := fun k => shownOf (linkAll P S t (inW w x) (lay k) (drawsOf (drawnSL K ds ρ.2))))
      (g := fun k => shownOf (simAll P S t (inW w x) (lay k) (drawsOf (drawnSL K ds ρ.2))))
      (s' := s') hc hss)
  refine ⟨fun k : Kc => addK k (s k), hb, fun c : Kc => ?_⟩
  have e := simOfAns K ds a xs Xi dec P S t Wt ext inW keysOf w x (lay (addK c (s c))) ρ
    (hSt _) (hk w x hv) (hy w x hv)
  have h := showsOfShown K ds a xs Xi dec x P S t (inW w x) (inW w x) (lay c)
    (lay (addK c (s c))) first rest ρ hs (hW _) (hss c).1
  rw [e] at h
  exact h

end OnBytes.LinkSim.Seam

#print axioms OnBytes.LinkSim.Seam.exactOfText
