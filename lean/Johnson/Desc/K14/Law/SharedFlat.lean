-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/SharedFlat.lean: THE SHARED CHAIN's WHOLE LIST OF BLOCKS, IN ORDER, IN THE
PROOF FILE's WRITTEN DESCRIPTION. Theorems.

WHY. Three blocks of that chain have no round: the front block, "(rec_gamma)" and "joins": no test
of the format would notice if one of them were left out of the list. This is the lock: the list IS
these blocks, in this order, at what onlineDescription returns.
  frontOf c           the front block as the carried chain holds it: carried to the description's
                      type of claims; its test on the plan asks beside that the chain has no link.
  flat_retype_all     the carried chain's flat list: the front; the kind's eight, carried; the
                      tests and the end, carried, each with "it states no run" laid to its test on
                      the plan (bareOf).
  shared_flat_pure    **at what onlineDescription returns**, at the seat's tests and end.
What is not claimed. That blocks (p14Of …) is some list: a premise here (eight_of_pass,
Johnson/Desc/K14/Law/K14SitsPlan.lean, gives it from the tests on the plan). That a text which runs
cannot be turned: a law locks a text only as long as it is compiled with it. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.K14Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Seat (tests last)

/-- The front block as the carried chain holds it. -/
def frontOf {Cl' : Type} (c : OnBytes.Model.Verify.Chains) : Block St Cl' :=
  bareOf { (frontBlock c).retype (Cl' := Cl') with
    planOk := ((frontBlock c).retype (Cl' := Cl')).planOk && ([] : List Unit).isEmpty }

/-- **The carried chain's whole list.** -/
theorem flat_retype_all {Cl' : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (ts : List (Block St Unit))
    (lst : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ((chainOf c P ts lst).retype (Cl' := Cl')).blocksInOrder = frontOf c ::
      ([b1, b2, b3, b4, b5, b6, b7, b8].map Block.retype ++
        ((ts ++ [lst ([b1, b2, b3, b4, b5, b6, b7, b8] ++ ts)]).map Block.retype).map bareOf) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := own_bare P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hc : chainOf c P ts lst =
      { first := frontBlock c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ ts
        last := lst ([b1, b2, b3, b4, b5, b6, b7, b8] ++ ts) } := by
    simp [chainOf, blocksOr, hb]
  rw [hc]
  show frontOf c :: (([] : List (Block St Cl')) ++ [] ++
    (([b1, b2, b3, b4, b5, b6, b7, b8] ++ ts).map Block.retype).map bareOf ++ [bareOf _]) = _
  simp only [List.nil_append, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    bareOf_self _ (bare_retype b1 h1), bareOf_self _ (bare_retype b2 h2),
    bareOf_self _ (bare_retype b3 h3), bareOf_self _ (bare_retype b4 h4),
    bareOf_self _ (bare_retype b5 h5), bareOf_self _ (bare_retype b6 h6),
    bareOf_self _ (bare_retype b7 h7), bareOf_self _ (bare_retype b8 h8)]
  rfl

/-- **At what onlineDescription returns.** -/
theorem shared_flat_pure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z) c ∧
      ∀ b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit,
        blocks (p14Of Z.p.chains (beforePointOf N)) = some [b1, b2, b3, b4, b5, b6, b7, b8] →
        (ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z)
          c).shared.blocksInOrder = frontOf Z.p.chains ::
            ([b1, b2, b3, b4, b5, b6, b7, b8].map Block.retype ++
              ((tests N ++ [last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests N)]).map
                Block.retype).map bareOf) := by
  obtain ⟨Z, N, B', c, hZ, hN, hF⟩ := shared_seat_of_pure h
  exact ⟨Z, N, B', c, hZ, hN, hF, fun b1 b2 b3 b4 b5 b6 b7 b8 hb =>
    flat_retype_all Z.p.chains (p14Of Z.p.chains (beforePointOf N)) b1 b2 b3 b4 b5 b6 b7 b8
      (tests N) last hb⟩

end Desc.K14.Law
