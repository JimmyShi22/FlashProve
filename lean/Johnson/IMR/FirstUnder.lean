-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/FirstUnder.lean: A LAW ABOUT ProofFile.onlineDescription's SEAT, NO PART OF IT.
IN WORDS. In the goals' scope, block number 2 (from 0) of the flat list of the description's first chain is K1's opening at link 0 as the chain holds it: guarded, marked, stamped with its place, with link 0's «opened» joined behind it. first_under says that this seated block stands UNDER the bare joined block K1.openingZero (Johnson/Desc/K1/Law/OpeningZero.lean; Block.UnderR: the same declared rounds, and wherever the seated block says yes the bare block says the same yes with the same record behind it). So a law that is typed «at any c with c.UnderR (K1.openingZero …)» can be called at the seated description.
OBJECT. c.blocksInOrder[2], which is c.links[0].hear[0]. USER. first_tied_seat (Johnson/Desc/K13/Law/AtTableFirst.lean), by its own road.

  frameAt_zero   frameAt's own text: at link 0 it hands out nothing. So at row 0 the two last arms of frames_arms fall.
  frames_zero    in scope, row 0 of framesOf is link 0's own arm: zeroAt … = some X, and the row's «opened» is openLayZero X (fvsOf …) Z.first.lin.kCol. The head's arm falls because link 0 is a layers' link in scope.
  first_under    the statement.

THE LETTERS OF THE STATEMENT. nm is the seated block's own name. X is zeroAt's value. kCol comes as
worded, at Z.first, because the seat's form (Joined, Johnson/IMR/SameSpot.lean) speaks of framesOf
at Z.first: Open.first (Bs.G₀.first = Z.first) is not called. The first letter, Bs.G₀.first, is
k1_first_sits' own.
Compiled with the whole library.
CALLED, NOT TYPED: k1_first_sits · Joined.rounds · Joined.yes (Johnson/IMR/FirstSeats.lean) · frames_arms (Johnson/IMR/FrameSeat.lean) · hear_at_flat (Johnson/IMR/FlatIx.lean) · flatIx_scope (Johnson/IMR/FlatScope.lean) · subs_scope (Johnson/IMR/LinkSeat.lean).
What is not claimed. The way back, that the seated block says yes wherever the bare block does: the seat's guards ask for more (no mark behind either half, the reply as it was), and whether the bare block's yes gives that is not looked at here. Nothing on the test on the plan, the oracles, the name or the place of either block. Nothing at an o other than OnBytes.secondHashFunction. Nothing of what K1.openingZero's yes means: that is K1's files' law. No soundness.

-/
import Johnson.IMR.FirstSeats
import Johnson.Desc.K1.Law.OpeningZero

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription K1.openingZero K1.gpOf)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- frameAt's own text: at link 0 it hands out nothing. -/
theorem frameAt_zero (built : Array OnBytes.Model.Stages.LinkH) (W : OnBytes.Model.Verify.Public) :
    Johnson.Desc.First.Walk.Seat.frameAt built W 0 = none := by
  unfold Johnson.Desc.First.Walk.Seat.frameAt
  cases built[0]? <;> rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **In scope, row number 0 of framesOf is link 0's own arm**: zeroAt has a value X, and the row's «opened» is openLayZero at X. -/
theorem frames_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame} {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    (hf : fs[0]? = some f) :
    ∃ X, Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X ∧
      f.opened = Johnson.Desc.First.Walk.openLayZero X
        (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol := by
  rcases frames_arms hfs 0 f hf with ⟨X, hX, hk, -⟩ | ⟨-, X, hX, -, hop, -⟩ | ⟨X, n, hX, -⟩ | ⟨X, hX, -⟩
  · exfalso
    have hsub := subs_scope hS hR O 0 (by decide)
    unfold ProofFile.subsOf at hsub
    rw [List.getElem?_map, Array.getElem?_toList, hX, Option.map_some, hk] at hsub
    cases Option.some.inj hsub
  · exact ⟨X, hX, hop⟩
  · rw [frameAt_zero] at hX
    cases hX
  · rw [frameAt_zero] at hX
    cases hX

/-- **IN SCOPE, BLOCK NUMBER 2 OF THE FIRST CHAIN's FLAT LIST STANDS UNDER THE BARE JOINED BLOCK K1.openingZero**: the same rounds, and its yes is that block's yes with the same record behind it. -/
theorem first_under (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ∃ (e : Block S Cl) (nm : String) (X : Johnson.Desc.First.Walk.LayPar), c.blocksInOrder[2]? = some e ∧ Johnson.Desc.First.Walk.Seat.zeroAt Z.p.built.links Z.p.X = some X ∧ e.UnderR (K1.openingZero Bs.G₀.first (K1.gpOf Z) nm X (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol : Block S Cl) := by
  obtain ⟨Lk, b, e1, e2, hj⟩ := k1_first_sits hS hR O
  have hix : flatIx c 0 0 = 2 := flatIx_scope hS hR O (l := 0) (by decide) 0
  have hfl : c.blocksInOrder[2]? = some b := by
    have h := hear_at_flat e1 e2
    rwa [hix] at h
  -- link 0's own row of framesOf
  obtain ⟨fs, f, hfs, hf, -⟩ := id hj
  obtain ⟨X, hX, hop⟩ := frames_zero hS hR O hfs hf
  refine ⟨b, b.name, X, hfl, hX, ?_, fun s rs gs t hy => ?_⟩
  · -- the rounds: the second half has none
    rw [hj.rounds]
    exact (List.append_nil _).symm
  · -- a yes: the opening's yes to m, then the row's «opened» from m on
    obtain ⟨fs', f', m, hfs', hf', h1, -, h3, -, -⟩ := hj.yes hy
    obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
    obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
    rw [hop] at h3
    have h1' : (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Cl).decide s
        (rs.take (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Cl).rounds.length)
        (gs.take (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Cl).openings) =
        .ok m := h1
    show ((VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Cl).decide s
        (rs.take (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Cl).rounds.length)
        (gs.take (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Cl).openings)).bind
        (fun s' => Johnson.Desc.First.Walk.openLayZero X
          (Johnson.Desc.First.Walk.Seat.fvsOf Z.p.built.links) Z.first.lin.kCol s') = .ok t
    rw [h1']
    exact h3

end

end IM

#print axioms IM.frameAt_zero
#print axioms IM.frames_zero
#print axioms IM.first_under
