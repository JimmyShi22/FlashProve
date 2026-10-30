-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Blind/KeepsAtFinish.lean

Every block of the proof file's first chain in front of its proximity test keeps the wiping of the
chain's state (`Keeps wipeS 0`, Honest/K10/WipeFold.lean, WipeS.lean): the premise `KeepsInFront` of
DoorL.lean in this folder, paid; and that file's law at the seated description with that premise
gone. Five theorems; no definition. In the kind K10's authors' calculus (Honest/K10/Wipe/), at their
word that this place is ours to type.

  `keeps_finish`: the first block behind the links, the last switch's place ("F:1", number 353 of
      the flat list), keeps. At an opening; general in the wiping; no premise on scope.
  `front_is_take_L`: in scope the blocks in front of the test's place are the chain's first 354.
  `keepsInFront_L`: in scope: `KeepsInFront c.blocksInOrder AtProof.placeL`.
  `doorL_at_open`: `doorL_at_first` (DoorL.lean) at the library's older hash and an opening's chain,
      for a side at the test's place: no premise on the blocks in front.
  `doorL_at_head`: the same under the head `P5J.AtMg` (Johnson/P5J/AtMg.lean), whose fields give the
      scope, the reading, the test on the plan and the opening.

By what. The seat: `IM.k2_finish_of` (Johnson/IMR/K2Seat.lean), `IM.back_of`, `IM.back_numbers`,
`IM.links_flat_352` (Johnson/IMR/BackSeat.lean), `IM.places_scope` (PlacesScope.lean),
`IM.places_nodup` (BorderW.lean), `Meaning.K2.flat_eq` (Johnson/Goal/Meaning/KeepsDriver.lean). The
calculus: `k2Pure_keeps2`, `failed_of`, `sameReply2` (Wipe/Lots2.lean), `guardMark_decides2`,
`guarded_decides2` (Wipe/Wrap2.lean), `keeps_of_decides2` (Wipe/Link2.lean), `open_front2`
(Wipe/Open2.lean), `takeWhile_take`, `seatKeeps2_wipe`, `seatRest2_wipe` (Wipe/SeatWipe.lean).

Over what it stands. Files of the kind K10's authors, rows of the sealed library
(Johnson/Desc/ProofFile/Honest/K10/: AskWipe, BatWipe, RoundsStretch, StAtZero, WipeFold, WipeS,
ZeroTie, Wipe/), and this folder's Wipe.lean, Fold.lean, Readers.lean, Top.lean and DoorL.lean.

Limits.
- In the goals' scope and at the library's older hash, but for `keeps_finish`. Under `IM.Open`:
  whether an opening can be had at any files is no theorem here.
- That the side stands at the test's place (`σ.block.place = AtProof.placeL`) is a premise of the
  two corollaries. In `doorL_at_open` Zp and Np are tied to nothing; under the head they are the
  opening's own.
- All limits of DoorL.lean's head hold of the two corollaries. That `enterFinish` returns at the
  state in front of the test is a hypothesis inside their conclusions; AtHandAtFinish.lean in this
  folder pays it.
- Of the blocks in front of the test alone. Nothing is shown of the test's own block or of a block
  behind it.
- The stand is the state that `midAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- No property of a prover or a protocol: nothing on completeness, soundness, binding or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.SeatWipe
import Johnson.IMR.K2Seat
import Johnson.P5J.AtMg
import Johnson.Desc.ProofFile.Honest.K12.Blind.DoorL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Blind
open VerifiableInference.Desc (Block Chain Place OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest
open ProofFile.Honest.K10 (Keeps wipeS Whole2 Decides2 SeatKeeps2 SeatRest2 k2Pure_keeps2 failed_of
  sameReply2 guardMark_decides2 guarded_decides2 keeps_of_decides2 open_front2 takeWhile_take
  seatKeeps2_wipe seatRest2_wipe)

/-- **The first block behind the links keeps.** At an opening of the proof file's description
(`IM.Open`, Johnson/IMR/SeatOpen.lean), general in w, under the kind K10's authors' two structures:
the block c.back[0] (the last switch's place, "F:1"), as `Chain.blocksInOrder` lays it, is `Keeps w 0`. No
premise on scope. -/
theorem keeps_finish {w : S → S} {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription
          ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (H : SeatKeeps2 w) (Hr : SeatRest2 w)
    (O : IM.Open o pol lay KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : c.back[0]? = some b) :
    Keeps w 0 ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) := by
  obtain ⟨b0, x, e0, hx, -, hla, -⟩ := IM.k2_finish_of O
  have eb : b0 = b := Option.some.inj (e0.symm.trans hb)
  subst eb
  have hm : (x.retype : Block S ProofFile.Cl) ∈ (ProofFile.k2Pure Z).blocks Bs.G₀ := by
    unfold ProofFile.Lot.blocks ProofFile.asCl
    exact List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩)
  have W : Whole2 w (x.retype : Block S ProofFile.Cl) := (k2Pure_keeps2 H Hr Z Bs.G₀).1 _ hm
  have D1 := guardMark_decides2 (failed_of H) W.1
  have D2 : Decides2 w (IM.seatedAs ProofFile.sameReply x.retype b0.name IM.k2PlaceF) :=
    guarded_decides2 ProofFile.sameReply VerifiableInference.Desc.First.hearsReply (sameReply2 H)
      (b := { IM.marked x.retype b0.name with place := IM.k2PlaceF })
      fun s s' rs gs gs' hs hg => D1 s s' rs gs gs' hs hg
  have hla' : b0 = IM.seatedAs ProofFile.sameReply x.retype b0.name IM.k2PlaceF := hla
  refine keeps_of_decides2 (fun s s' rs gs gs' hs hg => ?_) 0
  have e := D2 s s' rs gs gs' hs hg
  rw [← hla'] at e
  exact e

/-- **In scope the blocks in front of the first chain's proximity test are the chain's first 354.**
The twin of the kind K10's authors' `front_is_take` (Honest/K10/Wipe/SeatWipe.lean), at the test's
place. -/
theorem front_is_take_L {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription
                         ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    c.blocksInOrder.takeWhile (·.place != AtProof.placeL) = c.blocksInOrder.take 354 := by
  obtain ⟨-, ⟨b1, b', e1, -, -, hla⟩, -⟩ := IM.back_of O
  have h354 : c.blocksInOrder[354]? = some { b1 with planOk := b1.planOk && b1.hasNoClaimsAndNothingAfter } :=
    (IM.back_numbers hS hR O).1 1 b1 e1
  refine takeWhile_take (·.place) AtProof.placeL c.blocksInOrder 354 _ ?_ h354 ?_
  · rw [IM.places_scope hS hR O]
    exact IM.places_nodup
  · have e := IM.alone_place hla
    exact e

/-- **`KeepsInFront` at the first chain's proximity test: paid**, in the goals' scope, at an opening
at the library's older hash: every block of the chain in front of the test's place keeps `wipeS`:
the first block and the links by the kind K10's authors' `open_front2`, the one block more by
`keeps_finish`. The twin of their `keeps_at_closing`, one place further on. -/
theorem keepsInFront_L {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription
                         ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    KeepsInFront c.blocksInOrder AtProof.placeL := by
  unfold KeepsInFront
  rw [front_is_take_L hS hR O]
  obtain ⟨hfr, h352⟩ := IM.links_flat_352 hS hR O
  obtain ⟨b0, -, e0, -⟩ := IM.k2_finish_of O
  have h353 : c.blocksInOrder[353]? = some { b0 with planOk := b0.planOk && b0.hasNoClaimsAndNothingAfter } :=
    (IM.back_numbers hS hR O).1 0 b0 e0
  have hlen : (Meaning.K2.frontOf c).length = 353 := by
    unfold Meaning.K2.frontOf
    rw [List.length_cons, h352]
  have htake : c.blocksInOrder.take 353 = Meaning.K2.frontOf c := by
    rw [Meaning.K2.flat_eq hfr, List.take_left' hlen]
  intro y hy
  rw [show (354 : ℕ) = 353 + 1 from rfl, List.take_add_one, htake, h353] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact keeps_of_decides2 (open_front2 seatKeeps2_wipe seatRest2_wipe O y hy) 0
  · have e : y = { b0 with planOk := b0.planOk && b0.hasNoClaimsAndNothingAfter } := by simpa using hy
    rw [e]
    exact keeps_finish seatKeeps2_wipe seatRest2_wipe O e0

/-- **The door at the first chain's proximity test, with no premise on the blocks in front.**
`doorL_at_first` (DoorL.lean) at the library's older hash and at a chain c of which an opening is
had in the goals' scope, for a side that stands at the test's place: `KeepsInFront` is paid by
`keepsInFront_L`. Zp and Np are letters still: nothing here ties them to the opening's. -/
theorem doorL_at_open {P₀ : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P₀ = true) (hR₀ : VerifierAndGoals.readFiles P₀ = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P₀.pol lay P₀.KL F Z Bs base c A B) {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np c)}
    (hpl : (P5J.F0T OnBytes.secondHashFunction Zp Np c).planOk = true)
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np c) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt c.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np c) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hσ : σ.block.place = AtProof.placeL) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np c) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np c).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np c).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∀ (start : Local W₀ Rc ProofFile.Inst Tr → S) (fr : Front Y),
        start m.st.input =
          (P5J.F0T OnBytes.secondHashFunction Zp Np c).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np c).pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        doorTryL c.blocksInOrder start σ.block.place m.st.input fr = (enterFinish s).map wipeT ∧
        atHandL c.blocksInOrder start σ.block.place m.st.input fr = (enterFinish s).toOption.isSome ∧
        ∀ (T fall : T12), enterFinish s = .ok T →
          Agree (doorL c.blocksInOrder start σ.block.place fall m.st.input fr) T :=
  doorL_at_first hpl hR σ u pre t i St hrun hc (hσ ▸ keepsInFront_L hS hR₀ O)

/-- **The same under the head**: at files in the goals' scope at which the description's value is
laid, at the library's older hash (`P5J.AtMg`, Johnson/P5J/AtMg.lean): the scope, the reading, the
test on the plan and the opening, whose chain is cF, are the head's own fields. What is left as
premises: on the filling and the book (hR, St), on the run (hrun, hc), and that the side stands at
the test's place (hσ). Inside the conclusion three things stay hypotheses: that start is the
description's own, what the front shows, and that `enterFinish` returns at s; the third is paid in
AtHandAtFinish.lean. The head shows no test to accept; at the older hash it has members at the
goals' two named sets of public files (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean);
these files do not show that the premises on the filling, the book and the run hold with it. At the
older hash alone. -/
theorem doorL_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r₀ Zp Np cF)
    {W₀ Rc Ky Tr X₀ Y V Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (hσ : σ.block.place = AtProof.placeL) :
    ∃ (m : ProofFile.Honest.Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn)
      (rest : List Fmt.RoundView) (tr : Tr),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∀ (start : Local W₀ Rc ProofFile.Inst Tr → S) (fr : Front Y),
        start m.st.input =
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x) →
        fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
        doorTryL cF.blocksInOrder start σ.block.place m.st.input fr = (enterFinish s).map wipeT ∧
        atHandL cF.blocksInOrder start σ.block.place m.st.input fr = (enterFinish s).toOption.isSome ∧
        ∀ (T fall : T12), enterFinish s = .ok T →
          Agree (doorL cF.blocksInOrder start σ.block.place fall m.st.input fr) T := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact doorL_at_open h.scope h.reads O h.laid.planOk hR σ u pre t i St hrun hc hσ

end ProofFile.Honest.K12.Blind

#print axioms ProofFile.Honest.K12.Blind.keeps_finish
#print axioms ProofFile.Honest.K12.Blind.front_is_take_L
#print axioms ProofFile.Honest.K12.Blind.keepsInFront_L
#print axioms ProofFile.Honest.K12.Blind.doorL_at_open
#print axioms ProofFile.Honest.K12.Blind.doorL_at_head
