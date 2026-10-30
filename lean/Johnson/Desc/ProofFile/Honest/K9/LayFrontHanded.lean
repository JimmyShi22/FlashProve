-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/LayFrontHanded.lean: `k4_front_of_fold` (Honest/K9/LayFrontFold.lean) AT THE STATES
THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING: where a walk over the members in front
returns with the verifier's state s', the fit's marks being among the marks asked and all marks asked having been
silent. One statement and its proof; no definition; no goal is stated.
  **`k4_front_handed`**   under the head · hB · the premises of `attClauses_handed` on the
      walk, at A.length = 14 (2 g) + 9. THE END: the two members blk, b₄ · blk's own step and b₄'s · NO MARK ASKED AT
      blk's PLACE HAS SPOKEN AT ITS ROUNDS R, NONE ASKED AT b₄'s AT R₂ · sk is reached · and all of `k4_front_of_fold`'s
      end, at these very R₂, sk, sm, s'. HOW: `pair_handed` (Johnson/P1K8R/TwoStepsAtWalk.lean) at n := 14
      (2 g) + 3, then one call
WHAT IS NOT CLAIMED. That any walk returns: at a prover whose walk returns at no challenges the statement is true for
nothing. WHICH marks are asked is the caller's list ms: that K4's own marks are in it is asked by nobody here. No
member. Called by Honest/K9/K4TextsHanded.lean alone. At the full size and the format's second hash function alone. Nothing on
any property.
GROUND: beneath this file lie 290 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.LayFrontFold
import Johnson.P1K8R.TwoStepsAtWalk
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay Mid Step walk Mark markOf marksQuiet drawsFit)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **AT THE TWELVE FEED-FORWARD SEGMENTS, AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF THE BATCHING**: the
lookup on the calls and K4 have each taken their own step, at rounds at which no mark asked at their place has spoken;
and what `k4_front_of_fold` (Honest/K9/LayFrontFold.lean) says of these steps and of the state handed. -/
theorem k4_front_handed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {g : ℕ} (hg : g < 12) (ms : List Mark)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * (2 * g) + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {w₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok w₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr w₀ = .ok z) (hv : z.ver = some s') :
    ∃ (blk b₄ : Block S ProofFile.Cl) (sj sk sm : S) (R R₂ : List Fmt.RoundView) (cs d₂ : List Desc.OpenedColumn)
      (f₁ f₂ : List Fmt.Drawn) (p4 : OnBytes.Desc.First.K4.Par) (a a₀ : LayOwn) (fo : Forest.Heard)
      (o : Layer.Own),
      cF.blocksInOrder[14 * (2 * g) + 3]? = some blk ∧ cF.blocksInOrder[14 * (2 * g) + 4]? = some b₄ ∧
      blk.step 0 sj R cs = .ok (sk, cs.length) ∧ markOf ms blk.place f₁ (R.map (·.drawn)) = none ∧
      b₄.step 0 sk R₂ d₂ = .ok (sm, d₂.length) ∧ markOf ms b₄.place f₂ (R₂.map (·.drawn)) = none ∧
      Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + 4) (zp, sk) ∧
      LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4 ∧ p4.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[g]? = some p4.hp ∧ p4.g = g ∧
      b₄.place = IM.k4Place g ∧ OnBytes.Road.K4.Declares b₄ p4 ∧ roundsFit b₄.rounds R₂ = true ∧
      (OnBytes.Desc.First.K4.blockAtS p4).decide sk (R₂.map noDigest)
        (Sound.groupsAt 0 b₄ R₂ (d₂.take d₂.length)) = .ok sm ∧
      sk.here = .lay a ∧ a.fo = some fo ∧ sk.lookHeard? = some fo ∧ PscRun.Sized a.F ∧
      _root_.Fo.Tp.PadNames fo a.F ∧
      sm.own? = some o ∧ s'.here = .lay a₀ ∧ a₀.own = some o ∧ (∀ a₁, sm.here = .lay a₁ → a₀.own = a₁.own) ∧
      a₀.lookHeard = some fo := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨b₄, f4, -⟩ := P1K8.keeps_five h.scope h.reads O h.laid.planOk (l := 2 * g) (by omega) 0 (by omega)
  obtain ⟨blk, hb₁⟩ : ∃ blk, cF.blocksInOrder[14 * (2 * g) + 3]? = some blk := by
    have hlt : 14 * (2 * g) + 3 < cF.blocksInOrder.length := by
      rw [hall, List.length_append]
      omega
    exact ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨sj, sk, sm, R, R₂, cs, d₂, r₂, r₃, c₂, c₃, f₁, f₂, -, g3, -, hs1, -, k3, -, hs2, -, hrk, -, hfold⟩ :=
    P1K8.pair_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * (2 * g) + 3) hb₁ f4 ms hall hfit (by omega) hpos L hft
      hm ha hn hq hz hv
  rw [hA] at hfold
  obtain ⟨p4, a, a₀, fo, o, E⟩ :=
    k4_front_of_fold h.scope h.reads O h.laid.planOk hg hb₁ f4 g3 k3 hrk hfold
  exact ⟨blk, b₄, sj, sk, sm, R, R₂, cs, d₂, f₁, f₂, p4, a, a₀, fo, o, hb₁, f4, g3, hs1, k3, hs2, hrk, E⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k4_front_handed
