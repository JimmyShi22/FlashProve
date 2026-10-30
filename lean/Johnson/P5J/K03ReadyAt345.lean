-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03ReadyAt345.lean: THE OUTPUT HEAD's PROMISE K6Ready (Johnson/Desc/Kinds/Law/RunsStill.lean) IN FRONT OF THE HEAD's DIGITS, ALONG "REACHED": at every state reached at border 345 of the first chain (the front of the lookup on the digits at the head's link): what the head has heard is read back (K6HeardAt, Johnson/Desc/Kinds/Law/K6Claims.lean), and so K6Ready holds at what the state shows and its own ledger.
Why. The lookups' way back at the head across the digits (letters_back then letters_at, RunsStill.lean) asks K6Ready in front; the output head's files have K6HeardAt at 342 (P4.heard_342, Johnson/P4R/Head342.lean); from 342 to the digits' front it was walked by nobody. (Where this and lean/THEOREM.md differ, the page holds.)
  k6HeardAt_kept: K6HeardAt is carried along KeptW (Johnson/Desc/Kinds/Law/WeightAtSame.lean): the sister of k6HeardAt_front (along AlikeFront): given_kept · heard_kept · the ledger is later.
  heardAt_345: IN THE GOALS' SCOPE, AT THE OPENED LETTERS, UNDER F.planOk = true: three steps back (P4.peel), P4.heard_342, and kept_342 | kept_343 | kept_344 (Johnson/P4R/WaK6At346.lean).
  **k03_heardAt_345 · k03_ready_345**: AT THE CLOSED CONSTANT, UNDER THE HEAD, at h.toAtMg.rch (k3K 24 true).
NOTHING NEW IS ARGUED BUT k6HeardAt_kept's proof: the rest are calls. NEAR IT: P5J.heard_345 (Johnson/P5J/K03WtBackAt.lean) walks the same three steps for two of the five clauses ("heard" answers; the head's segment with a sized ledger): it is not called here and says less.

Limits. A fact on reached states: that a state is reached at 345 is not shown. "No mark" is not asked. The letters g, H, F0, G, rs stand under "there are". The head is a premise; a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.RchAtMg
import Johnson.P4R.Head342
import Johnson.P4R.WaK6At346
import Johnson.IMR.SeatOpen
import Johnson.Desc.Kinds.Law.K6Claims
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Kinds.Law.KeptWLegs
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain FileDescription Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.PscRun (Later)
open P4 (peel kept_342 kept_343 kept_344 heard_342)

/-- **K6HeardAt is carried along KeptW.** -/
theorem k6HeardAt_kept (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) {s s' : S}
    (a : KeptW s s') (k : K6HeardAt hh iU3 p s) : K6HeardAt hh iU3 p s' := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW, hhr, hL⟩ := k
  refine ⟨g, H, F0, G, rs, (given_kept hh iU3 p a).trans hg, heard_kept hh iU3 a H hH, hW, hhr,
    hL.trans ?_⟩
  obtain ⟨o, o', ho, ho', _, _, eo, _, _, _, hLo⟩ := a
  show Later (s.fork?.getD {}) (s'.fork?.getD {})
  unfold S.fork?
  rw [ho, ho']
  simp only [eo]
  cases o.opened
  · exact Later.refl _
  · exact hLo

/-- **What the head has heard is read back at every state reached at 345.** -/
theorem heardAt_345 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : ProofFile.InstPub} {s345 : S}
    (h345 : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 345 (z, s345)) :
    K6HeardAt Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) s345 := by
  obtain ⟨s344, B4, r4, g4, h344, hB4, -, d4⟩ := peel h345
  obtain ⟨s343, B3, r3, g3, h343, hB3, -, d3⟩ := peel h344
  obtain ⟨s342, B2, r2, g2, h342, hB2, -, d2⟩ := peel h343
  have k0 : K6HeardAt Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) s342 :=
    heard_342 (Str := Unit) hS hR O hOk ((z, s342), ()) h342
  have ho2 : ∃ o, s342.here = .head o := by
    obtain ⟨_, H, _, _, _, _, hH, _⟩ := k0
    cases hq : s342.here with
    | head o => exact ⟨o, rfl⟩
    | _ =>
      exfalso
      have hN : (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).heard s342 = none := by
        show (match s342.here with
          | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
            allOf o.F x (some (keptOf q x.wpl.sL))
          | _ => none) = none
        rw [hq]
      rw [hN] at hH
      cases hH
  obtain ⟨o2, ho2⟩ := ho2
  have k2 := kept_342 hS hR O hB2 d2 ho2
  obtain ⟨_, o3, _, ho3, _⟩ := id k2
  have k3 := kept_343 hS hR O hB3 d3 ho3
  obtain ⟨_, o4, _, ho4, _⟩ := id k3
  have k4 := kept_344 hS hR O hB4 d4 ho4
  exact k6HeardAt_kept _ _ _ ((k2.trans k3).trans k4) k0

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

/-- **AT THE CONSTANT: IN FRONT OF THE HEAD's DIGITS.** -/
theorem k03_heardAt_345 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (z : ProofFile.InstPub)
    (u : S × (FrD).E.Str) (hr : h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2)) :
    K6HeardAt (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) u.1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 345 (z, u.1) :=
    h.toAtMg.rch_is_reach _ _ hr
  have k := heardAt_345 h.scope h.reads O h.laid.planOk hr'
  rw [O.W] at k
  exact k

/-- **K6Ready THERE, AT WHAT THE STATE SHOWS AND ITS OWN LEDGER.** -/
theorem k03_ready_345 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (z : ProofFile.InstPub)
    (u : S × (FrD).E.Str) (hr : h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2))
    {zz : Seen} {U : Fork} (hz : seenOf u.1 = some zz) (hF : u.1.fork? = some U) :
    K6Ready (At.X Zp).hS (readsOf (At.X Zp)) (parOf (At.X Zp).hS (workOf (At.X Zp))) zz U :=
  k6Ready_at _ _ _ (k03_heardAt_345 h z u hr) hz hF

end P5J

#print axioms P5J.k6HeardAt_kept
#print axioms P5J.heardAt_345
#print axioms P5J.k03_heardAt_345
#print axioms P5J.k03_ready_345
