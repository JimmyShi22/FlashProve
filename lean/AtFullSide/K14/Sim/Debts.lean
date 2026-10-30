-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/Debts.lean: THE FIELDS OF `Owed` AT K14's SIX ROWS, AS THE FRAME's RULE TAKES THEM: at each of the goals' two named
sets of public files, at every row with letters that has the place, the parts, On and bud of a row of `simRows`: the body of the
field bud₂ of `BudDebts` and the body of the field on₂ of `OnDebts` (Honest/Law/OwedRule.lean). The frame's `owed_of_threads` turns
these two debts into `Owed.owed`: `bud` at every part and `On` at every called part, of the run's own values, at all coins.

  `own_letters`    the four own rows' On and bud ask nothing
  `six_bud_at_named`   **the body of bud₂ at the six**, at the two named sets
  `six_budDebts_at_named`   Lean holds that body against the field's own type
  `six_on_at_head`   **the body of on₂ at the six**, at every frame's sentence T₂ of the description's shared list
  `six_onFromS`    **OnFromS at the six**, the form that the frame's rule for rows takes
  `six_bud_at_head`   the body of bud₂ under the head at the files' own data
  `six_stops`      none of the six rows stops: `rowStopAt` is none at any challenges
  `k14_noSecondStop`   none of their parts has a second stop, by type

Limits. on₂ IS AN IMPLICATION FROM THE FRAME's SENTENCE AT THE STAND: the entry of a run into T₂ is the threads' debt, not paid here:
at a row of a sending what is read of T₂ is the number of rounds heard. bud₂ is at the positions that the frame lays at one request's
due challenges (`treeAsks`): the frame's rule is what says that a run's are these. All limits of AtFullSide/K14/BudAtNamed.lean and of
Honest/K14/OnRows.lean hold here. One request. No property of the protocol is claimed.
-/
import AtFullSide.K14.BudAtNamed
import Johnson.Desc.ProofFile.Honest.K14.OnRows
import Johnson.Desc.ProofFile.Honest.K14.Sim.Good

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

variable {W₀ Rc Ky X Pb : Type}

/-- The four own rows' letters ask nothing. -/
theorem own_letters (d : Data) (weights : W₀ → Weights)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Pb)
    (hr : r ∈ (ownRows d weights : List (Unlettered Empty (Common W₀ Rc Ky) X Pb))) :
    r.On = k14On ∧ r.bud = k14Bud := by
  unfold ownRows at hr
  rcases List.mem_append.1 hr with g | g
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  · split at g
    · obtain rfl := List.mem_singleton.1 g
      exact ⟨rfl, rfl⟩
    · cases g

/-- A part without a first stop, in the shared chain's type, never stops. -/
theorem stopAt_none_of {W : Type} (p : Part Empty W X) (hb : ∀ f o, p.bad f o = none) (v : Option Empty)
    (loc ds : List Fmt.Drawn) : p.stopAt v loc ds = none := by
  cases v with
  | some e => exact e.elim
  | none =>
    unfold Part.stopAt
    refine List.findSome?_eq_none_iff.2 fun j _ => ?_
    simp [hb]

/-- **K14 HAS NO SECOND STOP**, by type: what a shared chain's second stop may read is `Empty`: at the six rows' halves, the two at K1's places among them. -/
theorem k14_noSecondStop (d : Data) (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ∀ h ∈ ((simRows d A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half)),
      ∀ p ∈ h.parts, ∀ (u : Empty) (l o : List Fmt.Drawn), p.hid u l o = none :=
  fun _ _ _ _ u => nomatch u

/-- **None of the six rows stops**, at any challenges. -/
theorem six_stops (d : Data) (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Pb)
    (hr : r ∈ (simRows d A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)))
    (v : Option Empty) (loc ds : List Fmt.Drawn) :
    rowStopAt v (r.row.map (·.1)) loc ds = none := by
  have one : ∀ (p : Part Empty (Common W₀ Rc Ky) X) (s : Sim Pb), (∀ f o, p.bad f o = none) →
      rowStopAt v ([(p, s)].map (·.1)) loc ds = none := by
    intro p s hb
    simp [rowStopAt, stopAt_none_of p hb]
  rcases List.mem_append.1 hr with g | g
  · unfold ownRows at g
    rcases List.mem_append.1 g with g | g
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at g
      rcases g with rfl | rfl | rfl <;> exact one _ _ fun _ _ => rfl
    · split at g
      · obtain rfl := List.mem_singleton.1 g
        exact one _ _ fun _ _ => rfl
      · cases g
  · unfold sendingRows at g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl <;> exact one _ _ fun _ _ => rfl

end ProofFile.Honest.K14

namespace AtFullSide.K14
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (theProofRun)
open VerifierAndGoals.AtTheName (dpZ)
open VerifiableInference.Desc (Block Chain)
open Desc.K14 (St)
open OnBytes.SendSim.At (budAt)
open ProofFile.Honest ProofFile.Honest.K14

/-- **UNDER THE HEAD AT THE FILES' OWN DATA, WHERE THE VERIFIER's TEST ON THE FILES ACCEPTS: THE BODY OF bud₂ AT EACH OF THE SIX ROWS**, at every
row with letters that has their place, parts and bud. -/
theorem six_bud_at_head {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x₀)
    (live : FlashProve.protocolDataWellFormed (asDescriptionFiles Z) = true) :
      ∀ (X W₀ Rc Ky : Type) (Bk : ProverCoinCounts) (weights : W₀ → Weights) (rand : Rc → TableRand)
        (r : Unlettered Empty (Common W₀ Rc Ky) X Ky),
        r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand →
        ∀ L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X Ky,
          L.place = r.place → L.row = r.row → L.bud = r.bud →
          ∀ τ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
            ∀ (pre t : List (Block St ProofFile.Cl)) (n : Nat),
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ τ.block :: t →
            n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
            ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
            L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
              (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1)
                (u.rounds.map (·.2.length))
                (((rowsOfChain (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map
                  (·.2.length)).sum) := by
  have L₀ := P5J.dpZ_live live ▸ h.laid
  intro X W₀ Rc Ky Bk weights rand r hr L c1 c2 c4
  rcases List.mem_append.1 hr with g | g
  · have e : L.bud = k14Bud := c4.trans (own_letters _ weights r g).2
    intro τ _ u _ pre t n _ _ ρ _
    rw [e]
    trivial
  · unfold sendingRows at g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at g
    rcases g with rfl | rfl
    · exact bud₂_u h.scope live L₀ 0 _ _ L c1 c2 fun j ds asks hq => by rw [c4]; exact hq
    · exact bud₂_omega h.scope live L₀ 0 _ _ L c1 c2 fun j ds asks hq => by rw [c4]; exact hq

/-- **AT EITHER NAMED SET: THE SAME**, with the head and the test paid. -/
theorem six_bud_at_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    ∃ Zp Np cF x₀,
      P5J.AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x₀ ∧
      ∀ (X W₀ Rc Ky : Type) (Bk : ProverCoinCounts) (weights : W₀ → Weights) (rand : Rc → TableRand)
        (r : Unlettered Empty (Common W₀ Rc Ky) X Ky),
        r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand →
        ∀ L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X Ky,
          L.place = r.place → L.row = r.row → L.bud = r.bud →
          ∀ τ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
            ∀ (pre t : List (Block St ProofFile.Cl)) (n : Nat),
            (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ τ.block :: t →
            n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
            ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
            L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
              (asksFrom (treeAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ 1)
                (u.rounds.map (·.2.length))
                (((rowsOfChain (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map
                  (·.2.length)).sum) := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named Z hZ
  exact ⟨Zp, Np, cF, x₀, h, six_bud_at_head h (live_named Z hZ)⟩

/-- **The body above is the field's own**: Lean holds it against `BudDebts`, at a filling whose only rows are the six. SUCH A FILLING IS
SYNTHETIC: a maker's has rows of other kinds too, whose clauses are their writers'. -/
theorem six_budDebts_at_named (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles Z) :
    ∃ Zp Np cF x₀,
      P5J.AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x₀ ∧
      ∀ (X₀ X W₀ Rc Ky Tr : Type) (Bk : ProverCoinCounts) (weights : W₀ → Weights) (rand : Rc → TableRand)
        (G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X),
        G.first = [] → G.second = [] →
        (∀ L ∈ G.shared, ∃ r ∈ (simRows (simData Zp Np) (simPub Zp Np) weights rand :
            List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)),
          L.place = r.place ∧ L.row = r.row ∧ L.bud = r.bud) →
        BudDebts (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk G := by
  obtain ⟨Zp, Np, cF, x₀, h, hb⟩ := six_bud_at_named Z hZ
  refine ⟨Zp, Np, cF, x₀, h, fun X₀ X W₀ Rc Ky Tr Bk weights rand G h1 h3 hall => ?_⟩
  refine ⟨fun L hL => (by rw [h1] at hL; cases hL), fun L hL => ?_,
    fun L hL => (by rw [h3] at hL; cases hL)⟩
  obtain ⟨r, hr, c1, c2, c4⟩ := hall L hL
  exact hb X₀ W₀ Rc Ky Bk weights rand r hr L c1 c2 c4

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

/-- **UNDER THE HEAD: THE BODY OF on₂ AT EACH OF THE SIX ROWS**, at every frame's sentence T₂ of the description's shared list. -/
theorem six_on_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X}
    {G : Sides (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X}
    (T₂ : Thread Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hT : T₂.φ = .shared ∧ T₂.chain = 1 ∧ T₂.ft = 0 ∧
      T₂.bs = (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder ∧ T₂.hs = (G.prover H).shared)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop) (w₀ : W₀) (rc : Rc) (k : Coins Bk)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)
    (hr : r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hplace : L.place = r.place)
    (hrow : L.row = r.row) (hOn : L.On = r.On) :
    ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      ∀ (pre t : List (Block St ProofFile.Cl)),
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t → ∀ ρ p m ca,
      ρ.due (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true →
      InsideOf .shared Bk 1 (G.prover H).shared σ.block (ThrS T₂ S₂ pre.length)
        (σ.roundsTo u.number) k m (envOf (H.storedWords w₀ rc) (fun _ _ => none) p) →
      m.seen = roundsOf p →
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      L.On u ca m ((laidOf (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ [] p []).front 1
        (storedShown (H.storedWords w₀ rc) (storedAsks (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ρ))) := by
  rcases List.mem_append.1 hr with g | g
  · have e : L.On = k14On := hOn.trans (own_letters _ weights r g).1
    intro σ _ u _ pre t _ ρ p m ca _ _ _ _
    rw [e]
    trivial
  · exact on₂_row h T₂ hT S₂ w₀ rc k weights rand r g L hplace hrow hOn

/-- **UNDER THE HEAD: OnFromS AT EACH OF THE SIX ROWS**, the form that the frame's rule for rows takes, at every frame's sentence whose list is the
description's shared list, every letter, every number of the list that holds the row's place. -/
theorem six_onFromS (h : P5J.AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    (T₂ : Thread Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (hbs : T₂.bs = (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
    (S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (r : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)
    (hr : r ∈ simRows (simData Zp Np) (simPub Zp Np) weights rand)
    (L : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X₀ Ky) (hplace : L.place = r.place)
    (hrow : L.row = r.row) (hOn : L.On = r.On) (b : Nat) (blk : Block St ProofFile.Cl)
    (hx : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder[b]? = some blk) (hp : blk.place = L.place)
    (len : Nat → Nat → Nat) : OnFromS T₂ S₂ L b len := by
  rcases List.mem_append.1 hr with g | g
  · have e : L.On = k14On := hOn.trans (own_letters _ weights r g).1
    intro σ _ u _ k m E ca front _ _ _
    rw [e]
    trivial
  · exact onFromS_rows h T₂ hbs S₂ weights rand r g L hplace hrow hOn b blk hx hp len

end AtFullSide.K14

#print axioms ProofFile.Honest.K14.k14_noSecondStop
#print axioms ProofFile.Honest.K14.stopAt_none_of
#print axioms ProofFile.Honest.K14.six_stops
#print axioms AtFullSide.K14.six_bud_at_head
#print axioms AtFullSide.K14.six_onFromS
#print axioms ProofFile.Honest.K14.own_letters
#print axioms AtFullSide.K14.six_bud_at_named
#print axioms AtFullSide.K14.six_budDebts_at_named
#print axioms AtFullSide.K14.six_on_at_head
