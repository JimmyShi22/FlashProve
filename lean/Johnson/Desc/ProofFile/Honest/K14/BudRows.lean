-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BudRows.lean: kind K14: THE CLAUSES OF THE FRAME's DEBT bud₂ (a
field of BudDebts, Honest/Law/OwedRule.lean) AT THE ROWS OF BOTH SENDINGS OF THE SHARED CHAIN, AT
THE PROOF FILE's IOP AS WRITTEN IN LEAN (below: the description), FOR A LETTER bud THAT IS budAt
(Johnson/SendSim/At/Sim.lean) at the sending's public numbers: in the rule's own term. For all
public files Z that pass the library's two tests InScope and protocolDataWellFormed, and every public part Zp of
which the library's LaidAt holds at the proof file's own data and decision at Z. Counts on public
numbers. Statements with their proofs; no definition.

  front_two, none_before_u   general at lists of the form FlatOf: cut at a member that stands at
                  "send o_u"'s place, where no member behind the third stands there: in front lie
                  the list's first two members, and they state no oracle message: the rule's count
                  of the trees in front is 0
  no_later_u      no member of the description's shared list behind the third stands at "send
                  o_u"'s place
  bud_u_row       **the clause at "send o_u"'s row**: budAt at the very list of positions that bud₂
                  names
  bud_omega_row   **the clause at "send o_omega"'s row**: the like
  bud₂_u, bud₂_omega   **THE BODY OF THE FIELD bud₂ AT ONE ROW OF A FILLING**: at every
                  row with letters (Lettered, Honest/Rule.lean) that stands at the sending's place,
                  has one part, and whose letter bud follows from budAt: the field's text behind
                  "∀ L ∈ G.shared", written out by hand. By the frame's side_ok
                  (Honest/Law/Rule/Members.lean)
  budDebts_two_rows   **the frame's record BudDebts itself, at a filling whose only rows are of
                  these two sorts**: a synthetic filling: it is here so that LEAN HOLDS THE TWO
                  AGAINST THE FIELD's OWN TYPE

What is assumed. InScope Z, protocolDataWellFormed (asDescriptionFiles Z), LaidAt.
What is not claimed. The field bud₂ itself: it runs over ALL rows of a filling's shared chain; these
are its clauses at two rows. That any filling has such rows. That a run asks for no position beyond
what the frame's list treeAsks holds. A RUN OF ONE REQUEST: nothing on the union of the positions
that the requests of a batch read. The key file's description is not
treated. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BudBoth
import Johnson.Desc.ProofFile.Honest.K14.BudAtRow
import Johnson.Desc.ProofFile.Honest.Law.Rule.Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open OnBytes.SendSim.At (budAt)
open VerifierAndGoals (InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofData theProofRun)
open P5J (LaidAt F0T TS)
open Desc.K14 (P14 St blocks)
open Desc.K14.Law (flat_retype_all bareOf)
open Desc.K14.Honest (FlatOf flatOf_carried)

/-- Cut at a member that stands at "send o_u"'s place: in front lie the first two. -/
theorem front_two {Cl : Type} {x0 x1 x2 : Block St Cl} {rest pre t : List (Block St Cl)}
    {b : Block St Cl} (hx : x0 :: x1 :: x2 :: rest = pre ++ b :: t) (hp : b.place = sendPlace 2)
    (h0 : x0.place ≠ sendPlace 2) (h1 : x1.place ≠ sendPlace 2)
    (hno : ∀ y ∈ rest, y.place ≠ sendPlace 2) : pre = [x0, x1] := by
  match pre, hx with
  | [], hx => exact absurd ((List.cons.inj hx).1 ▸ hp) h0
  | [_], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    exact absurd (hx.2.1 ▸ hp) h1
  | [_, _], hx =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hx
    obtain ⟨rfl, rfl, -⟩ := hx
    rfl
  | _ :: _ :: _ :: pre', hx =>
    simp only [List.cons_append, List.cons.injEq] at hx
    exact absurd hp (hno b (by rw [hx.2.2.2]; simp))

/-- **The rule's count of the trees in front of "send o_u" is 0.** -/
theorem none_before_u {Cl : Type} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {xs : List (Block St Cl)}
    (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hno : ∀ y ∈ xs.drop 3, y.place ≠ sendPlace 2) (pre t : List (Block St Cl))
    (b : Block St Cl) (hx : xs = pre ++ b :: t) (hp : b.place = sendPlace 2) :
    (((rowsOfChain xs).take (pre.flatMap (·.rounds)).length).map (·.2.length)).sum = 0 := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, -, -, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, r1, o1, -, -, -, -⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have s0 : x0.rounds = [] := l0.rounds
  obtain rfl := front_two hx hp (by rw [q0]; decide) (by rw [l1.place, p1]; decide) hno
  simp [rowsOfChain, s0, l1.rounds, l1.oracles, r1, o1]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The step for no_later_u, at letters. -/
theorem no_later_u_at {Cl : Type} (l : List (Block St Unit)) (e : Block St Unit)
    (ts : List (Block St Unit)) (hl : ∀ z ∈ l, z.place ≠ sendPlace 2)
    (ht : ∀ z ∈ ts, z.place ≠ sendPlace 2) (he : e.place ≠ sendPlace 2) :
    ∀ y ∈ l.map (Block.retype (Cl' := Cl)) ++
      ((ts ++ [e]).map (Block.retype (Cl' := Cl))).map bareOf, y.place ≠ sendPlace 2 := by
  intro y hy
  simp only [List.mem_cons, List.mem_map, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with ⟨z, hz, rfl⟩ | ⟨_, ⟨z, hz | rfl, rfl⟩, rfl⟩
  · exact hl z hz
  · exact ht z hz
  · exact he

/-- No member of the shared list behind the third stands at "send o_u"'s place. -/
theorem no_later_u (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∀ y ∈ (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder.drop 3, y.place ≠ sendPlace 2 := by
  obtain ⟨-, p4, p7, p8⟩ := places4 (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, p6⟩ := places2 (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, pO⟩ := send_declares (qAt Zp Np) 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have ht : ∀ z ∈ tests Np, z.place ≠ sendPlace 2 := fun z hz e => by
    have hm : z.place ∈ (tests Np).map (·.place) := List.mem_map.2 ⟨z, hz, rfl⟩
    rw [e] at hm
    cases hO : Np.O with
    | none =>
      rw [H2K.JointK.tests_places_none Np hO] at hm
      simp [sendPlace] at hm
    | some nO =>
      rw [H2K.JointK.tests_places Np nO hO] at hm
      simp [sendPlace] at hm
  intro y hy
  have hb' : blocks (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8] := hb
  rw [shared_flat_at, flat_retype_all _ _ b1 b2 b3 b4 b5 b6 b7 b8 _ _ hb'] at hy
  refine no_later_u_at [b3, b4, b5, b6, b7, b8]
    (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests Np)) (tests Np) (fun z hz => ?_) ht
    (by rw [H2K.JointK.last_place]; decide) y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [p3]; decide
  · rw [p4]; decide
  · rw [pO]; decide
  · rw [p6]; decide
  · rw [p7]; decide
  · rw [p8]; decide

variable (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
  (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL (theProofData (asDescriptionFiles Z))
    (theProofRun (asDescriptionFiles Z)) Zp Np cF) (a : Nat) {X Pb W₀ Rc Ky : Type}
  (p : Part Empty (Common W₀ Rc Ky) X) (sim : Sim Pb)
  (σ : Side St ProofFile.Cl Empty (Common W₀ Rc Ky) X Pb)

include scope live L in
/-- **THE CLAUSE OF bud₂ AT THE ROW OF "send o_u"**, with budAt for the row's letter: a run of one
request. -/
theorem bud_u_row (hrow : σ.row = [(p, sim)]) (hp : σ.block.place = sendPlace 2)
    (u : Member Empty (Common W₀ Rc Ky) X Pb) (hu : u ∈ σ.members)
    (pre t : List (Block St ProofFile.Cl)) (n : Nat)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number) (ρ : Draws)
    (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    budAt (jobU ⟨qAt Zp Np, a⟩).Q (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1)
      (u.rounds.map (·.2.length))
      (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  have h0 : n = (pre.flatMap (·.rounds)).length := hn
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := made_of_laid L
  have hz : (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take
      (pre.flatMap (·.rounds)).length).map (·.2.length)).sum = 0 :=
    none_before_u (xs := (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder)
      (flatOf_carried Zp.p.chains (qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8 (tests Np) last hb) hb
      (no_later_u b1 b2 b3 b4 b5 b6 b7 b8 hb) pre t σ.block hx hp
  rw [h0, hz]
  exact budAt_u_at_files Z scope live Zp Np cF L a ρ hρ _

include scope live L in
/-- **THE CLAUSE OF bud₂ AT THE ROW OF "send o_omega"**, with budAt for the row's letter: a run of
one request. -/
theorem bud_omega_row (hrow : σ.row = [(p, sim)]) (hp : σ.block.place = sendPlace 5)
    (u : Member Empty (Common W₀ Rc Ky) X Pb) (hu : u ∈ σ.members)
    (pre t : List (Block St ProofFile.Cl)) (n : Nat)
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ σ.block :: t)
    (hn : n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number) (ρ : Draws)
    (hρ : ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    budAt (jobOmega ⟨qAt Zp Np, a⟩).Q (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1)
      (u.rounds.map (·.2.length))
      (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  have h0 : n = (pre.flatMap (·.rounds)).length := hn
  rw [h0, one_before_omega scope L pre t σ.block hx hp]
  exact budAt_omega_at_files Z scope live Zp Np cF L a ρ hρ _

include scope live L in
/-- **bud₂'s BODY AT ONE ROW OF A FILLING, "send o_u"'s**: at every row L with letters that stands
at that place, has one part, and whose letter bud follows from budAt at the sending's public
numbers: the text of the field bud₂ behind "∀ L ∈ G.shared". -/
theorem bud₂_u {Bk : ProverCoinCounts} (L' : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X Pb)
    (hpl : L'.place = sendPlace 2) (hrow : L'.row = [(p, sim)])
    (hb : ∀ j ds asks, budAt (jobU ⟨qAt Zp Np, a⟩).Q asks → L'.bud j ds asks) :
    ∀ τ, L'.side (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
      ∀ (pre t : List (Block St ProofFile.Cl)) (n : Nat),
      (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ τ.block :: t →
      n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true →
      L'.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map
            (·.2.length)).sum) :=
  fun τ hτ u hu pre t n hx hn ρ hρ => hb _ _ _
    (bud_u_row scope live L a p sim τ ((side_ok hτ).2.2.trans hrow) ((side_ok hτ).2.1.trans hpl)
      u hu pre t n hx hn ρ hρ)

include scope live L in
/-- **bud₂'s BODY AT ONE ROW OF A FILLING, "send o_omega"'s**: the like. -/
theorem bud₂_omega {Bk : ProverCoinCounts} (L' : Lettered Bk St ProofFile.Cl Empty (Common W₀ Rc Ky) X Pb)
    (hpl : L'.place = sendPlace 5) (hrow : L'.row = [(p, sim)])
    (hb : ∀ j ds asks, budAt (jobOmega ⟨qAt Zp Np, a⟩).Q asks → L'.bud j ds asks) :
    ∀ τ, L'.side (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = some τ → ∀ u ∈ τ.members,
      ∀ (pre t : List (Block St ProofFile.Cl)) (n : Nat),
      (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = pre ++ τ.block :: t →
      n = (pre.flatMap (·.rounds)).length + τ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (F0T OnBytes.secondHashFunction Zp Np cF) = true →
      L'.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (F0T OnBytes.secondHashFunction Zp Np cF) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder).take n).map
            (·.2.length)).sum) :=
  fun τ hτ u hu pre t n hx hn ρ hρ => hb _ _ _
    (bud_omega_row scope live L a p sim τ ((side_ok hτ).2.2.trans hrow) ((side_ok hτ).2.1.trans hpl)
      u hu pre t n hx hn ρ hρ)

include scope live L in
/-- **THE FRAME's RECORD BudDebts ITSELF, AT A FILLING WHOSE ONLY ROWS ARE THESE TWO SORTS**: no row
in the first and in the second chain; each row of the shared chain stands at one of the two
sendings' places, has one part, and has a letter bud that follows from budAt there. So Lean holds
bud₂_u and bud₂_omega against the field's own type. SUCH A FILLING IS SYNTHETIC: a maker's has rows
of other kinds too, whose clauses are their writers'. -/
theorem budDebts_two_rows {Bk : ProverCoinCounts} {Tr X₀ : Type}
    (G : Sides (F0T OnBytes.secondHashFunction Zp Np cF) Bk W₀ Rc Ky Tr X₀ X) (h1 : G.first = [])
    (h3 : G.second = [])
    (h2 : ∀ L' ∈ G.shared, (∃ q s, L'.row = [(q, s)]) ∧
      ((L'.place = sendPlace 2 ∧
          ∀ j ds asks, budAt (jobU ⟨qAt Zp Np, a⟩).Q asks → L'.bud j ds asks) ∨
        (L'.place = sendPlace 5 ∧
          ∀ j ds asks, budAt (jobOmega ⟨qAt Zp Np, a⟩).Q asks → L'.bud j ds asks))) :
    BudDebts (F0T OnBytes.secondHashFunction Zp Np cF) Bk G where
  bud₁ := fun L' hL => by rw [h1] at hL; cases hL
  bud₂ := fun L' hL => by
    obtain ⟨⟨q, s, hrow⟩, hc⟩ := h2 L' hL
    rcases hc with ⟨hpl, hb⟩ | ⟨hpl, hb⟩
    · exact bud₂_u scope live L a q s L' hpl hrow hb
    · exact bud₂_omega scope live L a q s L' hpl hrow hb
  bud₃ := fun L' hL => by rw [h3] at hL; cases hL

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.front_two
#print axioms ProofFile.Honest.K14.none_before_u
#print axioms ProofFile.Honest.K14.no_later_u_at
#print axioms ProofFile.Honest.K14.no_later_u
#print axioms ProofFile.Honest.K14.bud_u_row
#print axioms ProofFile.Honest.K14.bud_omega_row
#print axioms ProofFile.Honest.K14.bud₂_u
#print axioms ProofFile.Honest.K14.bud₂_omega
#print axioms ProofFile.Honest.K14.budDebts_two_rows
