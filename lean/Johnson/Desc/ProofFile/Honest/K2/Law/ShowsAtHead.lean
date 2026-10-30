-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ShowsAtHead.lean: the kind "the code switch" (K2): under the
library's head and the opening, at each place of the kind: where the lot's public test on the instance
says yes, the part shows something at every coin, every state and every list of challenges that the
rounds can draw. So the equation of the field exact of Good is not one of two nothings there.

  shows_at_head   the statement

By: plays_at_plan_fit (PlaysAtPlan.lean), serves_at_head, roomy_at_head, fits_at_head, answers_at_head
(PublicAtHead.lean), closing_at_head (ClosingAtHead.lean), switch_members (ExactProof.lean).

Limits. hq is a premise: that the public test says yes at a served instance is stated apart.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExactAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain Place Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Xi Tr X : Type}

/-- **Where the public test says yes the part shows something, at every coin.** -/
theorem shows_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (ok : Xi → Bool) (fs : List (Fall TS))
    {σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (hσ : Side.seated cF.blocksInOrder p.place (switchRow (coreSender freshTable) D readers
               (lotClosing Zp Bs.G₀) p ok (roundsAt Zp Bs.G₀ p.place)) fs = some σ)
    (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (hu : u ∈ σ.members)
    (c : u.part.Coins) (m : Mid (Local W₀ Rc Xi Tr) X) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (hd : drawsFit (u.rounds.map (·.1)) ds = true)
    (hq : publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link)
      m.st.input.x = true) :
    σ.shows .own u c m ds asks ≠ none := by
  obtain ⟨blk, member, -⟩ := k2_member_at_head h O hp
  obtain ⟨Pp, n, nm, st, before, after, hP, hn, -, ⟨-, hr, ho⟩, -, -⟩ :=
    k2_block_at_head h O hp member
  have hR := rounds_at_place hP hp hn nm st
  have hfind : cF.blocksInOrder.find? (fun b => b.place == p.place) = some blk := by
    rw [find_at_findIdx]
    have e := K1.borderNo_written h p.place
    unfold borderNo at e
    rw [e]
    exact member
  have hσ' : ({ block := blk
                row := switchRow (X := X) (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p ok
                  (roundsAt Zp Bs.G₀ p.place)
                fall := fallOf fs p.place } :
      Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) = σ := by
    unfold Side.seated at hσ
    rw [hfind] at hσ
    exact Option.some.inj hσ
  subst hσ'
  have hz : blk.rounds.zip blk.oracles = roundsAt Zp Bs.G₀ p.place := by
    rw [hr, ho, hR]
  have two : (roundsAt Zp Bs.G₀ p.place).length = 2 := by
    rw [hR]
    rfl
  obtain ⟨r₁, r₂, e2⟩ := List.length_eq_two.1 two
  rw [e2] at hz hu
  rw [switch_members (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p ok r₁ r₂ blk _ hz]
    at hu
  obtain rfl := List.mem_singleton.1 hu
  have hlen : blk.rounds.length ≤ blk.oracles.length := by
    rw [hr, ho]
    exact Nat.le_refl _
  have e1 : blk.rounds = [r₁.1, r₂.1] := by
    have t := List.map_fst_zip (l₁ := blk.rounds) (l₂ := blk.oracles) hlen
    rw [hz] at t
    exact t.symm
  have hd' : drawsFit blk.rounds ds = true := by
    rw [e1]
    exact hd
  obtain ⟨y, hy⟩ := plays_at_plan_fit (X := X) hP hp hn D readers Bs.G₀.first.layout
    (segmentsOf Zp Bs.G₀) p.place nm st blk hr ho (Face.own.sees m.st.input) (c, ()) ds hd' m
    (serves_at_head h.toAtMg O p hp) (roomy_at_head h.toAtMg O p hp)
    (fits_at_head h.toAtMg O p hp)
    (by unfold answersFit; exact beq_iff_eq.2 (answers_at_head h.toAtMg O hP p hp n hn))
    (closing_at_head h.toAtMg O p hp) hq
  have es : (switchHalf (X := X) (coreSender freshTable) D readers
      (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p).steps blk
        (Face.own.sees m.st.input) (c, ()) =
      Part.steps (seatedPart (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p) blk.name
        ⟨blk.place, 0⟩ [r₁, r₂] (Face.own.sees m.st.input) c := by
    show rowSteps blk.name blk.place (Face.own.sees m.st.input)
      [seatedPart (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p] 0
      (blk.rounds.zip blk.oracles) (c, ()) = _
    rw [hz]
    exact List.append_nil _
  rw [es] at hy
  unfold Side.shows
  show Option.map _ (play (Part.steps _ blk.name ⟨blk.place, 0⟩ [r₁, r₂] _ c) ds [] m).toOption ≠ none
  rw [hy]
  simp [Except.toOption]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.shows_at_head
