-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FreshAtHead.lean: TWO OF THE FOUR SENTENCES OF `ready_of` (Honest/K9/ReadyOf.lean), PAID: at
every state that stands in front of the batching of a segment l < 25 (`Front`): the open ledger is `Fresh`, and the open
book-keeping is `LinkReady`.

  **`back_to_open`**    in the goals' scope: a state reached in front of segment l's batching, at which book-keeping L and a
                        ledger G are open, has behind the segment's opening a state with book-keeping L₀ and a ledger G₀ that
                        are `Opened` (Honest/K9/OpenFresh.lean), with the same readings `lnk` and `cr` (Honest/K9/CrLot.lean),
                        and L's count of moments is L₀'s and the number of the sendings between (Honest/K9/MomLot.lean)
  **`fresh_at_front`**, **`link_at_front`**   under the library's hypothesis `AtMgA`
  **`ready_of_two`**    so the premise `ready` of `accepted_bat_at_head` from the two sentences that are left: "the slots taken
                        are the ledger's number of slots" and "claims are planned"

How. The cut of the fold at the opening is the library's (`waits_behind_switch`, Johnson/IMR/WaitsBehindSwitch.lean). That the
shape which the open book-keeping holds is the full size's: the library's fact `liveShape` on reached states (`foldFacts_raw`,
Honest/Thread/ReachFacts.lean) and `AtMg.shape_full`.

Limits. The full size and the hash function `secondHashFunction` alone: the hypothesis's. It is not proved that the invariant holds at any
run, nor that any state is reached. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.OpenFresh
import Johnson.Desc.ProofFile.Honest.K9.CrLot
import Johnson.Desc.ProofFile.Honest.K9.MomLot
import Johnson.P5J.CodesFullAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (Closed Plain cr lnk KeepsCr)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.K2
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **From the batching's front back to the segment's opening.** -/
theorem back_to_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.nAt l + 2) (z, s))
    {L : LinkCtx} {G : Fork} (hL : s.link? = some L) (hG : s.fork? = some G) :
    ∃ L₀ G₀, Opened L₀ G₀ ∧ lnk L₀ = lnk L ∧ cr G = cr G₀ ∧
      L.moments = L₀.moments +
        k1From l ((if l = 24 then 1 else 0) + 1) (IM.nAt l - ((if l = 24 then 1 else 0) + 1)) := by
  have hk : 14 * l + IM.nAt l + 2 =
      k2Number l + 1 + (IM.nAt l - ((if l = 24 then 1 else 0) + 1)) := by
    by_cases h24 : l = 24
    · subst h24
      rfl
    · simp only [k2Number, IM.nAt, if_neg h24]
  have hn : (if l = 24 then 1 else 0) + 1 + (IM.nAt l - ((if l = 24 then 1 else 0) + 1)) ≤ IM.nAt l := by
    by_cases h24 : l = 24
    · subst h24
      exact Nat.le_refl _
    · simp only [IM.nAt, if_neg h24]
      exact Nat.le_refl _
  obtain ⟨hle, rs, cols, f⟩ := h.fold
  have f0 : foldBlocks 0 (c.blocksInOrder.take (k2Number l + 1 +
               (IM.nAt l - ((if l = 24 then 1 else 0) + 1)))) (ProofFile.startS Z z) rs cols = .ok (s, [], []) := by
    rw [← hk]
    exact f
  obtain ⟨v, Rv, Cv, fv⟩ := fold_cut (k := k2Number l + 1) _ f0
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := k2Number l) fv
  obtain ⟨b, hb⟩ : ∃ b, c.blocksInOrder[k2Number l]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : k2Number l < c.blocksInOrder.length)⟩
  obtain ⟨rs', gs', dd⟩ := fold_next hb fu fv
  have e1 : k2Number l + 1 = 14 * l + ((if l = 24 then 1 else 0) + 1) + 2 := by
    unfold k2Number
    omega
  rw [e1] at fv f0
  have K := hear_back hS hR O hl (by omega) (fun e => by simp [e]) fv _ hn s [] [] f0
  have M := hear_moments hS hR O hl (by omega) (fun e => by simp [e]) fv _ hn s [] [] f0
  obtain ⟨G₀, L₀, g0, l0, e3, e4⟩ := K G L hG hL
  obtain ⟨L₁, l1, em⟩ := M L hL
  obtain rfl : L₀ = L₁ := Option.some.inj (l0.symm.trans l1)
  exact ⟨L₀, G₀, opened_at hS hR O hl hb dd l0 g0, e3, e4, em⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The open ledger in front of a batching is `Fresh`.** -/
theorem fresh_at_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {s : S}
    (hS : Front cF Zp l s) : ∀ G, s.fork? = some G → Fresh G := by
  intro G hG
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨z, hz⟩ := hS.reach
  obtain ⟨L, G', tl, hL, hG', -⟩ := open_of_stand hS.stand
  obtain ⟨L₀, G₀, ho, -, e, -⟩ := back_to_open h.scope h.reads O hl hz hL hG
  exact fresh_of_cr e ho.fresh

/-- **The open book-keeping in front of a batching is `LinkReady`.** -/
theorem link_at_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {s : S}
    (hS : Front cF Zp l s) : ∀ L, s.link? = some L → LinkReady L := by
  intro L hL
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨z, hz⟩ := hS.reach
  obtain ⟨L', G, tl, -, hG, -⟩ := open_of_stand hS.stand
  obtain ⟨L₀, G₀, ho, e, -, em⟩ := back_to_open h.scope h.reads O hl hz hL hG
  have eh : L₀.handed = L.handed := congrArg (·.1) e
  have el : L₀.list = L.list := congrArg (·.2.1) e
  have FF := foldFacts_raw h.toAtMg (fun k a => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ hr => hr) (P5J.laid_at_head h.toAtMg) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))
  have hsh : L.check.frame.shape = VerifiableInference.Desc.ReqLit.shapeFull := by
    have k := FF.liveShape _ (z, s) hz hS.clean
    have k' : s.live.frame.shape = P5J.At.shape Zp := k
    rw [live_open hL] at k'
    exact k'.trans h.toAtMg.shape_full
  refine ⟨by rw [← el]; exact ho.list.planned, by rw [← el]; exact ho.list.link, by rw [← eh]; exact ho.handed, ?_⟩
  rw [em, ho.moments]
  unfold ChainCheck.momentsOf
  rw [hsh, hS.number L hL]
  exact (moments_at hl).symm

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The premise `ready` of `accepted_bat_at_head`, from the two sentences that are left.** -/
theorem ready_of_two {l : ℕ} (hl : l < 25)
    (used : ∀ s, Front cF Zp l s → ∀ F u, s.fork? = some F → Desc.K9.usedOf s = some u → u = F.ns)
    (plan : ∀ s, Front cF Zp l s → ∀ F, s.fork? = some F → F.planClaimsF ≠ 0)
    {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} :
    ∀ κ s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said (14 * l + IM.nAt l + 2) κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false :=
  ready_of h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hl (fun _ hS => fresh_at_front h hl hS)
    (fun _ hS => link_at_front h hl hS) used plan

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.back_to_open
#print axioms ProofFile.Honest.K9.fresh_at_front
#print axioms ProofFile.Honest.K9.link_at_front
#print axioms ProofFile.Honest.K9.ready_of_two
