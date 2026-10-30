-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsIx.lean: Behind a segment's reads the record's vectors' arrays are the
plan's: u3Of is 0. The premise hix of vecPlanS_of_tie (AtFullSide/K1/ReadsCore.lean), at all 25
segments, under the head and hSaid.

  lay7_ix       what lay7B's yes says of the field ix
  ix_at_reads   the statement: tail_at_reads' road, at ix

Limits. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K1.TieTailAtHead
import Johnson.K8Q47R.MultipliedArraysNamedAndFound

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready (lay7B)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Model (HTailF2)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open OnBytes.Tie.Pv.Tail.Port (u3Of)

/-- What lay7B's yes says of the field ix. -/
theorem lay7_ix {tlP tl : HTailF2} {s : S} (h : lay7B tlP s = true) (ht : s.tl? = some tl) :
    tl.ix = tlP.ix := by
  unfold lay7B at h
  rw [ht] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

/-- At the plans' list of arrays u3Of is 0. -/
theorem u3_of_U {tl : HTailF2} (h : tl.ix.U = #[none, none, some 0, none]) : u3Of tl = 0 := by
  unfold u3Of
  rw [h]
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
include hSaid

/-- **BEHIND EACH SEGMENT's READS u3Of IS 0.** -/
theorem ix_at_reads {l : ℕ} (hl : l < 25) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[K1.noL l false]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false) k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl → u3Of tl = 0 := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O l hl
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have hU := IM.alone_underR hu
  have hW : Bs.G₀.W = Zp.p.X := O.W
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := h.pubOne
  have hS' := hS
  unfold Thread.Stepped at hS'
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS'.2)
  have hdec' := hdec
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨m2, f2, k2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).2
    obtain rfl : m2 = Xl := Option.some.inj (f2.symm.trans hX)
    obtain ⟨e1, -⟩ := K1Pen.k1Reads_makes_head Zp Bs.G₀ 24 m2 _ reads hX k2 hdec'
    refine u3_of_U ?_
    rw [lay7_ix e1 htl, hW]
    exact K8Q47.public_U hpub
  · by_cases he2 : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      have hg : g < 12 := by omega
      obtain ⟨m0, m1, fm, km, gm, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
      obtain rfl : m0 = Xl := Option.some.inj (fm.symm.trans hX)
      obtain ⟨hp, hG, e1, -⟩ := K1Pen.k1Reads_makes_layers Zp Bs.G₀ (2 * g) m0 _ reads hX km hdec'
      rw [gm] at hG
      refine u3_of_U ?_
      rw [lay7_ix e1 htl]
      exact K8Q47.U_of_plan hpub (Or.inr (Or.inl ⟨g, hp, hg, rfl, hW ▸ hG, rfl⟩))
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
      have hg : g < 12 := by omega
      obtain ⟨m0, m1, -, -, -, -, f2, k2, g2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
      obtain rfl : m1 = Xl := Option.some.inj (f2.symm.trans hX)
      obtain ⟨-, -, -, A, -, -, -, -, hA, -⟩ := IM.k5_of h.scope h.reads O g hg
      obtain ⟨a₀, hs0, hL0⟩ := attTlS_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid O hg hA
        _ hb k s μ E ds y cols s' hT hd hS
      have hts : s.tl? = some a₀.tl := by
        unfold S.tl?
        rw [hs0]
      obtain ⟨-, e2⟩ := K1Pen.k1Reads_makes_att Zp Bs.G₀ (2 * g + 1) m1 _ reads k2 hdec'
      have e3 : lay7B a₀.tl s' = true := by rw [e2]; exact lay7_self hts
      refine u3_of_U ?_
      rw [lay7_ix e3 htl, hL0.ix]
      exact K8Q47.U_of_plan hpub (Or.inr (Or.inr ⟨g, A, hg, rfl, hW ▸ hA, rfl⟩))

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lay7_ix
#print axioms ProofFile.Honest.K1.u3_of_U
#print axioms ProofFile.Honest.K1.ix_at_reads
