-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/TieTailAtHead.lean: hTl AND hcs OF matSeatF_head (K1/Law/TieMatPaid.lean): behind a segment's reads the record's number of matrices and its list of symbol arrays are the plan's; in front the
statement's codes are the public ones. Under the head and hSaid.

  lay7_fields          what lay7B's yes says of the two fields
  codes_at_reads       hcs
  tail_at_reads        hTl: at layers and at the head by the reads' own decision (k1Reads_makes_layers | _head), at attention by tlIsPlan at the front and k1Reads_makes_att

NO PROPERTY IS CLAIMED.
-/
import AtFullSide.K1.TieStateAtHead
import Johnson.K1PenR.AtK1Seat
import Johnson.Goal.Meaning.HidPlan

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
open OnBytes.Slice (frS)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (rchAt_raw)

/-- What lay7B's yes says of the two fields. -/
theorem lay7_fields {tlP tl : HTailF2} {s : S} (h : lay7B tlP s = true) (ht : s.tl? = some tl) :
    tl.gtTree = tlP.gtTree ∧ tl.NM = tlP.NM := by
  unfold lay7B at h
  rw [ht] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.2⟩

/-- lay7B at a state's own record. -/
theorem lay7_self {tl : HTailF2} {s : S} (ht : s.tl? = some tl) : lay7B tl s = true := by
  unfold lay7B
  rw [ht]
  simp

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

/-- **hcs.** -/
theorem codes_at_reads {l : ℕ} (hl : l < 25) :
    ∀ k s μ E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (K1.noL l false) k s μ E → s.st.codes = P5J.At.cs Zp := by
  intro k s μ E hT
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, Xl, reads, he, -, -⟩ := K1.k01_flat_reads h.scope h.reads O l hl
  have hT' : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (K1.noL l false) k s μ E := ⟨hT.1, hSaid _ _ _ hT.2⟩
  have hbl : K1.noL l false ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 he).1.le
  have hIn := inAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hT
  have σ : (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str := (fun _ => default, fun _ => default)
  have hr := thrS_rchAt h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w σ hbl hT'
  have hm : s.failed = none := (hIn (Sound.strsOf _ σ)).2
  have hpl : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc h.laid.planOk
  exact _root_.Meaning.K2.codes_field h.scope h.reads O hpl _ id (fun _ _ q => q) _ _ (rchAt_raw hr) hm

/-- **hTl.** -/
theorem tail_at_reads {l : ℕ} (hl : l < 25) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs[K1.noL l false]? = some blk →
      ∀ k s μ E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said (K1.noL l false) k s μ E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s μ E ds y cols s' →
      ∀ tl : HTailF2, s'.tl? = some tl →
        tl.NM = (_root_.Meaning.tlAt Zp.p.X l).NM ∧ tl.gtTree = (_root_.Meaning.tlAt Zp.p.X l).gtTree := by
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, Xl, reads, he, hX, hu⟩ := K1.k01_flat_reads h.scope h.reads O l hl
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have hU := IM.alone_underR hu
  have hW : Bs.G₀.W = Zp.p.X := O.W
  have hS' := hS
  unfold Thread.Stepped at hS'
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS'.2)
  have hdec' := hdec
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨m2, f2, k2, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).2
    obtain rfl : m2 = Xl := Option.some.inj (f2.symm.trans hX)
    obtain ⟨e1, -⟩ := K1Pen.k1Reads_makes_head Zp Bs.G₀ 24 m2 _ reads hX k2 hdec'
    obtain ⟨a1, a2⟩ := lay7_fields e1 htl
    have et : _root_.Meaning.tlAt Zp.p.X 24 = Bs.G₀.W.H.tl := by
      unfold _root_.Meaning.tlAt
      rw [hW]
      rfl
    rw [et]
    exact ⟨a2, a1⟩
  · by_cases he2 : l % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
      have hg : g < 12 := by omega
      obtain ⟨m0, m1, fm, km, gm, -⟩ := (IM.ground_named h.scope h.reads O.pub O.blank).1 g hg
      obtain rfl : m0 = Xl := Option.some.inj (fm.symm.trans hX)
      obtain ⟨hp, hG, e1, -⟩ := K1Pen.k1Reads_makes_layers Zp Bs.G₀ (2 * g) m0 _ reads hX km hdec'
      rw [gm] at hG
      obtain ⟨a1, a2⟩ := lay7_fields e1 htl
      have et : _root_.Meaning.tlAt Zp.p.X (2 * g) = hp.tl := by
        unfold _root_.Meaning.tlAt
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega,
          ← hW, hG]
        rfl
      rw [et]
      exact ⟨a2, a1⟩
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
      obtain ⟨a1, a2⟩ := lay7_fields e3 htl
      have et : _root_.Meaning.tlAt Zp.p.X (2 * g + 1) = A.seam.tl := by
        unfold _root_.Meaning.tlAt
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show (2 * g + 1) / 2 = g by omega, ← hW, hA]
        rfl
      rw [et]
      exact ⟨a2.trans hL0.NM, a1.trans hL0.gtTree⟩

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lay7_fields
#print axioms ProofFile.Honest.K1.codes_at_reads
#print axioms ProofFile.Honest.K1.tail_at_reads
