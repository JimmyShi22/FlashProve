-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/VecJoin.lean: the closing of a segment (K10): at a stand in front of a closing, the maker of each segment's
vector of reads returns at the challenges heard in front of that sending (`VecAt`,
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnAtHead.lean), from ONE named premise on the twelve layers' segments.

  `LayersVec`           the named premise: the same sentence at the seats of the even segments 2 g, g < 12
  **`vecAt_at_stand`**   under the head, at the head's thread, at a stand in front of the closing of segment l < 25: `VecAt`, from
                      `LayersVec`. The twelve attention's segments by `vec_att_later` (Pay/MadeVecAtt.lean), the output head's by
                      `head_vec_at` (AtFullSide/K10/MadeVecHead.lean)
  **`made_first_of_layers`**   the field `made` of `ThreeLeftFirst` at the reference sizes at each of the 25 closings of the first
                      thread, from `LayersVec` at its stands

Limits. `LayersVec` is a premise. The head and the return of `onlineProverFromPublicFiles` are premises. Where the thread's invariant holds at no
stand of a border the statements hold there for nothing. The full size and the older hash alone.
-/
import AtFullSide.K10.MadeVecHead
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeVecAtt
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeFirstVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open OnBytes.Model (Head.Covered)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (covOf u3Seats valsAt)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-- **The named premise on the layers' segments**: at each seat of an even segment 2 g, g < 12, up to l, the maker of the
segment's vector returns at the challenges in front of the sending. A definition, meant as a premise. -/
def LayersVec (Z : ProofFile.Pub) (G : ProofFile.Ground) (cov : Head.Covered) (heard : List Fmt.Drawn) (l : Nat) : Prop :=
  ∀ a s g, OnBytes.HonestTrace.seatAt (u3Seats Z G) a = some s → s.seg = 2 * g → g < 12 → s.seg ≤ l →
    ∀ V, valsAt Z G cov s.seg = .ok V → ∃ v, V.vec (heard.take s.heard) = .ok v

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. The option turns off one early look at a notation's text, which has no case for a
-- field access; it loosens nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a stand in front of a closing the makers of the vectors of reads return**, where the layers' do. -/
theorem vecAt_at_stand {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : Nat} (hl : l < 25)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m E)
    (hLay : LayersVec Zp G ((covOf Zp G m.st.input.x).toOption.getD default) m.st.heard l) :
    VecAt Zp G ((covOf Zp G m.st.input.x).toOption.getD default) m.st.heard l := by
  intro a st hst hle V hV
  by_cases h24 : st.seg = 24
  · have e24 : l = 24 := by omega
    subst e24
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    have hlen : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.scope O
    have hB : 343 ≤ 14 * 24 + IM.nAt 24 + 5 := by
      unfold IM.nAt
      split <;> omega
    have hBl : 14 * 24 + IM.nAt 24 + 5 ≤ cF.blocksInOrder.length := by
      rw [hlen]
      unfold IM.nAt
      split <;> omega
    exact head_vec_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hG hst h24 hB hBl hT hV
  · rcases Nat.even_or_odd' st.seg with ⟨g, hg | hg⟩
    · exact hLay a st g hst hg (by omega) hle V hV
    · have hT' := hT
      unfold Thr at hT'
      obtain ⟨-, hFit, -, -, hM, -, -⟩ := hT'
      have hB : 14 * (2 * g + 1) + 4 + 1 < 14 * l + IM.nAt l + 5 := by
        unfold IM.nAt
        split <;> omega
      exact vec_att_later h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) hG hst hg hB hM hFit _ V hV

end

/-! ## At the first thread -/

section
variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o Sz.ref O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

include hA in
/-- **The field `made` at each of the 25 closings of the first thread**, at the reference sizes, from the one premise on
the layers' segments at its stands. -/
theorem made_first_of_layers (l : Nat) (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied h.firstChain A.Z l p Qc blk)
    (hL : ∀ k s m En, Thr (firstThread h parts w) (14 * l + IM.nAt l + 5) k s m En →
      LayersVec A.Z A.G ((covOf A.Z A.G m.st.input.x).toOption.getD default) m.st.heard l)
    {k : Coins A.B} {s : TS} {m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit} {En : Env} {ds : _} {y : _} {cols : _}
    {s' : TS}
    (St : StepAt (firstThread h parts w) Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s')
    {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (ca : CsAll (closeCarries (lotJob
      (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) (widerRows Sz.ref A.Z A.G)
      (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).pub)) :
    ∃ R, (lotJob (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers))
        (widerRows Sz.ref A.Z A.G) (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).rows
          m.st.input m.st.heard ca = .ok R ∧ rowsFit s.st D.G R = true := by
  have hblk : h.firstChain.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h.head (List.getElem?_eq_some_iff.1 hblk).1
  exact made_first_of_vec I o O hA h parts w l Said Td
    (fun k s m En hT => vecAt_at_stand h.head A.H parts.script _ _ _ _ _ _ _ _ _ w (atPure_ok hA).2.1 hl hT
      (hL k s m En hT)) St Hb ca

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.LayersVec
#print axioms ProofFile.Honest.K10.vecAt_at_stand
#print axioms ProofFile.Honest.K10.made_first_of_layers
