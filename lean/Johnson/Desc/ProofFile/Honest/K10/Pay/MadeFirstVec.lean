-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeFirstVec.lean: the closing of a segment (K10): the field `made` of the three premises
that the exchange at a closing still takes (`ThreeLeft`, Pay/Five.lean), at each of the 25 closings of the first thread, from
ONE named premise: at each seat of the reads of a segment up to the closing's, the maker of the segment's vector of reads
returns at the challenges heard in front of that sending (`VecAt`, Pay/MadeOwnAtHead.lean).

  `readsReady_first`    `ReadsReady` (Pay/MadeFirst.lean) at a stand of the first thread in front of a closing, from `VecAt` there
  **`made_first_of_vec`**   the field `made` at the first thread, at the reference sizes, from `VecAt` at its stands

Limits. `VecAt` is a premise. The reference sizes alone. The head and the return of `onlineProverFromPublicFiles` are premises. Where the thread's
invariant holds at no stand of a border the field holds there for nothing.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeFirst
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open OnBytes.HonestTrace (Sz)
open OnBytes.HonestTrace.U3 (covOf)
open P5J (TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o Sz.ref O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

include hA in
/-- At a stand of the first thread in front of a closing the reads' own messages are ready, where the makers of the
vectors return. -/
theorem readsReady_first {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied h.firstChain A.Z l p Qc blk) {k : Coins A.B} {s : TS}
    {m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit} {En : Env}
    (hT : Thr (firstThread h parts w) (14 * l + IM.nAt l + 5) k s m En)
    (Vr : VecAt A.Z A.G ((covOf A.Z A.G m.st.input.x).toOption.getD default) m.st.heard l) :
    ReadsReady A.Z A.G Qc m.st.input.x m.st.heard := by
  obtain ⟨Bs, base, Op⟩ := h.head.laid.opened
  have eG : A.G = Bs.G₀ := (base_ground_atPure Op.made hA rfl).symm
  have hblk : h.firstChain.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hl : l < 25 := link_lt h.head (List.getElem?_eq_some_iff.1 hblk).1
  have hQ : Qc.link = l := (IM.k10Par_fields Td.2.1).1.trans (IM.k9Where_fields Td.1).2.1
  have hx := okStart_at_stand h.head A.H parts.script _ _ _ _ _ _ _ _ _ w (fun _ hv => hv.1) hT
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, hFit, -, -, -, -, -⟩ := hT'
  have hd : drawsFit (declsTo h.firstChain.blocksInOrder (14 * l + IM.nAt l + 5)) m.st.heard = true := hFit
  rw [eG] at Vr ⊢
  exact reads_at_closing h.head Op hl hQ hx hd Vr

include hA in
/-- **The field `made` at each of the 25 closings of the first thread**, at the reference sizes, from `VecAt` at its stands. -/
theorem made_first_of_vec (l : Nat) (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied h.firstChain A.Z l p Qc blk)
    (hV : ∀ k s m En, Thr (firstThread h parts w) (14 * l + IM.nAt l + 5) k s m En →
      VecAt A.Z A.G ((covOf A.Z A.G m.st.input.x).toOption.getD default) m.st.heard l)
    {k : Coins A.B} {s : TS} {m : Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit} {En : Env} {ds : _} {y : _} {cols : _}
    {s' : TS}
    (St : StepAt (firstThread h parts w) Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s')
    {D : BaseData} (Hb : CloseBase Qc (recOf s) D)
    (ca : CsAll (closeCarries (lotJob
      (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) (widerRows Sz.ref A.Z A.G)
      (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).pub)) :
    ∃ R, (lotJob (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers))
        (widerRows Sz.ref A.Z A.G) (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G Qc).rows
          m.st.input m.st.heard ca = .ok R ∧ rowsFit s.st D.G R = true :=
  made_first I o O hA h parts w l Said Td
    (fun k s m En hT => readsReady_first I o O hA h parts w Td hT (hV k s m En hT)) St Hb ca

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.readsReady_first
#print axioms ProofFile.Honest.K10.made_first_of_vec
