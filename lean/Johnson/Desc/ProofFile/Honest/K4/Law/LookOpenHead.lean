-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookOpenHead.lean: CONDITIONAL.

What is here. Three things beside Law/LookPtsHead.lean, at the thread with the library's own values
(`lettersHead`, Honest/Thread/FirstHead.lean), in front of the member of the feed-forward layers'
own rounds (sub-protocol K4). (1) Wherever the thread stands, the state's two readers of what the
lookup has heard find one structure, and THAT STRUCTURE AGREES IN ALL ELEVEN FIELDS of `OpenSame`
(Honest/K3/HeardWhole.lean) with the text `lookOfK3` of the authors of the kind "lookup" at the
challenges heard (`openSame_head`): no hypothesis on the parameter `look`. (2) So the tie at six
fields, `K4LookWideAt` (Law/ScriptAt.lean), holds there if `look` agrees with that text in these six
(`LookIsK3Wide`; `lookWide_k3`). (3) If `look Qp` is that very text at the public data's own group,
at every list of challenges, then `LookIsK3Wide` and `LookIsK3` hold (`look_fill`): the text does
not read its instance, and the public data's group is the member's (`pub_is`,
Law/W/FieldsAtStand.lean). Each proof is a chain of calls.

  `openSame_head`   **the eleven fields, where the thread stands.**
  `LookIsK3Wide`   the sentence on `look` at six fields. A definition.
  `lookWide_k3`   **`K4LookWideAt look Qp s mm`**, from it.
  `look_fill`   both sentences on `look`, where `look` is the text itself.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN: hT
: Thr is a hypothesis. hL (`LookIsK3Wide`) and hfill: HYPOTHESES ON THE PARAMETER `look`, at every
list of challenges: THAT ANY PROVER's HALF IS LAID OVER SUCH A `look` IS NOT SHOWN: the lot takes
`look` as a parameter (Honest/K4/Part.lean), and whoever lays the halves fills it. hfill IS NOT MET
AT THE FRAME's FILLING `widerFill` (Honest/AtPureWider.lean), WHICH LAYS K4's LOT OVER ANOTHER TEXT,
`k4LookAt` (Honest/K4/Look.lean), which is not that text as a whole structure wherever the shape has
a call (`lookOf_ne`, Law/LookAtFill.lean): there the two sentences are `lookAt_isK3`'s (the same
file), not `look_fill`'s. `lookOfK3` lays eleven fields and leaves the structure's eight others
blank: a part that read one of these off it would read a blank. By its authors' word it has been
evaluated at no data, and two of its fields are dear to make. Lh (`LaidK4`, Law/SeatedHead.lean) and
hQ: on public lists and numbers. The side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Of h together with Lh, hQ, hfill, hT and hL no example is known to
us. No test that can fail stands beside them. THE FULL SIZE ALONE, and the format's second hash function
alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 80 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 88 is not counted: all the numbers are floors. Through
Law/LookPtsHead.lean it imports a file of the authors of the kind "lookup". A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LookPtsHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FieldsAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (eAll)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block foldBlocks)
open VerifiableInference.Desc.First.FillK4 (lookLayB)
open VerifiableInference.Desc.Sound (MsgT mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pub)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open ProofFile.Honest.K3 (OpenSame)
open ProofFile.Honest.K3.Law.AtThr (lookOfK3 layers_tie_head)

/-- **The sentence on `look` at six fields**: at every list of challenges it agrees with the text of
the authors of the kind "lookup" in zx, zk, e, shape, zb0 and zb1. This defines a hypothesis; the
definition claims nothing. -/
def LookIsK3Wide (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub) (Zp : ProofFile.Pub)
    (cF : Chain TS ProofFile.Cl) (g : ℕ) (ξ : ProofFile.Inst) : Prop :=
  ∀ hd, (look Q hd).zx = (lookOfK3 Zp cF g ξ hd).zx ∧ (look Q hd).zk = (lookOfK3 Zp cF g ξ hd).zk ∧
    (look Q hd).e = (lookOfK3 Zp cF g ξ hd).e ∧
    (look Q hd).shape = (lookOfK3 Zp cF g ξ hd).shape ∧
    (look Q hd).zb0 = (lookOfK3 Zp cF g ξ hd).zb0 ∧ (look Q hd).zb1 = (lookOfK3 Zp cF g ξ hd).zb1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on Lh, hQ and hfill. **WHERE `look` IS THE TEXT ITSELF.** ξ₀, ξ: instances; the
text reads neither. -/
theorem look_fill {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp)
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} (ξ₀ ξ : ProofFile.Inst)
    (hfill : ∀ hd, look Qp hd = lookOfK3 Zp cF Qp.g ξ₀ hd) :
    LookIsK3Wide look Qp Zp cF g ξ ∧ LookIsK3 look Qp Zp cF g ξ := by
  obtain ⟨_, _, eg⟩ := pub_is Lh hQ
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · rw [hfill hd, eg]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [hfill hd, eg]
    exact ⟨rfl, rfl, rfl⟩

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh and hT. **THE ELEVEN FIELDS, WHERE THE THREAD STANDS.** ξ: any
instance. -/
theorem openSame_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ξ : ProofFile.Inst) :
    ∃ g₁, s.lookHeard? = some g₁ ∧ seatS.look s = some g₁ ∧
      OpenSame g₁ (lookOfK3 Zp cF g ξ mm.st.heard) := by
  have N := nine_head h Lh
  obtain ⟨_, t2⟩ := two_tests (Dm := h.𝔇) (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH (atK4_of_laid Lh) N.Sx N.Sd
    (fun q hq => thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  unfold lookLayB at t2
  split at t2
  · rename_i a ha
    rw [Bool.and_eq_true, decide_eq_true_eq] at t2
    obtain ⟨t3, e⟩ := t2
    cases hfo : a.fo with
    | none => simp [hfo] at t3
    | some g₁ =>
      have h1 : s.lookHeard? = some g₁ := by
        simp only [VerifiableInference.Desc.First.S.lookHeard?, ha]
        rw [← e]
        exact hfo
      have h2 : seatS.look s = some g₁ := by
        simp only [seatS, ha]
        exact hfo
      obtain ⟨_, _, _, _, hM, _, _⟩ := hT
      obtain ⟨e1, _, _, _, s₀, cols, _, _, hf⟩ := hM
      have hf' : foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) s₀ mm.seen cols = .ok (s, [], []) := by
        rw [← Lh.num]
        exact hf
      have W := layers_tie_head h g Lh.lt s₀ ξ mm.seen cols s [] [] a g₁ hf' ha hfo
      obtain ⟨er, _⟩ := ProofFile.Honest.K3.Law.AtThr.fold_rest 0 _ _ _ _ _ _ _ hf'
      have et : mm.seen.take ((cF.blocksInOrder.take (28 * g + 4)).flatMap (·.rounds)).length = mm.seen :=
        List.take_of_length_le (List.drop_eq_nil_iff.1 er.symm)
      rw [et, e1] at W
      exact ⟨g₁, h1, h2, W⟩
  · cases t2

/-- CONDITIONAL: on h, Lh, hT and hL. **THE TIE AT SIX FIELDS, WHERE THE THREAD STANDS.** -/
theorem lookWide_k3 {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hL : LookIsK3Wide look Qp Zp cF g mm.st.input.x) : K4LookWideAt look Qp s mm := by
  obtain ⟨g₁, h1, h2, W⟩ :=
    openSame_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT mm.st.input.x
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hL mm.st.heard
  exact ⟨g₁, h1, h2, b1.trans W.zx.symm, b2.trans W.zk.symm, b3.trans W.e.symm,
    b4.trans W.shape.symm, b5.trans W.zb0.symm, b6.trans W.zb1.symm⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.look_fill
#print axioms ProofFile.Honest.K4.W.openSame_head
#print axioms ProofFile.Honest.K4.W.lookWide_k3
