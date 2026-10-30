-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StatedHead.lean: CONDITIONAL. Statements with their proofs.

What is here: the clause stated of `K4FrontAt` (Law/Kept.lean), in its own text but at every number
n and all data, at every accepted step of the member of the feed-forward layers' own rounds
(sub-protocol K4) where the first chain's thread stands, at the library's own values (`lettersHead`,
Honest/Thread/FirstHead.lean), under h, the hypothesis on the public files (`P5J.AtMgA`), and at the
library's own list of the segment's arrays' names. WITH Law/FrontHead.lean's `asks_head`,
`names_head` AND `reads_head` THESE ARE THE FOUR CLAUSES THAT `k4_exchange_tenth`
(Law/ExchangeTenth.lean) LAYS TOGETHER THERE, at that list.
How. The data's stated function is by definition one function with three arms (`MgData.St`,
Johnson/Desc/Sound/MgAll.lean), whose layers' arm is `uLAt` at the public parameters and that list
of names (Johnson/Road/K4/ULayAt.lean; Johnson/P5J/LettersAll.lean). At the open segment's number
that arm is `uLay` at the plan's structure for the smallness test (`tlAt_plan`,
Johnson/Road/K4/K4PinsScope.lean); that the state's open segment bears the number m is a field of
the library's `RecIs` (Johnson/Road/K4/Rec/Whole.lean), had behind the step from
Law/FrontHead.lean's `ownFront_at_all`. Then the library's `statedAt_of_is`
(Johnson/Road/K4/ArmLay.lean).

Not shown here. THAT THE THREAD HOLDS AT ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: hT and hS
are hypotheses. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Of h together with hb, hT and hS no example is known to us
(`LaidK4`: h gives it at each group: `laid_at`, Law/LaidAtGroup.lean). THE FULL SIZE's WRITTEN LISTS
ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). THE CLAUSE IS SHOWN AT ONE VALUE OF
THE LETTER names ALONE: the library's own list of the segment's arrays' names (`P5J.At.names3 Zp m`,
Johnson/P5J/LettersAt3Lay.lean): the stated function is the data's own and does not move with that
letter, the matrices do: whether the clause holds at another list is shown by no statement. It says
what the stated function's cells ARE, by the definition of that function: nothing on what any
committed cell is worth. Nothing on soundness, on completeness or on any other property.
No property is claimed. The imports reach modules under Johnson/Goal/, as those of
Law/ElevenHead.lean do: A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.

  `recIs_behind_all`   behind an accept the open segment's part reads as the plan says
  `stated_head`   **the clause stated at the thread**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontHead
import Johnson.Road.K4.ArmLay
import Johnson.Road.K4.ULayAt
import Johnson.Road.K4.K4PinsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD K4NamedW CellsK KeptAtS kept_atS parOf k4DataWide StatedAt
  uLay uLAt statedIs_uLAt statedAt_of_is tlAt_plan)
open OnBytes.Road.K4.Rec (RecIs recPlanOf recIs_at_state recIs_behind)
open OnBytes.Road.K4.More (PS K4Fence)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit)
open VerifiableInference.Desc.First (S pubAll ePubAt bookAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (GQ MsgT MgData WideData mgBase linksFull moreAll second
  linkNo StatedIs matsOfData mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head)

/-! ## 1 At the composed meaning's own public tests -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

variable {k m : ℕ} {pl : Place} {par : Par}
  {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
  {layout : Option ByteArray} {n : ℕ}

/-- **Behind an accept the open segment's part reads as the plan says.** After the proof text of the
library's `four_of_kept` (Johnson/Road/K4/Rec/InTFour.lean). CONDITIONAL on every hypothesis named.
-/
theorem recIs_behind_all (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n) (Sn : K4NamedW Dm E k m par told n)
    {z : P} {s s' : S} (K : KeptAtS par s s')
    (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true)
    (hb : bookAt Dm.N PS[k]? s = true) (Fc : K4Fence Dm E m s) :
    ∀ A', segAt? s' = some A' →
      RecIs A' (recPlanOf (k4DataWide Dm E Bm) (k4DataWide Dm E Bm).sd)
        ((k4DataWide Dm E Bm).N.msgsAt PS[k]?) m := by
  intro A' hA'
  have OF := ownFront_at_all hH H Sx Sd Sn hE hb Fc
  have K0 := K
  obtain ⟨a, _, _, _, ha, _⟩ := K0
  obtain ⟨A₀, hA₀, _, _⟩ := OnBytes.Desc.First.K4.InT.segAt_lay ha
  exact recIs_behind K (OnBytes.Road.K4.Rec.sized_of_ledgerB OF.ledger) hA₀ hA'
    (recIs_at_state hA₀ OF.live OF.fresh OF.seats OF.shapes OF.sent OF.trees OF.codes OF.places
      OF.msgs)

end

/-! ## 2 At the thread with the library's own values -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE CLAUSE stated**, at the library's own list of the segment's arrays' names, at every number
nn and all data Dt. CONDITIONAL: on h, Lh, hb, hT and hS. -/
theorem stated_head
    {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {blk : Block TS ProofFile.Cl}
    (hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.bs[k]? = some blk)
    {c : Coins Bk} {s s' : TS} {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hS : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.Stepped blk c s mm E ds y
      cols s') :
    ∀ A' o cc, segAt? s' = some A' → s'.own? = some o → A'.L.arrayOf[o.v.iU3]? = some cc →
      second s' cc = true → ∀ (nn : ℕ) (Dt : Bound GQ),
      StatedAt h.𝔇.St (fun _ B => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) B) s' x.2.hp.tl o cc nn
        Dt := by
  intro A' o cc hA' ho hc h2 nn Dt
  have A := atK4_of_laid Lh
  obtain ⟨hH, Sx, Sd, _, hbd⟩ := nine_head h Lh
  have Sn := named_head h Lh
  obtain ⟨_, hdec⟩ := k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh blk hb s _ _ s' _
    hS.2
  have K : KeptAtS (parOf x) s s' := kept_atS hdec
  obtain ⟨_, t2, t3⟩ := thr_tests h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  have heard := k4_heard_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁
    (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A Sx Sd c s mm E hT
  have Fc := k4Fence_at h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A.here A.link
    (by rw [A.piece]; exact Nat.le_succ 2) (by omega) hT heard
  have r' := recIs_behind_all hH A Sx Sd Sn K
    (ePubAt_of_held (Dm := h.𝔇)
      (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
      (mgAll_more_base h.𝔇) t2) t3 Fc A' hA'
  -- the state behind stands in a layers' segment, whose context is the part's
  have K0 := K
  obtain ⟨a, _, _, _, ha, _, _, _, _, _, _, _, hR, _⟩ := K0
  obtain ⟨b, hb', _⟩ := hR.here a ha
  obtain ⟨A'', hA'', _, eL⟩ := OnBytes.Desc.First.K4.InT.segAt_lay hb'
  obtain rfl : A'' = A' := Option.some.inj (hA''.symm.trans hA')
  have ho' : b.own = some o := by
    unfold VerifiableInference.Desc.First.S.own? at ho
    rw [hb'] at ho
    exact ho
  have hc' : b.L.arrayOf[o.v.iU3]? = some cc := by
    rw [← eL]
    exact hc
  have hno : linkNo s' = m := by
    have hL : s'.link? = some b.L := by simp only [VerifiableInference.Desc.First.S.link?, hb']
    unfold linkNo
    rw [hL, ← eL]
    exact r'.link
  have htl : VerifiableInference.Desc.First.Look.tlAt (P5J.At.X Zp) m = some (parOf x).hp.tl :=
    tlAt_plan Sx.notHead Sx.step Sx.plan
  have e : uLAt (P5J.At.X Zp) (P5J.At.names3 Zp) (linkNo s') =
      uLay x.2.hp.tl fun _ B => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) B := by
    rw [hno]
    unfold uLAt
    rw [htl]
    rfl
  have I : StatedIs h.𝔇.St
      (uLay x.2.hp.tl fun _ B => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) B) s' := by
    rw [← e]
    exact statedIs_uLAt (P5J.At.X Zp) (P5J.At.names3 Zp) h.𝔇.uA h.𝔇.uH hb'
  exact statedAt_of_is I hb' ho' hc' h2 nn Dt

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.recIs_behind_all
#print axioms ProofFile.Honest.K4.stated_head
