-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FrontBridge.lean: FOR THE ITEM "totalB": TWO FILLINGS OF OUR FREE LETTER Front, AND ONE
BRIDGE BETWEEN THEM AT A STAND. Why: our assemblies (Honest/K9/TotalWorthTwo.lean) read the witness by the library's
clamped reader `LinkJoin.rdC`; the composed meaning's sentences, and so the frame's own thread, read it by
`Sound.seatTab`. The library ties the two by three "if and only if"s (Johnson/Desc/Sound/Clamp/FormsClamp.lean) UNDER A
FACT ON THE STATE's PART (`InsideAt`): a fact that can be had at a stand and not at every state. `GivesTotalB` is stated
at a stand: so the bridge stands there. Two definitions (premises' forms) and one theorem; no prover is in this file; no
goal is stated.
  `frontC h l xx tlD`   THE ASSEMBLIES' Front: at an entry o that is not "K8.equations": the library's `formsQ` at the
      head's data's readers, group and the reader `rdC`; at "K8.equations": its `formsQA` there, and the two sentences
      "worth" of the lookup on the digits (`LinkJoin.WorthTwo` at the data's letters)
  `frontS h l xx tlD`   THE EXCHANGE's Front: the frame's own filling `frontAt h l` (Honest/Law/Rule/HeadFront.lean: the
      same sentences at `seatTab`), and at "K8.equations" the two sentences "worth" beside
  **`givesTotalB_seat`**   l < 25: `GivesTotalB` at the frame's own thread at the head, at own := `h.𝔇.N.group l`, the
      reader `rdC` and `frontC`, gives it at `seatTab` and `frontS`: UNDER hin (`InsideAt` at the part of a stand's
      state in front) AND hbeh (`InsideAt` at the part behind what runs behind the batching). "Inside" for what is read
      ahead (`InsideAhead`) is idle at a stand: `noAhead_at_head` (Honest/K9/AheadAt.lean)
WHAT IS NOT CLAIMED. hin, hbeh or the premise hG here (paid in Honest/K9/InsideAtStand.lean, InsideBehind.lean and
FrontLaid.lean). That a stand is there: NO MEMBER. `givesTotalB_seat` is called by Honest/K9/FrontLaid.lean alone;
`frontC` and `frontS` are named there, and `frontS` in Honest/K9/TotalExchangeHead.lean too. Nothing on any property.
SINCE THIS FILE Honest/K9/AheadAt.lean's head's list of who calls `noAhead_at_head` lacks this file. That file is not
turned.
GROUND: beneath this file, beside the sealed library, lie 576 files, this one among them: what lies beneath
Honest/K9/TotalWorthTwo.lean, and two more of the frame's (Honest/Law/Rule/HeadFront.lean,
Honest/Law/NoHouse/EntryItem.lean): reading copies, all but ours.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalWorthTwo
import Johnson.Desc.ProofFile.Honest.K9.AheadAt
import Johnson.Desc.ProofFile.Honest.Law.Rule.HeadFront
import Johnson.Desc.Sound.Clamp.FormsClamp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The assemblies' Front**: what the table's item of the entry o of segment l says, READ AT THE CLAMPED READER; at
"K8.equations" the two sentences "worth" of the lookup on the digits beside. -/
def frontC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (xx : First.Look.Place) (tlD : HTailF2)
    (o : ℕ × String) (s : TS) (v : WtF) : Prop :=
  (o.2 ≠ "K8.equations" →
    Sound.formsQ (h.𝔇.Rd l) (h.𝔇.N.group l) o.1 o.2 s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) ∧
  (o.2 = "K8.equations" →
    Sound.formsQA (h.𝔇.N.sent l) (h.𝔇.N.group l) (h.𝔇.Rd l) o.1 o.2 s (LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) ∧
      LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent h.𝔇.l3.rad
        (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v)

/-- **The exchange's Front**: the frame's own filling `frontAt` (at the witness's tables by seat); at "K8.equations" the
two sentences "worth" beside. -/
def frontS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (xx : First.Look.Place) (tlD : HTailF2)
    (o : ℕ × String) (s : TS) (v : WtF) : Prop :=
  frontAt h l o s v ∧ (o.2 = "K8.equations" →
    LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent h.𝔇.l3.rad
      (fun j => h.𝔇.l3.seat xx.link true j.1) h.𝔇.l3.arr s v)

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE BRIDGE, AT A STAND**: from the clamped reader and `frontC` to the witness's tables by seat and `frontS`: by
the library's three "if and only if"s, under "inside the members' ranges" at the part in front (hin) and behind what
runs behind the batching (hbeh). -/
theorem givesTotalB_seat {l : ℕ} (hl : l < 25) {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} (xx : First.Look.Place)
    (tlD : HTailF2) (rw : S → Bool) (tst : S → Option String)
    (hG : GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) (h.𝔇.N.group l) (fun v => LinkJoin.rdC h.𝔇.cs h.𝔇.arr h.𝔇.ms v) rw tst
      (frontC h l xx tlD))
    (hin : ∀ κ s m En ds y cols s' x' z G, BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G →
      ∀ a, Desc.K9.segAt? s = some a → Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) a)
    (hbeh : ∀ κ s m En ds y cols s' x' z G,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G →
      ∀ t a, Lk.runBehind s' = .ok t → Desc.K9.atS.get? t = some a →
        Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) a) :
    GivesTotalB Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps l) (h.𝔇.N.group l) (fun v => Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) rw tst
      (frontS h l xx tlD) := by
  intro κ s m En ds y cols s' x' z G St v hF ht
  have hA := noAhead_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl Lk p (h.𝔇.N.sent l) (h.𝔇.N.group l)
    κ s m En ds y cols s' x' z G St
  have hI := hin κ s m En ds y cols s' x' z G St
  obtain ⟨h1, h2⟩ := hG κ s m En ds y cols s' x' z G St v (fun o ho => by
    obtain ⟨f1, f2⟩ := hF o ho
    refine ⟨fun hne => ?_, fun he => ⟨?_, f2 he⟩⟩
    · have ea : h.𝔇.ah o.1 o.2 = false := by
        show (o.2 == "K8.equations") = false
        exact beq_false_of_ne hne
      unfold frontAt at f1
      rw [ea, if_neg (by simp)] at f1
      exact (Sound.formsQ_clamp h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group l) (h.𝔇.Rd l) o.1 o.2 s v hI).2 f1
    · have ea : h.𝔇.ah o.1 o.2 = true := by
        show (o.2 == "K8.equations") = true
        rw [he]
        rfl
      unfold frontAt at f1
      rw [ea, if_pos rfl] at f1
      exact (Sound.formsQA_clamp h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group l) (h.𝔇.Rd l) (h.𝔇.N.sent l) o.1 o.2 s v
        fun a ha => ⟨hI a ha, fun b0 hh b J y hx => by
          rw [hA a ha b0] at hx
          cases hx⟩).2 f1) ht
  exact ⟨(Sound.totalBQ_clamp h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group l) Lk.runBehind s' v
    (hbeh κ s m En ds y cols s' x' z G St)).1 h1, h2⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.givesTotalB_seat
