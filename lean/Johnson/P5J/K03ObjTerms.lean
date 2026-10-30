-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03ObjTerms.lean: THE KIND "LOOKUP" (K3): THE TERMS OF THE COMPOSED MEANING's READERS AT THE CONSTANT: what the lookup's files' three joinings for the field "objects" (objects_att_mgAll | objects_lay_mgAll · calls_objects_head · digObjR_mgAll) leave beside tests and facts on reached states: hrun · hah · hlink · hpass · hfind · hSt. One definition, nine theorems. A joining: by calls alone.

UNDER h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (Johnson/P5J/MgAtAll.lean); 𝔇 := h.toAtMg.𝔇 h.𝔇; the lot's maker of claims K3Lot.ofForm.
THE WEIGHT LIES ELSEWHERE: Johnson/Desc/First/Look/K03States.lean: k03_atS2_calls | k03_atS2_digits (hA at both seats: not typed here) · sameReply_putFork · k03_objects_of (in scope, at the fifty places: what find? finds under "objects" at the description's own link: the kind's run behind the driver's guard on the reply's seat); guardRun_yes (Johnson/IMR/SeatForm.lean). hMg at the constant is "fun _ _ _ h => h" (by report): not typed here.
  k03_cl     ProofFile.Cl = Desc.Claim (rfl): the constant's type of claims is the library's.
  passR      what the guard asks: the reply's seat is as it was.
  k03_hrun   at a written segment m of the sort sub: (1 + shift sub, "objects") stands among 𝔇.runs m (2 + shift sub) "objects", and (6 + shift sub, "objects") among 𝔇.runs m (7 + shift sub) "objects".
  k03_hah    𝔇.ah pr "objects" = false.
  k03_hlink  where the head's own chain has a link l at m: 𝔇.Rd m = readersOfLink (holesAt X (headLink X) m l) l (𝔇.lk is ProofFile.linkAt Zp; LaidAt.linkAt ties it to the chain's letter).
  k03_hpass  laying a ledger passes the guard.
  k03_over   the guarded run is the run wherever the guard passes (RunOver).
  k03_hfind  AT EVERY m < 25, BOTH LOOKUPS: ONE LINK l FOR hlink AND hfind TOGETHER.
  k03_ix     the index IM.k3Ix of the lookup in link m is k03_hrun's number.
  k03_hSt    the stated functions leave the masks.
Limits. The head is a premise (a member of the head is proved at the second hash function OnBytes.secondHashFunction, at two written sets of public files VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap, in the side library (AtFullSide/Top/: headMember_zFull, headMember_zGap); at other files or hashes none is shown). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.ChainFree
import Johnson.Desc.First.Look.K03States
import Johnson.Desc.First.Batch.ReadersAt
import Johnson.Top.H.Keep.RunUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink holesAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The constant's type of claims is the library's. -/
theorem k03_cl : ProofFile.Cl = VerifiableInference.Desc.Claim := rfl

/-- What the driver's guard asks of a run: the reply's seat is as it was. -/
def passR (t t' : VerifiableInference.Desc.First.S) : Prop := ProofFile.sameReply t t' = true

theorem k03_hrun (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (sub : ModelPart)
    (hs : At.links[m]? = some sub) :
    (1 + shift sub, "objects") ∈ (h.toAtMg.𝔇 h.𝔇).runs m (2 + shift sub) "objects" ∧
      (6 + shift sub, "objects") ∈ (h.toAtMg.𝔇 h.𝔇).runs m (7 + shift sub) "objects" := by
  have e : ∀ k, (h.toAtMg.𝔇 h.𝔇).runs m k "objects" =
      VerifiableInference.Desc.First.runsOf sub k "objects" := by
    intro k
    show runsAt At.links m k "objects" = _
    unfold runsAt
    rw [hs]
    rfl
  rw [e, e]
  cases sub <;> exact ⟨by decide, by decide⟩

theorem k03_hah (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (pr : ℕ) :
    (h.toAtMg.𝔇 h.𝔇).ah pr "objects" = false := by
  show ("objects" == "K8.equations") = false
  decide

theorem k03_hlink (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ)
    (l : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim)
    (hl : cF.links[m]? = some l) :
    (h.toAtMg.𝔇 h.𝔇).Rd m = readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) m l) l :=
  VerifiableInference.Desc.K9.readersAt_some _ _ _ _ l ((h.laid.linkAt m).trans hl)

theorem k03_hpass : ∀ t G, passR t (t.putFork G) := sameReply_putFork

/-- The guarded run is the run wherever the guard passes. -/
theorem k03_over (run : ℕ → VerifiableInference.Desc.First.S →
    Except String (List ProofFile.Cl × VerifiableInference.Desc.First.S)) :
    RunOver passR (IM.guardRun ProofFile.sameReply run) run :=
  fun n t y hr hp => (IM.guardRun_yes run n t y).2 ⟨hr, hp⟩

/-- **ONE LINK FOR hlink AND hfind, AT EVERY WRITTEN SEGMENT, BOTH LOOKUPS.** -/
theorem k03_hfind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) (d : Bool) :
    ∃ l : Link VerifiableInference.Desc.First.S VerifiableInference.Desc.Claim,
      cF.links[m]? = some l ∧
      (h.toAtMg.𝔇 h.𝔇).Rd m = readersOfLink (holesAt (At.X Zp) (headLink (At.X Zp)) m l) l ∧
      ∃ nm run, (statesOfLink l (IM.k3Ix m d)).find? (fun r => r.1 == "objects") = some (nm, run) ∧
        RunOver passR run (objectsRun (seatOf K3Lot.ofForm d)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨l, h1, h2⟩ := k03_objects_of h.scope h.reads O m hm d
  exact ⟨l, h1, k03_hlink h m l h1, _, _, h2, k03_over _⟩

/-- The index of the lookup in link m is the table's number. -/
theorem k03_ix (m : ℕ) (hm : m < 25) (sub : ModelPart) (hs : At.links[m]? = some sub) :
    IM.k3Ix m false = 1 + shift sub ∧ IM.k3Ix m true = 6 + shift sub := by
  interval_cases m <;> (obtain rfl : _ = sub := Option.some.inj hs) <;> exact ⟨rfl, rfl⟩

theorem k03_hSt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ s Dt j, ((h.toAtMg.𝔇 h.𝔇).St.at1 s Dt).mask j = Dt.mask j := fun _ _ _ => rfl

end P5J

#print axioms P5J.k03_cl
#print axioms P5J.k03_hrun
#print axioms P5J.k03_hah
#print axioms P5J.k03_hlink
#print axioms P5J.k03_hpass
#print axioms P5J.k03_over
#print axioms P5J.k03_hfind
#print axioms P5J.k03_ix
#print axioms P5J.k03_hSt
