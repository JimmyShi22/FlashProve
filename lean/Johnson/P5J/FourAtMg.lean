-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FourAtMg.lean: FOUR OF THE PROOF FILE'S SEVEN FIELDS, WITH A WRITTEN STATEMENT, UNDER
    THE ONE HEAD: at the IOP as written in Lean that the verifier itself lays
(`AtMg`, AtMg.lean: in scope · the files are read · the value is laid · the named tests on the list
    of rounds accept), at the
composed meaning's constant (`mgAt`'s letter, MgAtConst.lean), at the places of the second form of
    the chain of promises with
"reached" NAMED (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean, ReachThree.lean).
  `LaidAt.atDepth`: in scope the laid data stand at the frame's depth of the committed table (by
      `data_depth`,
    `seat_in_scope`, `asks_written`: the proof of `laidPOf_depth32`, from the structure LaidAt's
        fields).
  `AtMg.rc`: what "reached" says of what the first chain hands on: reached at the number of the
      first chain's sub-protocols.
  `AtMg.places`: `plRF` (TowerFree.lean) at the seated term's letters.
  **`four_fields_at_mg`**: AtMg … → the three lists' heads → 2⁻¹²⁸ ≤ εs → `FourFields` …
      (FourFields.lean: fields 4 · 5 · 6 · 7 of
    `RowsOfProofFile`, in the form in which `rows_at_descB` takes or lays them), for every 𝔏 : Free
        ….
Limits. THE OTHER THREE FIELDS (the three chains lead: the kinds' laws and the tables) ARE NOT IN
    IT. (7) is free because the pieces carry
the cap as their errors. (6) binds the one next token as a field of the verifier's state.
THE RIDER BESIDE "REACHED" IS "THE PUBLIC PART IS A TYPED INSTANCE's" (h.typed: ∃ z, p
    = (instanceAsPlainRecord z).pub), not "the key fits" : it reads no letter of 𝔏 (so 𝔏 can be laid at
    constants whose own letter R is h.rc: no circle), it is other
files' seat's own R, and "the key fits" follows from it and one fact hk on 𝔏.Pm.shape 0
    (KeyFitsAtMg.lean).




    It stands over the form of "reached" in Johnson/Top/H0/Walk/ReachAt.lean, ReachThree.lean (the families step by the WRAPPED sub-protocols); h.rc is its EndAt₁ with the rider.
The default request is the constant's own (At.d₀), no letter;

pp is no letter (ppAtFiles Z.pol Z.KL) and E is closed (At.EAt Z: the top statements' own
    coding). 𝔇₀ and 𝔏 are letters. Whether AtMg can
be met at the release's own files is not shown here. The full size alone. No soundness follows.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TowerFree
import Johnson.P5J.MgAtConst
import Johnson.P5J.TokTerms
import Johnson.Top.H0.Walk.ReachThree
import Johnson.Desc.Laid.ProofFullScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain)
open Johnson.Desc.First.Walk.Tied (RchAt EndAt₁ rchAt_zero)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **In scope the laid data stand at the frame's depth of the committed table.** -/
theorem LaidAt.atDepth (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : D.at frS.P.T.a = D := by
  have e : D.a = frS.P.T.a :=
    ((LPFD.Full.data_depth _ L.data).trans
      (VerifiableInference.PlanWritten.seat_in_scope _ _ Z hZ (LPFD.asks_written L.asks)).2.1).trans
      (by decide)
  cases D
  subst e
  rfl

/-- **"The key fits", in the shared table's own word**: at the public part p the shared chain's
    first state has the shape that the shared table's promise asks at its
first border. A fact of the public part AND OF THE LETTER 𝔏.Pm. -/
def AtMg.kf (_ : AtMg o Z D r Zp Np cF) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (p : (F0T o Zp Np cF).XiPub) : Prop :=
  𝔏.Pm.shape 0 ((F0T o Zp Np cF).start₂ p) = true

/-- **The public part is a typed instance's.** A fact of the public part alone: it reads no letter
    of 𝔏. -/
def AtMg.typed (_ : AtMg o Z D r Zp Np cF) (p : (F0T o Zp Np cF).XiPub) : Prop :=
  ∃ z : LPFD.Full.XF × RecFull, p = (LPFD.Full.instanceAsPlainRecord z).pub

/-- **The condition beside the first table's promise**: "reached" (`RchAt`), and the
    statement's public part is a typed instance's. -/
def AtMg.rch (h : AtMg o Z D r Zp Np cF) (k : ℕ)
    (a : ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a))).Str) : Prop :=
  RchAt (F0T o Zp Np cF) k a ∧ h.typed a.1.1

/-- What goes on to the two later tables: reached at the number of the first chain's sub-protocols
    (`EndAt₁`), and the public part is a typed instance's. -/
def AtMg.rc (h : AtMg o Z D r Zp Np cF)
    (p : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) : Prop :=
  EndAt₁ (F0T o Zp Np cF) p ∧ h.typed p.1

/-- **The conditions and relations at the three chains, at the seated term, "reached" named.** -/
def AtMg.places (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :=
  plRF (pp := ppAtFiles Z.pol Z.KL) (X := At.X Zp) numsFull D (F0T o Zp Np cF) (fun s => s)
    (fun q : ProofFile.InstPub => q.request) (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) At.d₀ (At.cs Zp)
    (At.arr Zp)
    (At.ms Zp Z.lay) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
    (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X Zp)))
        tokVOf
    h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps
    (h.𝔇 𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    h.rch h.rc 𝔏

set_option maxHeartbeats 4000000 in
/-- **FIELDS 4 · 5 · 6 · 7 OF THE PROOF FILE's SEVEN, UNDER THE ONE HEAD.** -/
theorem four_fields_at_mg (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (q₁ : (F0T o Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T o Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T o Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (εs : ℝ≥0∞) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ εs) :
    FourFields numsFull (At.EAt Z) D 𝔏.rP ((F0T o Zp Np cF).pull LPFD.Full.instanceAsPlainRecord)
      (tpF numsFull (At.EAt Z) D (F0T o Zp Np cF) LPFD.Full.instanceAsPlainRecord 𝔏) (h.places 𝔇₀ 𝔏)
      (meansSome numsFull (ppAtFiles Z.pol Z.KL) (At.EAt Z) D ((F0T o Zp Np cF).pull
          LPFD.Full.instanceAsPlainRecord)
        (VerifiableInference.Desc.Sound.allOf (D.at frS.P.T.a)) (At.X Zp) (repHeard fun s => s))
      (ksK o Zp Np cF) εs :=
  fourFieldsF (Z := Z) (lay := some Z.lay) (X := At.X Zp) numsFull (At.EAt Z) D (F0T o Zp Np cF)
    LPFD.Full.instanceAsPlainRecord (fun s => s) (fun q : ProofFile.InstPub => q.request)
    (dtK (At.EAt Z) o Zp Np cF h.plan.shape 0) ProofFile.Inst.asked At.d₀ (At.cs Zp) (At.arr Zp)
    (At.ms Zp Z.lay)
    (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
    (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X Zp)))
        tokVOf
    h.plan.hN h.plan.hG (mgLetter (h.𝔇 𝔇₀) mgBase) At.ps
    (h.𝔇 𝔇₀).headPart (h.𝔇 𝔇₀).digitsPart (F0T o Zp Np cF) (At.smp Zp) At.tokOf
    (ksK o Zp Np cF) h.rch h.rc 𝔏 h.scope
    (fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request) (h.tieStart D 𝔇₀)
    (fun z y => ⟨rchAt_zero _ _, z, rfl⟩) h.laid.planOk
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data) q₁ q₂ q₃
    (pub_free_at_term (At.EAt Z) o Zp Np cF) (fun _ _ => rfl) εs hε

end P5J

#print axioms P5J.LaidAt.atDepth
#print axioms P5J.four_fields_at_mg
