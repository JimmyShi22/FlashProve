-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ReadersHead.lean: CONDITIONAL.

What is here. THE TIE ON SYMBOLS `K4SymsTieAt` (Law/W/OneTie.lean) IS NO HYPOTHESIS ANY MORE at the
thread with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean), in front of the
member of the feed-forward layers' own rounds (sub-protocol K4): it holds wherever the thread
stands, under h and `LaidK4` alone, at the list of the arrays' names `P5J.At.names3 Zp m`, the seats
that the segment sends at its first moment and the library's reader by seats. So does the tie on the
mask row IN ITS RIGHT FORM, cut at the lookup's place's number of slots (`K4MaskCutTieAt`, defined
here). Both compare two of the library's readers of one witness; Johnson/Road/K4/W/TwoReaders.lean
has them at every witness from four hypotheses, and each of the four is had here: `RecIs` out of the
thread (`recIs_front_head`, Law/RecFrontHead.lean); the two tests on the plan and the bound on the
slots by the library's `pins_head` (Johnson/Road/K4/K4HeadWritten.lean), whose one test in front the
library's `first_paid` (K4PlanAllPaid.lean) pays; `SitsIn` as a field of the library's `fitF_wide`
(K4PinsFirstWhole.lean). Each proof is a chain of calls.

  (`pinsTests_head`, `sitsIn_head`, `arrayNames_head`: the plan's side: in Law/W/ReadersPlan.lean.)
  `symsTie_head`   **`K4SymsTieAt`, where the thread stands.**
  `K4MaskCutTieAt`   the tie on the mask row, below the place's number of slots. A definition.
  `maskCut_head`   **`K4MaskCutTieAt`, where the thread stands.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN: hT
: Thr is a hypothesis. WHAT THE TIES SAY: that two readers read one thing: NOTHING ON WHAT A CELL OR
A MASK ENTRY IS WORTH, on integers (`MatsAre`), on an honest prover's cells (`CellIsList`) or on its
coins (`K4MaskTieAt`): these stay hypotheses of the tops. FROM THE PLACE's NUMBER OF SLOTS ON
NOTHING IS SAID OF THE MASK ROW: asked at every number the equation fails at a run whose pad at the
row's last place is not 0: there the data read the witness's pad, and the caller's reader answers 0.
Beneath `pins_head` and `first_paid` stand closed facts on written values that Lean's kernel has
decided in the library. Lh (`LaidK4`, Law/SeatedHead.lean) and hx: on public lists and numbers. The
side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with Lh, hx and hT no example is known to us. THE FULL SIZE ALONE, and the
format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any
other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. TWO
STATEMENTS OF FILES UNDER Johnson/Goal/ ARE CALLED BY NAME IN Law/W/ReadersPlan.lean:
`Meaning.scope_plans` (Johnson/Goal/Meaning/PlanShapes.lean) in `sitsIn_head` and
`OnBytes.Road.Hd.core_of_scope` (Johnson/Goal/Meaning/ScopeCore.lean) in `pinsTests_head`, as the
library's Johnson/Road/K4/K4PinsFirstScope.lean and K4PinsPaid.lean do. A LAW, NOT A PART: no file
that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.NuHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ReadersPlan
import Johnson.Desc.ProofFile.Honest.K4.Law.RecFrontHead
import Johnson.Road.K4.W.TwoReaders
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PlanAllPaid
import Johnson.Road.K4.K4PinsFirstScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (eAll parOf K4PinsTests pins_head first_paid written_of_head xNine_of_laid
  namesTied_of_scope XNine SitsIn fitF_wide pinsFill_const group_at layAt_plan cutW posFree
  maskRowsAt refPub_in_scope)
open OnBytes.Road.K4.W (sym_two mask_two)
open OnBytes.Maker (WholeD)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.PlanWritten (publicSteps_of)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt pubAt stepOf sigListCalls Stored.entries)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ mgBase seatTab)
open VerifiableInference.OnPublicFiles (layNu)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Here_head)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-! ## The two ties, where the thread stands -/

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hT and hx. **THE TIE ON SYMBOLS, WHERE THE THREAD STANDS.** xl: the
lookup's place at the segment. -/
theorem symsTie_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    K4SymsTieAt Q xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW (P5J.At.names3 Zp m)
      (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  intro a ha d a' ha' i hi c' hc'
  have hR := recIs_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha
  have hs := sitsIn_head h Lh hx
  have Pt := pinsTests_head h Lh
  have N := nine_head h Lh
  obtain ⟨x₁, hx₁, el, _, _, _, en⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at el en
  have hk := Lh.num
  have hm := Lh.seg
  subst hk hm
  have hB := Pt.arrays xl el en
  have q := sym_two xl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xl.link false j.1)
    (cutW Stored.entries h.𝔇.l3.wOf hRef (2 ^ kRef))
    (posFree (maskRowsAt (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull).d12.M h.𝔇.N.indexNo))
    x.2.hp.tl h.𝔇.l3.oW h.𝔇.l3.arr h.𝔇.ms h.𝔇.N (2 * g) h.𝔇.l3.msgW hs hB hR
    (Q.wit c mm.st.input (mm.st.heard ++ d)) a' ha' i hi c' hc'
  have enm : h.𝔇.sent.arrayOf.getD xl.link #[] = P5J.At.names3 Zp (2 * g) := by
    rw [el]
    exact arrayNames_head h (2 * g)
  rw [enm] at q
  exact q

/-- **THE TIE ON THE MASK ROW, CUT AT THE PLACE's NUMBER OF SLOTS, stated at the stand in front of
the member**: at every continuation d of the challenges heard and every j below `xl.ns`: the data's
mask row at j is what the lookup's caller reads off the witness at the place `.mask j`. This defines
a hypothesis; the definition claims nothing. -/
def K4MaskCutTieAt {m : ℕ} {x : Bool × Par} (xl : VerifiableInference.Desc.First.Look.Place)
    (own : List (ℕ × ℕ)) (rdOf : WtF → ℕ × ℕ → MsgQ) (c : Coins Bk) (s : TS)
    (mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X') : Prop :=
  ∀ a, segAt? s = some a → ∀ d j, j < xl.ns →
    (dataQ own a (rdOf (Q.wit c mm.st.input (mm.st.heard ++ d)))).mask j =
      layNu xl (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad
          h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1)
          h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ d)) (.mask j)

/-- CONDITIONAL: on h, Lh, hT and hx. **THE CUT TIE ON THE MASK ROW, WHERE THE THREAD STANDS.** -/
theorem maskCut_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    K4MaskCutTieAt h Q (m := m) (x := x) xl (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm := by
  intro a ha d j hj
  have hR := recIs_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha
  have hs := sitsIn_head h Lh hx
  have Pt := pinsTests_head h Lh
  have N := nine_head h Lh
  obtain ⟨x₁, hx₁, el, _, _, _, en⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at el en
  have hk := Lh.num
  have hm := Lh.seg
  subst hk hm
  exact mask_two xl h.𝔇.sent h.𝔇.l3.rad (fun j => h.𝔇.l3.seat xl.link false j.1)
    (cutW Stored.entries h.𝔇.l3.wOf hRef (2 ^ kRef))
    (posFree (maskRowsAt (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull).d12.M h.𝔇.N.indexNo))
    x.2.hp.tl h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc h.𝔇.l3.arr h.𝔇.ms h.𝔇.N (2 * g)
    h.𝔇.l3.msgW _ hs (Pt.maskPlan xl el en) hR (Pt.ell xl el en)
    (Q.wit c mm.st.input (mm.st.heard ++ d)) j hj

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.symsTie_head
#print axioms ProofFile.Honest.K4.W.maskCut_head
