-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/HotHead.lean: CONDITIONAL.

What is here. Toward the field hot of the hypotheses `ItemRight` (Law/W/SlotsOfStand.lean),
`RightFoot` (Law/W/ItemRightOf.lean) and `FootRest` (Law/W/FootAtStand.lean): the selector's
identity at the token point of the feed-forward layers' own rounds (sub-protocol K4): out of the
thread in front of K4's member, at the thread with the library's own values (`lettersHead`,
Honest/Thread/FirstHead.lean). Three statements are joined: the item worth "rider" is open there and
the thread holds its sentence (Law/W/OpenAtHead.lean); there is a list of rounds whose end values
are what the state holds as heard (Law/W/StandsHead.lean); so the sentence gives the identity at the
heard point (Johnson/Road/K4/W/HotOfRider.lean). The lookup's place at the segment has the plan's
own values by the library's `layAt_plan`, `attAt_even` and `tlAt_plan`
(Johnson/Road/K4/K4PinsScope.lean). Each proof is a chain of calls.

  `k4_hot_head`   **`HotPoint` at the cells that the lookup's caller reads off the Script's
      witness**, at every continuation ds' of the challenges heard, at the point of the array that
      `lastOf` cuts off what the state holds as heard.
  `k4_hot_mats`   the same at the cells of matrices Mm, under hC: the field's text once D := DF, y,
      zt and the witness are laid as the field has them.

Not shown here. THAT THE THREAD HOLDS AT ANY RUN: hT : Thr is a hypothesis. THE CLAUSE OF hT THAT IS
SPENT is what the public item `.left m` says beside its test: it is owed behind the member of the
lookup on the calls, and no file of the honest side shows it there. THE FIELD hot ITSELF:
`k4_hot_head` ends at the cells that the lookup's caller reads and at a point cut off what the state
IN FRONT of the member holds as heard by the lookup; the field stands at the state BEHIND the
member's step. Between the two, each a caller's to show: what K4's own hearing is handed is what the
state holds as heard by the lookup (two fields of the state); `DF.lT` is the layout's number of
position bits, at which the verifier cuts; the array that is cut is the hearing's own token point;
the layout is the hearing's; the witness behind the step is the witness in front at a longer list of
challenges. THAT THE CELLS WHICH THE LOOKUP's CALLER READS OFF THE WITNESS's MESSAGES ARE THE CELLS
OF THE MATRICES Mm: hC is a hypothesis of `k4_hot_mats`: it ties two readers of one witness;
Johnson/Road/K4/W/MatsOfSyms.lean has it from an equation of committed symbols at one plan; the
library's nearest statement is `cells_lay` (Johnson/Road/K4/K4PinsRider.lean), at another tuple of
messages. The statements stand at the plan `par.hp.tl`. hH, A (`AtK4`), Sx (`K4OnX`;
Law/SeatedHead.lean has it under h and `LaidK4`, at the member's own parameters) and T (`TreesFit`):
hypotheses on public lists and numbers. hf, hh, hzt and hx name F', g, zt and x. The side library
AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). Of h together with hH, A, Sx, hT, hf, hh, T, hzt, hx and hC no example is known to us.
THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness,
on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 18 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 23 is not counted: all the numbers are floors. They come with
h and with the files that it joins. A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OpenAtHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StandsHead
import Johnson.Road.K4.W.HotOfRider
import Johnson.Road.K4.K4PinsScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road (Mats cellsOf cellsAt pt TreesFit)
open OnBytes.Road.K4 (AtK4 K4OnX layAt_plan attAt_even tlAt_plan)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.W (HotPoint hotPoint_of_worth)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Look (pubAt stepOf layAt layCells)
open VerifiableInference.Desc.Sound (MsgT WideData linksFull)
open VerifiableInference.OnPublicFiles (headLink layMs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE SELECTOR's IDENTITY AT K4's TOKEN POINT, OUT OF THE THREAD.** x: the lookup's place at the
segment. g, F': what the state holds as heard, and its ledger. E₀: any value serves: the library's
lemma is stated at the wider meaning, which takes it; the conclusion does not read it. CONDITIONAL:
on h, hH, A, Sx, hT, hf, hh, T, hzt and hx. -/
theorem k4_hot_head (E₀ : WideData ProofFile.InstPub)
    {k m : ℕ} {pl : Place} {par : Par} {pol KL : ByteArray} {layout : Option ByteArray}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) {g : Forest.Heard} {F' : Fork} (hf : s.fork? = some F')
    (hh : s.lookHeard? = some g) (T : TreesFit (P5J.At.X Zp).y.fo DF)
    {zt : Array OnBytes.E} (hzt : lastOf g.zx DF.lT = .ok zt)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some x) :
    HotPoint DF
      (layCells x (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) par.hp.tl h.𝔇.sent h.𝔇.l3.rad
        h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
        (layMs x h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr
          h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ ds'))))
      (pt Reading.gl zt) := by
  obtain ⟨x₁, hx₁, _, e1, e2, e3, _⟩ := layAt_plan Sx.pubOf Sx.notHead Sx.step Sx.plan
  obtain rfl : x₁ = x := Option.some.inj (hx₁.symm.trans hx)
  have h2 : m % 2 = 0 := by
    rw [Sx.g]
    omega
  have hW := rider_lay_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT ds' Sx.pc2
    (attAt_even h2) hx (tlAt_plan Sx.notHead Sx.step Sx.plan)
  obtain ⟨hS, hsx⟩ := stands_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ E₀ hH A Sx hT hf hh
  rw [← e1, ← e2, ← e3] at hS
  rw [← e1] at hsx T
  exact hotPoint_of_worth _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW hf hh hS T hsx hzt

/-- **AT THE CELLS OF MATRICES Mm.** CONDITIONAL: as `k4_hot_head`, and on hC. -/
theorem k4_hot_mats (E₀ : WideData ProofFile.InstPub)
    {k m : ℕ} {pl : Place} {par : Par} {pol KL : ByteArray} {layout : Option ByteArray}
    (hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false) (A : AtK4 linksFull PS k m pl)
    (Sx : K4OnX (P5J.At.X Zp) pol KL layout m par) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (ds' : List Fmt.Drawn) {g : Forest.Heard} {F' : Fork} (hf : s.fork? = some F')
    (hh : s.lookHeard? = some g) (T : TreesFit (P5J.At.X Zp).y.fo DF)
    {zt : Array OnBytes.E} (hzt : lastOf g.zx DF.lT = .ok zt)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some x)
    {y : Layer.Lay} {Mm : Mats Cb.Gl.E}
    (hC : cellsOf DF (cellsAt y Mm) =
      layCells x (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) par.hp.tl h.𝔇.sent h.𝔇.l3.rad
        h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
        (layMs x h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat x.link false j.1) h.𝔇.l3.arr
          h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ ds')))) :
    HotPoint DF (cellsOf DF (cellsAt y Mm)) (pt Reading.gl zt) := by
  rw [hC]
  exact k4_hot_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ E₀ hH A Sx hT ds' hf hh T hzt hx

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_hot_head
#print axioms ProofFile.Honest.K4.W.k4_hot_mats
