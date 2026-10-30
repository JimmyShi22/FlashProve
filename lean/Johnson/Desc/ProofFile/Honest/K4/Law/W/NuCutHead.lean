-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/NuCutHead.lean: CONDITIONAL.

What is here. `LookNuAt` (Law/W/LookHead.lean: what is left of what the lookup's three claims ask:
«there is a reading ν of the lookup's places whose mask entries are the data's mask row, whose cells
are the planes' matrix, and at which the lookup's sentence on the planes holds»), at the thread with
the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean), at a stand of the member of
the feed-forward layers' own rounds (sub-protocol K4): FROM THE TIE ON THE MASK ROW IN ITS RIGHT
FORM, cut at the lookup's place's number of slots (`K4MaskCutTieAt`, Law/W/ReadersHead.lean). Asked
at every number that tie fails at a run whose pad at the row's last place is not 0
(Law/W/ReadersHead.lean's head). Here ν is THE DATA's OWN MASK ROW at the mask places and the
lookup's caller's reading elsewhere; the sentence on the planes holds of the caller's reading
(`planes_lay_head`, Law/W/NuHead.lean), the two readings agree at every cell and, by the cut tie, at
the lookup's own mask entries, which begin at slot 0 here and lie below the place's number of slots
(the library's `public_elems`), and the sentence reads no mask place from their end on
(`planes_congr`, Johnson/Road/K4/W/PlanesCongr.lean). AND SINCE BOTH TIES OF THE LIBRARY's READERS
ARE THEOREMS WHERE THE THREAD STANDS (`symsTie_head`, `maskCut_head`): `LookNuAt` with neither of
the two left (`nu_thread_head`); the tie on what the lookup has heard (`K4LookTieAt`) stays a
hypothesis. The first proof is a chain of calls; the second is one call.

  `nuCut_head`   `LookNuAt` at the data's mask row and matrices, from the two ties.
  `nu_thread_head`   **`LookNuAt` at the library's own reader, seats and names**: neither the tie on
      symbols nor the tie on the mask row is asked; `K4LookTieAt` is.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN, OR
THAT THERE IS A STAND: hT and Zs are hypotheses. THE CLAUSES OF hT THAT ARE SPENT: the sentence of
the open item on the planes' worth, and what the public item `.left m` says beside its test: both
are owed behind the member of the lookup on the calls, and no file of the honest side shows them
there. hLk (`K4LookTieAt`, Law/ScriptAt.lean): a hypothesis here. Lh, hQ, hx: on public lists and
numbers. Nothing is said of what a cell or a mask entry is worth. The side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with Lh,
hQ, Zs, hT, hLk, hx, tie and hCut no example is known to us. No test that can fail stands beside
them. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors.
`nuCut_head` RESTS, through `lam_head` (Law/W/FullHead.lean), ON A STATEMENT OF A FILE UNDER
Johnson/Goal/ (`Meaning.P34.pub34_all`); `nu_thread_head`, through `symsTie_head` and
`maskCut_head`, on two more, `Meaning.scope_plans` and `OnBytes.Road.Hd.core_of_scope`
(Law/W/ReadersHead.lean's head names the files). A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.ReadersHead
import Johnson.Road.K4.W.PlanesCongr
import Johnson.Desc.First.Look.K3CallerMasksLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (eAll layAt_plan attAt_even tlAt_plan)
open OnBytes.Road.K4.W (mats_of_syms syms_of_plain planes_congr)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (layAt pubAt stepOf matsOfE msgLay)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ matsOfData mgAll_more_base seatTab)
open VerifiableInference.OnPublicFiles (layMs layNu K3Planes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pubP)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hQ, Zs, hT, hLk, hx, tie and hCut. **`LookNuAt` FROM THE CUT TIE.** ds':
a continuation of the challenges behind the step. -/
theorem nuCut_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {p : Par} {blk : Block TS ProofFile.Cl} {own : List (ℕ × ℕ)}
    {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hLk : K4LookTieAt look Qp s mm)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {names : Array (ℕ × String)}
    (tie : K4SymsTieAt Q xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW
      (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW names own rdOf c s mm)
    (hCut : K4MaskCutTieAt h Q (m := m) (x := x) xl own rdOf c s mm) (ds' : List Fmt.Drawn) :
    ∀ F0, s.fork? = some F0 →
      LookNuAt o F0 (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))).mask
        (matsOfData x.2.hp.tl names
          (dataQ own A' (rdOf (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))) := by
  intro F0 hF0 rs hI
  have N := nine_head h Lh
  have A := atK4_of_laid Lh
  obtain ⟨eY, eS, _⟩ := pub_is Lh hQ
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  obtain ⟨x₁, hx₁, _, e1, e2, e3, en⟩ := layAt_plan N.Sx.pubOf N.Sx.notHead N.Sx.step N.Sx.plan
  have ex : x₁ = xl := Option.some.inj (hx₁.symm.trans hx)
  rw [ex] at e1 e2 e3 en
  have hN : FoNums.nMasks xl.fs ≤ xl.ns := by
    rw [_root_.FoLedger.elems_eq, e1, en]
    exact (_root_.Fo.Pub2.public_elems N.Sx.pubOf).1 _ _ N.Sx.plan
  have h2 : m % 2 = 0 := by
    rw [N.Sx.g]
    omega
  have hW := planes_lay_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ A hT (ds ++ ds') N.Sx.pc2
    (attAt_even h2) hx (tlAt_plan N.Sx.notHead N.Sx.step N.Sx.plan)
  obtain ⟨_, _, g₁, _, _, _, L, hh, _⟩ := left_of_promise (Dm := h.𝔇)
    (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH A N.Sx
    (fun _ hq => thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  obtain ⟨g', hg1, hg2, _⟩ := hLk
  obtain rfl : g' = o.H.fo := Option.some.inj (hg2.symm.trans (stand_look Zs))
  obtain rfl : g₁ = o.H.fo := Option.some.inj (hh.symm.trans hg1)
  obtain ⟨a, _, _, ha, _, _, _, _, hdata⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  obtain ⟨i1, i2⟩ := moved_state Zs.stepped.1
  rw [L.shape, Fu.lay, ← e1, ← e2, ← e3] at hI
  have P := hW o.H.fo F0 hF0 hg1 rs hI
  rw [hdata, i1, i2, List.append_assoc]
  have hM : matsOfData x.2.hp.tl names
      (dataQ own a (rdOf (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))) =
      matsOfE (msgLay xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
        (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1)
          h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))) :=
    mats_of_syms xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc _
      names _ (syms_of_plain xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW _ names _
        (tie a ha (ds ++ ds')))
  let νL : _root_.Fo.Pl → Cb.Gl.E :=
    layNu xl (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad
      h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1)
      h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds')))
  let νD : _root_.Fo.Pl → Cb.Gl.E := fun p => match p with
    | .mask j =>
      (dataQ own a (rdOf (Q.wit c mm.st.input (mm.st.heard ++ (ds ++ ds'))))).mask j
    | q => νL q
  have hm : ∀ j, j < xl.F.next + FoNums.nMasks xl.fs → νL (.mask j) = νD (.mask j) :=
    fun j hj => (hCut a ha (ds ++ ds') j (by rw [e3] at hj; omega)).symm
  have hcell : ∀ r c', νL (.cell r c') = νD (.cell r c') := fun _ _ => rfl
  have P' : K3Planes xl.fs xl.lm xl.F.next νD rs :=
    planes_congr xl.fs xl.lm xl.F.next hm hcell rs P
  refine ⟨νD, rfl, fun r _ c' _ => ?_, ?_⟩
  · rw [hM, Fu.lay]
    rfl
  · rw [L.shape, Fu.lay, ← e1, ← e2, ← e3]
    exact P'

/-- CONDITIONAL: on h, Lh, hQ, Zs, hT, hLk and hx. **`LookNuAt`, WITH NEITHER TIE OF THE LIBRARY's
READERS ASKED.** hLk, the tie on what the lookup has heard, stays a hypothesis. -/
theorem nu_thread_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {p : Par} {blk : Block TS ProofFile.Cl}
    {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk (h.𝔇.N.sent m 0)
      (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm E ds y cols s' A' o)
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    (hLk : K4LookTieAt look Qp s mm)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (ds' : List Fmt.Drawn) :
    ∀ F0, s.fork? = some F0 →
      LookNuAt o F0
        (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
          (Q.wit c y.2.st.input (y.2.st.heard ++ ds')))).mask
        (matsOfData x.2.hp.tl (P5J.At.names3 Zp m)
          (dataQ (h.𝔇.N.sent m 0) A' (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms
            (Q.wit c y.2.st.input (y.2.st.heard ++ ds'))))) :=
  nuCut_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ Zs hT hLk hx
    (symsTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT hx)
    (maskCut_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT hx) ds'

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.nuCut_head
#print axioms ProofFile.Honest.K4.W.nu_thread_head
