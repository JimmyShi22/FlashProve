-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LookHead.lean: CONDITIONAL.

What is here. The field look of the hypothesis `FootRest` (Law/W/FootAtStand.lean): `LookLeft`
(Johnson/Road/K4/W/LookCols.lean: four clauses: heard, ok, sized, shape), at the state behind the
step of the member of the feed-forward layers' own rounds (sub-protocol K4), at the thread with the
library's own values (`lettersHead`, Honest/Thread/FirstHead.lean). Three clauses are paid, and two
of the five conjuncts of heard: what the lookup has left in front of the member (`K3Left`,
Johnson/Top/H/K3LeftStatement.lean, out of the thread by `left_of_promise`, Law/W/StandsHead.lean)
has the shape and the rounds; the library's `steps_ok` has the test on the shape; the library's
`hear_foLater` (Johnson/Road/K4/PlanesOfYes.lean) carries the ledger behind the step. Each proof is
a chain of calls.

  `LookNuAt`   what is left of the clause heard. A definition.
  `look_head`   **`LookLeft tl o (seatS.fork s') mask Mm`**, from hν.

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT THE THREAD HOLDS AT ANY RUN, OR
THAT ANY STEP OF THE MEMBER ACCEPTS: hT : Thr and Zs : `K4Stand` (Law/SlotsTrue.lean) are
hypotheses. THE CLAUSE OF hT THAT IS SPENT is what the public item `.left m` says beside its test:
it is owed behind the member of the lookup on the calls, and no file of the honest side shows it
there. hν (`LookNuAt`): THE CONTENT THAT IS LEFT OF THE FIELD look: at all rounds whose end values
are what the lookup has heard there is one reading ν of the mask row and of the planes' cells at
which the lookup's own sentence on the planes holds (`K3Planes`), the data's mask row is ν's, and
the planes' matrix is ν's inside its sizes: a hypothesis here; `nu_thread_head`
(Law/W/NuCutHead.lean) has it at a stand, where the thread stands. hLk: `K4LookTieAt`
(Law/ScriptAt.lean), of which the first two clauses are read. Lh (`LaidK4`, Law/SeatedHead.lean) and
hQ: on public lists and numbers. The side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Of h together with Lh, hT, hQ, Zs, hLk and hν no example is known
to us. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with h and with the files that it joins, most with Law/ElevenHead.lean. `look_head` RESTS,
through `lam_head` (Law/W/FullHead.lean), ON A STATEMENT OF A FILE UNDER Johnson/Goal/
(`Meaning.P34.pub34_all`). A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OneTie
import Johnson.Road.K4.W.LookCols
import Johnson.Road.K4.PlanesOfYes
import Johnson.Road.K4.LookOfLeft
import Johnson.Road.K4.RefPubSteps
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own matIx)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (eAll hear_foLater steps_ok)
open OnBytes.Road.K4.W (LookLeft)
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (publicSteps_of)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT MsgQ mgAll_more_base)
open VerifiableInference.OnPublicFiles (K3Planes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_pubP)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **What is left of the clause heard of `LookLeft`**: F0: the ledger in front of the member. At
all rounds rs whose end values are what the lookup has heard, from the first slot 0: one reading ν.
This defines a hypothesis; the definition claims nothing. -/
def LookNuAt (o : Own) (F0 : Fork) (mask : ℕ → Cb.Gl.E) (Mm : Road.Mats Cb.Gl.E) : Prop :=
  ∀ rs : TwV.Rounds Cb.Gl.E,
    _root_.Fo.HeardIs Reading.gl o.H.fo F0 (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb 0 rs) →
    ∃ ν : _root_.Fo.Pl → Cb.Gl.E, (mask = fun j => ν (.mask j)) ∧
      (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < _root_.Fo.planeCols o.H.fo.shape o.v.y.h.lmb,
        Mm (matIx o.v.y).iB r c = ν (.cell r c)) ∧
      K3Planes o.H.fo.shape o.v.y.h.lmb 0 ν rs

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE FIELD look, BEHIND THE STEP FROM A STAND.** tl, mask, Mm: free: three of the four clauses
do not read them. CONDITIONAL: on h, Lh, hQ, Zs, hT, hLk and hν. -/
theorem look_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
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
    (hLk : K4LookTieAt look Qp s mm) {tl : HTailF2} {mask : ℕ → Cb.Gl.E}
    {Mm : Road.Mats Cb.Gl.E} (hν : ∀ F0, s.fork? = some F0 → LookNuAt o F0 mask Mm) :
    LookLeft tl o (seatS.fork s') mask Mm := by
  have N := nine_head h Lh
  obtain ⟨eY, eS, _⟩ := pub_is Lh hQ
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  obtain ⟨F, F', g₁, rs, _, hfn, L, hh, hk⟩ := left_of_promise (Dm := h.𝔇)
    (eAll Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
    (mgAll_more_base h.𝔇) N.hH (atK4_of_laid Lh) N.Sx
    (fun _ hq => thr_pubP (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁) hT hq)
  obtain ⟨g', hg1, hg2, _⟩ := hLk
  obtain rfl : g' = o.H.fo := Option.some.inj (hg2.symm.trans (stand_look Zs))
  obtain rfl : g₁ = o.H.fo := Option.some.inj (hh.symm.trans hg1)
  obtain ⟨a, a₀, _, _, hhere, eF, _, hhear, _⟩ :=
    step_tape Zs.seat Zs.sits Zs.stepped Zs.seg Zs.heard
  have e0 : s.fork? = some a₀.F := by
    simp only [VerifiableInference.Desc.First.S.fork?, hhere]
  obtain rfl : a₀.F = F' := Option.some.inj (e0.symm.trans hk)
  have hL := hear_foLater (P := { Qp.P with tokv := s.tokv }) hhear
  rw [eF] at hL
  have esh : o.H.fo.shape = o.v.y.fo := by rw [L.shape, Fu.lay]
  have hI : _root_.Fo.HeardIs Reading.gl o.H.fo a₀.F
      (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb 0 rs) := by
    rw [L.shape, Fu.lay, ← hfn]
    exact L.heardIs
  obtain ⟨ν, n1, n2, n3⟩ := hν a₀.F e0 rs hI
  rw [seg_fork Zs.seg Zs.heard]
  exact
    { heard := ⟨a₀.F, 0, rs, ν, hI, hL.1, n1, n2, n3⟩
      ok := by
        rw [L.shape]
        exact steps_ok (publicSteps_of h.pubOne)
      sized := hL.2 (Zs.sized a₀ hhere)
      shape := esh }

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.look_head
