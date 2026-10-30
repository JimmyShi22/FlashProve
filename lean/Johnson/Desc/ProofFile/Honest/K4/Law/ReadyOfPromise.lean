-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ReadyOfPromise.lean: CONDITIONAL.

What is here. FOUR CLAUSES OF `K4ReadyS` (Law/HearsShape.lean: what the accepting decision of K4,
the sub-protocol of the feed-forward layers' own rounds, asks of the verifier's state in front) OUT
OF THE PROMISE IN FRONT, at the library's composed meaning's public tests and the full size's
written lists: nothing is owed · what the lookup returned is there · room in the ledger · every slot
of the lookup's last claim is shown. A definition of a hypothesis's form, and statements with their
proofs.

  `mayWait_k4`   no count of rows may wait in front of the member.
  `shown_of_filled`   a form whose slots are filled is shown, where all is free from the next slot
      on.
  `K4LookFacts p fo`   what stays, on what the lookup has heard.
  `k4ReadyS_of_tests`   **K4ReadyS**, from "no mark", the state's book-keeping, the tests of the
      public items that are open in front, the comparison, K4LookFacts and the test on the tokens.

Not shown here. THAT THE HYPOTHESES CAN HOLD TOGETHER: this file gives no example (by binder:
`mayWait_k4`: H · `shown_of_filled`: R, h · `k4ReadyS_of_tests`: ePub, eMore, hH, H, Sd, hm, hs, t0,
hn, hL, htk). WHAT STAYS OF `K4ReadyS`: that the state bears no mark (hm: the thread's form has it);
`K4LookFacts`: eight clauses on what the lookup has heard: its shape is the plan's; three readings
of its points return; three sizes; and the calls' points end as the lookup's own
(Law/LookOfPromise.lean has five of the eight out of the promise in front); AND the test on the
state's tokens (Law/TokensHead.lean has it under h, the hypothesis on the public files
(`P5J.AtMgA`), and `LaidK4`, wherever the first chain's thread stands in front of the member). One
comparison of public numbers is asked: the plan's next free slot in front, what the hearing takes
and k' are at most the plan's number of slots. THE FULL SIZE ALONE. Dm is a free parameter. A LAW,
NOT A PART: no file that defines a part of the proof file's description may import this one: its
imports reach Johnson/Goal/. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 4 modules under Johnson/Goal/ and 2 under Johnson/Bridge/, and none of
the others; what lies behind these is not counted; 29 of the modules that it reaches have RecCompile
in their names, none of them RecCompile's Honest*, Both or PassH*. The modules under Johnson/Goal/
and RecCompile come with the library's `eleven_at_all`'s file, through Law/PromiseAll.lean.

Kin. `mayWait_k4`: another kind's like law, by the same steps: `mayWait_k5`
(Honest/K5/Law/Ready.lean). `k4ReadyS_of_promise` (Law/LookOfPromise.lean, above this file) has the
same end with less asked on what the lookup has heard.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HearsShape
import Johnson.Desc.ProofFile.Honest.K4.Law.PromiseAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open D6.Ret (Room)
open OnBytes.Model (Forest.Heard Fork Aff lastOf Verify.Public)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Desc.First.K4.RtPub (zkFits tokensFit)
open OnBytes.Road.K4 (CellsK AtK4 K4OnD k4Means_mgWide)
open OnBytes.Road.K4.More (PS)
open VerifiableInference.Desc (Place Wit First.S)
open VerifiableInference.Desc.First (ModelPart Meaning pubAll shapeAt mayWait pubWide_hand pubSets
  openSets start pubHeld classA)
open VerifiableInference.Desc.First.FillK4 (isLay filledB lookLayB)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT mgWide MgData WideData mgBase linksFull moreAll)

/-- The table's public items (`Pub` alone would name another type in this namespace). -/
local notation "PubI" => VerifiableInference.Desc.First.Pub

/-- **No count of rows may wait in front of the member.** -/
theorem mayWait_k4 {links : List ModelPart} {ps : List Place} {k m : Nat} {pl : Place}
    (H : AtK4 links ps k m pl) : mayWait links pl = false := by
  unfold mayWait
  rw [H.link]
  simp only [H.sub, Option.getD_some, H.piece]
  cases (m == 0) <;> rfl

/-- **A form whose slots are filled is shown**, where every slot from the next on is free. -/
theorem shown_of_filled {F : Fork} {a : Aff} {n : Nat} (R : Room F n) (h : filledB F a = true) :
    OnBytes.Desc.First.K4.Rt.Shown F a := by
  intro j hj
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
  unfold filledB at h
  have hx' := List.all_eq_true.1 h x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx'
  have hF : OnBytes.PscRun.Filled F x.1 := hx'.2
  refine ⟨?_, hF⟩
  by_cases hlt : x.1 < F.next
  · exact hlt
  · exact absurd hF (R.free x.1 (by omega))

/-- **What stays of `K4ReadyS` on what the lookup has heard.** This defines a hypothesis; the
definition claims nothing. -/
structure K4LookFacts (p : Par) (fo : Forest.Heard) : Prop where
  shape : fo.shape = p.P.y.fo
  more : ∃ (Z ztF : Array E) (ends : Array (Array E)),
    (lastOf fo.zx p.P.y.h.la).toOption = some Z ∧
      (fo.zk.mapM fun zk => (lastOf zk p.P.y.h.la).toOption) = some ends ∧
      (lastOf fo.zx p.P.y.h.lt).toOption = some ztF ∧ ztF.size = p.P.y.h.lt ∧
      zkFits p.P fo.zk = true ∧ fo.e.size = p.P.y.calls.size ∧ ends.all (· == Z) = true

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- **The state in front, out of the promise's tests.** E₀: any value serves. -/
theorem k4ReadyS_of_tests (E₀ : WideData P) {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {k m : ℕ} {pl : Place} {par : Par} {n k' : ℕ} (ePub : Mg.pub = pubAll Dm.pubD (Bm).pub)
    (eMore : Mg.more = moreAll) (hH : isLay Dm.links (headLink X) = false)
    (H : AtK4 linksFull PS k m pl) (Sd : K4OnD Dm m par n) {z : P} {s : First.S}
    (hm : s.failed = none) (hs : shapeAt linksFull (some pl) s = true)
    (t0 : ∀ q ∈ (pubSets Mg.more linksFull PS)[k]?.getD [], Mg.pub q (z, s) = true)
    (hn : n + (k4Takes par.P par.hp par.g + k') ≤ par.hp.ns)
    (hL : ∀ fo, seatS.look s = some fo → K4LookFacts par fo)
    (htk : tokensFit { par.P with tokv := seatS.tokv s } par.g = true) : K4ReadyS par s := by
  obtain ⟨oQ, -, -, -⟩ := open_at H
  have Em := k4Means_mgWide Dm E₀ Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have hand : ∀ (q : PubI), classA q = false → ∀ a,
      (mgWide Dm E₀ Bm).pub q a = Mg.pub q a := fun q hq a => by
    rw [ePub]
    exact pubWide_hand E₀.d12 E₀.dP Dm.pubD (Bm).pub q hq a
  have t : ∀ q ∈ k4OpenQ m, Mg.pub q (z, s) = true := by
    intro q hq
    refine t0 q ?_
    rw [eMore, oQ]
    exact hq
  have hlay : isLay Dm.links m = true := by
    rw [Sd.links]
    unfold isLay
    rw [H.sub]
    rfl
  have t1 := t (.ledger m) (by simp [k4OpenQ])
  rw [← hand _ rfl, Em.ledger] at t1
  have t2 := t (.freeAbove m) (by simp [k4OpenQ])
  rw [← hand _ rfl, Em.freeAbove] at t2
  have t2' : VerifiableInference.Desc.First.freeAboveB par.hp.ns s = true := by
    have e : (OnBytes.Road.K4.k4DataWide Dm E₀ Bm).nsOf m = some par.hp.ns := Sd.nsOf
    rw [e] at t2
    exact t2
  have t3 := t (.callerIn m) (by simp [k4OpenQ])
  rw [← hand _ rfl, Em.callerIn m _ hlay] at t3
  have t3' : VerifiableInference.Desc.First.FillK4.callerInLayB n s = true := by
    have e : (OnBytes.Road.K4.k4DataWide Dm E₀ Bm).nextOf m = some n := Sd.nextOf
    rw [e] at t3
    exact t3
  have t4 := t (.look m) (by simp [k4OpenQ])
  rw [← hand _ rfl, Em.look m _ hlay] at t4
  have hR := room_of_items t1 t2' t3' hn
  have hw : s.noneWaits = true := by
    simp only [shapeAt, Bool.and_eq_true, Bool.or_eq_true, mayWait_k4 H] at hs
    rcases hs.1.2 with e | e
    · exact e
    · cases e
  have t4' : lookLayB s = true := t4
  unfold lookLayB at t4'
  cases ha : s.here with
  | lay a =>
    rw [ha] at t4'
    dsimp only at t4'
    cases hfo : a.fo with
    | none =>
      rw [hfo] at t4'
      simp at t4'
    | some fo =>
      rw [hfo] at t4'
      simp only [Bool.and_eq_true] at t4'
      have h3 : seatS.look s = some fo := by
        rw [OnBytes.Desc.First.K4.seatS_look ha]
        exact hfo
      obtain ⟨hsh, Z, ztF, ends, a1, a2, a3, a4, a5, a6, a7⟩ := hL fo h3
      have hce : OnBytes.Desc.First.K4.Rt.Shown (seatS.fork s) fo.cEnd := by
        refine shown_of_filled hR ?_
        rw [OnBytes.Desc.First.K4.seatS_fork ha]
        exact t4'.1
      refine ⟨hm, ?_, fo, k', Z, ztF, ends, h3, hsh, hR, a1, a2, a3, a4, hce, a5, a6, a7, htk⟩
      rw [OnBytes.Desc.First.K4.seatS_owed ha, hw]
      rfl
  | between => rw [ha] at t4'; cases t4'
  | att _ => rw [ha] at t4'; cases t4'
  | head _ => rw [ha] at t4'; cases t4'
  | fin _ => rw [ha] at t4'; cases t4'
  | mem _ => rw [ha] at t4'; cases t4'

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.mayWait_k4
#print axioms ProofFile.Honest.K4.shown_of_filled
#print axioms ProofFile.Honest.K4.K4LookFacts
#print axioms ProofFile.Honest.K4.k4ReadyS_of_tests
