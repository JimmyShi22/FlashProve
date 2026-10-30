-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/OkAtStand.lean: CONDITIONAL. Statements with their proofs.

What is here: two premises of `stack_stand`, `ownBack_join` (Law/StackAtStand.lean) and
`ownBack_merged` (Law/MergeStartAtStand.lean), each in its own text, at a stand (`K4Stand`,
Law/SlotsTrue.lean) of the layers' own rounds (the sub-protocol K4). hok, that the three words of
the second token sumcheck's first challenge lie below the prime: from `drawsFit` (Honest/Frame.lean)
at the member's declared rounds and the challenges, which the statements at a thread hold in their
own binders. hz0, that the lookup's point is not empty: from the hearing's return, where the layout
has at least one token coordinate. SO `ownBack_fit`: `OwnBack` (Johnson/Road/K4/W/Join.lean) whole
with these two premises exchanged for `drawsFit` and that one public comparison.
How. hok: that challenge is the first element that the tape's round at the sumcheck's first round
has sampled (the library's `tscIn_tape`, OnBytes/Desc/First/P1/TscLaw.lean, at `LedG`'s field c3);
the tape samples what the challenges hold; `drawFit` asks every word of an element below the prime;
then the library's `small_paired` and `small_eps` (Johnson/Road/K4/OwnCoin.lean). hz0: the hearing
reads the point's last token coordinates (`led_ztF`, Law/PtsHear.lean), and that reading refuses a
point that is too short.

Not shown here. No property is claimed. That the premises can be met: no example is known. THE
MEMBER's STEP TESTS NO WORD's SIZE: at a stand without `drawsFit` hok stays a premise. What stays of
`OwnBack` in `ownBack_fit`: `JoinWorth` (Law/StackStart.lean: the lookup's join: nothing here shows
it), hm (what the slots of the panels' weight claims are worth) and three premises on public data
(hP, hnE, hU). Nothing on soundness, on completeness or on any other property.

  `draws_small`   where `drawsFit` accepts, every sampled element's three words lie below the prime
  `lastOf_le`   a point whose last k coordinates are read has at least k
  `stand_ok`   **hok at a stand**
  `stand_z0`   **hz0 at a stand**
  `ownBack_fit`   **`OwnBack` whole**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MergeStartAtStand
import Johnson.Road.K4.OwnCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE okE)
open OnBytes.Model (Reading Aff Fork Tsc WsClaim WsUnit lastOf)
open OnBytes.Model.Layer (Own ClaimEnv callsTS nEndT)
open OnBytes.PscRun (Later)
open OnBytes.Road (UnitOK claimVal)
open OnBytes.Road.K4 (SmallTape small_eps small_paired)
open OnBytes.Desc.First.P1 (tapeEps tscIn_tape)
open OnBytes.Desc.First.K4 (Par formsBack entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.K4.SlotsOwn (worldBehind)

/-- Where `drawsFit` accepts, every sampled element's three words lie below the prime. -/
theorem draws_small : ∀ (dl : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit dl ds = true →
    ∀ R ∈ ds, ∀ x ∈ R.elems, okE (OnBytes.E.ofTriple x) = true := by
  intro dl
  induction dl with
  | nil =>
    intro ds h R hR
    cases ds with
    | nil => cases hR
    | cons _ _ => cases h
  | cons d dl ih =>
    intro ds h R hR
    cases ds with
    | nil => cases hR
    | cons R₀ Rs =>
      have h' : (drawFit d R₀ && drawsFit dl Rs) = true := h
      rw [Bool.and_eq_true] at h'
      rcases List.mem_cons.1 hR with rfl | hR'
      · intro x hx
        have h1 := h'.1
        unfold drawFit at h1
        simp only [Bool.and_eq_true] at h1
        have h2 := List.all_eq_true.1 h1.1.2 x hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        show (OnBytes.okF x.1 && OnBytes.okF x.2.1 && OnBytes.okF x.2.2) = true
        simp only [OnBytes.okF, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨h2.1.1, h2.1.2⟩, h2.2⟩
      · exact ih Rs h'.2 R hR'

/-- A point whose last k coordinates are read has at least k. -/
theorem lastOf_le {z Z : Array OnBytes.E} {k : Nat} (h : (lastOf z k).toOption = some Z) :
    k ≤ z.size := by
  by_contra hk
  unfold lastOf OnBytes.Model.cutLast at h
  rw [if_pos (by omega)] at h
  cases h

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **hok AT A STAND**: CONDITIONAL on the stand and on `drawsFit` at some list of declared rounds.
-/
theorem stand_ok
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    {dl : List Fmt.DeclaredRound} (hd : drawsFit dl ds = true) :
    ∀ tT, o.H.tT = some tT → okE tT.p.eps = true := by
  intro tT' hT'
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  obtain rfl : ({ tT with p := { tT.p with rowMade := true } } : Tsc) = tT' :=
    Option.some.inj (L.kTT.symm.trans hT')
  show okE tT.p.eps = true
  have hsm : SmallTape (OnBytes.K.Kc.paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) := by
    refine small_paired _ _ fun r hr x hx => ?_
    have e := yields_drawn l ds [] y.1 (play_yields l ds [] m y hy)
    have hm : r.drawn ∈ ds := by
      rw [← e]
      exact List.mem_map.2 ⟨r, hr, rfl⟩
    exact draws_small dl ds hd _ hm x hx
  have c3 := L.c3
  rw [(cuts { Q.P with tokv := s.tokv } Q.hp Q.g _).2.2.1] at c3
  obtain ⟨_, _, _, _, eps, _, _, _, _, _, _, _, _, _, _, _, ht, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, heps, _⟩ := tscIn_tape c3
  have h1 := small_eps (hsm.drop (rJ3 { Q.P with tokv := s.tokv } Q.g))
  rw [ht] at h1
  rw [heps]
  exact h1

/-- **hz0 AT A STAND**: CONDITIONAL on the stand and on one comparison of a public number. -/
theorem stand_z0
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hlt : 1 ≤ Q.P.y.h.lt) : o.H.fo.zx.isEmpty = false := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, _, L⟩ := stand_led_tape Z
  have h1 := lastOf_le (led_ztF L)
  have h2 : 0 < o.H.fo.zx.size := by omega
  rw [Array.isEmpty_eq_false_iff]
  intro e
  rw [e] at h2
  exact Nat.lt_irrefl 0 h2

/-- **`OwnBack` WHOLE AT A STAND**: CONDITIONAL on the named premises; hJW: the lookup's join; hm:
what the slots of the panels' weight claims are worth; hd, hlt: in the stead of hok and hz0. -/
theorem ownBack_fit
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) {F₁ F₂ : Fork}
    {fs₂ : Array Aff} (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂)) (F : Fork)
    (hL : Later F₂ F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    {dl : List Fmt.DeclaredRound} (hd : drawsFit dl ds = true) (hlt : 1 ≤ Q.P.y.h.lt)
    (hP : ∀ S, OnBytes.Desc.First.K4.Honest.Sides.of Q
        (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some S → TermsPub S)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hJW : ∀ D, stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ4 Q.P Q.g)))
        (k4SentAt (seenAt m y (rJ4 Q.P Q.g)).rounds (k4TermsEnds Q)) = some D →
      ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
        o.v.y.calls.mapM o.v.weighedOf = some weighed →
        ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
          o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
        o.H.tT = some tT' →
        JoinWorth o.H tT' parts (worldBehind T own rdOf k y A ds' F entry) D)
    (hU : ∀ (i : ℕ) (u : WsUnit), Q.P.wsLay.U[i]? = some u → UnitOK Q.P.wsLay.lk u)
    (hm : ∀ (TS : List Nat) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
      ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
         rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
      ∀ a x, cl[a]? = some x →
        (worldBehind T own rdOf k y A ds' F entry).slot (o.K.sV + a) =
          claimVal Reading.gl Q.P.wsLay
            (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) x) :
    OnBytes.Road.K4.W.OwnBack Reading.gl (worldBehind T own rdOf k y A ds' F entry) o := by
  exact ownBack_merged Z hT hLk ds' h1 hb F hL entry hP hnE (stand_ok Z hd) (stand_z0 Z hlt) hJW hU
    hm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.draws_small
#print axioms ProofFile.Honest.K4.lastOf_le
#print axioms ProofFile.Honest.K4.stand_ok
#print axioms ProofFile.Honest.K4.stand_z0
#print axioms ProofFile.Honest.K4.ownBack_fit
