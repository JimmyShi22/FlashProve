-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MergeStartAtStand.lean: CONDITIONAL. Statements with their
proofs.

What is here: at a stand (`K4Stand`, Law/SlotsTrue.lean) of the layers' own rounds (the sub-protocol
K4), under the premises below, the form at which the verifier starts the merge's sumcheck is worth
the total of the cube of the honest job: the premise hσ of `merge_stand` and `ownBack_stand`
(Law/OwnAtStand.lean) and of `ownBack_join` (Law/StackAtStand.lean), to the letter. A call of
`merge_start_total` (Law/SumMergeStart.lean); here its premises are shown at a stand: the honest
list of claims is the panels' list as the verifier makes it (`claimEnv_is`, Law/ClaimsAre.lean) and,
in the first group, the embedding's claim, whose slot `opened_left` (Law/SlotsTrue.lean) has; the
coefficients are the powers that the makers read (`at_mergePow`, Law/PtsPow.lean).

THE PREMISES: `K4Stand` · `Thr` (Honest/Thread/Thr.lean): with it `K4Seated.fits` is spent: at
shapes that do not fit these statements say nothing · `K4LookTieAt` (Law/ScriptAt.lean), one field:
the calls' points · hU: each unit of the weights' layout is as the layout leaves it (`UnitOK`,
Johnson/Road/FormsKeysWOk.lean): public · hm.

Not shown here. No property is claimed. That the premises can be met: no example is known. WHAT
STAYS A HYPOTHESIS ON WHAT IS SUMMED: hm: each slot of a panel's weight claim is worth that claim's
value on the committed matrix: the field merged of the hypothesis `OpenedOwn`
(Johnson/Road/K4/W/OpenedOwn.lean), in its own text, at the list of claims that the verifier's
hearing makes. In `ownBack_merged` besides: `JoinWorth` and the four other premises of
Law/StackAtStand.lean. Nothing ties the matrix to a commitment. That the step of K4's member accepts
is a premise. Nothing on soundness, on completeness or on any other property.

  `forall2_from`   a small step on lists
  `merge_start_stand`   **THE MERGE's START AT A STAND**
  `ownBack_merged`   **`OwnBack` whole**, with the merge's start no longer a premise
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.SumMergeStart
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Desc.ProofFile.Honest.K4.Law.MergeLed
import Johnson.Desc.ProofFile.Honest.K4.Law.W.EmbRight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Aff Fork Tsc WsClaim WsUnit wsClaimShape wsForkStart powers)
open OnBytes.Model.Layer (Own ClaimEnv callsTS nEndT)
open OnBytes.PscRun (Sized Later)
open OnBytes.Road (UnitOK claimVal)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (Par mergeSlots formsBack entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.K4.SlotsOwn (worldBehind)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- Members of a list, each related to the value of f at its number counted from k. -/
theorem forall2_from {α : Type} (R : Nat → α → Prop) (f : Nat → Nat) : ∀ (l : List α) (k : Nat),
    (∀ a x, l[a]? = some x → R (f (k + a)) x) →
    List.Forall₂ R ((List.range' k l.length).map f) l := by
  intro l
  induction l with
  | nil =>
    intro k _
    exact List.Forall₂.nil
  | cons x l ih =>
    intro k h
    rw [List.length_cons, List.range'_succ, List.map_cons]
    refine List.Forall₂.cons (h 0 x rfl) (ih (k + 1) fun a z hz => ?_)
    have e : k + 1 + a = k + (a + 1) := by omega
    rw [e]
    exact h (a + 1) z hz

/-- **THE MERGE's START AT A STAND**: the premise hσ of `merge_stand`, to the letter. F: any ledger
later than the one that the step leaves. CONDITIONAL on the named premises; hm: what the slots of
the panels' weight claims are worth. -/
theorem merge_start_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) (F : Fork)
    (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hU : ∀ (i : ℕ) (u : WsUnit), Q.P.wsLay.U[i]? = some u → UnitOK Q.P.wsLay.lk u)
    (hm : ∀ (TS : List Nat) (cl : List WsClaim), callsTS { Q.P with tokv := s.tokv } = some TS →
      ({ v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs,
         rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some cl →
      ∀ a x, cl[a]? = some x →
        (worldBehind T own rdOf k y A ds' F entry).slot (o.K.sV + a) =
          claimVal Reading.gl Q.P.wsLay
            (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) x) :
    ∀ cls, mergeClaimsAt Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))) = some cls →
      (wsForkStart (mergeSlots Q.hp Q.g o)
          (powers ((ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE)
            (mergeSlots Q.hp Q.g o).size)).value Reading.gl
          (worldBehind T own rdOf k y A ds' F entry) =
        Reading.gl.val (mergeJobOf Q.P.wsLay
          (k4Wit Q cells weights tokens (look Q) m.st.input).w cls
          (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
            (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))).rhoW).cube.total := by
  intro cls hcls
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, ha, L⟩ := stand_led_tape Z
  obtain ⟨⟨l, _, hy⟩, _⟩ := Z.stepped.1
  obtain ⟨a', a₀, fo, ha', ha0, haF, _, hh0, _⟩ :=
    step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain rfl : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh0
  have hSz : Sized a'.F := by
    rw [haF]
    exact Z.sized a₀ ha0
  have el := stand_look Z
  obtain ⟨g, _, h2, _, hzk, _⟩ := hLk
  rw [h2] at el
  obtain rfl := Option.some.inj el
  have hD := stand_drawn hy (entries Q.P Q.hp Q.g)
  have hh := k4_heard_front Z.seat hT
  have hr := stand_reach Z
  have e6 := (k4StartAt_eq Q).2.2.2.2.2.2
  have n6 : k4StartAt Q 4 + 10 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  have n0 : 17 ≤ k4StartAt Q 4 := by
    simp only [k4StartAt]
    omega
  -- the coefficients
  have hu : tapeEps u5 = (ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE := by
    rw [L.u5e, (cuts { Q.P with tokv := s.tokv } Q.hp Q.g _).2.2.2.2.2.2]
    exact tape_beta hy _ _
  have hrho : (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))).rhoW =
      powers ((ownE ds (rE Q.P Q.hp Q.g) 1).headD zeroE) (mergeSlots Q.hp Q.g o).size := by
    rw [at_mergePow _ _ L ds hD hr hh (rE Q.P Q.hp Q.g + 1) (by omega), hu, mergeSlots_size hh0]
  rw [hrho]
  -- the list: its count and its claims' shapes
  obtain ⟨hk, ln, hLs⟩ := W.stand_run Z hT
  have s6 : (starts Q).getD 6 0 = rE Q.P Q.hp Q.g + 1 := by rw [k4_starts]; rfl
  obtain ⟨cls', hc', hlen, _, hshape⟩ := merge_run
    (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1)) (stand_own_fits Z hT _)
    (by rw [ln _ (by omega), s6]) (hLs _)
  obtain rfl : cls' = cls := Option.some.inj (hc'.symm.trans hcls)
  have okU : ∀ c, (wsClaimShape Q.P.wsLay c).isOk = true →
      wsClaimShape Q.P.wsLay c = .ok () := by
    intro c h
    cases hc : wsClaimShape Q.P.wsLay c with
    | ok _ => rfl
    | error _ =>
      rw [hc] at h
      cases h
  have hcl : ∀ c ∈ cls', ∃ u, Q.P.wsLay.U[c.ui]? = some u ∧ wsClaimShape Q.P.wsLay c = .ok () ∧
      UnitOK Q.P.wsLay.lk u := by
    intro c hc
    have hs := okU c (hshape c hc)
    obtain ⟨u, hu'⟩ := shape_unit hs
    exact ⟨u, hu', hs, hU _ u hu'⟩
  -- the list: the panels' claims, then the embedding's
  have hcls' := hcls
  unfold mergeClaimsAt at hcls'
  obtain ⟨cp, hcp, h3⟩ := Option.bind_eq_some_iff.mp hcls'
  have h3' : (if (Q.g == 0) = true then
      (Option.map (fun x => [x]) (embClaim Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))))).bind fun z => some (cp ++ z)
      else (some []).bind fun z => some (cp ++ z)) = some cls' := h3
  have hsplit : ∃ ce, (if (Q.g == 0) = true then
      Option.map (fun x => [x]) (embClaim Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))))
      else some []) = some ce ∧ cp ++ ce = cls' := by
    by_cases hg : (Q.g == 0) = true
    · rw [if_pos hg] at h3' ⊢
      obtain ⟨ce, h, e⟩ := Option.bind_eq_some_iff.mp h3'
      exact ⟨ce, h, Option.some.inj e⟩
    · rw [if_neg hg] at h3' ⊢
      obtain ⟨ce, h, e⟩ := Option.bind_eq_some_iff.mp h3'
      exact ⟨ce, h, Option.some.inj e⟩
  obtain ⟨ce, hce, rfl⟩ := hsplit
  unfold panelClaims at hcp
  obtain ⟨env, henv, h5⟩ := Option.bind_eq_some_iff.mp hcp
  obtain ⟨TS, hTS, h6⟩ := Option.bind_eq_some_iff.mp h5
  have envAt : ∀ n, k4StartAt Q 4 ≤ n → claimEnvOf Q (ptsOf Q
      (k4Wit Q cells weights tokens (look Q) m.st.input) (m.st.heard ++ ds.take n)) =
      some (OnBytes.Desc.First.K4.envOf { Q.P with tokv := s.tokv } o) := fun n hn =>
    claimEnv_is _ _ hh0 hSz ds hD (by omega) hh hzk n hn
  rw [envAt _ (by omega)] at henv
  obtain rfl := Option.some.inj henv
  have hmP := hm TS cp hTS h6
  -- the slots against the claims
  have hslot : List.Forall₂ (fun sl c => (worldBehind T own rdOf k y A ds' F entry).slot sl =
      claimVal Reading.gl Q.P.wsLay (wmOf (k4Wit Q cells weights tokens (look Q) m.st.input).w) c)
      (mergeSlots Q.hp Q.g o).toList (cp ++ ce) := by
    have hl' : cp.length + ce.length = Q.hp.NCL := by rw [← List.length_append]; exact hlen
    by_cases hg : (Q.g == 0) = true
    · rw [if_pos hg] at hce
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hce
      have hnum : Q.hp.NCL - 1 = cp.length := by
        have : cp.length + 1 = Q.hp.NCL := hl'
        omega
      unfold mergeSlots
      rw [if_pos hg, if_pos hg, hnum, Array.toList_append, Array.toList_map, Array.toList_range,
        List.range_eq_range']
      refine List.rel_append (forall2_from _ (o.K.sV + ·) cp 0 fun a' z hz => ?_)
        (List.Forall₂.cons ?_ List.Forall₂.nil)
      · rw [Nat.zero_add]
        exact hmP a' z hz
      · unfold embClaim at hx
        rw [if_pos hg, envAt _ (by omega)] at hx
        have hx1 : (OnBytes.Desc.First.K4.envOf { Q.P with tokv := s.tokv } o).claimE o.H.ZE
            o.H.tkh Q.P.V (k4Wit Q cells weights tokens (look Q) m.st.input).tokv = some x := by
          rw [← at_ZE (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard L ds hD
              (by omega) hg hh (rE Q.P Q.hp Q.g + 1) (by omega),
            ← at_tkh (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard L ds hD
              (by omega) hg hh (rE Q.P Q.hp Q.g + 1) (by omega)]
          exact hx
        obtain ⟨u, hu', hs, hUu⟩ := hcl x (List.mem_append_right _ List.mem_cons_self)
        refine ((opened_left Z ds' F hL entry).emb hg).trans ?_
        exact W.emb_claim_read hg (envAt (rE Q.P Q.hp Q.g) (by omega))
          (by
            rw [at_ZE _ _ L ds hD (by omega) hg hh (rE Q.P Q.hp Q.g) (by omega),
              at_tkh _ _ L ds hD (by omega) hg hh (rE Q.P Q.hp Q.g) (by omega)]
            exact hx1) hu' hs hUu
    · rw [if_neg hg] at hce
      obtain rfl := Option.some.inj hce
      have hnum : Q.hp.NCL - 0 = cp.length := by
        have : cp.length + 0 = Q.hp.NCL := hl'
        omega
      unfold mergeSlots
      rw [if_neg hg, if_neg hg, hnum, Array.toList_append, Array.toList_map, Array.toList_range,
        List.range_eq_range']
      refine List.rel_append (forall2_from _ (o.K.sV + ·) cp 0 fun a' z hz => ?_) List.Forall₂.nil
      rw [Nat.zero_add]
      exact hmP a' z hz
  exact merge_start_total Q.P.wsLay (k4Wit Q cells weights tokens (look Q) m.st.input).w
    (worldBehind T own rdOf k y A ds' F entry) (cp ++ ce).toArray (mergeSlots Q.hp Q.g o) _
    (fun c hc => hcl c (by simpa using hc)) hslot
    (by
      rw [OnBytes.Desc.First.P1.powers_size, mergeSlots_size hh0, List.size_toArray]
      exact Nat.le_of_eq hlen)

/-- CONDITIONAL on the named premises. **`OwnBack` WHOLE AT A STAND, WITH THE MERGE's START NO
LONGER A PREMISE.** hJW (`JoinWorth`), which stays a hypothesis, is one of the four sentences of the
batched sumcheck's start; hm: what the slots of the panels' weight claims are worth. -/
theorem ownBack_merged
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (ds' : List Fmt.Drawn) {F₁ F₂ : Fork}
    {fs₂ : Array Aff} (h1 : Later A.F F₁) (hb : formsBack o F₁ = some (fs₂, F₂)) (F : Fork)
    (hL : Later F₂ F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    (hP : ∀ S, OnBytes.Desc.First.K4.Honest.Sides.of Q
        (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some S → TermsPub S)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hok : ∀ tT, o.H.tT = some tT → OnBytes.okE tT.p.eps = true)
    (hz0 : o.H.fo.zx.isEmpty = false)
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
  have hLA : Later A.F F := (h1.trans (OnBytes.Desc.First.K4.formsBack_later hb)).trans hL
  exact ownBack_join Z hT hLk ds' h1 hb F hL entry hP hnE hok hz0 hJW
    (merge_start_stand Z hT hLk ds' F hLA entry hU hm)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.forall2_from
#print axioms ProofFile.Honest.K4.merge_start_stand
#print axioms ProofFile.Honest.K4.ownBack_merged
