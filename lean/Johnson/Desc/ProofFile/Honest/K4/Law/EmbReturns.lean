-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/EmbReturns.lean: CONDITIONAL. A statement with its proof.

What is here: in the first group of layers, at a stand (`K4Stand`, Law/SlotsTrue.lean) of the
layers' own rounds (the sub-protocol K4), four functions of the honest side return: the structure
that the claims read is made; the claim on the embedding is made; its unit stands in the weights'
layout; the verifier's test on a claim's shape accepts it. These are the four hypotheses env, claim,
hu and hs of `emb_head` (Law/W/EmbHead.lean) and of `emb_at` (Law/W/ItemRightOf.lean), in their
letters: at the sampled values as the embedding's value finds them (`W.ptsE`,
Law/W/RightGated.lean).
How. The public test on the parts (`k4Fits`, by `K4Seated.fits`) has the merge's list of claims made
at the merge's first round, each of its members passing that test (`merge_run`, Law/SumAtRun.lean);
in the first group the list's last member is the embedding's claim; `claimEnv_is`
(Law/ClaimsAre.lean), `at_ZE` and `at_tkh` (Law/PtsAt.lean) say that what this claim reads is the
same one round earlier. After the proof text of `merge_start_stand` (Law/MergeStartAtStand.lean).

Not shown here. No property is claimed. That the premises can be met: no example is known.
`K4Seated.fits` is spent: at shapes that do not fit the statement says nothing. `K4LookTieAt`
(Law/ScriptAt.lean) is asked, of which one field is read: the calls' points. RETURNS ALONE: nothing
on what the claim's value is. Nothing on soundness, on completeness or on any other property.

  `emb_returns_stand`   **the four returns**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MergeStartAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightGated

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (WsClaim WsUnit wsClaimShape)
open OnBytes.Model.Layer (Own ClaimEnv)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (Par entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- CONDITIONAL on the stand, the thread, the tie on the lookup and the first group. **THE FOUR
RETURNS.** -/
theorem emb_returns_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (hLk : K4LookTieAt look Q s m) (hg : (Q.g == 0) = true) :
    ∃ (ce : ClaimEnv) (cl : WsClaim) (un : WsUnit),
      claimEnvOf Q
        (W.ptsE Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) = some ce ∧
      ce.claimE
        (W.ptsE Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).ZE
        (W.ptsE Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).tkh Q.P.V
        (k4Wit Q cells weights tokens (look Q) m.st.input).tokv = some cl ∧
      Q.P.wsLay.U[cl.ui]? = some un ∧ wsClaimShape Q.P.wsLay cl = .ok () := by
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
  -- the merge's list at its first round
  obtain ⟨hk, ln, hLs⟩ := W.stand_run Z hT
  have s6 : (starts Q).getD 6 0 = rE Q.P Q.hp Q.g + 1 := by rw [k4_starts]; rfl
  obtain ⟨cls, hcls, _, _, hshape⟩ := merge_run
    (k4Wit Q cells weights tokens (look Q) m.st.input) hk
    (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1)) (stand_own_fits Z hT _)
    (by rw [ln _ (by omega), s6]) (hLs _)
  -- its last member
  have hcls' := hcls
  unfold mergeClaimsAt at hcls'
  obtain ⟨cp, _, h3⟩ := Option.bind_eq_some_iff.mp hcls'
  have h3' : (if (Q.g == 0) = true then
      (Option.map (fun x => [x]) (embClaim Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
          (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g + 1))))).bind fun z => some (cp ++ z)
      else (some []).bind fun z => some (cp ++ z)) = some cls := h3
  rw [if_pos hg] at h3'
  obtain ⟨ce₁, hce, e⟩ := Option.bind_eq_some_iff.mp h3'
  obtain rfl : cp ++ ce₁ = cls := Option.some.inj e
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hce
  have envAt : ∀ n, k4StartAt Q 4 ≤ n → claimEnvOf Q (ptsOf Q
      (k4Wit Q cells weights tokens (look Q) m.st.input) (m.st.heard ++ ds.take n)) =
      some (OnBytes.Desc.First.K4.envOf { Q.P with tokv := s.tokv } o) := fun n hn =>
    claimEnv_is _ _ hh0 hSz ds hD (by omega) hh hzk n hn
  unfold embClaim at hx
  rw [if_pos hg, envAt _ (by omega)] at hx
  have hx1 : (OnBytes.Desc.First.K4.envOf { Q.P with tokv := s.tokv } o).claimE o.H.ZE
      o.H.tkh Q.P.V (k4Wit Q cells weights tokens (look Q) m.st.input).tokv = some x := by
    rw [← at_ZE (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard L ds hD
        (by omega) hg hh (rE Q.P Q.hp Q.g + 1) (by omega),
      ← at_tkh (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard L ds hD
        (by omega) hg hh (rE Q.P Q.hp Q.g + 1) (by omega)]
    exact hx
  have hs : wsClaimShape Q.P.wsLay x = .ok () := by
    have h := hshape x (List.mem_append_right _ List.mem_cons_self)
    cases hc : wsClaimShape Q.P.wsLay x with
    | ok _ => rfl
    | error _ =>
      rw [hc] at h
      cases h
  obtain ⟨u, hu'⟩ := shape_unit hs
  refine ⟨_, x, u, envAt (rE Q.P Q.hp Q.g) (by omega), ?_, hu', hs⟩
  show (OnBytes.Desc.First.K4.envOf { Q.P with tokv := s.tokv } o).claimE
    (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g))).ZE
    (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (m.st.heard ++ ds.take (rE Q.P Q.hp Q.g))).tkh Q.P.V
    (k4Wit Q cells weights tokens (look Q) m.st.input).tokv = some x
  rw [at_ZE _ _ L ds hD (by omega) hg hh (rE Q.P Q.hp Q.g) (by omega),
    at_tkh _ _ L ds hD (by omega) hg hh (rE Q.P Q.hp Q.g) (by omega)]
  exact hx1

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.emb_returns_stand
