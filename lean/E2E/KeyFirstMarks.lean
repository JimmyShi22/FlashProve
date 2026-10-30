-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyFirstMarks.lean: the claims half of the walk of marks: at the key file's first chain's last state every open row of the
own group passes the clauses of the adding (`claimsAtB`). The own group is made at the chain's sub-protocol "w.1.send", its
rows are laid there, and only the seal stands behind it; so no walk over the earlier members is needed.

Main names.
  `joinAll_claims`, `rows_claims`: the text behind W's commitment lays the mark on the group that it makes.
  `sendW_claims`: so "w.1.send" does.
  `claims_of_fold`: at a fold over the whole chain.
  `claims_of_thr`: at a stand of a thread at border 19, in scope.

What stays open. Sample rows: `SamplesDense` is the other half. That a thread stands.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyMarkJoined
import E2E.KeyShapeFirstBack
import E2E.KeyShapeFullSourced
import Johnson.Desc.K13.Law.Own
import Johnson.Desc.Ground.Shape.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons_ok foldBlocks_append_ok)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP)
open VerifiableInference.Desc.Ground.Sh (claimsAtB claimsAt_iff newGroup_claims join_claims addRows_claims)
open VerifiableInference.Desc.Key (ChainState FirstState Claim sendW Pieces Source LaterPlaces)
open VerifiableInference.Desc.K13 (rows joinAll St)
open VerifiableInference.Desc.K13.Law (rows_is bind_ok there_ok pure_ok ebind_ok rowsB_ok)
open AtPublicFiles.AtFiles (sendWAt flat₁ flat₁_cut seal_same KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (public_first_sourced)

/-- The joinings keep the mark. -/
theorem joinAll_claims (g g' : Nat) : ∀ (l : List Nat) (d d' : St), joinAll g l d = .ok d' →
    claimsAtB d.st g' = true → claimsAtB d'.st g' = true
  | [], d, d', h, hc => by
    have e : d = d' := Except.ok.inj h
    rw [← e]
    exact hc
  | o :: l, d, d', h, hc => by
    simp only [joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    exact joinAll_claims g g' l d₁ d' h2 (join_claims _ _ _ _ _ h1 g' hc)

/-- **The text behind W's commitment lays the mark on the group that it makes.** -/
theorem rows_claims {Sh : LinShape} {claim : OnBytes.LinClaim} {ids : Array Nat} {d : St}
    {o : OnBytes.LinFirst × St} (h : rows Sh claim ids d = .ok o) :
    claimsAtB o.2.st o.1.own = true := by
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, hw, ⟨n, d₀⟩, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, hr, d₄, h4, rfl⟩ := h
  have hn : n = d.st.groups.size := by
    unfold newGroupP at hb
    split at hb
    · exact (Prod.mk.inj (Option.some.inj hb)).1.symm
    · cases hb
  have c0 : claimsAtB d.st n = true := by
    refine claimsAt_iff.2 fun G hG => ?_
    rw [hn, Array.getElem?_eq_none (Nat.le_refl _)] at hG
    cases hG
  have c1 := newGroup_claims _ _ _ _ _ hb n c0
  have c2 := joinAll_claims n n _ _ _ h1 c1
  have c3 := join_claims _ _ _ _ _ h2 n c2
  have c4 : claimsAtB d₃.st n = true := by
    split at h3
    · exact join_claims _ _ _ _ _ h3 n c3
    · rw [← Option.some.inj h3]
      exact c3
  exact addRows_claims _ _ _ _ h4 n c4

section
variable {β Cl : Type}

/-- **"w.1.send" lays the claim's group with the mark.** -/
theorem sendW_claims (one : OneTime) (N : Pieces) (sent : Nat) (groups : List (List Nat))
    (bw : Block (ChainState β) Cl) (hw : sendW one N sent groups = some bw) (s s' : ChainState β)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : bw.decide s rs gs = .ok s') :
    ∃ l, s'.lin = some l ∧ claimsAtB s'.d.st l.own = true := by
  unfold sendW at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  dsimp only at h
  rw [VerifiableInference.Desc.decide_andThen] at h
  obtain ⟨t₃, -, hr⟩ := ebind_ok.1 h
  obtain ⟨p, l₀, o, hp, -, ho, rfl⟩ := rowsB_ok _ _ hr
  obtain ⟨-, rfl⟩ := (VerifiableInference.Desc.Key.lens_get _ _).1 hp
  refine ⟨o.1, ?_, ?_⟩
  · rw [VerifiableInference.Desc.Key.lens_set]
  · rw [VerifiableInference.Desc.Key.lens_set]
    exact rows_claims ho

end

section
variable (Q : AtPublicFiles.KeyShape.Pub1) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (N : H2U.PlaceNums)

/-- **At a fold over the whole first chain.** -/
theorem claims_of_fold (bw : Block FirstState Claim) (hw : sendWAt Q D told = some bw) {ft : Nat}
    {s e : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {r : List Fmt.RoundView} {c : List OpenedColumn}
    (h : foldBlocks ft (flat₁ Q D told N) s rs cols = .ok (e, r, c)) :
    ∃ l, e.lin = some l ∧ claimsAtB e.d.st l.own = true := by
  rw [flat₁_cut Q D told N bw hw] at h
  obtain ⟨s₁, r₁, c₁, -, f⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h
  obtain ⟨-, s₂, _, -, f⟩ := foldBlocks_cons_ok.1 f
  obtain ⟨-, s₃, _, -, f⟩ := foldBlocks_cons_ok.1 f
  obtain ⟨-, s₄, _, st₄, f⟩ := foldBlocks_cons_ok.1 f
  obtain ⟨-, s₅, _, st₅, f⟩ := foldBlocks_cons_ok.1 f
  have q : (Except.ok (s₅, _, _) : Except String (FirstState × List Fmt.RoundView × List OpenedColumn)) = .ok (e, r, c) := f
  obtain rfl : s₅ = e := (Prod.mk.inj (Except.ok.inj q)).1
  have d₄ := (Block.step_ok.1 st₄).2.2.1
  have d₅ := (Block.step_ok.1 st₅).2.2.1
  obtain ⟨l, hL⟩ : ∃ l, (VerifiableInference.Desc.Key.firstChain Q.one D told Q.set N).last =
      VerifiableInference.Desc.Key.firstChainEnd VerifiableInference.Desc.Key.pieces l := ⟨_, rfl⟩
  rw [hL] at d₅
  have key : ∀ (rs' : List Fmt.RoundView) (gs' : List (List (Nat × List UInt64))),
      (VerifiableInference.Desc.Key.firstChainEnd (Cl := Claim) VerifiableInference.Desc.Key.pieces l).asBare.decide s₄
        rs' gs' = .ok s₅ → s₅ = s₄ := fun rs' gs' h =>
    seal_same (Cl := Claim) VerifiableInference.Desc.Key.pieces l s₄ s₅ rs' gs' h
  have e₅ : s₅ = s₄ := key _ _ d₅
  rw [e₅]
  exact sendW_claims _ _ _ _ bw hw _ _ _ _ d₄

end

section
variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {Nn : H2U.PlaceNums} {P : LaterPlaces} {V W Xh Pb : Type} {Bk : ProverCoinCounts}

/-- **At a stand of a thread at border 19, in scope.** -/
theorem claims_of_thr (hs : KeySourced Z X Nn P) (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X Nn P).S₁ (keyFileDescription X Nn P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X Nn P).first.blocksInOrder) {k : Coins Bk} {e₁ : (keyFileDescription X Nn P).S₁} {m : Mid W Xh} {E : Env}
    (h : Thr T₁ 19 k e₁ m E) : ∃ l, e₁.lin = some l ∧ claimsAtB e₁.d.st l.own = true := by
  obtain ⟨bw, hw, -, -, -⟩ := public_first_sourced hs scope
  obtain ⟨-, -, -, -, s₀, cols, -, -, hf⟩ := h.2.2.2.2.1
  have hl := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  rw [hbs, ← hl, List.take_length] at hf
  exact claims_of_fold _ X.Y.D.1 X.Y.told.1 Nn bw hw hf

end

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.joinAll_claims
#print axioms AtPublicFiles.KeyLastChain.rows_claims
#print axioms AtPublicFiles.KeyLastChain.sendW_claims
#print axioms AtPublicFiles.KeyLastChain.claims_of_fold
#print axioms AtPublicFiles.KeyLastChain.claims_of_thr
