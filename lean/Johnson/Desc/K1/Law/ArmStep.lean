-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmStep.lean: what the sub-protocol at a link's reads (the commitment, then the step
without a round that closes the approximate range proof's list of tables) leaves of that proof's
parameters in the verifier's state: the facts hs ho hfun htab hu3 that the feed-forward links'
files' and attention's files' halves of the exchange ask (Johnson/Desc/K1/Law/ArmHalves.lean),
as far as they are facts OF THIS STEP.
OBJECT: `IM.k1Quiet G l X` and `blkL Z G l false X arrs`.
USER: Johnson/Desc/K1/Law/ArmAtReads.lean.
LETTERS: Z, G, l, X, arrs; s, s' (the states in front and behind); b₀ | a₀ (the open link's part).
  `close_turns`, `closed_turns`   closing the list lays the list and leaves the places' numbering
                   (`tabAt`) and the number of the array of the reads (`u3Of`). (The
                   feed-forward files name a lemma closing_turns of their own, Johnson/Road/K4/ClosedTurns.lean: these
                   two are its twins.)
  `LayTurns`, `lay_at_reads`   from a state that stands in a feed-forward link: the plan hp is the public
                   parameters' at the link's group (G.W.G[X.g]?); what the link's own rounds returned is
                   laid (o); behind, the parameters tl' have o's list, hp.tl's numbering and number
  `AttTurns`, `att_at_reads`   from a state that stands in an attention link: the plan Ap is
                   G.W.A[X.g]?; behind, tl' has the numbering and the number of THE STATE's OWN
                   parameters in front (tlF); and, where the array of the reads is in the ledger, its
                   list is `funsAt Ap s`: `K5Law.block4_funs` IS CALLED
                   (Johnson/Desc/First/Att/Claims/FunsAtTl.lean)
What is not claimed. That the state's own parameters in front of an attention link's reads are the
plan's. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmBySort
import Johnson.Desc.K1.Law.LookAtLater
import Johnson.Desc.First.Att.Claims.FunsAtTl
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S LayOwn AttOwn)
open VerifiableInference.Desc.K8.ReadsQuiet (closed layers_ok head_ok)
open VerifiableInference.Desc.First.Att (readsAtSO readsStepO)
open OnBytes.Model.Stages (LinkH)
open Meaning.K2 (bindE)
open K5Law (funsAt block4_funs)

variable {Cl : Type}

/-! ## 1 Closing the list -/

theorem close_turns {tl tl' : HTailF2} {funs : Array HFun}
    (h : First.K8.Order.close tl funs = .ok tl') :
    tl'.funs = funs ∧ (∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg) ∧ u3Of tl' = u3Of tl := by
  unfold First.K8.Order.close at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, fun _ _ _ => rfl, rfl⟩

theorem closed_turns {tl tl' : HTailF2} {funs : Array HFun} {L : LinkCtx} {st : Statement}
    (h : closed tl funs L st = .ok tl') :
    tl'.funs = funs ∧ (∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg) ∧ u3Of tl' = u3Of tl := by
  unfold closed at h
  obtain ⟨t, h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact close_turns h1

/-! ## 2 A feed-forward link -/

/-- What stands behind the step, from a state in a feed-forward link whose own rounds' return is
own?. -/
def LayTurns (G : ProofFile.Ground) (X : LinkH) (own? : Option Layer.Own) (s' : S) : Prop :=
  ∃ hp o tl', G.W.G[X.g]? = some hp ∧ own? = some o ∧ s'.tl? = some tl' ∧ tl'.funs = o.funs ∧
    (∀ Fn c sg, hp.tl.tabAt Fn c sg = tl'.tabAt Fn c sg) ∧ u3Of tl' = u3Of hp.tl

theorem kinds_at {G : ProofFile.Ground} {l : ℕ} {X : LinkH} (hX : G.built[l]? = some X) {k : ℕ × ℕ}
    (hk : (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some k) : k = (X.kind, X.g) := by
  rw [List.getElem?_map, Array.getElem?_toList, hX] at hk
  exact (Option.some.inj hk).symm

/-- Which block stands behind the reads' commitment. -/
theorem readsQuietAt_cases {G : ProofFile.Ground} {l : ℕ} {X : LinkH} {piece : ℕ} {q : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some q) :
    First.Att.readsAtO G.W l X.g = some q ∨
      K8.ReadsQuiet.blockAt G.W.G G.W.hS G.W.HLy G.W.H
        (G.built.toList.map fun Y => (Y.kind, Y.g)) l = some q := by
  unfold ProofFile.readsQuietAt at h
  by_cases k1 : (X.kind == 1) = true
  · rw [if_pos k1] at h
    by_cases k2 : (piece == 4) = true
    · rw [if_pos k2] at h
      exact Or.inl h
    · rw [if_neg k2] at h
      cases h
  · rw [if_neg k1] at h
    by_cases k2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos k2] at h
      exact Or.inr h
    · rw [if_neg k2] at h
      cases h

theorem blockAt_cases {G : ProofFile.Ground} {l : ℕ} {X : LinkH} (hX : G.built[l]? = some X)
    {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G.W.G G.W.hS G.W.HLy G.W.H
      (G.built.toList.map fun Y => (Y.kind, Y.g)) l = some q) :
    (∃ hp, G.W.G[X.g]? = some hp ∧ q = K8.ReadsQuiet.layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩) ∨
      q = K8.ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩ := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := kinds_at hX hk
  dsimp only at h
  split at h
  · obtain ⟨hp, hg, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inl ⟨hp, hg, rfl⟩
  · split at h
    · exact Or.inr (Option.some.inj h).symm
    · cases h

theorem quiet_lay (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (hX : G.built[l]? = some X) :
    ∀ (s : S) rs gs (s' : S), (IM.k1Quiet G l X).decide s rs gs = .ok s' →
      ∀ a : LayOwn, s.here = .lay a → LayTurns G X a.own s' := by
  unfold IM.k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s rs gs s' h => nomatch h
  | some q =>
    intro s rs gs s' hd a ha
    have hd' : q.decide s rs gs = .ok s' := hd
    rcases readsQuietAt_cases hq with hz | hz
    · unfold First.Att.readsAtO at hz
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hz
      have hd'' : readsAtSO A s = .ok s' := hd'
      obtain ⟨a', t, tl, ha', _⟩ := Meaning.K2.readsAtSO_eq hd''
      rw [ha] at ha'
      cases ha'
    · rcases blockAt_cases hX hz with ⟨hp, hg, rfl⟩ | rfl
      · obtain ⟨a', own, tl', ha', ho, hc, rfl⟩ := layers_ok hd'
        rw [ha] at ha'
        cases ha'
        obtain ⟨e1, e2, e3⟩ := closed_turns hc
        exact ⟨hp, own, tl', hg, ho, rfl, e1, e2, e3⟩
      · obtain ⟨a', cov, x, t, tl', ha', _⟩ := head_ok hd'
        rw [ha] at ha'
        cases ha'

/-- The commitment's three writes at a state in a feed-forward link. -/
theorem here_commit_lay {Lt : Type} {s : S} {b₀ : LayOwn} (hs : s.here = .lay b₀)
    (d : _root_.Desc.Plain.DState Lt) (L : LinkCtx) (F : Fork) :
    (((laid s d).putLink L).putFork F).here = .lay { b₀ with L := L, F := F } := by
  have e1 : (laid s d).here = .lay b₀ := hs
  have e2 : ((laid s d).putLink L).here = .lay { b₀ with L := L } := by
    unfold S.putLink
    rw [e1]
  unfold S.putFork
  rw [e2]

def LaterLay (G : ProofFile.Ground) (X : LinkH) (B : Block S Unit) : Prop :=
  ∀ (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    ∀ b₀ : LayOwn, s.here = .lay b₀ → LayTurns G X b₀.own s'

theorem laterLay_joined (G : ProofFile.Ground) (X : LinkH) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (nm : String) (q : Block S Unit)
    (hq : ∀ (s : S) rs gs (s' : S), q.decide s rs gs = .ok s' →
      ∀ a : LayOwn, s.here = .lay a → LayTurns G X a.own s') :
    LaterLay G X (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h b₀ hs
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨_, F, _, y, _, _, _, e, _⟩ := commitAtS_slots h1
  have hs₁ := here_commit_lay hs y.w y.L y.F
  rw [← e] at hs₁
  exact hq _ _ _ _ h3 { b₀ with L := y.L, F := y.F } hs₁

/-- **At a feed-forward link's reads.** -/
theorem lay_at_reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (hX : G.built[l]? = some X) (pr : ℕ) (reads : Option (List ℕ)) :
    LaterLay G X (IM.k1Reads Z G l X pr reads) :=
  laterLay_joined G X _ _ _ _ _ _ (quiet_lay G l X hX)

/-! ## 3 An attention link -/

/-- The step at an attention link: what it lays at the parameters. -/
theorem readsAtSO_turns {A : Attention.Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    ∃ a tl', s.here = .att a ∧ s'.tl? = some tl' ∧
      (∀ Fn c sg, a.tl.tabAt Fn c sg = tl'.tabAt Fn c sg) ∧ u3Of tl' = u3Of a.tl := by
  unfold readsAtSO at h
  dsimp only at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨r, hr, h⟩ := bindE h
    cases h
    unfold readsStepO at hr
    obtain ⟨_, _, hr⟩ := bindE hr
    obtain ⟨_, _, hr⟩ := bindE hr
    obtain ⟨_, _, hr⟩ := bindE hr
    obtain ⟨tl', hc, hr⟩ := bindE hr
    obtain ⟨_, _, hr⟩ := bindE hr
    cases hr
    obtain ⟨_, e2, e3⟩ := close_turns hc
    exact ⟨a, tl', ha, rfl, e2, e3⟩
  · cases h

/-- What stands behind the step, from a state s in an attention link with the ledger F₀. -/
def AttTurns (G : ProofFile.Ground) (X : LinkH) (F₀ : Fork) (s s' : S) : Prop :=
  ∃ Ap tlF tl', G.W.A[X.g]? = some Ap ∧ s.tl? = some tlF ∧ s'.tl? = some tl' ∧
    (∀ Fn c sg, tlF.tabAt Fn c sg = tl'.tabAt Fn c sg) ∧ u3Of tl' = u3Of tlF ∧
    ((F₀.trees[Ap.iU3]?).isSome = true → tl'.funs.toList = funsAt Ap s)

/-- **At an attention link's reads.** -/
theorem att_at_reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH)
    (hX : G.built[l]? = some X) (pr : ℕ)
    (reads : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h2 : rs.length = 2) (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') (a₀ : AttOwn)
    (hs : s.here = .att a₀) : AttTurns G X a₀.F s s' := by
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes _ _ _ _ _ (IM.k1Quiet G l X) s s' r₁ r₂ gs h
  obtain ⟨_, F, _, y, _, _, _, e, _⟩ := commitAtS_slots h1
  have hs₁ := K5Law.here_commit hs y.w y.L y.F
  rw [← e] at hs₁
  have htl : s₁.tl? = s.tl? := (commitAtS_tl _ _ _ _ s s₁ _ gs₁ h1).1
  have hk : ∃ z : Block S Unit, First.Att.readsAtO G.W l X.g = some z ∧ IM.k1Quiet G l X = z := by
    revert h3
    unfold IM.k1Quiet
    dsimp only
    cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
    | none => exact fun h => nomatch h
    | some q =>
      intro h3
      have h3' : q.decide s₁ rs₂ gs₂ = .ok s' := h3
      rcases readsQuietAt_cases hq with hz | hz
      · exact ⟨q, hz, rfl⟩
      · exfalso
        rcases blockAt_cases hX hz with ⟨hp, hg, rfl⟩ | rfl
        · obtain ⟨a', own, tl', ha', _⟩ := layers_ok h3'
          rw [hs₁] at ha'
          cases ha'
        · obtain ⟨a', cov, x, t, tl', ha', _⟩ := head_ok h3'
          rw [hs₁] at ha'
          cases ha'
  obtain ⟨z, hz, ez⟩ := hk
  have hz' := hz
  unfold First.Att.readsAtO at hz'
  obtain ⟨Ap, hAp, rfl⟩ := Option.map_eq_some_iff.1 hz'
  rw [ez] at h3
  have h3' : readsAtSO Ap s₁ = .ok s' := h3
  obtain ⟨a₁, tl', ha₁, htl', e2, e3⟩ := readsAtSO_turns h3'
  have hF : s₁.tl? = some a₁.tl := by
    unfold S.tl?
    rw [ha₁]
  refine ⟨Ap, a₁.tl, tl', hAp, htl ▸ hF, htl', e2, e3, fun hT => ?_⟩
  have hw : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).andThen
      (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).name (IM.k1Quiet G l X)).decide s
      [r₁, r₂] gs = .ok s' := h
  rw [ez] at hw
  have hb := block4_funs G.first (gpOf Z) l pr 1 reads _ G.W l X.g _ hz hAp hw hs hT
  rw [htl'] at hb
  exact Option.some.inj hb

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.closed_turns
#print axioms VerifiableInference.Desc.K1.lay_at_reads
#print axioms VerifiableInference.Desc.K1.att_at_reads
