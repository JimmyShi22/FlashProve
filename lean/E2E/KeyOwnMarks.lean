-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnMarks.lean: the marks that the key file's own test asks on entry, carried from the last chain's first state to
border 2: every open row of the own group passes the clauses of the adding (the library's `claimsAtB`), and every sample row
is dense. So `claims` and `dense` of `OwnAsks` follow from those marks at the chain's first state.

Main names.
  `SamplesDense`, `OwnMark`: the marks.
  `takeOver_inv`: what a yes of the taking-over is made of.
  `dense_renamed`.
  `second_mark`: the first member carries `OwnMark`. `hfresh`: Omega's new number is no member yet.
  `mark_at_two`: at a stand at border 2, under a premise on every letter ends, not what `lotSamplesDense` pays; `mark_stand` (E2E/KeyOwnMarkStand.lean) is the form met.
  `fresh_A0`, `fresh_of_shape`: that premise, at the written shape, by a closed line.
  `asks_of_mark`: the clauses `claims` and `dense` of `OwnAsks` on entry.

What stays open. `hstart`: that the chain begins at a state with `OwnMark`: the first chain's walk up to its last border,
and the shared chain's sample rows. `hrun`: the own group has not begun its test: at the shape.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastValues
import E2E.KeyOwnFront
import Johnson.Desc.K12.Honest.Shape.TestClaims
import Johnson.Desc.Third.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open OnBytes.Slice.ProxRun (DenseRow)
open _root_.Desc.Plain (DState)
open ProofFile.Honest
open ProofFile.Honest.Sh (claimsB claimsB_of_mark runRows_dense)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons_ok step_iff named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart takeOver takenSources Loc₃)
open VerifiableInference.Desc.Third.Law (ok_of_bind some_of_named k14Second_inv law_k14Second takenSources_same)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource thirdPar ownTest)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF KeySourced ThirdShaped)
open AtPublicFiles.AtFiles.Full (A0)

/-- Every sample row of the statement is dense. -/
def SamplesDense (S : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), S.oracles[o]? = some x → ∀ r ∈ x.sampleRows.toList, DenseRow r

/-- **The marks on the chain's state.** -/
structure OwnMark (s : S₃) : Prop where
  claims : claimsAtB s.st s.loc.own = true
  samples : SamplesDense s.st
  shared : ∀ b, s.loc.border = some b → SamplesDense b.shared.st

/-- **A yes of the taking-over.** -/
theorem takeOver_inv {S : LinShape} {own : Nat} {o : VerifiableInference.Desc.Third.SharedOut} {d : DState Loc₃}
    {mine : Nat} {d₂ : DState Loc₃} (h : takeOver S own o d = .ok (mine, d₂)) :
    ∃ (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src)) (ids : Array Nat) (d₀ d₁ : DState Loc₃),
      adoptP d sent given = some (ids, d₀) ∧ elsewhereP d₀ mine o.st o.omega = some d₁ ∧
        joinP d₁ own mine false = some d₂ := by
  unfold takeOver at h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨⟨ids, d₀⟩, ha, h⟩ := ok_of_bind h
  obtain ⟨m', _, h⟩ := ok_of_bind h
  obtain ⟨d₁, h1, h⟩ := ok_of_bind h
  obtain ⟨d₂', h2, h⟩ := ok_of_bind h
  have e : (m', d₂') = (mine, d₂) := Except.ok.inj h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  exact ⟨_, _, ids, d₀, d₁, some_of_named ha, some_of_named h1, some_of_named h2⟩

/-- The taking over leaves the groups. -/
theorem adopt_groups {L : Type} {d d' : DState L} {sent : Array OracleNotice} {given : Array (Nat × Fmt.Src)}
    {ids : Array Nat} (h : adoptP d sent given = some (ids, d')) : d'.st.groups = d.st.groups := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, rfl⟩ := Prod.mk.inj e
    rfl
  · cases h

theorem dense_renamed {r : OnBytes.Row} (o : Nat) (h : DenseRow r) : DenseRow (r.renamed o) := by
  refine ⟨fun t ht => ?_, fun f hf => ?_⟩
  · simp only [OnBytes.Row.renamed, Array.toList_map, List.mem_map] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact h.1 u hu
  · simp only [OnBytes.Row.renamed, Array.toList_map, List.mem_map] at hf
    obtain ⟨u, hu, rfl⟩ := hf
    exact h.2 u hu

/-- **The first member carries the marks.** -/
theorem second_mark {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hfresh : ∀ G, s.st.groups[s.loc.own]? = some G → s.st.oracles.size ∉ G.members.toList)
    (hm : OwnMark s) : OwnMark s' := by
  have hsay := (law_k14Second (Cl := Cl) p).2 _ _ _ _ h
  obtain ⟨x, ⟨mine, d₂⟩, dot, b, hb, ha, hd, hab, e⟩ := k14Second_inv p s s' rs gs h
  obtain ⟨x', y, G, dot', hb', hl, hy, -, hsz, hnew, -, -, -, -, -, -, hold, -, -⟩ := hsay
  obtain rfl : x = x' := Option.some.inj (hb.symm.trans hb')
  have hmine : mine = s.st.oracles.size := by
    have q : s'.loc = { s.loc with border := none, omega := mine } := by
      rw [e]
    have q' := q.symm.trans hl
    exact congrArg (·.omega) q'
  have hown : s'.loc.own = s.loc.own := by
    rw [hl]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨sent, given, ids, d₀, d₁, e0, e1, e2⟩ := takeOver_inv ha
    have c1 := adopt_claims _ _ _ _ _ e0 s.loc.own hm.claims
    have hnot : ∀ G : GrpSh, (stSh d₀.st).groups[s.loc.own]? = some G → mine ∉ G.members := by
      intro G' hG'
      rw [grp_get, adopt_groups e0] at hG'
      obtain ⟨G₀, hG₀, rfl⟩ := Option.map_eq_some_iff.1 hG'
      rw [hmine]
      exact hfresh G₀ hG₀
    have c2 := elsewhere_claims _ _ _ _ _ e1 s.loc.own hnot c1
    have c3 := join_claims _ _ _ _ _ e2 s.loc.own c2
    have c4 := addRow_claims _ _ _ _ hab s.loc.own c3
    rw [hown, e]
    exact c4
  · intro o X hX r hr
    by_cases hlt : o < s.st.oracles.size
    · rw [hold o hlt] at hX
      exact hm.samples o X hX r hr
    · by_cases he : o = s.st.oracles.size
      · subst he
        rw [hnew] at hX
        obtain rfl := Option.some.inj hX
        simp only [Array.toList_map, List.mem_map] at hr
        obtain ⟨u, hu, rfl⟩ := hr
        exact dense_renamed _ (hm.shared x hb x.shared.omega y hy u hu)
      · have hge : s'.st.oracles.size ≤ o := by
          rw [hsz]
          omega
        rw [Array.getElem?_eq_none hge] at hX
        cases hX
  · intro b' hb''
    rw [hl] at hb''
    cases hb''

/-- The first member's new number is no member, at the written shape. -/
theorem fresh_A0 : ((A0.1.st.groups[A0.2.own]?).all fun G => !G.members.contains A0.1.st.oracles.length) = true := by
  decide +kernel

theorem fresh_of_shape {s : S₃} (hsh : sh₃ SF s = A0) :
    ∀ G, s.st.groups[s.loc.own]? = some G → s.st.oracles.size ∉ G.members.toList := by
  intro G hG hmem
  have h := fresh_A0
  rw [← hsh] at h
  have hg : (stSh s.st).groups[s.loc.own]? = some (grpSh G) := by
    rw [grp_get, hG]
    rfl
  have h' : (((stSh s.st).groups[s.loc.own]?).all fun G =>
      !G.members.contains (stSh s.st).oracles.length) = true := h
  rw [hg] at h'
  have hl : (stSh s.st).oracles.length = s.st.oracles.size := by
    show (s.st.oracles.toList.map orcSh).length = _
    simp
  rw [hl] at h'
  have h'' : (!(G.members.toList.contains s.st.oracles.size)) = true := h'
  simp [hmem] at h''

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {Bk : ProverCoinCounts} {V W Y Pb : Type}
  {T₃ : Thread Bk (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl V W Y Pb}
  {v : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}

/-- **At a stand at border 2 the marks hold**, where the chain begins at them. -/
theorem mark_at_two (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hbs : T₃.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) (hZ : ThirdShaped T₃ v A0)
    (hstart : ∀ k w h s₀, T₃.begun k w h s₀ → OwnMark s₀) {k : Coins Bk} {st : S₃} {m : Mid W Y} {E : Env}
    (hT : Thr T₃ 2 k st m E) : OwnMark st := by
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hT.2.2.2.2.1
  have hm₀ := hstart _ _ _ _ hbeg
  obtain ⟨-, -, hlin, -⟩ := AtPublicFiles.AtFiles.Full.first_of_sourced hs scope fun _ _ _ _ => true
  have hS : Xs.chains.made.sized.key.once.shape = SF := hlin.symm.trans (AtPublicFiles.AtFiles.Full.six_sourced hs scope).lin
  have hsh₀ : sh₃ SF s₀ = A0 := by
    have q := hZ.first _ _ _ _ hT.2.2.2.2.2.2 hbeg
    have q' : sh₃ Xs.chains.made.sized.key.once.shape s₀ = A0 := q
    rw [hS] at q'
    exact q'
  obtain ⟨b₀, b₁, e, d₀, d₁⟩ : ∃ b₀ b₁, (descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2 = [b₀, b₁] ∧
      b₀.decide = (batchLinearConstraintsSecondPart (Cl := Unit) (thirdPar Xs.chains)).decide ∧
      b₁.decide = (takenSources (ownTest Pl) : Block S₃ Unit).decide := ⟨_, _, rfl, rfl, rfl⟩
  rw [hbs, e] at hf
  obtain ⟨-, s₁, _, hs₁, h₁⟩ := foldBlocks_cons_ok.1 hf
  obtain ⟨-, s₂, _, hs₂, h₂⟩ := foldBlocks_cons_ok.1 h₁
  have hy₁ := ((step_iff _ b₀ s₀ s₁ _ _ _).1 hs₁).2.1
  have hy₂ := ((step_iff _ b₁ s₁ s₂ _ _ _).1 hs₂).2.1
  rw [d₀] at hy₁
  rw [d₁] at hy₂
  have m₁ := second_mark (Cl := Unit) _ s₀ s₁ _ _ hy₁ (fresh_of_shape hsh₀) hm₀
  have e₂ : s₂ = s₁ := takenSources_same _ s₁ s₂ _ _ hy₂
  have q : (Except.ok (s₂, _, _) : Except String (S₃ × List Fmt.RoundView × List OpenedColumn)) = .ok (st, [], []) := h₂
  have e₃ : s₂ = st := (Prod.mk.inj (Except.ok.inj q)).1
  rw [← e₃, e₂]
  exact m₁

end

/-- **The clauses `claims` and `dense` of `OwnAsks` on entry**, at a state with the marks whose own group has not begun. -/
theorem asks_of_mark {st : S₃} {t : T12} (he : enterOwn st = .ok t) (hm : OwnMark st)
    (hrun : ∀ G, st.st.groups[st.loc.own]? = some G → G.inRun = false) (hG : ∃ G, st.st.groups[st.loc.own]? = some G) :
    claimsB t = true ∧ ∀ G, t.st.groups[t.g]? = some G →
      ∀ r ∈ (OnBytes.Slice.runRows t.st G).toList, DenseRow r := by
  have e : t = {
      st := st.st, book := st.book, roots := st.roots, g := st.loc.own, pass := .nothing,
      mask := st.loc.mask } := (Except.ok.inj he).symm
  subst e
  obtain ⟨G, hG⟩ := hG
  have hc : claimsB {
      st := st.st, book := st.book, roots := st.roots, g := st.loc.own, pass := .nothing,
      mask := st.loc.mask } = true := claimsB_of_mark hG (hrun G hG) hm.claims
  exact ⟨hc, fun G' hG' => runRows_dense hG' hc fun o _ x hx r hr => hm.samples o x hx r hr⟩

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.takeOver_inv
#print axioms AtPublicFiles.KeyLastChain.adopt_groups
#print axioms AtPublicFiles.KeyLastChain.dense_renamed
#print axioms AtPublicFiles.KeyLastChain.second_mark
#print axioms AtPublicFiles.KeyLastChain.fresh_A0
#print axioms AtPublicFiles.KeyLastChain.fresh_of_shape
#print axioms AtPublicFiles.KeyLastChain.mark_at_two
#print axioms AtPublicFiles.KeyLastChain.asks_of_mark
