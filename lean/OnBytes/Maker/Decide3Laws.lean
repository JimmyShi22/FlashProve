-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Decide3Laws.lean: a yes of the shipped verifier's decision on a key file or a proof
file gives a yes of the three decisions as one (`decide3`, OnBytes/Maker/Decide3.lean) at the three
views of the file as read, if the key and these views pass the tests on the words (`okSeeds`,
`okView`, OnBytes/Maker/OkView.lean).

Of the things in which the two texts differ (the head of OnBytes/Maker/Decide3.lean), two are met
here: `decide3` names the trees that the third chain takes over by made-up names, and it gets the
first view without the round in which the first chain is sealed and puts a round without a digest
in its place. Neither is read by a block's run: that is the law "blind" on the blocks as programs
(`tailRefusal_blind`, `keyRefusal_blind`, `refusalOn_blind`: OnBytes/TypedOracleCompiler/Laws/), which this file
calls.

  `tailAt`          the made-up reading at which `decide3` decides: three views, the key, and the
                    made-up names
  `runs3_eq`        `runs3` is the shipped text's decision (a run of the first block, then
                    `tailRefusal`) at that reading
  `decide3_eq`      `decide3` is the tests on the key's and the views' words, and that decision
  `okView_alike`, `okView_withSeal`
                    the test on the words reads no digest drawn, and a sealing round passes it
  `okRead`          the key and the three views of a file as read pass the tests on the words
  `SealedLast`      a view's last round holds no value and draws nothing but a digest
  `dropSeal`        the view without its last round
  `decideKey_iff`, `decideProof_iff`
                    the three decisions as one, at views that are the file's but for digests, say
                    yes if and only if the file's key and views pass the tests on the words and the
                    shipped decision on the file as read says yes
  `decideKey_of_yes`, `decideProof_of_yes`
                    the same at the file's own three views, the first without its sealing round

What is asked. `SealedLast` of the first view as read, and `okRead`: not shown here
(OnBytes/Maker/OfThreeChains.lean has the second of what the program has read). For a proof file:
that the
first chain's block carries the law's relation (`hb`); for the program's own block that is
`carries_programBlock`.
Not claimed. That the views of a typed transcript are a file's views. Nothing on reading, and
nothing on soundness.


-/
import OnBytes.Maker.Decide3
import OnBytes.TypedOracleCompiler.Laws.LawCall

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TwoLaws

/-- The made-up reading at which `decide3` decides. -/
def tailAt (key : TableKey) (n₁ n₂ : Nat) (v₁ v₂ v₃ : Fmt.View) : TailRead :=
  ⟨{ Three.tagChain 1 n₁ with view := v₁ }, ⟨0, .empty, 0, 0⟩, key,
    { Three.tagChain 2 n₂ with view := v₂ }, { Three.tagChain 0 0 with view := v₃ }⟩

/-- A run's verdict through `judge`. -/
theorem judge_ok {α : Type} (front : String) (b : Blk α) (s : Start) (v : Fmt.View) :
    (∃ f, b.runOn s v = .error f ∧ judge front b s v = .error (refusalName front f.name)) ∨
      ∃ a, b.runOn s v = .ok a ∧ judge front b s v = .ok a := by
  unfold judge
  cases b.runOn s v with
  | error f => exact Or.inl ⟨f, rfl, rfl⟩
  | ok a => exact Or.inr ⟨a, rfl, rfl⟩

/-- **The three runs are the shipped text's decision at the made-up reading.** -/
theorem runs3_eq (front : String) (p : TailPublic) (key : TableKey) (b₁ : Blk FirstEnd)
    (s₁ : Start) (n₁ n₂ : Nat) (v₁ v₂ v₃ : Fmt.View) :
    runs3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ =
      (match judge front b₁ s₁ (withSeal v₁) with
        | .error why => some why
        | .ok real => tailRefusal p real (tailAt key n₁ n₂ (withSeal v₁) v₂ v₃)).isNone := by
  unfold runs3
  rcases judge_ok front b₁ s₁ (withSeal v₁) with ⟨f, e1, e2⟩ | ⟨e, e1, e2⟩
  · rw [e1, e2]
    rfl
  · rw [e1, e2]
    dsimp only
    unfold tailRefusal
    rcases judge_ok "shared-chain-" (sharedBlock p.lin key) (sharedStart p) v₂ with
      ⟨f, e3, e4⟩ | ⟨x, e3, e4⟩
    · show (match (sharedBlock p.lin key).runOn (sharedStart p) v₂ with
          | .error _ => false
          | .ok e₂ => _) = _
      rw [e3]
      show false = (match judge "shared-chain-" (sharedBlock p.lin key) (sharedStart p) v₂ with
          | .error why => some why
          | .ok end2 => _).isNone
      rw [e4]
      rfl
    · show (match (sharedBlock p.lin key).runOn (sharedStart p) v₂ with
          | .error _ => false
          | .ok e₂ => _) = _
      rw [e3]
      show _ = (match judge "shared-chain-" (sharedBlock p.lin key) (sharedStart p) v₂ with
          | .error why => some why
          | .ok end2 => _).isNone
      rw [e4]
      dsimp only
      rcases judge_ok "second-chain-" (secondBlock p.lin e.lin (x.goesOn (Three.tagChain 2 n₂)))
          (secondStart p e (Three.tagChain 1 n₁)) v₃ with ⟨f, e5, e6⟩ | ⟨u, e5, e6⟩
      · rw [e5]
        show false = (match judge "second-chain-"
            (secondBlock p.lin e.lin (x.goesOn (Three.tagChain 2 n₂)))
            (secondStart p e (Three.tagChain 1 n₁)) v₃ with
          | .error why => some why
          | .ok () => none).isNone
        rw [e6]
        rfl
      · rw [e5]
        show true = (match judge "second-chain-"
            (secondBlock p.lin e.lin (x.goesOn (Three.tagChain 2 n₂)))
            (secondStart p e (Three.tagChain 1 n₁)) v₃ with
          | .error why => some why
          | .ok () => none).isNone
        rw [e6]
        rfl

/-- **`decide3` is the tests on the key's and the three views' words, and the shipped text's
decision at the made-up reading.** -/
theorem decide3_eq (front : String) (p : TailPublic) (key : TableKey) (b₁ : Blk FirstEnd)
    (s₁ : Start) (n₁ n₂ : Nat) (v₁ v₂ v₃ : Fmt.View) :
    decide3 p key b₁ s₁ n₁ n₂ v₁ v₂ v₃ =
      (okSeeds key && okView v₁ && okView v₂ && okView v₃ &&
        (match judge front b₁ s₁ (withSeal v₁) with
          | .error why => some why
          | .ok real => tailRefusal p real (tailAt key n₁ n₂ (withSeal v₁) v₂ v₃)).isNone) := by
  unfold decide3
  rw [runs3_eq front]

/-- The test on the rounds' items reads no digest drawn. -/
theorem okRounds_alike : ∀ {l l' : List Fmt.RoundView}, LAlike RVAlike l l' →
    (l.all fun r => r.vals.all okGot) = l'.all fun r => r.vals.all okGot
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.all_cons, List.all_cons, h.vals, okRounds_alike t]

/-- **The test on the words has one value at views that are alike.** -/
theorem okView_alike {v v' : Fmt.View} (h : ViewAlike v v') : okView v = okView v' := by
  unfold okView
  rw [okRounds_alike h.rounds, h.opened]

/-- A sealing round holds no item: it passes the test. -/
theorem okView_withSeal (v : Fmt.View) : okView (withSeal v) = okView v := by
  have e : ([sealRV].all fun r => r.vals.all okGot) = true := rfl
  show ((v.rounds ++ [sealRV]).all (fun r => r.vals.all okGot) &&
    v.opened.all fun o => o.2.2.all okF) = _
  rw [List.all_append, e, Bool.and_true]
  rfl

/-- The key and the three views of a file as read pass the tests on the words. -/
def okRead (r : TailRead) : Bool :=
  okSeeds r.key && okView r.first.view && okView r.shared.view && okView r.second.view

/-- The made-up first chain has as many roots as it says. -/
theorem tagChain_roots (c : UInt8) (N : Nat) : (Three.tagChain c N).roots.length = N := by
  unfold ChainRead.roots Three.tagChain
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold rootsT
  rw [List.filterMap_map]
  simp [Function.comp_def]

/-- A view's last round holds no value and draws nothing but a digest. -/
def SealedLast (v : Fmt.View) : Prop :=
  ∃ l d, v.rounds = l ++ [(⟨[], ⟨[], [], [], d⟩⟩ : Fmt.RoundView)]

/-- The view without its last round. -/
def dropSeal (v : Fmt.View) : Fmt.View := { v with rounds := v.rounds.dropLast }

/-- A view whose last round is a sealing round is, but for the digest, the view with that round
taken off and put back. -/
theorem viewAlike_withSeal {v : Fmt.View} (h : SealedLast v) :
    ViewAlike v (withSeal (dropSeal v)) := by
  obtain ⟨l, d, e⟩ := h
  refine ⟨?_, rfl⟩
  show LAlike RVAlike v.rounds (v.rounds.dropLast ++ [sealRV])
  rw [e, List.dropLast_concat]
  exact (LAlike.refl (fun _ => ⟨rfl, DrawnAlike.refl _⟩) l).append
    (.cons ⟨rfl, ⟨rfl, rfl, rfl⟩⟩ .nil)

/-- **A key file.** The tests on the words and the shipped decision at what was read, and the three
decisions as one at views that are the file's but for digests. -/
theorem decideKey_iff (k : Params.KeyChains) (table : Params.TableName) (r : TailRead) (n₂ : Nat)
    {v₁ v₂ v₃ : Fmt.View} (h1 : ViewAlike r.first.view (withSeal v₁))
    (h2 : ViewAlike r.shared.view v₂) (h3 : ViewAlike r.second.view v₃) :
    decideKey k r.key r.first.roots.length n₂ v₁ v₂ v₃ =
      (okRead r && (Key.keyRefusal k table r).isNone) := by
  unfold decideKey okRead
  rw [decide3_eq "one-time-chain-",
    keyRefusal_blind k table r (tailAt r.key r.first.roots.length n₂ (withSeal v₁) v₂ v₃) h1 rfl h2
      h3 (tagChain_roots 1 _).symm,
    okView_alike h1, okView_withSeal, okView_alike h2, okView_alike h3]
  rfl

/-- **A proof file.** -/
theorem decideProof_iff (c : Params.ProofChains) (table : Params.TableName) {block : Blk FirstEnd}
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) block block) (r : ProofRead)
    (n₂ : Nat) {v v₁ v₂ v₃ : Fmt.View} (h1 : ViewAlike v (withSeal v₁))
    (h2 : ViewAlike r.shared.view v₂) (h3 : ViewAlike r.second.view v₃) :
    decideProof c r.key block r.first.roots.length n₂ v₁ v₂ v₃ =
      (okSeeds r.key && okView v && okView r.shared.view && okView r.second.view &&
        (refusalOn c table block v r).isNone) := by
  unfold decideProof
  rw [decide3_eq "first-chain-",
    refusalOn_blind c table hb h1 r (tailAt r.key r.first.roots.length n₂ (withSeal v₁) v₂ v₃) rfl
      h2 h3 (tagChain_roots 1 _).symm,
    okView_alike h1, okView_withSeal, okView_alike h2, okView_alike h3]
  rfl

theorem viewAlike_refl (v : Fmt.View) : ViewAlike v v :=
  ⟨LAlike.refl (fun _ => ⟨rfl, DrawnAlike.refl _⟩) _, rfl⟩

/-- **The shipped verifier's yes on a key file gives the yes of the three decisions as one**, at the
file's own three views, the first without its sealing round, if the key and the views pass the tests
on the words. -/
theorem decideKey_of_yes (k : Params.KeyChains) (table : Params.TableName) (r : TailRead)
    (n₂ : Nat) (hseal : SealedLast r.first.view) (hw : okRead r = true)
    (hyes : Key.keyRefusal k table r = none) :
    decideKey k r.key r.first.roots.length n₂ (dropSeal r.first.view) r.shared.view
      r.second.view = true := by
  rw [decideKey_iff k table r n₂ (viewAlike_withSeal hseal) (viewAlike_refl _) (viewAlike_refl _),
    hyes, hw]
  rfl

/-- **The same on a proof file.** -/
theorem decideProof_of_yes (c : Params.ProofChains) (table : Params.TableName)
    {block : Blk FirstEnd}
    (hb : Carries (Alike AnyGiven false) (FirstEndAlike AnyGiven) block block) (r : ProofRead)
    (n₂ : Nat) (hseal : SealedLast r.first.view) (hw : okRead r = true)
    (hyes : proofRefusal c table block r = none) :
    decideProof c r.key block r.first.roots.length n₂ (dropSeal r.first.view) r.shared.view
      r.second.view = true := by
  have h : refusalOn c table block r.first.view r = none := by
    rw [proofRefusal_eq] at hyes
    exact hyes
  rw [decideProof_iff c table hb r n₂ (viewAlike_withSeal hseal) (viewAlike_refl _)
    (viewAlike_refl _), h]
  show (okRead r && true) = true
  rw [hw]
  rfl

end OnBytes.Maker
