-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeChain.lean: from two provers' sides to this folder's second
player as a whole: `runC` (Honest/Walk.lean) returns the same of two provers whose parts pass on
values of two different types, where sub-protocol by sub-protocol their rounds are related by
`AlikeTo` (Honest/Alike.lean). Definitions, and lemmas with their proofs.

  1  `StrAlike`   two answers whose errors are strings
  2  `StepsAlike`   two lists of rounds: a player reads the same of them beside their moves, and
     they are related from every pair of states in `Pre`, up to `Post`
  3  `memberSteps`, `chainSteps_cons`   `chainSteps` (Honest/Frame.lean), sub-protocol by
     sub-protocol
  4  `MembersAlike`, `chainSteps_alike`   a chain: the hypothesis sub-protocol by sub-protocol,
     under a family of relations that is numbered by the sub-protocol
  5  `ProversAlike`, `runC_alike`   two provers; `runC`

No equation between types. A prover's side's parts are given coins of types of their own. The
hypothesis on a sub-protocol speaks of the two answers of `memberSteps`, in which the coins are put
in. So it does not ask that the two sides' coins have one type.

Limits.
  * The shared chain's prover's sides, and what its parts pass on, are the same in both provers.
  * That `readyTests` answers alike is a hypothesis (`ProversAlike.tests`): of a prover it reads the
    sides' places, `inRange` and `dummy`.
  * The families `Inv`, `I₁` and `I₃` relate two states of a run (`Mid`), so they run over the field
    `opened` too. `ProversAlike.start` and `meet` are asked at every value of that field, the same
    in both states: `ChainProgress.start` (Honest/Walk.lean) lays the columns that it is handed over whatever
    stands there: more than `runC` needs, which lays `some front` and lengthens it (`ChainProgress.settle`).
    `first` and `second` ask more too, through `AlikeTo` (Honest/Alike.lean, Limits): behind each
    hearing the rest is asked whatever columns are read next, not only those that `runC` reads. What
    a family needs of the field it has to say itself, as `MidBy` (Honest/AlikeParts.lean) does.
  * That `play` returns the same of two lists does not by itself give `StepsAlike`
    (Honest/Alike.lean, why the relation has two stages; and `FacedAll` asks what `play` does not
    return). And `play` leaves the field as it is: from states where it is `some l`, as `ChainProgress.start`
    lays it, what `play` returns says nothing of the states asked, unless no round reads the field
    and `Post` is kept by `Mid.took`. Two sides that agree only at the columns that a walk reads are
    not reached.
  * `run`, `midAt`, `midAtW`, `midSharedAtW`, `silentAt` and the speakers of Honest/StratC.lean are
    not treated here.
  * No lemma about `Owed` is carried from one prover to the other.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Alike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription OpenedColumn)

variable {S Cl V W X X' Xi W₀ Rc Ky Tr X₀ : Type}

/-! ## 1 Answers whose errors are strings -/

/-- Both are answers, and related; or both are the same error. -/
def StrAlike {α β : Type} (P : α → β → Prop) : Except String α → Except String β → Prop
  | .ok a, .ok b => P a b
  | .error e, .error e' => e = e'
  | _, _ => False

theorem StrAlike.bind {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {f : α → Except String γ} {g : β → Except String δ}
    (hfg : ∀ a b, P a b → StrAlike Q (f a) (g b)) :
    ∀ {x : Except String α} {y : Except String β}, StrAlike P x y →
      StrAlike Q (x.bind f) (y.bind g)
  | .ok _, .ok _, q => hfg _ _ q
  | .error _, .error _, q => q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

theorem StrAlike.map {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop} {f : α → γ} {g : β → δ}
    (hfg : ∀ a b, P a b → Q (f a) (g b)) :
    ∀ {x : Except String α} {y : Except String β}, StrAlike P x y →
      StrAlike Q (x.map f) (y.map g)
  | .ok _, .ok _, q => hfg _ _ q
  | .error _, .error _, q => q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

/-- As Honest/Frame.lean turns a string into an error. -/
theorem StrAlike.unfit {α β : Type} {P : α → β → Prop} :
    ∀ {x : Except String α} {y : Except String β}, StrAlike P x y →
      AnsAlike P (unfit x) (unfit y)
  | .ok _, .ok _, q => q
  | .error _, .error _, q => congrArg (fun s => (⟨.unfit, s⟩ : Refusal)) q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

/-! ## 2 Two lists of rounds -/

/-- **Two lists of rounds**: a player reads the same of them beside their moves; and from every pair
of states in `Pre` they are related, up to `Post`. -/
def StepsAlike (Pre Post : Mid W X → Mid W X' → Prop) (l : List (Step W X))
    (l' : List (Step W X')) : Prop :=
  FacedAll l l' ∧ ∀ m m', Pre m m' → AlikeTo Post l l' m m'

theorem StepsAlike.nil (P : Mid W X → Mid W X' → Prop) : StepsAlike P P [] [] :=
  ⟨True.intro, fun _ _ h => h⟩

theorem StepsAlike.append {P Q R : Mid W X → Mid W X' → Prop} {a b : List (Step W X)}
    {a' b' : List (Step W X')} (h₁ : StepsAlike P Q a a') (h₂ : StepsAlike Q R b b') :
    StepsAlike P R (a ++ b) (a' ++ b') :=
  ⟨FacedAll.append a a' b b' h₁.1 h₂.1, fun m m' h =>
    AlikeTo.append R b b' a a' m m' (AlikeTo.mono h₂.2 a a' m m' (h₁.2 m m' h))⟩

/-! ## 3 `chainSteps`, sub-protocol by sub-protocol -/

/-- **One sub-protocol's rounds**, as `chainSteps` prepares them: its tests, and the coins that the
book gives the prover's side at the sub-protocol's place. -/
def memberSteps (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) : Except String (List (Step W X)) :=
  if b.oracles.length != b.rounds.length then
    .error (b.name ++ ": its lists of rounds and of oracle messages differ in length")
  else
    match hs.find? fun h => h.place == b.place with
    | none =>
      .ok ((b.rounds.zip b.oracles).map (fun r => (⟨b.name, ⟨b.place, 0⟩, r.1, r.2,
        fun _ _ => none, fun _ _ => none, 0, false, none⟩ : Step W X)))
    | some h =>
      if h.rounds != b.rounds.length then
        .error (b.name ++ ": the prover's half has another number of rounds")
      else if B.cuts.lookup b.place != some (h.parts.map (·.moves.length)) then
        .error (b.name ++ ": the book has no cut for this place, or the row is cut otherwise")
      else if rows.any (fun r => r.1.place == b.place && decide (h.parts.length ≤ r.1.part)) then
        .error (b.name ++ ": the book has a row for a part that the half does not have")
      else if B.ahead.any (fun e =>
          e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part)) then
        .error (b.name ++ ": an entry of the book names a part that the half does not have")
      else
        ((lendRow B rows look b.place h.parts 0).mapError (b.name ++ ": " ++ ·)).map fun c =>
          h.steps b v c

theorem chainSteps_cons (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (bs : List (Block S Cl)) (hs : List (Placed V W X)) :
    chainSteps B rows look v (b :: bs) hs =
      (memberSteps B rows look v b hs).bind fun l₁ =>
        (chainSteps B rows look v bs hs).map fun l => l₁ ++ l := by
  unfold memberSteps
  rw [chainSteps]
  by_cases h0 : (b.oracles.length != b.rounds.length) = true
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0]
    cases hs.find? (fun h => h.place == b.place) with
    | none => rfl
    | some h =>
      dsimp only
      by_cases h1 : (h.rounds != b.rounds.length) = true
      · rw [if_pos h1, if_pos h1]
        rfl
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : (B.cuts.lookup b.place != some (h.parts.map (·.moves.length))) = true
        · rw [if_pos h2, if_pos h2]
          rfl
        · rw [if_neg h2, if_neg h2]
          by_cases h3 : (rows.any (fun r =>
              r.1.place == b.place && decide (h.parts.length ≤ r.1.part))) = true
          · rw [if_pos h3, if_pos h3]
            rfl
          · rw [if_neg h3, if_neg h3]
            by_cases h4 : (B.ahead.any (fun e =>
                e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part))) = true
            · rw [if_pos h4, if_pos h4]
              rfl
            · rw [if_neg h4, if_neg h4]
              generalize (lendRow B rows look b.place h.parts 0).mapError (b.name ++ ": " ++ ·) = q
              cases q <;> rfl

/-! ## 4 A chain -/

/-- **The hypothesis, sub-protocol by sub-protocol.** `Inv j`: the relation between the two runs'
states before sub-protocol number `j` of the chain. At each sub-protocol the two provers' rounds get
the same error from the tests of Honest/Frame.lean and the book, or are related from `Inv j` up to
`Inv (j + 1)`. -/
def MembersAlike (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (hs : List (Placed V W X)) (hs' : List (Placed V W X'))
    (Inv : Nat → Mid W X → Mid W X' → Prop) : Nat → List (Block S Cl) → Prop
  | _, [] => True
  | j, b :: bs =>
    StrAlike (StepsAlike (Inv j) (Inv (j + 1))) (memberSteps B rows look v b hs)
        (memberSteps B rows look v b hs') ∧
      MembersAlike B rows look v hs hs' Inv (j + 1) bs

/-- **A chain's rounds.** -/
theorem chainSteps_alike (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (hs : List (Placed V W X)) (hs' : List (Placed V W X'))
    (Inv : Nat → Mid W X → Mid W X' → Prop) :
    ∀ (bs : List (Block S Cl)) (j : Nat), MembersAlike B rows look v hs hs' Inv j bs →
      StrAlike (StepsAlike (Inv j) (Inv (j + bs.length))) (chainSteps B rows look v bs hs)
        (chainSteps B rows look v bs hs')
  | [], j, _ => StepsAlike.nil (Inv j)
  | b :: bs, j, h => by
    rw [chainSteps_cons, chainSteps_cons]
    refine StrAlike.bind (fun l₁ l₁' q₁ => ?_) h.1
    refine StrAlike.map (fun l l' q => ?_)
      (chainSteps_alike B rows look v hs hs' Inv bs (j + 1) h.2)
    have e : j + (b :: bs).length = j + 1 + bs.length := by
      rw [List.length_cons]
      omega
    rw [e]
    exact q₁.append q

/-! ## 5 Two provers -/

/-- **Two provers that differ in the first and the second chain's sides, and in the type of what
these pass on.** The letters name one index, one value of the stored tables' pads and encoding
randomness, one instance and one run's coins. Of these only the index (`tests`) and the coins
(`first`, `second`) stand in a field. `stored`, `trace` and `key` are asked as whole functions, and
`first`, `second`, `start` and `meet` at every input w. `I₁`, `I₃`: the families of relations along
the first and the second chain. A list of hypotheses: no pair of provers is proved to meet it in
this file. Who has to prove which field: whoever chooses the two provers' fields: `stored`, `trace`,
`key`, `ownShared₀`, `shared`, `tests`, `start`, `meet`; for `first` and `second`, sub-protocol by
sub-protocol: the author of the kind whose prover's side is there; at a side that does not touch
what the other prover keeps: `lift_movesTo` (Honest/AlikeParts.lean). -/
structure ProversAlike (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (H' : Prover W₀ Rc Xi Ky Tr X₀ X') (w₀ : W₀) (rc : Rc) (x : Xi) (c : Coins B)
    (I₁ I₃ : Nat → Mid (Local W₀ Rc Xi Tr) X → Mid (Local W₀ Rc Xi Tr) X' → Prop) : Prop where
  stored : H.stored = H'.stored
  trace : H.trace = H'.trace
  key : H.key = H'.key
  ownShared₀ : H.ownShared₀ = H'.ownShared₀
  shared : H.shared = H'.shared
  /-- the tests that read neither a challenge nor the instance answer alike -/
  tests : readyTests F B H w₀ = readyTests F B H' w₀
  first : ∀ w : Local W₀ Rc Xi Tr,
    MembersAlike B (B.rowsOf 0) (c.look 0) (Face.own.sees w) H.first H'.first I₁ 0 F.first.blocksInOrder
  second : ∀ w : Local W₀ Rc Xi Tr,
    MembersAlike B (B.rowsOf 2) (c.look 2) (Face.own.sees w) H.second H'.second I₃ 0 F.second.blocksInOrder
  /-- the two starts of the first chain are related, at every value `o` of the columns opened, the
  same in both -/
  start : ∀ (w : Local W₀ Rc Xi Tr) (o : Option (List OpenedColumn)),
    I₁ 0 ⟨⟨w, [], H.own₀⟩, [], [], o⟩ ⟨⟨w, [], H'.own₀⟩, [], [], o⟩
  /-- and so are the two starts of the second, from related ends of the first -/
  meet : ∀ (w : Local W₀ Rc Xi Tr) (e₁ : Mid (Local W₀ Rc Xi Tr) X)
    (e₁' : Mid (Local W₀ Rc Xi Tr) X') (e₂ : Mid (Common W₀ Rc Ky) X₀) (o : Option (List OpenedColumn)),
    I₁ (0 + F.first.blocksInOrder.length) e₁ e₁' →
    I₃ 0 ⟨⟨w, e₁.st.heard ++ e₂.st.heard, H.meet e₁.st.own e₂.st⟩, e₁.loc, e₁.seen ++ e₂.seen, o⟩
      ⟨⟨w, e₁'.st.heard ++ e₂.st.heard, H'.meet e₁'.st.own e₂.st⟩, e₁'.loc, e₁'.seen ++ e₂.seen,
        o⟩

/-- What `ready` prepares of the two provers. -/
structure Ready.Like (I₁ I₁' I₃ I₃' : Mid (Local W₀ Rc Xi Tr) X → Mid (Local W₀ Rc Xi Tr) X' → Prop)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) (R' : Ready W₀ Rc Xi Ky Tr X₀ X') : Prop where
  own : R.own = R'.own
  common : R.common = R'.common
  shared : R.shared = R'.shared
  first : StepsAlike I₁ I₁' R.first R'.first
  second : StepsAlike I₃ I₃' R.second R'.second

theorem ready_alike {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {H' : Prover W₀ Rc Xi Ky Tr X₀ X'} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B}
    {I₁ I₃ : Nat → Mid (Local W₀ Rc Xi Tr) X → Mid (Local W₀ Rc Xi Tr) X' → Prop}
    (h : ProversAlike F B H H' w₀ rc x c I₁ I₃) :
    AnsAlike (Ready.Like (I₁ 0) (I₁ (0 + F.first.blocksInOrder.length)) (I₃ 0)
      (I₃ (0 + F.second.blocksInOrder.length))) (ready F B H w₀ rc x c) (ready F B H' w₀ rc x c) := by
  unfold ready
  rw [← h.tests, ← h.trace, ← h.key]
  cases readyTests F B H w₀ with
  | error e => exact rfl
  | ok u =>
    show AnsAlike _ (match H.trace w₀ x with
      | none => _
      | some tr => _) (match H.trace w₀ x with
      | none => _
      | some tr => _)
    cases H.trace w₀ x with
    | none => exact rfl
    | some tr =>
      refine AnsAlike.bind (fun m₁ m₁' q₁ => ?_)
        (chainSteps_alike B (B.rowsOf 0) (c.look 0) _ H.first H'.first I₁ F.first.blocksInOrder 0
          (h.first _)).unfit
      have es : sharedSteps F B H' ⟨w₀, rc, H.key x⟩ c.shared =
          sharedSteps F B H ⟨w₀, rc, H.key x⟩ c.shared := by
        unfold sharedSteps
        rw [h.shared]
      rw [es]
      cases sharedSteps F B H ⟨w₀, rc, H.key x⟩ c.shared with
      | error e => exact rfl
      | ok m₂ =>
        exact AnsAlike.map (fun m₃ m₃' q₃ => ⟨rfl, rfl, rfl, q₁, q₃⟩)
          (chainSteps_alike B (B.rowsOf 2) (c.look 2) _ H.second H'.second I₃ F.second.blocksInOrder 0
            (h.second _)).unfit

/-- **`runC` returns the same of the two provers**: the same run, the same three ends of the
verifier's, the same places of rejection; or the same error of the player's own. -/
theorem runC_alike {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {H' : Prover W₀ Rc Xi Ky Tr X₀ X'} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B}
    {I₁ I₃ : Nat → Mid (Local W₀ Rc Xi Tr) X → Mid (Local W₀ Rc Xi Tr) X' → Prop}
    (h : ProversAlike F B H H' w₀ rc x c I₁ I₃) (ρ : Draws) :
    runC F B H w₀ rc x c ρ = runC F B H' w₀ rc x c ρ := by
  apply AnsAlike.eq
  have eS : H'.storedWords w₀ rc = H.storedWords w₀ rc := by
    unfold Prover.storedWords
    rw [h.stored]
  unfold runC
  rw [eS]
  refine AnsAlike.bind (fun R R' hR => ?_) (ready_alike h)
  have s₁ : OptAlike (fun a b => TookAll (AlikeTo (I₁ (0 + F.first.blocksInOrder.length)) R.first R'.first)
      { a with opened := some [] } { b with opened := some [] })
      (some (R.start₁ H)) (some (R'.start₁ H')) := by
    intro cols
    show AlikeTo _ R.first R'.first ⟨⟨R.own, [], H.own₀⟩, [], [], some ([] ++ cols)⟩
      ⟨⟨R'.own, [], H'.own₀⟩, [], [], some ([] ++ cols)⟩
    rw [← hR.own]
    exact hR.first.2 _ _ (h.start R.own _)
  refine AnsAlike.bind (fun a₁ a₁' ha₁ => ?_)
    (start_like ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ _ TookAll.took F.first.blocksInOrder
      (some (F.start₁ (F.pub x))) [] s₁)
  refine AnsAlike.bind (fun z₁ z₁' hz₁ => ?_)
    (walk_alike ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ _ R.first R'.first ρ.first a₁ a₁' hR.first.1
      (ha₁.mono fun _ _ q => q.here))
  rw [← hz₁.laid]
  by_cases hq : sealQuiet z₁.laid
  · simp only [hq, Bool.not_true, Bool.false_eq_true, if_false]
    have e₂ : R'.start₂ H' = R.start₂ H := by
      show (⟨⟨R'.common, [], H'.ownShared₀⟩, [], [], none⟩ : Mid (Common W₀ Rc Ky) X₀) =
        ⟨⟨R.common, [], H.ownShared₀⟩, [], [], none⟩
      rw [← hR.common, ← h.ownShared₀]
    rw [e₂, ← hR.shared]
    refine AnsAlike.bind (P := fun a b => a = b) (fun a₂ a₂' ea => ?_) ?_
    · subst ea
      refine AnsAlike.bind (P := fun a b => a = b) (fun z₂ z₂' ez => ?_) ?_
      · subst ez
        have s₃ : OptAlike (fun a b =>
              TookAll (AlikeTo (I₃ (0 + F.second.blocksInOrder.length)) R.second R'.second)
                { a with opened := some (z₁.cols ++ z₂.cols) }
                { b with opened := some (z₁.cols ++ z₂.cols) })
            (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
            (z₁'.mid.bind fun m₁ => z₂.mid.map fun m₂ => R'.start₃ H' m₁ m₂) := by
          have hm := hz₁.mid
          revert hm
          cases z₁.mid with
          | none =>
            cases z₁'.mid with
            | none => exact fun _ => True.intro
            | some _ => exact fun hm => False.elim hm
          | some m₁ =>
            cases z₁'.mid with
            | none => exact fun hm => False.elim hm
            | some m₁' =>
              intro hm
              cases z₂.mid with
              | none => exact True.intro
              | some m₂ =>
                intro cols
                show AlikeTo _ R.second R'.second
                  ⟨⟨R.own, m₁.st.heard ++ m₂.st.heard, H.meet m₁.st.own m₂.st⟩, m₁.loc,
                    m₁.seen ++ m₂.seen, some ((z₁.cols ++ z₂.cols) ++ cols)⟩
                  ⟨⟨R'.own, m₁'.st.heard ++ m₂.st.heard, H'.meet m₁'.st.own m₂.st⟩, m₁'.loc,
                    m₁'.seen ++ m₂.seen, some ((z₁.cols ++ z₂.cols) ++ cols)⟩
                rw [← hR.own]
                exact hR.second.2 _ _ (h.meet R.own m₁ m₁' m₂ _ hm)
        rw [← hz₁.ver, ← hz₁.cols]
        refine AnsAlike.bind (fun a₃ a₃' ha₃ => ?_)
          (start_like ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ _
            TookAll.took F.second.blocksInOrder (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols) s₃)
        refine AnsAlike.map (fun z₃ z₃' hz₃ => ?_)
          (walk_alike ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ _ R.second
            R'.second ρ.second a₃ a₃' hR.second.1 (ha₃.mono fun _ _ q => q.here))
        rw [← hz₁.reads, ← hz₁.refused, ← hz₃.laid, ← hz₃.reads, ← hz₃.cols, ← hz₃.ver,
          ← hz₃.refused]
      · cases walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ <;> exact rfl
    · cases ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) [] <;> exact rfl
  · simp only [hq, Bool.not_false, if_true]
    exact rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.chainSteps_cons
#print axioms ProofFile.Honest.chainSteps_alike
#print axioms ProofFile.Honest.ready_alike
#print axioms ProofFile.Honest.runC_alike
#print axioms ProofFile.Honest.StrAlike.bind
#print axioms ProofFile.Honest.StrAlike.map
#print axioms ProofFile.Honest.StrAlike.unfit
#print axioms ProofFile.Honest.StepsAlike.nil
#print axioms ProofFile.Honest.StepsAlike.append
#print axioms ProofFile.Honest.StrAlike
#print axioms ProofFile.Honest.StepsAlike
#print axioms ProofFile.Honest.memberSteps
#print axioms ProofFile.Honest.MembersAlike
#print axioms ProofFile.Honest.ProversAlike
#print axioms ProofFile.Honest.Ready.Like
