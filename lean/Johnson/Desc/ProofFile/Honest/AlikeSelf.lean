-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeSelf.lean: three small cases of the relations `AlikeTo`
(Honest/Alike.lean) and `StepsAlike` (Honest/AlikeChain.lean). One definition, and lemmas with their
proofs.

  1  `FacedAll.refl`, `AlikeTo.refl`   a list of rounds beside itself
  2  `KeepsTo`, `AlikeTo.self`, `StepsAlike.self`   the same, with a property of the state carried
     along: for a prover's side that is one and the same term in both provers
  3  `idle_faced`, `idle_alike`, `member_idle`   a sub-protocol at whose place no prover's side is
     defined, in two provers whose parts pass on values of two types: nothing is said and nothing is
     passed on there; each round's challenge is heard

Limits.
  * Sections 1 and 2: one type of passed-on value.
  * `KeepsTo`, and the premise hP of `idle_alike` and `member_idle`, speak of the next state with
    any columns read (`Mid.took`), as `AlikeTo` does: more than either player needs. At
    `opened = none` `Mid.took` returns the state as it was, and nothing more is asked than without
    it. At `some l` the states asked are reached by no `play` from `m`: what is known of `play`
    from `m` alone does not pay, unless every round is blind (`Step.Blind`, Honest/Blind.lean) and
    `Post` is kept by `Mid.took`.
  * `I`, `I'`, `P`, `Pre`, `Post` are on states of a run (`Mid`), so they run over the field
    `opened` too; behind the last round the later one is asked with any columns read, so it has to
    be kept by `Mid.took`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Oracle)

variable {S Cl V W X X' : Type}

/-! ## 1 A list beside itself -/

theorem AnsAlike.self {α : Type} {P : α → α → Prop} :
    ∀ (x : Except Refusal α), (∀ a, x = .ok a → P a a) → AnsAlike P x x
  | .ok a, h => h a rfl
  | .error _, _ => rfl

theorem FacedAll.refl : ∀ l : List (Step W X), FacedAll l l
  | [] => True.intro
  | _ :: l => ⟨⟨rfl, rfl, rfl, rfl⟩, FacedAll.refl l⟩

theorem AlikeTo.refl : ∀ (l : List (Step W X)) (m : Mid W X), AlikeTo (fun a b => a = b) l l m m
  | [], _ => rfl
  | _ :: ss, _ => fun _ =>
    AnsAlike.self _ fun _ _ => ⟨rfl, fun _ =>
      AnsAlike.self _ fun m₁ _ cols => AlikeTo.refl ss (m₁.took cols)⟩

/-! ## 2 With a property of the state carried along -/

/-- **The rounds lead from the state `m` to states with `Post`**: wherever a round's message and
what follows its challenge return no error, the same holds of the rest from the next state,
whatever columns are read before the next round (`Mid.took`). -/
def KeepsTo (Post : Mid W X → Prop) : List (Step W X) → Mid W X → Prop
  | [], m => Post m
  | s :: ss, m =>
    ∀ back x, s.tell back m = .ok x → ∀ d m₁, s.hear x d m = .ok m₁ →
      ∀ cols, KeepsTo Post ss (m₁.took cols)

theorem AlikeTo.self {Post : Mid W X → Prop} :
    ∀ (l : List (Step W X)) (m : Mid W X), KeepsTo Post l m →
      AlikeTo (fun a b => a = b ∧ Post a) l l m m
  | [], _, h => ⟨rfl, h⟩
  | _ :: ss, _, h => fun back =>
    AnsAlike.self _ fun x hx => ⟨rfl, fun d =>
      AnsAlike.self _ fun m₁ hm cols =>
        AlikeTo.self ss (m₁.took cols) (h back x hx d m₁ hm cols)⟩

/-- **A list of rounds beside itself**, from equal states with `I` to equal states with `I'`. -/
theorem StepsAlike.self (I I' : Mid W X → Prop) (l : List (Step W X))
    (h : ∀ m, I m → KeepsTo I' l m) :
    StepsAlike (fun a b => a = b ∧ I a) (fun a b => a = b ∧ I' a) l l :=
  ⟨FacedAll.refl l, fun m m' q => by
    obtain ⟨e, hi⟩ := q
    subst e
    exact AlikeTo.self l m (h m hi)⟩

/-! ## 3 A sub-protocol without a prover's side -/

theorem idle_faced (nm : String) (a : Addr) :
    ∀ rs : List (Fmt.DeclaredRound × List Oracle),
      FacedAll
        (rs.map fun r => (⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W X))
        (rs.map fun r => (⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W X'))
  | [] => True.intro
  | _ :: rs => ⟨⟨rfl, rfl, rfl, rfl⟩, idle_faced nm a rs⟩

/-- **Rounds without a move, in two provers.** `P k`: the relation after `k` of them. `hP`: hearing
a challenge, with anything shown and whatever columns are read behind it, leads from `P k` to
`P (k + 1)`. -/
theorem idle_alike (nm : String) (a : Addr) (P : Nat → Mid W X → Mid W X' → Prop)
    (hP : ∀ k m m' d e cols, P k m m' →
      P (k + 1) (Mid.took ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [e], m.opened⟩ cols)
        (Mid.took ⟨m'.st.hears d, m'.loc ++ [d], m'.seen ++ [e], m'.opened⟩ cols)) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (k : Nat) (m : Mid W X) (m' : Mid W X'),
      P k m m' →
      AlikeTo (P (k + rs.length))
        (rs.map fun r => (⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W X))
        (rs.map fun r => (⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W X')) m m'
  | [], _, _, _, h => h
  | r :: rs, k, m, m', h => by
    have e : k + (r :: rs).length = k + 1 + rs.length := by
      rw [List.length_cons]
      omega
    rw [e]
    show AlikeTo (P (k + 1 + rs.length))
      ((⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ : Step W X) ::
        rs.map fun r => (⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W X))
      ((⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ : Step W X') ::
        rs.map fun r => (⟨nm, a, r.1, r.2, fun _ _ => none, fun _ _ => none, 0, false, none⟩ :
          Step W X')) m m'
    intro back
    exact ⟨rfl, fun d cols => idle_alike nm a P hP rs (k + 1) _ _ (hP k m m' d _ cols h)⟩

/-- **A sub-protocol at whose place neither prover has a side.** -/
theorem member_idle (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) (hs' : List (Placed V W X'))
    (hf : (hs.find? fun h => h.place == b.place) = none)
    (hf' : (hs'.find? fun h => h.place == b.place) = none)
    (Pre Post : Mid W X → Mid W X' → Prop) (P : Nat → Mid W X → Mid W X' → Prop)
    (h0 : ∀ m m', Pre m m' → P 0 m m')
    (hP : ∀ k m m' d e cols, P k m m' →
      P (k + 1) (Mid.took ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [e], m.opened⟩ cols)
        (Mid.took ⟨m'.st.hears d, m'.loc ++ [d], m'.seen ++ [e], m'.opened⟩ cols))
    (h1 : ∀ m m', P (0 + (b.rounds.zip b.oracles).length) m m' → Post m m') :
    StrAlike (StepsAlike Pre Post) (memberSteps B rows look v b hs)
      (memberSteps B rows look v b hs') := by
  unfold memberSteps
  by_cases hc : (b.oracles.length != b.rounds.length) = true
  · rw [if_pos hc, if_pos hc]
    exact rfl
  · rw [if_neg hc, if_neg hc, hf, hf']
    exact ⟨idle_faced b.name ⟨b.place, 0⟩ (b.rounds.zip b.oracles), fun m m' q =>
      AlikeTo.mono h1 _ _ m m'
        (idle_alike b.name ⟨b.place, 0⟩ P hP (b.rounds.zip b.oracles) 0 m m' (h0 m m' q))⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.AlikeTo.refl
#print axioms ProofFile.Honest.AlikeTo.self
#print axioms ProofFile.Honest.StepsAlike.self
#print axioms ProofFile.Honest.idle_alike
#print axioms ProofFile.Honest.member_idle
#print axioms ProofFile.Honest.AnsAlike.self
#print axioms ProofFile.Honest.FacedAll.refl
#print axioms ProofFile.Honest.idle_faced
#print axioms ProofFile.Honest.KeepsTo
