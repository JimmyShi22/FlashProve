-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeLots.lean: from two lists of prover's sides, related one by one,
to the hypothesis `MembersAlike` on a whole chain (Honest/AlikeChain.lean), and to the tests of
Honest/Frame.lean that read the sides' places. Definitions, and lemmas with their proofs.

  1  `hear_heard`, `AlikeTo.counted`, `Cnt`, `StepsAlike.counted`   every round lengthens the list
     of challenges heard by one: so a relation can be given the number of challenges heard
  2  `forall₂_find`   of two lists related entry by entry (`List.Forall₂`): what `find?` returns
  3  `member_single`, `member_none`, `HalfAlike`, `members_of_index`, `members_of_halves`   the
     hypothesis on two prover's sides; a chain's sub-protocols from it
  4  `strays_places`, `twice_places`, `HalfAlike.places`, `readyTests_alike`   the tests that read
     neither a challenge nor the instance

Limits.
  * `Inv`, `P`, `Q` relate two states of a run (`Mid`), so they run over the field `opened` too.
    Through `AlikeTo`, `HalfAlike` and hI ask `Inv (j + 1)` behind the sub-protocol's last hearing
    with any columns read (`Mid.took`): a family has to be kept by that, as `AtFront`
    (Honest/AlikeHalf.lean) is.
    `Cnt` adds nothing on that field.
  * No pair of prover's sides is proved to meet `HalfAlike` here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeParts
import Johnson.Desc.ProofFile.Honest.AlikeChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)

variable {S Cl V W X X' Xi W₀ Rc Ky Tr X₀ : Type}

/-! ## 1 The number of challenges heard -/

/-- What follows a round's challenge has heard that challenge, and no other. -/
private theorem hear_heard {s : Step W X} {x : Told} {d : Fmt.Drawn} {m m₁ : Mid W X}
    (h : s.hear x d m = .ok m₁) : m₁.st.heard = m.st.heard ++ [d] := by
  cases hm : s.move with
  | none =>
    have e : s.hear x d m =
        .ok ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨x.vals, d⟩], m.opened⟩ := by
      simp only [Step.hear, hm]
    have e2 : (Except.ok ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨x.vals, d⟩], m.opened⟩ :
        Except Refusal (Mid W X)) = .ok m₁ := e.symm.trans h
    injection e2 with e3
    rw [← e3]
    rfl
  | some mv =>
    rw [hear_by s mv hm] at h
    generalize (if s.last then s.stop (m.loc ++ [d]) (s.nth + 1) else none) = g at h
    cases g with
    | some e =>
      have h2 : (Except.error e : Except Refusal (Mid W X)) = .ok m₁ := h
      exact nomatch h2
    | none =>
      have e2 : (Except.ok ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
          m.seen ++ [⟨x.vals, d⟩], m.opened⟩ : Except Refusal (Mid W X)) = .ok m₁ := h
      injection e2 with e3
      rw [← e3]
      rfl

theorem AnsAlike.mono_ok {α β : Type} {P Q : α → β → Prop} :
    ∀ {x : Except Refusal α} {y : Except Refusal β}, (∀ a b, x = .ok a → P a b → Q a b) →
      AnsAlike P x y → AnsAlike Q x y
  | .ok a, .ok b, h, q => h a b rfl q
  | .error _, .error _, _, q => q
  | .ok _, .error _, _, q => q
  | .error _, .ok _, _, q => q

/-- **After the rounds as many more challenges are heard as there are rounds.** -/
theorem AlikeTo.counted (Q : Mid W X → Mid W X' → Prop) :
    ∀ (l : List (Step W X)) (l' : List (Step W X')) (m : Mid W X) (m' : Mid W X') (k : Nat),
      m.st.heard.length = k → AlikeTo Q l l' m m' →
      AlikeTo (fun a b => Q a b ∧ a.st.heard.length = k + l.length) l l' m m'
  | [], [], _, _, _, hk, q => ⟨q, hk⟩
  | s :: ss, _ :: ss', _, _, k, hk, q => fun back =>
    AnsAlike.mono (fun _ _ r => ⟨r.1, fun d =>
      AnsAlike.mono_ok (fun a b ha t cols => by
        have e : a.st.heard.length = k + 1 := by
          rw [hear_heard ha, List.length_append, hk]
          rfl
        have e2 : k + (s :: ss).length = k + 1 + ss.length := by
          rw [List.length_cons]
          omega
        rw [e2]
        exact AlikeTo.counted Q ss ss' (a.took cols) (b.took cols) (k + 1) e (t cols)) (r.2 d)⟩)
      (q back)
  | [], _ :: _, _, _, _, _, q => False.elim q
  | _ :: _, [], _, _, _, _, q => False.elim q

/-- A relation between two states of a run, with the number of challenges heard. -/
def Cnt (P : Mid W X → Mid W X' → Prop) (k : Nat) (m : Mid W X) (m' : Mid W X') : Prop :=
  P m m' ∧ m.st.heard.length = k

theorem StepsAlike.counted {P Q : Mid W X → Mid W X' → Prop} {l : List (Step W X)}
    {l' : List (Step W X')} (h : StepsAlike P Q l l') (k : Nat) :
    StepsAlike (Cnt P k) (Cnt Q (k + l.length)) l l' :=
  ⟨h.1, fun m m' q => AlikeTo.counted Q l l' m m' k q.2 (h.2 m m' q.1)⟩

/-! ## 2 Two lists related entry by entry -/

/-- The first entries that pass two tests which agree on related entries are related. -/
theorem forall₂_find {α β : Type} {R : α → β → Prop} (p : α → Bool) (p' : β → Bool)
    (hp : ∀ a b, R a b → p a = p' b) {l : List α} {l' : List β} (h : List.Forall₂ R l l') :
    OptAlike R (l.find? p) (l'.find? p') := by
  induction h with
  | nil => exact True.intro
  | @cons a b l l' hab _ ih =>
    have e : p' b = p a := (hp a b hab).symm
    cases hpa : p a with
    | true =>
      rw [hpa] at e
      simp only [List.find?_cons, hpa, e]
      exact hab
    | false =>
      rw [hpa] at e
      simp only [List.find?_cons, hpa, e]
      exact ih

/-! ## 3 Two prover's sides; a chain's sub-protocols -/

/-- A sub-protocol's rounds depend on the list of prover's sides through the side at its place
alone. -/
theorem member_single (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) (h : Placed V W X)
    (hf : (hs.find? fun h => h.place == b.place) = some h) :
    memberSteps B rows look v b hs = memberSteps B rows look v b [h] := by
  have hp : (h.place == b.place) = true :=
    List.find?_some (p := fun g : Placed V W X => g.place == b.place) hf
  unfold memberSteps
  rw [hf]
  simp only [List.find?_cons, hp]

theorem member_none (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X))
    (hf : (hs.find? fun h => h.place == b.place) = none) :
    memberSteps B rows look v b hs = memberSteps B rows look v b [] := by
  unfold memberSteps
  rw [hf]
  rfl

/-- **The hypothesis on two prover's sides.** They are at one place; and at every sub-protocol of
the chain `bs` that is there, its number being `j`: the tests of Honest/Frame.lean and the book
return the same error for both, or the two sides' rounds are related from `Inv j` up to
`Inv (j + 1)`. -/
def HalfAlike (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (Inv : Nat → Mid W X → Mid W X' → Prop)
    (h : Placed V W X) (h' : Placed V W X') : Prop :=
  h.place = h'.place ∧
    ∀ j b, bs[j]? = some b → (h.place == b.place) = true →
      StrAlike (StepsAlike (Inv j) (Inv (j + 1))) (memberSteps B rows look v b [h])
        (memberSteps B rows look v b [h'])

theorem members_of_index (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (hs : List (Placed V W X)) (hs' : List (Placed V W X'))
    (Inv : Nat → Mid W X → Mid W X' → Prop) :
    ∀ (suf : List (Block S Cl)) (o : Nat),
      (∀ j b, suf[j]? = some b →
        StrAlike (StepsAlike (Inv (o + j)) (Inv (o + j + 1))) (memberSteps B rows look v b hs)
          (memberSteps B rows look v b hs')) →
      MembersAlike B rows look v hs hs' Inv o suf
  | [], _, _ => True.intro
  | b :: suf, o, H =>
    ⟨H 0 b rfl, members_of_index B rows look v hs hs' Inv suf (o + 1) fun j b' hj => by
      have q := H (j + 1) b' (by rw [List.getElem?_cons_succ]; exact hj)
      have e : o + (j + 1) = o + 1 + j := by omega
      rw [e] at q
      exact q⟩

/-- **A chain's sub-protocols, from its prover's sides one by one.** `hI`: at every sub-protocol of
the chain, also where a side is defined, the rounds as they are with no prover's side supplied are
related from `Inv j` up to `Inv (j + 1)`; `idle_front` and `idle_plain` (Honest/AlikeHalf.lean)
prove it for two families. -/
theorem members_of_halves (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (bs : List (Block S Cl)) (Inv : Nat → Mid W X → Mid W X' → Prop)
    (hs : List (Placed V W X)) (hs' : List (Placed V W X'))
    (hP : List.Forall₂ (HalfAlike B rows look v bs Inv) hs hs')
    (hI : ∀ j b, bs[j]? = some b →
      StrAlike (StepsAlike (Inv j) (Inv (j + 1)))
        (memberSteps B rows look v b ([] : List (Placed V W X)))
        (memberSteps B rows look v b ([] : List (Placed V W X')))) :
    MembersAlike B rows look v hs hs' Inv 0 bs := by
  refine members_of_index B rows look v hs hs' Inv bs 0 fun j b hj => ?_
  rw [Nat.zero_add]
  have q := forall₂_find (fun h : Placed V W X => h.place == b.place)
    (fun h : Placed V W X' => h.place == b.place)
    (fun a a' r => by
      show (a.place == b.place) = (a'.place == b.place)
      rw [r.1]) hP
  cases hf : hs.find? (fun h => h.place == b.place) with
  | none =>
    cases hf' : hs'.find? (fun h => h.place == b.place) with
    | none =>
      rw [member_none B rows look v b hs hf, member_none B rows look v b hs' hf']
      exact hI j b hj
    | some h' =>
      rw [hf, hf'] at q
      exact False.elim q
  | some h =>
    cases hf' : hs'.find? (fun h => h.place == b.place) with
    | none =>
      rw [hf, hf'] at q
      exact False.elim q
    | some h' =>
      rw [hf, hf'] at q
      rw [member_single B rows look v b hs h hf, member_single B rows look v b hs' h' hf']
      have q' : HalfAlike B rows look v bs Inv h h' := q
      exact q'.2 j b hj (List.find?_some (p := fun g : Placed V W X => g.place == b.place) hf)

/-! ## 4 The tests that read the places -/

theorem strays_places (bs : List (Block S Cl)) (hs : List (Placed V W X)) :
    strays bs hs = (hs.map (·.place)).filter fun a => !(bs.any fun b => b.place == a) := by
  unfold strays
  rw [List.filter_map]
  rfl

theorem twice_places (hs : List (Placed V W X)) :
    twice hs = ((hs.map (·.place)).filter fun a =>
      1 < ((hs.map (·.place)).filter fun c => c == a).length).eraseDups := by
  unfold twice
  refine congrArg List.eraseDups (List.filter_congr fun a _ => ?_)
  rw [List.filter_map, List.length_map]
  rfl

theorem HalfAlike.places {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {bs : List (Block S Cl)} {Inv : Nat → Mid W X → Mid W X' → Prop}
    {hs : List (Placed V W X)} {hs' : List (Placed V W X')}
    (h : List.Forall₂ (HalfAlike B rows look v bs Inv) hs hs') :
    hs.map (·.place) = hs'.map (·.place) := by
  induction h with
  | nil => rfl
  | @cons a b l l' hab _ ih =>
    show a.place :: l.map (·.place) = b.place :: l'.map (·.place)
    rw [hab.1, ih]

/-- **The tests that read neither a challenge nor the instance answer alike**, where the prover's
sides of the first and the second chain are at the same places, the shared chain's sides are the
same, and so are `inRange` and `dummy`. -/
theorem readyTests_alike (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (H' : Prover W₀ Rc Xi Ky Tr X₀ X') (w₀ : W₀)
    (h1 : H.first.map (·.place) = H'.first.map (·.place))
    (h3 : H.second.map (·.place) = H'.second.map (·.place)) (h2 : H.shared = H'.shared)
    (hr : H.inRange = H'.inRange) (hd : H.dummy = H'.dummy) :
    readyTests F B H w₀ = readyTests F B H' w₀ := by
  unfold readyTests
  rw [strays_places F.first.blocksInOrder H.first, strays_places F.first.blocksInOrder H'.first,
    strays_places F.second.blocksInOrder H.second, strays_places F.second.blocksInOrder H'.second,
    twice_places H.first, twice_places H'.first, twice_places H.second, twice_places H'.second, h1,
    h3, h2, hr, hd]

end ProofFile.Honest

#print axioms ProofFile.Honest.hear_heard
#print axioms ProofFile.Honest.AlikeTo.counted
#print axioms ProofFile.Honest.StepsAlike.counted
#print axioms ProofFile.Honest.forall₂_find
#print axioms ProofFile.Honest.members_of_halves
#print axioms ProofFile.Honest.readyTests_alike
#print axioms ProofFile.Honest.AnsAlike.mono_ok
#print axioms ProofFile.Honest.member_single
#print axioms ProofFile.Honest.member_none
#print axioms ProofFile.Honest.members_of_index
#print axioms ProofFile.Honest.strays_places
#print axioms ProofFile.Honest.twice_places
#print axioms ProofFile.Honest.HalfAlike.places
#print axioms ProofFile.Honest.Cnt
#print axioms ProofFile.Honest.HalfAlike
