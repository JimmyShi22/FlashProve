-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Maker/OkOfNames.lean: where the program has read a file's three chains, every name under
which a round of the three lists opens a tree stands for a tree of the file: the second clause of
`Three.Whole.fits` (OnBytes/Three/Data.lean).

The first two chains open their own trees alone. The third list at which the makers' tests are
asked is the dry run's, with made-up names for the earlier chains' trees (`tagChain`). A made-up
name stands for a tree only if its number is below the number of trees that the earlier chain has
sent. That is had from the reading: the reading's own third list goes with the dry run's name by
name (`named_of_read`, OnBytes/Maker/OwesOfRead.lean); there the root of a tree that is taken over
has 32 bytes, by the format's own test; and the name of a tree that the earlier chain has not sent
has an empty root.

Main names:
  `given_of_ok`: in a description that passes the format's test the root of a tree that is taken
    over has 32 bytes.
  `treesOf_lt`, `treesOf_tag`, `named_tag1`, `named_tag2`: names of a chain as read; made-up
    names, and for which tree they stand.
  `lalike_right`: to a member of the second of two lists that are alike there is one of the first.
  `nameOk`, `nameOk_own`: the clause's test on one name.
  `third_names`: the clause at the dry run's third list. `names_of_read`: the clause.

Limits: that the first chain's rounds open that chain's own trees alone (`OwnAlone R₁`) and
`OwnBook` of its book are premises. The lists are those of this reading's own dry runs. Nothing on
the other clauses. Nothing on soundness.
-/
import OnBytes.Maker.OkOfRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Three (tagChain tagRoot tagRun named)
open OnBytes.Params (Rounds)

/-! ### A taken-over tree's root in a description that passes the format's test -/

theorem given_of_roundsOk (P : Fmt.Plan) (noRand : Bool) (firstTree : Nat) :
    ∀ (rs : List Fmt.Round) (after : Bool) (sent : Nat),
      Fmt.roundsOk P noRand firstTree after sent rs = true →
      ∀ r ∈ rs, ∀ o ∈ r.opens, ∀ root start, o.2 = .given root start → root.size = 32
  | [], _, _, _, _, hr => by cases hr
  | r :: rs, after, sent, h, x, hx => by
    unfold Fmt.roundsOk at h
    rw [Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx'
    · intro o ho root start e
      have h1 := h.1
      unfold Fmt.Round.ok at h1
      simp only [Bool.and_eq_true, List.all_eq_true] at h1
      have h2 := (h1.2 o ho).2
      rw [e] at h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact h2.1
    · exact given_of_roundsOk P noRand firstTree rs _ _ h.2 x hx'

/-- In a description that passes the format's test the root of a tree that is taken over has 32
bytes. -/
theorem given_of_ok {S : Fmt.Spec} (h : S.ok = true) :
    ∀ r ∈ S.rounds, ∀ o ∈ r.opens, ∀ root start, o.2 = .given root start → root.size = 32 := by
  unfold Fmt.Spec.ok at h
  simp only [Bool.and_eq_true] at h
  exact given_of_roundsOk _ _ _ S.rounds _ _ h.1.1.2

/-! ### Names -/

/-- A name of a tree of a chain as read whose root is not empty is the name of a tree that the chain
has sent. -/
theorem treesOf_lt (c : ChainRead) (n : ℕ) (ρ σ : ByteArray) (e : treesOf c n = .given ρ σ)
    (h : ρ.size ≠ 0) : n < c.roots.length := by
  by_contra hn
  have h0 : c.roots[n]? = none := List.getElem?_eq_none (Nat.le_of_not_lt hn)
  unfold treesOf ChainRead.tree at e
  rw [h0] at e
  have e' : Fmt.Src.given ByteArray.empty ByteArray.empty = .given ρ σ := e
  injection e' with e1 _
  exact h (e1 ▸ rfl)

/-- The made-up name of the tree number n. -/
theorem treesOf_tag (c : UInt8) (N n : ℕ) (h : n < N) :
    treesOf (tagChain c N) n = .given (tagRoot n) (tagRun c) := by
  have h0 : (tagChain c N).roots[n]? = some (tagRoot n) := by
    rw [tagChain_rootsList, List.getElem?_map, List.getElem?_range h]
    rfl
  unfold treesOf ChainRead.tree
  rw [h0]
  rfl

theorem named_tag1 (here n : ℕ) : named here (.given (tagRoot n) (tagRun 1)) = some (0, n) := by
  show (if (tagRoot n).size = 0 then none
    else if (tagRun 1 == tagRun 1) = true then some (0, (tagRoot n).size - 1)
    else if (tagRun 1 == tagRun 2) = true then some (1, (tagRoot n).size - 1) else none) = _
  rw [if_neg (by rw [tagRoot_size]; omega), if_pos (by decide), tagRoot_size]
  rfl

theorem named_tag2 (here n : ℕ) : named here (.given (tagRoot n) (tagRun 2)) = some (1, n) := by
  show (if (tagRoot n).size = 0 then none
    else if (tagRun 2 == tagRun 1) = true then some (0, (tagRoot n).size - 1)
    else if (tagRun 2 == tagRun 2) = true then some (1, (tagRoot n).size - 1) else none) = _
  rw [if_neg (by rw [tagRoot_size]; omega), if_neg (by decide), if_pos (by decide), tagRoot_size]
  rfl

/-- To a member of the second of two lists that are alike there is one of the first. -/
theorem lalike_right {α : Type} {P : α → α → Prop} : ∀ {l l' : List α}, LAlike P l l' →
    ∀ y ∈ l', ∃ x ∈ l, P x y
  | _, _, .nil, _, h => by cases h
  | _, _, .cons (a := a) (b := b) p t, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self .., p⟩
    · obtain ⟨x, hx, q⟩ := lalike_right t y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, q⟩

/-- The test of the second clause of `Three.Whole.fits` on one name. -/
def nameOk (here : ℕ) (s : Fmt.Src) : Bool :=
  match named here s with
  | none => false
  | some y => (here == 2 || y.1 == here) && decide (y.1 ≤ here)

theorem nameOk_own (here n : ℕ) : nameOk here (.own n) = true := by
  show ((here == 2 || here == here) && decide (here ≤ here)) = true
  simp

section Read
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **Every name in the dry run's third list stands for a tree of the file.** -/
theorem third_names
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    ∀ y ∈ R₃, ∀ o ∈ y.1.opens, nameOk 2 o.2 = true := by
  obtain ⟨_, _, o₃, e₃⟩ := read_ok T hS₁
  have A := named_of_read T hS₁ b₁ R₃ hd
  intro y hy o ho
  obtain ⟨x, hx, k⟩ := lalike_right A y hy
  obtain ⟨u, hu, q⟩ := lalike_right k.opens o ho
  have g := of_rounds e₃ (fun z => ∀ o ∈ z.opens, ∀ root start, o.2 = .given root start →
    root.size = 32) (given_of_ok o₃) x hx u hu
  obtain ⟨_, q2⟩ := q
  revert g q2
  rcases u.2 with n | ⟨ρ, σ⟩ <;> rcases o.2 with n' | ⟨ρ', σ'⟩ <;> intro g q2
  · exact nameOk_own 2 n'
  · cases q2
  · cases q2
  · have hs : ρ.size ≠ 0 := by rw [g ρ σ rfl]; norm_num
    cases q2 with
    | given G =>
      rcases G with ⟨n, a1, a2⟩ | ⟨n, a1, a2⟩
      · rw [treesOf_tag 1 _ n (treesOf_lt _ n ρ σ a1 hs)] at a2
        injection a2 with e1 e2
        rw [← e1, ← e2]
        show (match named 2 (.given (tagRoot n) (tagRun 1)) with
          | none => false
          | some y => ((2 : ℕ) == 2 || y.1 == 2) && decide (y.1 ≤ 2)) = true
        rw [named_tag1]
        rfl
      · rw [treesOf_tag 2 _ n (treesOf_lt _ n ρ σ a1 hs)] at a2
        injection a2 with e1 e2
        rw [← e1, ← e2]
        show (match named 2 (.given (tagRoot n) (tagRun 2)) with
          | none => false
          | some y => ((2 : ℕ) == 2 || y.1 == 2) && decide (y.1 ≤ 2)) = true
        rw [named_tag2]
        rfl

/-- **The second clause of `Three.Whole.fits`, from the reading**, if the first chain's rounds open
that chain's own trees alone. -/
theorem names_of_read
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (o₁ : OwnAlone R₁)
    (b₁ : OwnBook dry.book) (R₃ : Rounds)
    (hd : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    ([(0, R₁), (1, R₂), (2, R₃)].all fun x => x.2.all fun r => r.1.opens.all fun o =>
      nameOk x.1 o.2) = true := by
  have o₂ := (shared_own p r.key T.shared_dry).1
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun x hx o ho => ?_, fun x hx o ho => ?_, third_names T hS₁ b₁ R₃ hd⟩
  · obtain ⟨n, e⟩ := o₁ x hx o ho
    rw [e]
    exact nameOk_own 0 n
  · obtain ⟨n, e⟩ := o₂ x hx o ho
    rw [e]
    exact nameOk_own 1 n

end Read

end OnBytes.Maker

#print axioms OnBytes.Maker.third_names
#print axioms OnBytes.Maker.names_of_read
