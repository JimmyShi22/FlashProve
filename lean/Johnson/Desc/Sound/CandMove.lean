-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/CandMove.lean: FROM A FAMILY OF CANDIDATES AT A LAW's OWN LETTERS TO ONE TUPLE OF
CANDIDATES OF THE MEMBERS. Theorems, proved.

`TestGivesCand` (WordsLaw.lean) asks, at a block that closes pins, ONE TUPLE c of messages, one for
each member (`Mem`, World.lean), each a candidate of its member (`CandAt`): in the list of the
member's word as the strings hold it, with the answers of the sample that the record holds. A law of
a proximity test gives a family of candidates over its own group's members j, each over its own
shape and radius, of a word and at a sample in the law's own letters.
  `cand_cross` (proved): the library's `OMsg.Cand` crosses from one oracle message of the library to
    an equal one.
  `candAt_of_cand` (proved): ONE MEMBER: a candidate of a word f at a sample σ is a candidate of the
    member, where (s1) f is the strings' reading of the member's word and (s2) the record holds a
    sample with σ's answers, at a seed that the library's sample map reads as it reads σ's. NO
    EQUATION OF SEEDS.
  `candAt_of_alike` (proved): the same from a candidate AT ANOTHER LIST's MEMBER that is alike
    (`Alike`, PinMove.lean: one shape AND RADIUS, one seat): (s3) the radius is in `Alike`.
  `om_of_entry`, `candAt_of_port` (proved): the same from a candidate at the library's oracle
    message of a shape and a radius (`portOmZ`): (s3) the member's entry is that shape with that
    radius.
  `tuple_of_port` (proved): THE TUPLE FROM SUCH A FAMILY: with it: each of its messages is the
    family's own, up to the types' equation.
  `tupleOf`; `tuple_of_family` (proved): THE TUPLE: mem : J → Mem one to one, `mine` its values: the
    family's messages, each carried to its member's own type; each is a candidate of its member.
Limits. (s1), (s2), (s3) are premises at each member. Nothing says that the row's ins hold of the
witness that the tuple lays. No game: no transcript stands in this file. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.Sound.SeedMove

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice

/-- A candidate crosses from one oracle message of the library to an equal one. -/
theorem cand_cross {o o₂ : OMsg GE} (ho : o = o₂) (f : o.Str) (f₂ : o₂.Str) (σ : o.Smp)
    (σ₂ : o₂.Smp) (m : o.Msg) (m₂ : o₂.Msg) (hf : HEq f f₂) (hσ : HEq σ σ₂) (hm : HEq m m₂)
    (h : o.Cand f σ m) : o₂.Cand f₂ σ₂ m₂ := by
  subst ho
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hσ
  obtain rfl := eq_of_heq hm
  exact h

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A : Type}
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **One member**: a candidate of the word f at the sample σ is a candidate of the member. -/
theorem candAt_of_cand (x : Mem) (a : A) (y : Strs) (f : ((sigOf cs x.1.l).om x.2).Str)
    (σ : ((sigOf cs x.1.l).om x.2).Smp) (m : ((sigOf cs x.1.l).om x.2).Msg)
    (s1 : f = wordsOf G cs x.1.l x.1.seat y x.2)
    (s2 : ∃ z, smp a x.1 x.2 = some z ∧ z.2 = σ.2 ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ.1)
    (h : ((sigOf cs x.1.l).om x.2).Cand f σ m) : CandAt cs G smp x a y m := by
  obtain ⟨z, hz, e2, e1⟩ := s2
  refine ⟨z, hz, ?_⟩
  have ez : z = (z.1, σ.2) := Prod.ext rfl e2
  have eσ : σ = (σ.1, σ.2) := rfl
  rw [← s1, ez, cand_congr ((sigOf cs x.1.l).om x.2) f z.1 σ.1 σ.2 m e1, ← eσ]
  exact h

/-- **The same from a candidate at another list's member that is alike.** -/
theorem candAt_of_alike (x x₂ : Mem) (hx : Alike x₂ x) (a : A) (y : Strs)
    (f : ((sigOf cs x₂.1.l).om x₂.2).Str) (σ : ((sigOf cs x₂.1.l).om x₂.2).Smp)
    (m : ((sigOf cs x₂.1.l).om x₂.2).Msg) (m' : ((sigOf cs x.1.l).om x.2).Msg) (hm : HEq m m')
    (s1 : HEq f (wordsOf G cs x.1.l x.1.seat y x.2))
    (s2 : ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a x.1 x.2 = some z ∧ HEq σ σ' ∧
      z.2 = σ'.2 ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1)
    (h : ((sigOf cs x₂.1.l).om x₂.2).Cand f σ m) : CandAt cs G smp x a y m' := by
  obtain ⟨z, σ', hz, hσ, e2, e1⟩ := s2
  exact candAt_of_cand cs G smp x a y _ σ' m' rfl ⟨z, hz, e2, e1⟩
    (cand_cross (om_alike cs x₂ x hx) f _ σ σ' m m' s1 hσ hm h)

open Classical in
/-- The tuple of a family: at a member that is a value of mem: the family's message there; 0
elsewhere. -/
def tupleOf {J : Type} (mem : J → Mem) (c : (j : J) → ((sigOf cs (mem j).1.l).om (mem j).2).Msg)
    (x : Mem) : ((sigOf cs x.1.l).om x.2).Msg :=
  if h : ∃ j, mem j = x then h.choose_spec ▸ c h.choose else 0

theorem tupleOf_at {J : Type} (mem : J → Mem) (hinj : Function.Injective mem)
    (c : (j : J) → ((sigOf cs (mem j).1.l).om (mem j).2).Msg) (j : J) :
    tupleOf cs mem c (mem j) = c j := by
  have h : ∃ j', mem j' = mem j := ⟨j, rfl⟩
  have e : h.choose = j := hinj h.choose_spec
  unfold tupleOf
  rw [dif_pos h]
  have key : ∀ (j' : J) (q : mem j' = mem j), j' = j → (q ▸ c j' :
      ((sigOf cs (mem j).1.l).om (mem j).2).Msg) = c j := by
    intro j' q e'
    subst e'
    rfl
  exact key _ _ e

/-- **The tuple**: each of its messages is a candidate of its member. -/
theorem tuple_of_family {J : Type} (mem : J → Mem) (hinj : Function.Injective mem)
    (mine : List Mem) (hmine : ∀ x ∈ mine, ∃ j, mem j = x) (a : A) (y : Strs)
    (c : (j : J) → ((sigOf cs (mem j).1.l).om (mem j).2).Msg)
    (h : ∀ j, CandAt cs G smp (mem j) a y (c j)) :
    ∀ x ∈ mine, CandAt cs G smp x a y (tupleOf cs mem c x) := by
  intro x hx
  obtain ⟨j, rfl⟩ := hmine x hx
  rw [tupleOf_at cs mem hinj c j]
  exact h j

/-- A member's oracle message of the library, by the member's entry. -/
theorem om_of_entry (x : Mem) (sh : OnBytes.OracleShape) (e0 : ℕ) (he : x.1.l.get x.2 = (sh, e0)) :
    portOmZ cs sh e0 = (sigOf cs x.1.l).om x.2 := by
  show portOmZ cs sh e0 = portOmZ cs (x.1.l.get x.2).1 (x.1.l.get x.2).2
  rw [he]

/-- **One member, from a candidate at a shape and a radius**: (s3) the member's entry is that shape
with that radius. -/
theorem candAt_of_port (x : Mem) (sh : OnBytes.OracleShape) (e0 : ℕ)
    (he : x.1.l.get x.2 = (sh, e0)) (a : A) (y : Strs) (f : (portOmZ cs sh e0).Str)
    (σ : (portOmZ cs sh e0).Smp) (m : (portOmZ cs sh e0).Msg)
    (m' : ((sigOf cs x.1.l).om x.2).Msg) (hm : HEq m m')
    (s1 : HEq f (wordsOf G cs x.1.l x.1.seat y x.2))
    (s2 : ∃ (z σ' : ((sigOf cs x.1.l).om x.2).Smp), smp a x.1 x.2 = some z ∧ HEq σ σ' ∧
      z.2 = σ'.2 ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val σ'.1)
    (h : (portOmZ cs sh e0).Cand f σ m) : CandAt cs G smp x a y m' := by
  obtain ⟨z, σ', hz, hσ, e2, e1⟩ := s2
  exact candAt_of_cand cs G smp x a y _ σ' m' rfl ⟨z, hz, e2, e1⟩
    (cand_cross (om_of_entry cs x sh e0 he) f _ σ σ' m m' s1 hσ hm h)

/-- **THE TUPLE, FROM A FAMILY OF CANDIDATES AT SHAPES AND RADII**: one message a member, each a
candidate of its member, each the family's own message (up to the types' equation). -/
theorem tuple_of_port {J : Type} (mem : J → Mem) (hinj : Function.Injective mem) (mine : List Mem)
    (hmine : ∀ x ∈ mine, ∃ j, mem j = x) (sh : J → OnBytes.OracleShape) (e0 : J → ℕ)
    (he : ∀ j, (mem j).1.l.get (mem j).2 = (sh j, e0 j)) (a : A) (y : Strs)
    (f : ∀ j, (portOmZ cs (sh j) (e0 j)).Str) (σ : ∀ j, (portOmZ cs (sh j) (e0 j)).Smp)
    (c' : ∀ j, (portOmZ cs (sh j) (e0 j)).Msg)
    (s1 : ∀ j, HEq (f j) (wordsOf G cs (mem j).1.l (mem j).1.seat y (mem j).2))
    (s2 : ∀ j, ∃ (z σ' : ((sigOf cs (mem j).1.l).om (mem j).2).Smp),
      smp a (mem j).1 (mem j).2 = some z ∧ HEq (σ j) σ' ∧ z.2 = σ'.2 ∧
      ((sigOf cs (mem j).1.l).om (mem j).2).Z.val z.1 =
        ((sigOf cs (mem j).1.l).om (mem j).2).Z.val σ'.1)
    (h : ∀ j, (portOmZ cs (sh j) (e0 j)).Cand (f j) (σ j) (c' j)) :
    ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
      (∀ x ∈ mine, CandAt cs G smp x a y (c x)) ∧ ∀ j, HEq (c (mem j)) (c' j) := by
  let c₁ : (j : J) → ((sigOf cs (mem j).1.l).om (mem j).2).Msg := fun j =>
    cast (congrArg OMsg.Msg (om_of_entry cs (mem j) (sh j) (e0 j) (he j))) (c' j)
  have hc : ∀ j, HEq (c' j) (c₁ j) := fun j => (cast_heq _ _).symm
  refine ⟨tupleOf cs mem c₁, tuple_of_family cs G smp mem hinj mine hmine a y c₁ fun j =>
    candAt_of_port cs G smp (mem j) (sh j) (e0 j) (he j) a y (f j) (σ j) (c' j) (c₁ j) (hc j)
      (s1 j) (s2 j) (h j), fun j => ?_⟩
  rw [tupleOf_at cs mem hinj c₁ j]
  exact (hc j).symm

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.om_of_entry
#print axioms VerifiableInference.Desc.Sound.candAt_of_port
#print axioms VerifiableInference.Desc.Sound.tuple_of_port
#print axioms VerifiableInference.Desc.Sound.cand_cross
#print axioms VerifiableInference.Desc.Sound.candAt_of_cand
#print axioms VerifiableInference.Desc.Sound.candAt_of_alike
#print axioms VerifiableInference.Desc.Sound.tupleOf_at
#print axioms VerifiableInference.Desc.Sound.tuple_of_family
