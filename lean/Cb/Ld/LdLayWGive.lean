-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayWGive.lean: rules of composition for a chain of interactive oracle reductions: when the
honest prover of a whole chain gives up, and that it does not always: from the links' withheld sets
to the chain's.

Definitions, statements (in `Cb.Spec`) and proofs. Rules of the framework only: no protocol, no
code occurs here.
`Honest.withheld`: Ior/Honest.lean. `Rels.core`: Ior/Chain.lean. `Link`, `Chain`, `Chain.AllB`:
Ior/KnowCollRulesChain.lean.

Why: completeness, zero knowledge and "the masks are still fresh" (Ior/Honest.lean,
Ior/KnowCollRulesMask.lean) are asked at the verifier messages that the honest side does not
withhold. A guard for them has to show two things of the withheld set of the whole chain at a
member of the relation: it is not empty (else executions that fail are not exercised), and it is
not everything (else the three properties hold of nothing). The bundles' numbers do not help where
a link's bound `pHid` is 1 or more. Here both are had link by link.

Main names:
  `c.Each Q`: every link of the chain c has Q; `p.Each Q`, `s.Each Q`, `S.Each Q`, `r.Each Q`: the
    same for a list of moves, a segment, a list of segments, the preamble of a request.
  `l.RoomAt k`: there is a verifier message of the link l that is withheld at no witness with the
    core k (and no explicit part).
  `l.GivesAt k p`: there is a set S of verifier messages of l, of probability at least p, that is
    withheld at every witness with the core k.
  `Spec.ldLayW_room`: a chain with all of the bundle but zero knowledge in every link (`c.AllB`),
    every link with room at k: the chain as one link has room at k. (The cores are handed on
    unchanged: the bundle's field `keeps`.)
  `Spec.ldLayW_gives`: `c.AllB`, and not every link fails to give up at k with probability p: the
    chain as one link gives up at k with probability at least p.
  `Spec.ldLayW_room_free`: a link that withholds nothing has room; `Spec.ldLayW_room_nums`: so has
    a link with the bundle (`l.GoodB`) whose two probabilities add up to less than 1;
    `Spec.ldLayW_each_nums`: and every link of a chain with `c.AllB` whose sums do.

Limits: this file does not say that the probability of the withheld set is bounded from above (room
is one verifier message). No link with room, and none that gives up, is exhibited here. "At every
witness with the core k": valid or not.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefKit
import Ior.SeqProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K : Type}

/-- Every link of the chain has Q. -/
def Chain.Each (Q : ∀ A B : Joint K, Link K A B → Prop) : {A B : Joint K} → Chain K A B → Prop
  | A, B, .one l => Q A B l
  | _, C, .snoc (B := B) c l => c.Each Q ∧ Q B C l

/-- There is a verifier message that is withheld at no witness with the core k. -/
def Link.RoomAt {A B : Joint K} (l : Link K A B) (k : K) : Prop :=
  ∃ ρ : Rho l.R.shape, ∀ w x, A.rels.core w = k → ρ ∉ l.H.withheld w x

/-- A set of verifier messages of probability at least p is withheld at every witness with the
core k. -/
def Link.GivesAt {A B : Joint K} (l : Link K A B) (k : K) (p : ℝ≥0∞) : Prop :=
  ∃ S : Set (Rho l.R.shape), p ≤ prRho S ∧ ∀ w x, A.rels.core w = k → S ⊆ l.H.withheld w x

namespace Chain
variable {A B C : Joint K} (Q : ∀ A B : Joint K, Link K A B → Prop)

theorem each_one (l : Link K A B) : (Chain.one l).Each Q ↔ Q A B l := by rw [Each]
theorem each_snoc (c : Chain K A B) (l : Link K B C) : (c.snoc l).Each Q ↔ c.Each Q ∧ Q B C l := by
  rw [Each]

end Chain
end IOR
end Iop

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E] (Q : ∀ A B : Joint Kc, Link Kc A B → Prop)

def LdProg.Each : {a b : LdStage E Kc} → LdProg a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc p m => p.Each ∧ m.chain.Each Q

structure LdSeg.Each {a d : LdStage E Kc} (s : LdSeg a d) : Prop where
  body : s.body.Each Q
  bat  : s.bat.Each Q
  fold : s.fold.Each Q
  snd  : Q _ _ s.snd.link
  loc  : s.loc.Each Q

def LdSegs.Each : {a b : LdStage E Kc} → LdSegs a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc S s => S.Each ∧ s.Each Q

structure LdReq.Each {a z : LdStage E Kc} (r : LdReq a z) : Prop where
  first : Q _ _ r.first.link
  more  : r.more.Each Q
  segs  : r.segs.Each Q
  last  : r.last.Each Q

theorem LdProg.each_nil (a : LdStage E Kc) : (LdProg.nil a).Each Q ↔ True := by rw [LdProg.Each]
theorem LdProg.each_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).Each Q ↔ p.Each Q ∧ m.chain.Each Q := by rw [LdProg.Each]
theorem LdSegs.each_nil (a : LdStage E Kc) : (LdSegs.nil a).Each Q ↔ True := by rw [LdSegs.Each]
theorem LdSegs.each_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).Each Q ↔ S.Each Q ∧ s.Each Q := by rw [LdSegs.Each]

end

namespace Spec

/-- States: if `c.AllB`, room, link by link, is room of the chain. -/
def ldLayW_room : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W) (k : K),
    c.AllB → c.Each (fun _ _ l => l.RoomAt k) → (c.link d).RoomAt k

/-- States: if `c.AllB` and some link gives up, the chain does. -/
def ldLayW_gives : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W) (k : K) (p : ℝ≥0∞),
    c.AllB → ¬ c.Each (fun _ _ l => ¬ l.GivesAt k p) → (c.link d).GivesAt k p

def ldLayW_room_free : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B) (k : K), (∀ w x, l.H.withheld w x = ∅) → l.RoomAt k

def ldLayW_room_nums : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B) (k : K),
    l.GoodB → l.P.pBad + l.P.pHid < 1 → l.RoomAt k

def ldLayW_each_nums : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (k : K),
    c.AllB → c.pBad + c.pHid < 1 → c.Each (fun _ _ l => l.RoomAt k)

def ldLayW_append : Prop :=
  ∀ (K : Type) (Q : ∀ A B : Joint K, Link K A B → Prop) (A B C : Joint K)
      (c : Chain K A B) (c' : Chain K B C),
    (c.append c').Each Q ↔ c.Each Q ∧ c'.Each Q

def ldLayW_onto : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (A : Joint Kc)
      (a b : LdStage E Kc) (c₀ : Chain Kc A a.J) (p : LdProg a b),
    (p.onto c₀).Each Q ↔ c₀.Each Q ∧ p.Each Q

def ldLayW_app : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Q : ∀ A B : Joint Kc, Link Kc A B → Prop)
      (a b c : LdStage E Kc) (p : LdProg a b) (q : LdProg b c),
    (p.app q).Each Q ↔ p.Each Q ∧ q.Each Q

def ldLayW_seg : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (A : Joint Kc)
      (a d : LdStage E Kc) (c₀ : Chain Kc A a.J) (s : LdSeg a d),
    (s.onto c₀).Each Q ↔ c₀.Each Q ∧ s.Each Q

def ldLayW_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Q : ∀ A B : Joint Kc, Link Kc A B → Prop) (A : Joint Kc)
      (a b : LdStage E Kc) (c₀ : Chain Kc A a.J) (S : LdSegs a b),
    (S.onto c₀).Each Q ↔ c₀.Each Q ∧ S.Each Q

/-- The preamble of a request. -/
def ldLayW_req : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (Q : ∀ A B : Joint Kc, Link Kc A B → Prop)
      (a z : LdStage E Kc) (r : LdReq a z),
    r.chain.Each Q ↔ r.Each Q

end Spec

theorem ldLayW_room : Spec.ldLayW_room := by
  intro K A B c d k
  induction c with
  | one l =>
      intro _ h
      rw [link_one]
      exact (each_one _ l).1 h
  | snoc c l ih =>
      intro hB h
      obtain ⟨hc, hl⟩ := (each_snoc _ c l).1 h
      have gB := chain_goodB K _ _ c d ((allB_snoc c l).1 hB).1
      obtain ⟨ρ₁, h₁⟩ := ih ((allB_snoc c l).1 hB).1 hc
      obtain ⟨ρ₂, h₂⟩ := hl
      rw [link_snoc]
      refine ⟨Rho.app ρ₁ ρ₂, fun w x hk => ?_⟩
      refine (Honest.not_mem_withheld_seq (c.link d).H l.H w x (Rho.app ρ₁ ρ₂)).2 ⟨?_, fun cn => ?_⟩
      · rw [Rho.fst_app]
        exact h₁ w x hk
      · rw [Rho.snd_app]
        exact h₂ _ _ ((gB.keeps w x cn _).trans hk)

theorem ldLayW_gives : Spec.ldLayW_gives := by
  intro K A B c d k p
  induction c with
  | one l =>
      intro _ h
      rw [link_one]
      exact Classical.not_not.1 fun h' => h ((each_one _ l).2 h')
  | snoc c l ih =>
      intro hB h
      have gB := chain_goodB K _ _ c d ((allB_snoc c l).1 hB).1
      rw [link_snoc]
      by_cases hl : l.GivesAt k p
      · obtain ⟨S, hp, hS⟩ := hl
        refine ⟨Rho.cylSnd (c.link d).R.shape S,
          le_of_le_of_eq hp (prRho_cylSnd _ S).symm,
          fun w x hk ρ hρ => ?_⟩
        by_contra hn
        exact ((Honest.not_mem_withheld_seq (c.link d).H l.H w x ρ).1 hn).2
          (Classical.arbitrary _) (hS _ _ ((gB.keeps w x _ _).trans hk) hρ)
      · obtain ⟨S, hp, hS⟩ := ih ((allB_snoc c l).1 hB).1 fun hc => h ((each_snoc _ c l).2 ⟨hc, hl⟩)
        refine ⟨Rho.cylFst l.R.shape S,
          le_of_le_of_eq hp (prRho_cylFst _ S).symm,
          fun w x hk ρ hρ => ?_⟩
        by_contra hn
        exact ((Honest.not_mem_withheld_seq (c.link d).H l.H w x ρ).1 hn).1 (hS w x hk hρ)

theorem ldLayW_room_free : Spec.ldLayW_room_free := fun _ _ _ l _ h =>
  ⟨Classical.arbitrary _, fun w x _ hρ => by rw [h w x] at hρ; exact hρ⟩

theorem ldLayW_room_nums : Spec.ldLayW_room_nums := by
  intro K A B l k g hlt
  by_contra hn
  have hall : ∀ ρ : Rho l.R.shape, ρ ∈ l.H.Bad ∪ l.P.cov k := fun ρ => by
    by_contra hρ
    refine hn ⟨ρ, fun w x hk hw => hρ ?_⟩
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (hk ▸ g.cover w x hw)
  have h1 : (1 : ℝ≥0∞) ≤ prRho l.H.Bad + prRho (l.P.cov k) :=
    le_trans (le_of_eq (pr_univ _).symm) (pr_le_add _ fun ρ _ => hall ρ)
  exact absurd (lt_of_le_of_lt (le_trans h1 (add_le_add g.prBad (g.prCov k))) hlt) (lt_irrefl _)

theorem ldLayW_each_nums : Spec.ldLayW_each_nums := by
  intro K A B c k
  induction c with
  | one l =>
      intro hB h
      rw [pBad_one, pHid_one] at h
      exact (each_one _ l).2 (ldLayW_room_nums K _ _ l k ((allB_one l).1 hB) h)
  | snoc c l ih =>
      intro hB h
      rw [pBad_snoc, pHid_snoc] at h
      exact (each_snoc _ c l).2
        ⟨ih ((allB_snoc c l).1 hB).1 (lt_of_le_of_lt (add_le_add le_self_add le_self_add) h),
          ldLayW_room_nums K _ _ l k ((allB_snoc c l).1 hB).2
            (lt_of_le_of_lt (add_le_add le_add_self le_add_self) h)⟩

theorem ldLayW_append : Spec.ldLayW_append := by
  intro K Q A B C c c'
  induction c' with
  | one l => rw [append_one, each_snoc, each_one]
  | snoc c' l ih => rw [append_snoc, each_snoc, each_snoc, ih, and_assoc]

theorem ldLayW_onto : Spec.ldLayW_onto := by
  intro E Kc _ _ Q A a b c₀ p
  induction p with
  | nil => rw [LdProg.onto_nil, LdProg.each_nil, and_true]
  | snoc p m ih => rw [LdProg.onto_snoc, ldLayW_append, ih, LdProg.each_snoc, and_assoc]

theorem ldLayW_app : Spec.ldLayW_app := by
  intro E Kc _ _ Q a b c p q
  induction q with
  | nil => rw [LdProg.app_nil, LdProg.each_nil, and_true]
  | snoc q m ih => rw [LdProg.app_snoc, LdProg.each_snoc, LdProg.each_snoc, ih, and_assoc]

theorem ldLayW_seg : Spec.ldLayW_seg := by
  intro E Kc _ _ Q A a d c₀ s
  unfold LdSeg.onto
  rw [ldLayW_onto, each_snoc, ldLayW_onto, ldLayW_onto, ldLayW_onto]
  exact ⟨fun h => ⟨h.1.1.1.1.1, ⟨h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩⟩,
    fun h => ⟨⟨⟨⟨⟨h.1, h.2.body⟩, h.2.bat⟩, h.2.fold⟩, h.2.snd⟩, h.2.loc⟩⟩

theorem ldLayW_segs : Spec.ldLayW_segs := by
  intro E Kc _ _ Q A a b c₀ S
  induction S with
  | nil => rw [LdSegs.onto_nil, LdSegs.each_nil, and_true]
  | snoc S s ih => rw [LdSegs.onto_snoc, ldLayW_seg, ih, LdSegs.each_snoc, and_assoc]

theorem ldLayW_req : Spec.ldLayW_req := by
  intro E Kc _ _ Q a z r
  unfold LdReq.chain
  rw [ldLayW_onto, ldLayW_segs, ldLayW_onto, each_one]
  exact ⟨fun h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩, fun h => ⟨⟨⟨h.first, h.more⟩, h.segs⟩, h.last⟩⟩

end Cb
