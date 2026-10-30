-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/OmegaDeclared.lean: no soundness is claimed.
The third clause of HandedRoots | HandedNumbers (OpensAtW.lean: «Omega's tree in the shared chain's end's book has the number nΩ»), paid by the running test on taken sources and one test on the plan. The book-keeping at border 2 holds that test (tiedB): every pair that it reads off the record's book is opened by a declared round of the proximity test's block under «taken c n». Omega's copy is a member of the own group (three_members, Johnson/Desc/Last/ShapeGives.lean), its pair is (1, the number of its tree), and that tree bears the number of Omega's tree in the shared chain's book (Laid.tree). So that number is declared: some round opens «taken 1 ‹that number›». Where the block's declared rounds name one number only under «taken 1 ·», it is that one.
  **omega_declared**   shapeAt p ‹the block's rounds› 2 f o s = true → ∃ tO, s.book.trees[f.book.trees.size]? = some tO ∧ ∃ r ∈ ‹the rounds›, ∃ x ∈ r.opens, x.2 = .taken 1 tO.number
  OneOmega π nΩ        a test on the plan (a condition on the block's declared rounds alone): whatever is opened under «taken 1 n» has n = nΩ
  **omega_clause**     shapeAt … = true → OneOmega π nΩ → ∀ q T, o.book.place[o.omega]? = some q → o.book.trees[q.1]? = some T → T.number = nΩ
Does not show. That OneOmega holds at the release's plan (a value). That nΩ is the number under which the shared chain sent the tree: it is the number that the shared chain's book bears. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.OpensAtW
import Johnson.Desc.Third.Law.Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.K12.Seat (onOwn enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut Border Laid takenOf)
open VerifiableInference.Desc.Third.Law (start₃E_book start₃E_border start₃E_st)
open VerifiableInference.Desc.Last (Handed shapeAt BehindOk behindOk_of_two tied_of three_members)

/-- **The number of the tree of Omega's copy is declared.** -/
theorem omega_declared (π : P12) {p : P₁₄} {f : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds 2 f o s = true) :
    ∃ tO : Tree, s.book.trees[f.book.trees.size]? = some tO ∧
      ∃ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, ∃ x ∈ r.opens,
        x.2 = .taken 1 tO.number := by
  obtain ⟨⟨s₀, B⟩, hT⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨ts, hts, ca, -⟩ := tied_of (onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) hT
  have hbook : s₀.book = f.book := (start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start).1
  obtain ⟨G₀, G', -, hG', hmem, -, -⟩ := three_members B (start₃E_st _ _ _ _ _ _ _ _ _ _ _ B.start)
    (start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start)
  obtain ⟨q, T, tO, -, -, -, h4, -, -⟩ := L.tree
  have htk : tkOf { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                    mask := s.loc.mask } s.loc.omega = some ts :=
    (takenOf_tkOf s _ rfl).symm.trans hts
  unfold tkOf at htk
  have hG'' : (s.st.groups[s.loc.own]?) = some G' := hG'
  have htk' : (G'.members.toList ++ s.loc.mask.toList).mapM (pairAt s.book s.loc.omega) =
      some ts := by
    have h0 : ((s.st.groups[s.loc.own]?).bind fun G =>
      (G.members.toList ++ s.loc.mask.toList).mapM (pairAt s.book s.loc.omega)) = some ts := htk
    rw [hG''] at h0
    exact h0
  have W := optMapM_ok _ _ _ htk'
  have hi : s.loc.omega ∈ G'.members.toList ++ s.loc.mask.toList := by
    rw [hmem]
    simp
  obtain ⟨y', hy', hp⟩ := forall₂_mem_l W _ hi
  have hS : Sits s.book s.loc.omega s₀.book.trees.size tO.number :=
    ⟨0, tO, by rw [omega_is L]; exact L.place, h4, rfl⟩
  rw [pairAt_of_sits hS] at hp
  have e : y' = (1, tO.number) := by
    have := Option.some.inj hp
    rw [← this]
    simp
  subst e
  obtain ⟨r, hr, x, hx, ex⟩ := tied_a ca _ hy'
  exact ⟨tO, by rw [← hbook]; exact h4, r, hr, x, hx, ex⟩

/-- **A test on the plan**: the block's declared rounds open one number only under "taken 1 ·". -/
def OneOmega (π : P12) (nΩ : ℕ) : Prop :=
  ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, ∀ x ∈ r.opens, ∀ n, x.2 = .taken 1 n → n = nΩ

/-- **The third clause.** -/
theorem omega_clause (π : P12) {p : P₁₄} {f : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds 2 f o s = true) {nΩ : ℕ}
    (h1 : OneOmega π nΩ) (q : ℕ × ℕ) (T : Tree) (hq : o.book.place[o.omega]? = some q)
    (hT : o.book.trees[q.1]? = some T) : T.number = nΩ := by
  obtain ⟨tO, h4, r, hr, x, hx, ex⟩ := omega_declared π hs
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hs
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  have hbook : s₀.book = f.book := (start₃E_book _ _ _ _ _ _ _ _ _ _ _ B.start).1
  obtain ⟨g, hg⟩ := start₃E_border _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans L.border)
  obtain ⟨q', T', tO', a1, a2, -, a4, a5, -⟩ := L.tree
  obtain rfl : q' = q := Option.some.inj (a1.symm.trans hq)
  obtain rfl : T' = T := Option.some.inj (a2.symm.trans hT)
  rw [hbook] at a4
  obtain rfl : tO' = tO := Option.some.inj (a4.symm.trans h4)
  rw [← a5]
  exact h1 r hr x hx _ ex

end ToldDesc

#print axioms ToldDesc.omega_declared
#print axioms ToldDesc.omega_clause
