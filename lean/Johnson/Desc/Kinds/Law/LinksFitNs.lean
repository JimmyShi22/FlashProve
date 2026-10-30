-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LinksFitNs.lean: what an accept of the program's own public test linksFit
(OnBytes/Model/StagesLinks.lean:480-484) says on the number of hidden scalars of every segment.
Theorems.

What is proved.
  linkLaid_ns    linkLaid shape layout maskRow l X = .ok () implies X.ns + shape.answers ≤ maskRow.
  linksLaid_ns   linksLaid links codes shape layout = .ok () implies: the mask code that the shape
          names is there, and every link's ns + shape.answers is at most its message length.
  **linksFit_ns**   the same of linksFit links codes shape layout kCol = .ok ().

Existential quantifier: zk, fixed by codes.mask[shape.maskCode]? = some zk.
Why. Law/PlanK6NoNs.lean's planK6_of_bound takes Wp.H.ns ≤ b as a premise. The theorem
built_head_ns (Johnson/Desc/ProofFile/Law/HeadNs.lean) gives linksFit at the links that the maker
built, and that the last of them bears X.H.ns.
Not proved here. That any list of links passes the test. Nothing on soundness.

-/
import OnBytes.TieK.LinksEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes OnBytes.Params
open OnBytes.Model.Stages (LinkH linkLaid linksLaid linksFit)
open OnBytes.TieK (ok_of_bind forIn_keeps)

theorem linkLaid_ns {shape : ReqShape} {layout : ReqLayout} {m l : Nat} {X : LinkH}
    (h : linkLaid shape layout m l X = .ok ()) : X.ns + shape.answers ≤ m := by
  refine Nat.le_of_not_lt fun hgt => ?_
  replace hgt : X.ns + shape.answers > m := hgt
  unfold linkLaid at h
  rw [if_pos hgt] at h
  obtain ⟨_, hu, -⟩ := ok_of_bind h
  cases hu

theorem linksLaid_ns {links : Array LinkH} {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (h : linksLaid links codes shape layout = .ok ()) :
    ∃ zk, codes.mask[shape.maskCode]? = some zk ∧
      ∀ X ∈ links.toList, X.ns + shape.answers ≤ zk.ell := by
  unfold linksLaid at h
  cases hz : codes.mask[shape.maskCode]? with
  | none =>
    rw [hz] at h
    cases h
  | some zk =>
    rw [hz] at h
    dsimp only at h
    obtain ⟨u, h, -⟩ := ok_of_bind h
    refine ⟨zk, rfl, ?_⟩
    have key : ∀ x ∈ links.toList.zipIdx, x.1.ns + shape.answers ≤ zk.ell := by
      refine forIn_keeps _ links.toList.zipIdx
        (fun pre _ => ∀ x ∈ pre, x.1.ns + shape.answers ≤ zk.ell) ?_
        links.toList.zipIdx [] PUnit.unit u rfl (by intro x hx; cases hx) h
      intro pre a rest _ s s' hI hf
      obtain ⟨X, l⟩ := a
      dsimp only at hf
      obtain ⟨w, hw, hf⟩ := ok_of_bind hf
      refine ⟨PUnit.unit, (Except.ok.inj hf).symm, ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hI x hx
      · obtain rfl := List.mem_singleton.1 hx
        exact linkLaid_ns hw
    intro X hX
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hX
    exact key (links.toList[i], i) (by
      rw [List.mem_zipIdx_iff_getElem?]
      simp)

/-- **An accept of the program's own test bounds every segment's number of hidden scalars.** -/
theorem linksFit_ns {links : Array LinkH} {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    {kCol : Nat} (h : linksFit links codes shape layout kCol = .ok ()) :
    ∃ zk, codes.mask[shape.maskCode]? = some zk ∧
      ∀ X ∈ links.toList, X.ns + shape.answers ≤ zk.ell := by
  unfold linksFit at h
  dsimp only at h
  split at h
  · obtain ⟨_, hu, -⟩ := ok_of_bind h
    cases hu
  · obtain ⟨_, -, h⟩ := ok_of_bind h
    obtain ⟨_, -, h⟩ := ok_of_bind h
    exact linksLaid_ns h

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.linkLaid_ns
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.linksLaid_ns
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.linksFit_ns
