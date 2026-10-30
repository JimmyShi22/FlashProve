-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrameFindsOf.lean: `FrameFinds a n` (SeatsThereOf.lean: the running
frame finds the mask's message and each array's) FROM FACTS ON THE ONE PART a, EACH WITH A PAYER OF
ITS OWN. Theorems. No text already in the library turns.

  `FrameAtLink first l Xl a`: what is asked of the part: its link's list of names is the built
    link's; its layout is the first chain's; its frame stands in link l, a link under way, at the
    first chain's shape, with `reqGroups` of that shape, as many kept messages as the group's target
    has, and ALL of the link's own messages sent.
  `frameFinds_of`: **FrameAtLink · every entry of the built link's list of names is `NamedHeld`
    (NamedOfBuilt.lean) · n ≤ the number of these entries · some message of link l has mask rows ·
    l < the number of links ⊢ FrameFinds a n.**
Limits. ON ONE PART: nothing on «reached». «n ≤ the number of entries» is given by no test of the
maker's: a fact on the plan. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.WhereIsSome
import Johnson.Desc.First.Link.Law.NamedOfBuilt
import Johnson.Desc.First.Link.Law.SeatsThereOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.K9 (maskAt)

/-- What is asked of the part. -/
structure FrameAtLink (first : Params.First) (l : ℕ) (Xl : LinkH) (a : K9.Part) : Prop where
  names : a.L.arrayOf = Xl.arrayOf
  layout : a.L.check.rows.layout = first.layout
  next : a.L.check.frame.next = .laterOrClose
  link : a.L.check.frame.link = l
  shape : a.L.check.frame.shape = first.shape
  groups : a.L.check.frame.groups = reqGroups first.shape
  kept : a.L.check.frame.keptBefore.size = ((reqGroups first.shape).getD l {}).target.kept.size
  own : ∀ L, first.shape.link[l]? = some L → a.L.check.frame.own.size = L.messages.length

theorem frameFinds_of {first : Params.First} {l : ℕ} {Xl : LinkH} {a : K9.Part}
    (H : FrameAtLink first l Xl a)
    (hQ : ∀ (τ born : ℕ) (name : String), Xl.arrayOf[τ]? = some (born, name) →
      NamedHeld first l Xl τ born name)
    {n : ℕ} (hC : n ≤ Xl.arrayOf.size) {L : Params.ReqLink} (hL : first.shape.link[l]? = some L)
    (hM : (L.messages.any fun x => x.shape.maskRows != 0) = true) : FrameFinds a n := by
  have hlen : l < first.shape.link.length := (List.getElem?_eq_some_iff.1 hL).1
  have own : ∀ i, i < L.messages.length → (a.L.check.frame.whereIs l i).isSome = true := by
    intro i hi
    have := whereIs_own a.L.check.frame H.next (i := i) (by rw [H.own L hL]; exact hi)
    rwa [H.link] at this
  refine ⟨?_, fun i hi => ?_⟩
  · unfold maskAt
    rw [H.shape, H.link, hL]
    show ((L.messages.findIdx? fun x => x.shape.maskRows != 0).bind fun m =>
      a.L.check.frame.whereIs l m).isSome = true
    cases e : L.messages.findIdx? fun x => x.shape.maskRows != 0 with
    | none =>
      rw [List.findIdx?_eq_none_iff] at e
      obtain ⟨x, hx, hp⟩ := List.any_eq_true.1 hM
      rw [e x hx] at hp
      exact nomatch hp
    | some j =>
      obtain ⟨hj, _⟩ := List.findIdx?_eq_some_iff_getElem.1 e
      exact own j hj
  · have hi' : i < Xl.arrayOf.size := by omega
    obtain ⟨hle, A, L', m, h1, h2, h3, h4, _, _⟩ :=
      hQ i (Xl.arrayOf[i]).1 (Xl.arrayOf[i]).2 (Array.getElem?_eq_getElem hi')
    refine ⟨Xl.arrayOf[i], A, by rw [H.names]; exact Array.getElem?_eq_getElem hi', by
      rw [H.layout]
      exact h1, ?_⟩
    by_cases hb : (Xl.arrayOf[i]).1 = l
    · rw [hb] at h2 ⊢
      obtain rfl : L' = L := Option.some.inj (h2.symm.trans hL)
      exact own _ (List.getElem?_eq_some_iff.1 h3).1
    · refine whereIs_kept a.L.check.frame H.next (by rw [H.groups, H.shape])
        (by rw [H.kept, H.shape, H.link]) (L := L') (m := m) (by rw [H.shape]; exact h2) h3
        (by rw [H.link]; omega) (by rw [H.link]; exact h4) (by rw [H.link, H.shape]; omega)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.frameFinds_of
