-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/K2Share/OwnKept.lean: kind K2's own texts hand on the invariant of
Johnson/Goal/Meaning/OwnInv.lean: the switch at its three sorts of place, and the four quiet steps.
Theorems, proved: by the kind's own readings of a yes (link_inv, head_inv, finish_inv) and
the scripts of Johnson/Goal/Meaning/K2Share/RecFronts.lean.

  ctx_kept, k2_ownRel   a yes of the switch's text leaves what ctxOf reads: at a link it writes the
    walk's state of the calls by firstKept, which leaves the rows; at the head it writes kept and
    ids; at the finish sw.
  enterHead_ownRel, enterFin_ownRel   two of the record's own entries.
  headFrontQ_ownRel, headOpenQ_ownRel, finishFrontQ_ownRel, finishBehindQ_ownRel   the four quiet
    steps. AT headOpenQ THE CONTEXT THAT IS LEFT OPEN IS THE WALK's front's VALUE AT THE LETTERS P:
    so it is asked that P.X.arrayOf = A P.l.

Object, letters. Object: decideWith sendByL8 p; the four texts.
Letters: A, lay: free.

What is not claimed. That any letters P meet that premise. Nothing on soundness.
-/
import Johnson.Goal.Meaning.K2Share.RecFronts
import Johnson.Goal.Meaning.OwnInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.Keeps (Whole Fn Decides)
open Meaning.K2 (OwnInv OwnRel SameCtx ctxOf own_of_ctx own_of_quiet quiet_mark ownRel_trans
  unmarked_eq whole_ownC)
open _root_.Tw.K2 (sendByL8)

variable {A : Nat → Array (Nat × String)} {lay : ReqLayout}

/-! ## The switch, at its three sorts of place -/

/-- **A yes of the switch's text leaves what ctxOf reads.** -/
theorem ctx_kept {p : P2} {s s' : S} {rs gs} (h : decideWith sendByL8 p s rs gs = .ok s') :
    SameCtx s s' := by
  cases hp : p.stands with
  | link =>
    obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, L⟩ := link_inv hp h
    rw [L.hOut]
    simp [SameCtx, ctxOf, L.hHere, _root_.Johnson.Desc.First.Walk.firstKept]
  | head =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := head_inv hp h
    rw [H.hOut]
    simp [SameCtx, ctxOf, H.hHere]
  | finish =>
    obtain ⟨r₁, r₂, a, G, w, roots, -, H⟩ := finish_inv hp h
    rw [H.hOut]
    simp [SameCtx, ctxOf, H.hHere]

theorem k2_ownRel {Cl : Type} (p : P2) : Whole (OwnRel A lay) (codeSwitchKind (Cl := Cl) p) :=
  whole_ownC ⟨fun _ _ _ _ h => ctx_kept h, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## The record's own three entries -/

theorem enterHead_ownRel (s : S) (tl : HTailF2) : OwnRel A lay s (s.enterHead tl) := by
  unfold S.enterHead
  split
  · intro I
    refine ⟨I.1, fun x hx => ?_⟩
    obtain rfl : (1, s.check.rows, 0, #[]) = x := Option.some.inj hx
    exact ⟨I.1, fun h0 => absurd rfl h0⟩
  · exact own_of_quiet (quiet_mark s _)

theorem enterFin_ownRel (s : S) : OwnRel A lay s s.enterFin := by
  unfold S.enterFin
  split
  · intro I
    exact ⟨I.1, fun x hx => nomatch hx⟩
  · exact own_of_quiet (quiet_mark s _)

/-! ## The four quiet steps -/

/-- **"H.0.front".** -/
theorem headFrontQ_ownRel (tl : HTailF2) : Fn (OwnRel A lay) (headFrontQ tl) := fun s t h I => by
  unfold headFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨x, hx, h⟩ := ebind h
      obtain ⟨s₁, h1, h⟩ := ebind h
      have I1 : OwnInv A lay s₁ := by
        rw [unmarked_eq h1]
        exact enterHead_ownRel s tl I
      split at h
      · rename_i a ha
        cases h
        refine own_of_ctx ?_ I1
        simp [SameCtx, ctxOf, ha]
      · cases h

/-- **"H.1.quiet"**, where the letters' list of arrays is A at the letters' number. -/
theorem headOpenQ_ownRel (P : HeadPar) (hA : P.X.arrayOf = A P.l) :
    Fn (OwnRel A lay) (headOpenQ P) := fun s t h I => by
  unfold headOpenQ at h
  split at h
  · rename_i a ha
    split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        obtain ⟨⟨st, f, mine⟩, hb, h⟩ := ebind h
        dsimp only at h
        obtain ⟨⟨L, out⟩, hfr, h⟩ := ebind h
        dsimp only at h
        have hL := (_root_.Johnson.Desc.First.Walk.Law.front_ok hfr).2.2.1
        split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · obtain ⟨s₁, h1, h⟩ := ebind h
                split at h
                · rename_i b hb'
                  cases h
                  refine ⟨I.1, fun x hx => ?_⟩
                  obtain rfl : ((if b.opened = true then 2 else 1), L.check.rows, L.link,
                    L.arrayOf) = x := Option.some.inj hx
                  refine ⟨?_, fun _ => ?_⟩
                  · show L.check.rows.layout = lay
                    rw [hL]
                    exact I.1
                  · show L.arrayOf = A L.link
                    rw [hL]
                    exact hA
                · cases h
        · cases h
  · cases h

/-- **"F.0.front".** -/
theorem finishFrontQ_ownRel : Fn (OwnRel A lay) finishFrontQ := fun s t h I => by
  unfold finishFrontQ at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i G x hG hx
        obtain ⟨s₁, h1, h⟩ := ebind h
        have I1 : OwnInv A lay s₁ := by
          rw [unmarked_eq h1]
          exact enterFin_ownRel s I
        split at h
        · rename_i a ha
          cases h
          exact ⟨I1.1, fun x hx => nomatch hx⟩
        · cases h
      · cases h
      · cases h

/-- **"F.0.quiet".** -/
theorem finishBehindQ_ownRel : Fn (OwnRel A lay) finishBehindQ := fun s t h I => by
  unfold finishBehindQ at h
  split at h
  · rename_i a ha
    obtain ⟨m, -, rfl⟩ := Keeps.emap_ok h
    refine own_of_ctx ?_ I
    simp [SameCtx, ctxOf, ha]
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.k2_ownRel
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_ownRel
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_ownRel
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_ownRel
#print axioms VerifiableInference.Desc.First.K2.finishBehindQ_ownRel
