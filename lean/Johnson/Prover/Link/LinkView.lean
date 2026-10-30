-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkView.lean: THE ROUNDS OF THE FRAME's VIEW AT linkNext ARE linkAll's ROUNDS.
Statement and proof. The frame (Johnson/Prover/Link/LinkFrame.lean) makes the view's rounds of a
function of the draws so far (rvOf); the laws of this folder speak of all rounds at a whole family
of draws (linkAll, LinkAll.lean). Here the two are one list.

  drawsOf Ds     a list of draws as a function of the round's number
  rvOf_link      as many draws as declared rounds, and as many as linkAll's rounds · each declared
                 round's items, the roots apart, are the sorts that linkAll shows in it (a public
                 list: linkAll_items, LinkItems.lean)
                 ⟹ rvOf ds 0 [] linkNext Ds = (linkAll at drawsOf Ds).rs

By: rvOf_fits (the frame's) · linkNext_at (LinkCausal.lean) · linkAll_drawn (LinkShape.lean).
Not shown here. The view's opened columns. That a plan declares these items. Nothing on a
decision, on soundness or on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15)
open TypedOracleCompiler.Run.PQ (RD)

/-- A list of draws as a function of the round's number. -/
def drawsOf (Ds : List Fmt.Drawn) : ℕ → Fmt.Drawn := fun j => Ds.getD j ⟨[], [], [], none⟩

theorem length_rvOf (next : ℕ → List Fmt.Drawn → MsgV) : ∀ (ds : List RD) (i : ℕ)
    (hist Ds : List Fmt.Drawn), Ds.length = ds.length → (rvOf ds i hist next Ds).length = ds.length
  | [], _, _, _, _ => rfl
  | _ :: _, _, _, [], h => by cases h
  | _ :: ds, i, hist, D :: Ds, h =>
    congrArg (· + 1) (length_rvOf next ds (i + 1) (hist ++ [D]) Ds (Nat.succ.inj h))

variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins)

/-- **The rounds of the frame's view at linkNext are linkAll's rounds.** -/
theorem rvOf_link (ds : List RD) (Ds : List Fmt.Drawn) (hl : Ds.length = ds.length)
    (hn : (linkAll P S t X C (drawsOf Ds)).rs.length = ds.length)
    (hi : ds.map (fun d => d.items.filter (· != .root)) =
      (linkAll P S t X C (drawsOf Ds)).rs.map sortsOf) :
    rvOf ds 0 [] (linkNext P S t X C) Ds = (linkAll P S t X C (drawsOf Ds)).rs := by
  refine List.ext_getElem? fun j => ?_
  by_cases hj : j < ds.length
  · obtain ⟨d, hd⟩ : ∃ d, ds[j]? = some d := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨D, hD⟩ : ∃ D, Ds[j]? = some D := ⟨_, List.getElem?_eq_getElem (hl ▸ hj)⟩
    obtain ⟨r, hr⟩ : ∃ r, (linkAll P S t X C (drawsOf Ds)).rs[j]? = some r :=
      ⟨_, List.getElem?_eq_getElem (hn ▸ hj)⟩
    have hv : (linkNext P S t X C (0 + j) ([] ++ Ds.take j)).vals = r.vals := by
      rw [Nat.zero_add, List.nil_append, (linkNext_at P S t X C Ds j).1]
      show (((linkAll P S t X C (drawsOf Ds)).rs[j]?).map (·.vals)).getD [] = _
      rw [hr]
      rfl
    have hf : r.vals.map itemOf = d.items.filter (· != .root) := by
      have e := congrArg (·[j]?) hi
      simp only [List.getElem?_map, hd, hr, Option.map_some] at e
      exact (Option.some.inj e).symm
    have hdr : r.drawn = D := by
      rw [linkAll_drawn P S t X C (drawsOf Ds) j r hr]
      show Ds.getD j _ = D
      rw [List.getD_eq_getElem?_getD, hD]
      rfl
    rw [rvOf_fits (linkNext P S t X C) ds 0 [] Ds j d D hd hD (by rw [hv]; exact hf), hv, hr,
      ← hdr]
  · rw [List.getElem?_eq_none (by rw [length_rvOf _ ds 0 [] Ds hl]; omega),
      List.getElem?_eq_none (by rw [hn]; omega)]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.length_rvOf
#print axioms Johnson.Prover.Link.rvOf_link
