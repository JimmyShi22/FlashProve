-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/KindsRow.lean: a list of maps (`Maps`, OnBytes/Flat/CarrySMaps.lean) brought to a
chain's own list of written rounds.

Laid along a typed list, the written rounds of a list of maps come out as a row of lists in the
typed list's brackets, some of them empty; and a chain of a file ends in a sealing round that no
typed list has. Here are the two steps from such a list of maps to one over
the chain's own list of rounds: written rounds behind the last typed round are skipped; and the maps
are carried along an equation of lists of written rounds. What is asked of the maps, the bounds on
the written counts and the image go along.

Main names:
  `Maps.thenSkips M es : Maps (ds ++ es) s'`: the rounds es behind M's are skipped; `ok_thenSkips`,
    `held_thenSkips`, `heldN_thenSkips`.
  `Maps.trL`, `Maps.trR`, `view_app`, `pass_app`, `view_thenSkips`: the image of two stretches in a
    row is the two images in a row, of the two parts of the written transcript; the tests of work
    the like; skipped rounds leave the image as it is.
  `Maps.castD e M : Maps ds' s'` for e : ds' = ds; `ok_castD`, `held_castD`, `heldN_castD`.
  `Maps.toChain M es e`: both, for e : ds' = ds ++ es; `ok_toChain`, `held_toChain`,
    `heldN_toChain`.

Limits: the equation of lists is the caller's. A test of work in a skipped round is not looked at.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Flat.CarrySNum

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice
open scoped ENNReal

namespace Maps

/-- The written rounds es behind M's are skipped. -/
def thenSkips : {ds : List RDT} → {s' : Shape} → Maps ds s' → (es : List RDT) → Maps (ds ++ es) s'
  | _, _, .nil, es => skips es
  | _, _, .step M rest, es => .step M (rest.thenSkips es)
  | _, _, .skip d rest, es => .skip d (rest.thenSkips es)

theorem ok_thenSkips : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (es : List RDT), M.OK →
    (M.thenSkips es).OK
  | _, _, .nil, es, _ => ok_skips es
  | _, _, .step _ rest, es, h => ⟨h.1, ok_thenSkips rest es h.2⟩
  | _, _, .skip _ rest, es, h => ok_thenSkips rest es h

theorem held_thenSkips {εs : ℝ≥0∞} : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (es : List RDT) (ε : Err s'), M.Held εs ε → (M.thenSkips es).Held εs ε
  | _, _, .nil, es, _, _ => held_skips εs es
  | _, _, .step _ rest, es, (_, ε), h => ⟨h.1, held_thenSkips rest es ε h.2⟩
  | _, _, .skip _ rest, es, ε, h => held_thenSkips rest es ε h

theorem heldN_thenSkips {k : ℕ} : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s')
    (es : List RDT) (ε : Err s'), M.HeldN k ε → (M.thenSkips es).HeldN k ε
  | _, _, .nil, es, _, _ => heldN_skips k es
  | _, _, .step _ rest, es, (_, ε), h => ⟨h.1, heldN_thenSkips rest es ε h.2⟩
  | _, _, .skip _ rest, es, ε, h => heldN_thenSkips rest es ε h

theorem view_skips : ∀ (es : List RDT) (τ : Tr (uLT (ckP .two) es)), (skips es).view τ = ()
  | [], _ => rfl
  | _ :: es, (_, _, τ) => view_skips es τ

/-! ### the image along two stretches in a row -/

/-- The first stretch's part of a written transcript. -/
def trL : (ds es : List RDT) → Tr (uLT (ckP .two) (ds ++ es)) → Tr (uLT (ckP .two) ds)
  | [], _, _ => ()
  | _ :: ds, es, (m, c, τ) => (m, c, trL ds es τ)

/-- The second stretch's part. -/
def trR : (ds es : List RDT) → Tr (uLT (ckP .two) (ds ++ es)) → Tr (uLT (ckP .two) es)
  | [], _, τ => τ
  | _ :: ds, es, (_, _, τ) => trR ds es τ

/-- The image of two stretches in a row: the two images in a row. -/
theorem view_app : ∀ {ds es : List RDT} {s' t' : Shape} (M : Maps ds s') (N : Maps es t')
    (τ : Tr (uLT (ckP .two) (ds ++ es))),
    (M.app N).view τ = Tr.app (M.view (trL ds es τ)) (N.view (trR ds es τ))
  | _, _, _, _, .nil, _, _ => rfl
  | _, _, _, _, .step (d := d) M rest, N, (m, c, τ) =>
      congrArg (fun z => (M.fm m, M.g (valsOf (toRD d) c), z)) (view_app rest N τ)
  | _, _, _, _, .skip _ rest, N, (_, _, τ) => view_app rest N τ

/-- The tests of work of two stretches in a row. -/
theorem pass_app : ∀ {ds es : List RDT} {s' t' : Shape} (M : Maps ds s') (N : Maps es t')
    (τ : Tr (uLT (ckP .two) (ds ++ es))),
    (M.app N).pass τ = (M.pass (trL ds es τ) && N.pass (trR ds es τ))
  | _, _, _, _, .nil, _, _ => (Bool.true_and _).symm
  | _, _, _, _, .step (d := d) _ rest, N, (_, c, τ) =>
      (congrArg (GChal.pass (b := d.entry.work) c && ·) (pass_app rest N τ)).trans
        (Bool.and_assoc _ _ _).symm
  | _, _, _, _, .skip _ rest, N, (_, _, τ) => pass_app rest N τ

/-- Skipped rounds behind a stretch leave its image as it is. -/
theorem view_thenSkips : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (es : List RDT)
    (τ : Tr (uLT (ckP .two) (ds ++ es))), (M.thenSkips es).view τ = M.view (trL ds es τ)
  | _, _, .nil, es, τ => view_skips es τ
  | _, _, .step (d := d) M rest, es, (m, c, τ) =>
      congrArg (fun z => (M.fm m, M.g (valsOf (toRD d) c), z)) (view_thenSkips rest es τ)
  | _, _, .skip _ rest, es, (_, _, τ) => view_thenSkips rest es τ

variable {ds ds' : List RDT} {s' : Shape}

/-- The maps, carried along an equation of lists of written rounds. -/
def castD (e : ds' = ds) (M : Maps ds s') : Maps ds' s' := e ▸ M

theorem ok_castD (e : ds' = ds) {M : Maps ds s'} (h : M.OK) : (M.castD e).OK := by
  subst e
  exact h

theorem held_castD (e : ds' = ds) {M : Maps ds s'} {εs : ℝ≥0∞} {ε : Err s'} (h : M.Held εs ε) :
    (M.castD e).Held εs ε := by
  subst e
  exact h

theorem heldN_castD (e : ds' = ds) {M : Maps ds s'} {k : ℕ} {ε : Err s'} (h : M.HeldN k ε) :
    (M.castD e).HeldN k ε := by
  subst e
  exact h

/-- **To a chain's own list of rounds**: M's written rounds, then rounds that are skipped. A test of
work in a round of es is not looked at: whoever skips a round that bears work drops its test. -/
def toChain (M : Maps ds s') (es : List RDT) (e : ds' = ds ++ es) : Maps ds' s' :=
  (M.thenSkips es).castD e

theorem ok_toChain {M : Maps ds s'} (es : List RDT) (e : ds' = ds ++ es) (h : M.OK) :
    (M.toChain es e).OK :=
  ok_castD e (ok_thenSkips M es h)

theorem held_toChain {M : Maps ds s'} (es : List RDT) (e : ds' = ds ++ es) {εs : ℝ≥0∞}
    {ε : Err s'} (h : M.Held εs ε) : (M.toChain es e).Held εs ε :=
  held_castD e (held_thenSkips M es ε h)

theorem heldN_toChain {M : Maps ds s'} (es : List RDT) (e : ds' = ds ++ es) {k : ℕ} {ε : Err s'}
    (h : M.HeldN k ε) : (M.toChain es e).HeldN k ε :=
  heldN_castD e (heldN_thenSkips M es ε h)

end Maps

end OnBytes.Flat
