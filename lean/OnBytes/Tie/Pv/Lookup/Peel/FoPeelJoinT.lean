-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPeelJoinT.lean.
Two stretches of a file's written rounds behind each other.

A chain of a file has the rounds `uLT C ds`, ds : List RDT (OnBytes/Maker/Trees.lean). A routine
of the verifier reads a stretch of them. This file says that the shape, a transcript, the view's
rounds and the tests of work of a joined list ds ++ es are made of those of ds and of es. For
rounds with at most one tree the same is in OnBytes/Slice/Unfold.lean (`joinT`, `uL_append`,
`joinT_heq`) and OnBytes/Slice/WrittenView.lean (`rvSL_joinT`). No protocol occurs here.

Main names.
 * `uLT_append`: uLT C (ds ++ es) = uLT C ds ++ uLT C es.
 * `joinR C ds es τ σ`: two written transcripts as one of the joined list. `joinR_heq`: it is the
   library's Tr.app τ σ. `toJoin`: a transcript of the two shapes in a row, as one of the joined
   list; `toJoin_app`: toJoin C ds es (Tr.app τ σ) = joinR C ds es τ σ.
 * `fstR`, `sndR`, `joinR_split`: every transcript of the joined list is the join of its two parts.
 * `rvT_join`, `rvT_app`: the view's rounds are those of the parts in a row.
 * `passT_join`, `passT_app`: all tests of work pass if and only if they pass in both parts.
 * `rvT_length`: a view has as many rounds as the list.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Maker.Trees

set_option autoImplicit false

namespace Fo.Peel
open Iop Run Run.PQ OnBytes.Maker

variable (C : CK)

/-- The shape of a joined list of rounds is the two shapes joined. -/
theorem uLT_append : ∀ ds es : List RDT, uLT C (ds ++ es) = uLT C ds ++ uLT C es
  | [], _ => rfl
  | d :: ds, es => congrArg ((roundT C d).up :: ·) (uLT_append ds es)

/-- Two written transcripts, joined, as a transcript of the joined list of rounds. -/
def joinR : (ds es : List RDT) → Tr (uLT C ds) → Tr (uLT C es) → Tr (uLT C (ds ++ es))
  | [], _, _, σ => σ
  | _ :: ds, es, (m, c, τ), σ => (m, c, joinR ds es τ σ)

theorem heq_consR {r : Round} {s t : Shape} (h : s = t) (m : r.Msg) (c : r.Chal) (u : Tr s)
    (v : Tr t) (huv : HEq u v) : HEq ((m, c, u) : Tr (r :: s)) ((m, c, v) : Tr (r :: t)) := by
  subst h
  rw [eq_of_heq huv]

/-- The joined transcript is the library's. -/
theorem joinR_heq : ∀ (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)),
    HEq (joinR C ds es τ σ) (Tr.app τ σ)
  | [], _, _, _ => HEq.rfl
  | _ :: ds, es, (m, c, τ), σ => heq_consR (uLT_append C ds es) m c _ _ (joinR_heq ds es τ σ)

/-- A transcript of the two shapes in a row, as a transcript of the joined list. -/
def toJoin (ds es : List RDT) (x : Tr (uLT C ds ++ uLT C es)) : Tr (uLT C (ds ++ es)) :=
  cast (congrArg Iop.Tr (uLT_append C ds es).symm) x

theorem toJoin_app (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)) :
    toJoin C ds es (Tr.app τ σ) = joinR C ds es τ σ :=
  eq_of_heq ((cast_heq _ _).trans (joinR_heq C ds es τ σ).symm)

/-- The first part of a transcript of the joined list. -/
def fstR : (ds es : List RDT) → Tr (uLT C (ds ++ es)) → Tr (uLT C ds)
  | [], _, _ => ()
  | _ :: ds, es, (m, c, τ) => (m, c, fstR ds es τ)

/-- The second part. -/
def sndR : (ds es : List RDT) → Tr (uLT C (ds ++ es)) → Tr (uLT C es)
  | [], _, τ => τ
  | _ :: ds, es, (_, _, τ) => sndR ds es τ

theorem joinR_split : ∀ (ds es : List RDT) (τ : Tr (uLT C (ds ++ es))),
    joinR C ds es (fstR C ds es τ) (sndR C ds es τ) = τ
  | [], _, _ => rfl
  | _ :: ds, es, (m, c, τ) => congrArg (fun x => (m, c, x)) (joinR_split ds es τ)

theorem fstR_join : ∀ (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)),
    fstR C ds es (joinR C ds es τ σ) = τ
  | [], _, (), _ => rfl
  | _ :: ds, es, (m, c, τ), σ => congrArg (fun x => (m, c, x)) (fstR_join ds es τ σ)

theorem sndR_join : ∀ (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)),
    sndR C ds es (joinR C ds es τ σ) = σ
  | [], _, _, _ => rfl
  | _ :: ds, es, (_, _, τ), σ => sndR_join ds es τ σ

/-- The rounds of a joined transcript, as a view holds them. -/
theorem rvT_join : ∀ (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)),
    rvT C (ds ++ es) (joinR C ds es τ σ) = rvT C ds τ ++ rvT C es σ
  | [], _, _, _ => rfl
  | d :: ds, es, (m, c, τ), σ =>
    congrArg (rvT C [d] (m, c, ()) ++ ·) (rvT_join ds es τ σ)

theorem rvT_app (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)) :
    rvT C (ds ++ es) (toJoin C ds es (Tr.app τ σ)) = rvT C ds τ ++ rvT C es σ := by
  rw [toJoin_app, rvT_join]

/-- The tests of work of a joined transcript. -/
theorem passT_join : ∀ (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)),
    passT C (ds ++ es) (rhoT C (ds ++ es) (joinR C ds es τ σ)) =
      (passT C ds (rhoT C ds τ) && passT C es (rhoT C es σ))
  | [], _, _, _ => rfl
  | d :: ds, es, (_, c, τ), σ => by
    show (GChal.pass (b := d.entry.work) c &&
        passT C (ds ++ es) (rhoT C (ds ++ es) (joinR C ds es τ σ))) =
      ((GChal.pass (b := d.entry.work) c && passT C ds (rhoT C ds τ)) &&
        passT C es (rhoT C es σ))
    rw [passT_join ds es τ σ, Bool.and_assoc]

theorem passT_app (ds es : List RDT) (τ : Tr (uLT C ds)) (σ : Tr (uLT C es)) :
    passT C (ds ++ es) (rhoT C (ds ++ es) (toJoin C ds es (Tr.app τ σ))) =
      (passT C ds (rhoT C ds τ) && passT C es (rhoT C es σ)) := by
  rw [toJoin_app, passT_join]

/-- A view has as many rounds as the list. -/
theorem rvT_length : ∀ (ds : List RDT) (τ : Tr (uLT C ds)), (rvT C ds τ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => congrArg (· + 1) (rvT_length ds τ)

end Fo.Peel
