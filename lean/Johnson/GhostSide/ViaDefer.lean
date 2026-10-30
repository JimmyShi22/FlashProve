-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/GhostSide/ViaDefer.lean: a translation of queries and the run in which some queries are
deferred. Definitions, lemmas and proofs. Generic in the family of oracles: no scheme occurs here.
This file states no goal of the release. A device of a proof.

Rom/Via.lean shows that an algorithm translated by a bijection φ of the queries, run on a lazily
sampled table, is the algorithm itself run on the translated table (OComp.runLazy_via). Here the
like for the run with a table and a log (OComp.runDefer, Rom/Handle/Defs.lean), in which the queries
that a mark names get fresh answers that are logged and not written; and for writing a log into a
table (Table.lay).

Main names (namespace Rom).
  ReadsBack φ τ    τ reads a log's entry at the image of a point back as the entry at the point.
  MarksVia φ mk mk'   mk' marks the image of a point just when mk marks the point.
  lazyAnswer_img   a lazy answer at the image of a point, translated.
  OComp.runDefer_via   the translated algorithm under mk', with table and log translated at the end,
                   is the algorithm under mk from the translated table and log.
  Table.via_lay1, Table.via_lay   to write a log and then translate is to translate and then write
                   the translated log.
  Table.via_via    translating there and back gives the table.
The proofs follow those of OComp.runLazy_via and lazyAnswer_via (Rom/Via.lean).
Terms: lean/GLOSSARY.md.

-/
import Rom.Via
import Rom.Handle.Defs

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob Via

variable {S : OSpec} {α : Type}

/-- τ reads a log's entry at the image of a point back as the entry at the point. -/
def ReadsBack (φ : QMap S) (τ : QA S → QA S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o) (r : S.Rng (φ o q).1),
    τ ⟨(φ o q).1, (φ o q).2.1, r⟩ = ⟨o, q, (φ o q).2.2 r⟩

/-- mk' marks the image of a point just when mk marks the point. -/
def MarksVia (φ : QMap S) (mk mk' : Mark S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o), mk' (φ o q).1 (φ o q).2.1 = mk o q

/-- A lazy answer at the image of a point, translated, is a lazy answer of the translated table at
the point. -/
theorem lazyAnswer_img {φ ψ : QMap S} (h : QMap.Inv φ ψ) (T : Table S) (o : S.ι) (q : S.Dom o) :
    (lazyAnswer T (φ o q).1 (φ o q).2.1).map (fun p => ((φ o q).2.2 p.1, Table.via φ p.2)) =
      lazyAnswer (Table.via φ T) o q := by
  cases hT : T (φ o q).1 (φ o q).2.1 with
  | some r =>
    have hV : Table.via φ T o q = some ((φ o q).2.2 r) := by
      show (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
      rw [hT]
      rfl
    rw [lazy_some hT, lazy_some hV, PMF.pure_map]
  | none =>
    have hV : Table.via φ T o q = none := by
      show (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
      rw [hT]
      rfl
    rw [lazy_none hT, lazy_none hV, PMF.map_comp, ← map_unif_rng h o q, PMF.map_comp]
    refine congrArg (fun f => PMF.map f (PMF.uniformOfFintype (S.Rng (φ o q).1)))
      (funext fun r => ?_)
    show ((φ o q).2.2 r, Table.via φ (T.set (φ o q).1 (φ o q).2.1 r)) =
      ((φ o q).2.2 r, (Table.via φ T).set o q ((φ o q).2.2 r))
    rw [via_set h]

/-- The translated algorithm, run with deferred queries. -/
theorem OComp.runDefer_via {φ ψ : QMap S} (h : QMap.Inv φ ψ) {τ : QA S → QA S}
    (hτ : ReadsBack φ τ) {mk mk' : Mark S} (hm : MarksVia φ mk mk') :
    ∀ (c : OComp S α) (T : Table S) (lg : Trace S),
      ((c.via φ).runDefer mk' T lg).map (fun x => (x.1, Table.via φ x.2.1, x.2.2.map τ)) =
        c.runDefer mk (Table.via φ T) (lg.map τ)
  | .pure a, T, lg => PMF.pure_map _ _
  | .sample n k, T, lg => by
      show ((unif (Fin (n + 1))).bind fun r => ((k r).via φ).runDefer mk' T lg).map _ =
        (unif (Fin (n + 1))).bind fun r => (k r).runDefer mk (Table.via φ T) (lg.map τ)
      rw [PMF.map_bind]
      exact congrArg (unif (Fin (n + 1))).bind
        (funext fun r => OComp.runDefer_via h hτ hm (k r) T lg)
  | .query o q k, T, lg => by
      show ((Handler.defer mk' Handler.lazy (T, lg) (φ o q).1 (φ o q).2.1).bind fun p =>
          ((k ((φ o q).2.2 p.1)).via φ).interp (Handler.defer mk' Handler.lazy) p.2).map _ =
        (Handler.defer mk Handler.lazy (Table.via φ T, lg.map τ) o q).bind fun p =>
          (k p.1).interp (Handler.defer mk Handler.lazy) p.2
      rw [PMF.map_bind]
      cases hmk : mk o q with
      | true =>
        have e1 : Handler.defer mk' Handler.lazy (T, lg) (φ o q).1 (φ o q).2.1 =
            (unif (S.Rng (φ o q).1)).map fun r =>
              (r, (T, lg ++ [⟨(φ o q).1, (φ o q).2.1, r⟩])) := if_pos ((hm o q).trans hmk)
        have e2 : Handler.defer mk Handler.lazy (Table.via φ T, lg.map τ) o q =
            (unif (S.Rng o)).map fun r => (r, (Table.via φ T, lg.map τ ++ [⟨o, q, r⟩])) :=
          if_pos hmk
        rw [e1, e2, PMF.bind_map, PMF.bind_map, ← bind_unif_via h o q]
        refine congrArg (PMF.uniformOfFintype (S.Rng (φ o q).1)).bind (funext fun r => ?_)
        have h0 := OComp.runDefer_via h hτ hm (k ((φ o q).2.2 r)) T
          (lg ++ [⟨(φ o q).1, (φ o q).2.1, r⟩])
        rw [List.map_append, List.map_cons, List.map_nil, hτ] at h0
        exact h0
      | false =>
        have hn : ¬ mk' (φ o q).1 (φ o q).2.1 = true := by
          rw [hm o q, hmk]
          exact Bool.false_ne_true
        have hn' : ¬ mk o q = true := by
          rw [hmk]
          exact Bool.false_ne_true
        have e1 : Handler.defer mk' Handler.lazy (T, lg) (φ o q).1 (φ o q).2.1 =
            (lazyAnswer T (φ o q).1 (φ o q).2.1).map fun p => (p.1, (p.2, lg)) := if_neg hn
        have e2 : Handler.defer mk Handler.lazy (Table.via φ T, lg.map τ) o q =
            (lazyAnswer (Table.via φ T) o q).map fun p => (p.1, (p.2, lg.map τ)) := if_neg hn'
        rw [e1, e2, PMF.bind_map, PMF.bind_map, ← lazyAnswer_img h T o q, PMF.bind_map]
        refine congrArg (lazyAnswer T (φ o q).1 (φ o q).2.1).bind (funext fun p => ?_)
        exact OComp.runDefer_via h hτ hm (k ((φ o q).2.2 p.1)) p.2 lg

/-- One entry: to write it where the table is empty and then translate is to translate and then
write the translated entry where the table is empty. -/
theorem Table.via_lay1 {φ ψ : QMap S} (h : QMap.Inv φ ψ) (T : Table S) (o : S.ι) (q : S.Dom o)
    (r : S.Rng (φ o q).1) :
    Table.via φ (T.lay1 (φ o q).1 (φ o q).2.1 r) =
      (Table.via φ T).lay1 o q ((φ o q).2.2 r) := by
  cases hT : T (φ o q).1 (φ o q).2.1 with
  | none =>
    have hV : Table.via φ T o q = none := by
      show (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
      rw [hT]
      rfl
    simp only [Table.lay1, hT, hV]
    exact via_set h T o q r
  | some r₀ =>
    have hV : Table.via φ T o q = some ((φ o q).2.2 r₀) := by
      show (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = _
      rw [hT]
      rfl
    simp only [Table.lay1, hT, hV]

/-- To write a log and then translate is to translate and then write the translated log. -/
theorem Table.via_lay {φ ψ : QMap S} (h : QMap.Perm φ ψ) {τ : QA S → QA S} (hτ : ReadsBack φ τ) :
    ∀ (lg : Trace S) (T : Table S), Table.via φ (T.lay lg) = (Table.via φ T).lay (lg.map τ)
  | [], _ => rfl
  | e :: l, T => by
    obtain ⟨o', q', r'⟩ := e
    obtain ⟨b, hb, -, -⟩ := h.right o' q'
    have key : ∀ z : Σ o₁ : S.ι, S.Dom o₁ × (S.Rng o₁ → S.Rng (ψ o' q').1),
        φ (ψ o' q').1 (ψ o' q').2.1 = z → ∀ r : S.Rng z.1,
          τ ⟨z.1, z.2.1, r⟩ = ⟨(ψ o' q').1, (ψ o' q').2.1, z.2.2 r⟩ ∧
          Table.via φ (T.lay1 z.1 z.2.1 r) =
            (Table.via φ T).lay1 (ψ o' q').1 (ψ o' q').2.1 (z.2.2 r) := by
      rintro z rfl r
      exact ⟨hτ _ _ r, Table.via_lay1 h.left T _ _ r⟩
    obtain ⟨k1, k2⟩ := key ⟨o', q', b⟩ hb r'
    show Table.via φ ((T.lay1 o' q' r').lay l) =
      (Table.via φ T).lay (τ ⟨o', q', r'⟩ :: l.map τ)
    rw [Table.via_lay h hτ l, k1, k2]
    rfl

/-- Translating there and back gives the table. -/
theorem Table.via_via {φ ψ : QMap S} (h : QMap.Perm φ ψ) (T : Table S) :
    Table.via φ (Table.via ψ T) = T := by
  funext o q
  obtain ⟨b, hb, h1, -⟩ := h.left o q
  show ((Table.via ψ T) (φ o q).1 (φ o q).2.1).map (φ o q).2.2 = T o q
  rw [(at_back h.right T (φ o q).1 (φ o q).2.1 ⟨o, q, b⟩ hb).1]
  show ((T o q).map b).map (φ o q).2.2 = T o q
  cases T o q with
  | none => rfl
  | some r =>
    show some ((φ o q).2.2 (b r)) = some r
    rw [h1]

end Rom

#print axioms Rom.OComp.runDefer_via
#print axioms Rom.Table.via_lay
#print axioms Rom.Table.via_via
