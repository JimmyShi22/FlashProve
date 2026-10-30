-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TapeCut.lean: THE FLAT TAPE OF A WRITTEN TRANSCRIPT, CUT AS THE CHAIN'S MAPS
CUT THE TRANSCRIPT. A kind's text hears the tape `paired ((rvT … τ).map f) es`
(OnBytes/K/Kc/Laws.lean); the chain's maps read the cuts `Maps.trL`, `Maps.trR` of τ
(OnBytes/Flat/KindsRow.lean). Here: what this folder's functions read off the tape at a masked
sumcheck's place are the words `midRs`, `midY`, `midV` (StageView.lean) of the sumcheck's cut.
Definitions, statements and proofs. Lists alone.

  `KeepsWords f`: the map f of a view's rounds leaves a round's items and its drawn elements.
  `tapeW f ds τ es`: the tape. `tapeW_cons`, `tapeW_app`: round by round; along two stretches in a
    row: the first stretch's tape, then the second's on the entries that are left.
  `flat_sent`, `flat_drawn`: the tape's round of a written round holds `sentE` and `drawnE`.
  `mid_ms`, `mid_yr`, `mid_vr`, `mid_rest`: on the tape of the rounds behind a sumcheck's first
    round, whatever follows: `msOf ws` (as many weights as variables' rounds), as pairs, is `midRs`;
    `roundAt w` behind these rounds is `midY` under w; `sentOf` one round further is `midV`; two
    rounds further the tape is what follows.
  `stage_tape`: the same for a whole sumcheck's tape t, with its first round: what that round sent
    and the first word that it drew; `msOf ws (t.drop 1)`; `roundAt w (t.drop (k + 1))`; `sentOf
    (t.drop (k + 2))`; `t.drop (k + 3)`.
  `drawnOf`: what the tape's first round drew.
  `IsTape f ds c t`: t is the tape of the written transcript c over ds, on some entries.
    `IsTape.right`: behind the first stretch's rounds the tape is the second cut's. `IsTape.one`,
    `IsTape.stage`: what is read off it at a single round's place, and at a sumcheck's.

NO ARGUMENT: inductions on the list of written rounds.

Limits. Lists alone: no function's return, no law, no reading in a field. The names, the numbers nz
and rows of the tape's rounds are not spoken of.
-/
import OnBytes.Desc.First.P1.StageView
import OnBytes.Desc.First.P1.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open _root_.Run (ckP)

/-- The map of a view's rounds leaves a round's items and its drawn elements. -/
structure KeepsWords (f : Fmt.RoundView → Fmt.RoundView) : Prop where
  vals : ∀ r, (f r).vals = r.vals
  elems : ∀ r, (f r).drawn.elems = r.drawn.elems

/-- The flat tape of a written transcript. -/
def tapeW (f : Fmt.RoundView → Fmt.RoundView) (ds : List RDT) (τ : Tr (uLT (ckP .two) ds))
    (es : List Fmt.Entry) : Tape :=
  paired ((rvT (ckP .two) ds τ).map f) es

section
variable {f : Fmt.RoundView → Fmt.RoundView}

theorem tapeW_cons (f : Fmt.RoundView → Fmt.RoundView) (d : RDT) (ds : List RDT) (m : (wT d).Msg)
    (c : (wT d).Chal) (τ : Tr (uLT (ckP .two) ds)) (es : List Fmt.Entry) :
    tapeW f (d :: ds) (m, c, τ) es = flatOf (f (rvW d m c)) es.head? :: tapeW f ds τ es.tail := by
  cases es <;> rfl

theorem flat_sent (hf : KeepsWords f) (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (e : Option Fmt.Entry) : (flatOf (f (rvW d m c)) e).sent = sentE d m := by
  show leading (f (rvW d m c)).vals = _
  rw [hf.vals]
  rfl

theorem flat_drawn (hf : KeepsWords f) (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (e : Option Fmt.Entry) : (flatOf (f (rvW d m c)) e).drawn = drawnE d c := by
  show (f (rvW d m c)).drawn.elems.map OnBytes.E.ofTriple = _
  rw [hf.elems]
  rfl

theorem tail_drop {α : Type} (l : List α) (n : ℕ) : l.tail.drop n = l.drop (n + 1) := by
  cases l <;> simp

/-- The tape along two stretches in a row. -/
theorem tapeW_app (f : Fmt.RoundView → Fmt.RoundView) : ∀ (as bs : List RDT)
    (τ : Tr (uLT (ckP .two) (as ++ bs))) (es : List Fmt.Entry),
    tapeW f (as ++ bs) τ es =
      tapeW f as (Maps.trL as bs τ) es ++ tapeW f bs (Maps.trR as bs τ) (es.drop as.length)
  | [], _, _, _ => rfl
  | a :: as, bs, (m, c, τ), es => by
    show tapeW f (a :: (as ++ bs)) (m, c, τ) es =
      tapeW f (a :: as) (m, c, Maps.trL as bs τ) es ++
        tapeW f bs (Maps.trR as bs τ) (es.drop (as.length + 1))
    rw [tapeW_cons, tapeW_cons, tapeW_app f as bs τ es.tail, tail_drop, List.cons_append]

/-! ### The rounds behind a sumcheck's first round -/

variable {dY dV : RDT}

theorem mid_ms (hf : KeepsWords f) : ∀ (vs : List RDT)
    (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV]))) (es : List Fmt.Entry)
    (ws : List OnBytes.Psc.Weight) (more : Tape), ws.length = vs.length →
    (msOf ws (tapeW f (vs ++ [dY, dV]) σ es ++ more)).map (fun m => (m.2.1, m.2.2)) =
      midRs dY dV vs σ
  | [], _, _, [], _, _ => by
    rw [msOf_nil]
    rfl
  | d :: vs, (m, c, σ), es, w :: ws, more, h => by
    show (msOf (w :: ws) (tapeW f (d :: (vs ++ [dY, dV])) (m, c, σ) es ++ more)).map _ =
      (sentE d m, (drawnE d c).headD OnBytes.zeroE) :: midRs dY dV vs σ
    rw [tapeW_cons, List.cons_append, msOf_cons, List.map_cons,
      mid_ms hf vs σ es.tail ws more (Nat.succ.inj h), flat_sent hf, flat_drawn hf]
  | [], _, _, _ :: _, _, h => by simp at h
  | _ :: _, _, _, [], _, h => by simp at h

theorem mid_yr (hf : KeepsWords f) : ∀ (vs : List RDT)
    (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV]))) (es : List Fmt.Entry) (w : OnBytes.Psc.Weight)
    (more : Tape),
    roundAt w ((tapeW f (vs ++ [dY, dV]) σ es ++ more).drop vs.length) =
      (w, (midY dY dV vs σ).1, (midY dY dV vs σ).2)
  | [], (m, c, σ), es, w, more => by
    show roundAt w (tapeW f (dY :: [dV]) (m, c, σ) es ++ more) =
      (w, sentE dY m, (drawnE dY c).headD OnBytes.zeroE)
    rw [tapeW_cons, List.cons_append]
    show (w, (flatOf (f (rvW dY m c)) es.head?).sent,
      (flatOf (f (rvW dY m c)) es.head?).drawn.headD OnBytes.zeroE) = _
    rw [flat_sent hf, flat_drawn hf]
  | d :: vs, (m, c, σ), es, w, more => by
    show roundAt w ((tapeW f (d :: (vs ++ [dY, dV])) (m, c, σ) es ++ more).drop
      (vs.length + 1)) = (w, (midY dY dV vs σ).1, (midY dY dV vs σ).2)
    rw [tapeW_cons, List.cons_append, List.drop_succ_cons]
    exact mid_yr hf vs σ es.tail w more

theorem mid_vr (hf : KeepsWords f) : ∀ (vs : List RDT)
    (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV]))) (es : List Fmt.Entry) (more : Tape),
    sentOf ((tapeW f (vs ++ [dY, dV]) σ es ++ more).drop (vs.length + 1)) = midV dY dV vs σ
  | [], (m, c, m', c', σ), es, more => by
    show sentOf ((tapeW f (dY :: [dV]) (m, c, m', c', σ) es ++ more).drop (0 + 1)) = sentE dV m'
    rw [tapeW_cons, List.cons_append, List.drop_succ_cons, tapeW_cons, List.cons_append]
    show (flatOf (f (rvW dV m' c')) es.tail.head?).sent = _
    rw [flat_sent hf]
  | d :: vs, (m, c, σ), es, more => by
    show sentOf ((tapeW f (d :: (vs ++ [dY, dV])) (m, c, σ) es ++ more).drop
      (vs.length + 1 + 1)) = midV dY dV vs σ
    rw [tapeW_cons, List.cons_append, List.drop_succ_cons]
    exact mid_vr hf vs σ es.tail more

theorem mid_rest (f : Fmt.RoundView → Fmt.RoundView) : ∀ (vs : List RDT)
    (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV]))) (es : List Fmt.Entry) (more : Tape),
    (tapeW f (vs ++ [dY, dV]) σ es ++ more).drop (vs.length + 2) = more
  | [], (m, c, m', c', σ), es, more => by
    show (tapeW f (dY :: [dV]) (m, c, m', c', σ) es ++ more).drop (0 + 1 + 1) = more
    rw [tapeW_cons, List.cons_append, List.drop_succ_cons, tapeW_cons, List.cons_append,
      List.drop_succ_cons]
    rfl
  | d :: vs, (m, c, σ), es, more => by
    show (tapeW f (d :: (vs ++ [dY, dV])) (m, c, σ) es ++ more).drop (vs.length + 2 + 1) = more
    rw [tapeW_cons, List.cons_append, List.drop_succ_cons]
    exact mid_rest f vs σ es.tail more

/-! ### A whole sumcheck -/

/-- **What is read off the tape at a masked sumcheck's place.** -/
theorem stage_tape (hf : KeepsWords f) (dE : RDT) (vs : List RDT) (mE : (wT dE).Msg)
    (cE : (wT dE).Chal) (σ : Tr (uLT (ckP .two) (vs ++ [dY, dV]))) (es : List Fmt.Entry)
    (more : Tape) (ws : List OnBytes.Psc.Weight) (hw : ws.length = vs.length)
    (w : OnBytes.Psc.Weight) {t : Tape}
    (ht : t = tapeW f (dE :: (vs ++ [dY, dV])) (mE, cE, σ) es ++ more) :
    sentOf t = sentE dE mE ∧ tapeEps t = (drawnE dE cE).headD OnBytes.zeroE ∧
      (msOf ws (t.drop 1)).map (fun m => (m.2.1, m.2.2)) = midRs dY dV vs σ ∧
      roundAt w (t.drop (vs.length + 1)) = (w, (midY dY dV vs σ).1, (midY dY dV vs σ).2) ∧
      sentOf (t.drop (vs.length + 2)) = midV dY dV vs σ ∧ t.drop (vs.length + 3) = more := by
  rw [tapeW_cons, List.cons_append] at ht
  subst ht
  refine ⟨flat_sent hf dE mE cE _, ?_, ?_, ?_, ?_, ?_⟩
  · show (flatOf (f (rvW dE mE cE)) es.head?).drawn.headD OnBytes.zeroE = _
    rw [flat_drawn hf]
  · rw [List.drop_succ_cons, List.drop_zero]
    exact mid_ms hf vs σ es.tail ws more hw
  · rw [List.drop_succ_cons]
    exact mid_yr hf vs σ es.tail w more
  · rw [List.drop_succ_cons]
    exact mid_vr hf vs σ es.tail more
  · rw [List.drop_succ_cons]
    exact mid_rest f vs σ es.tail more

/-! ### A tape of a written transcript, on some entries -/

/-- What the tape's first round drew. -/
def drawnOf (t : Tape) : List OnBytes.E := (t.head?.map (·.drawn)).getD []

/-- t is the flat tape of the written transcript c over ds, on some entries. -/
def IsTape (f : Fmt.RoundView → Fmt.RoundView) (ds : List RDT) (c : Tr (uLT (ckP .two) ds)) (t : Tape) : Prop :=
  ∃ es, t = tapeW f ds c es

theorem tapeW_length (f : Fmt.RoundView → Fmt.RoundView) : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds))
    (es : List Fmt.Entry), (tapeW f ds τ es).length = ds.length
  | [], _, _ => rfl
  | d :: ds, (m, c, τ), es => by
    rw [tapeW_cons, List.length_cons, tapeW_length f ds τ es.tail, List.length_cons]

/-- Behind the first stretch's rounds the tape is the second cut's. -/
theorem IsTape.right {as bs : List RDT} {c : Tr (uLT (ckP .two) (as ++ bs))} {t : Tape}
    (h : IsTape f (as ++ bs) c t) : IsTape f bs (Maps.trR as bs c) (t.drop as.length) := by
  obtain ⟨es, rfl⟩ := h
  refine ⟨es.drop as.length, ?_⟩
  have e := drop_length_add (tapeW f as (Maps.trL as bs c) es)
    (tapeW f bs (Maps.trR as bs c) (es.drop as.length)) 0
  rw [tapeW_length, Nat.add_zero, List.drop_zero] at e
  rw [tapeW_app, e]

/-- What is read off the tape at a single round's place. -/
theorem IsTape.one (hf : KeepsWords f) {d : RDT} {bs : List RDT}
    {c : Tr (uLT (ckP .two) ([d] ++ bs))} {t : Tape} (h : IsTape f ([d] ++ bs) c t) :
    sentOf t = sentE d (Maps.trL [d] bs c).1 ∧
      tapeEps t = (drawnE d (Maps.trL [d] bs c).2.1).headD OnBytes.zeroE ∧
      drawnOf t = drawnE d (Maps.trL [d] bs c).2.1 := by
  obtain ⟨es, rfl⟩ := h
  obtain ⟨m, c', σ⟩ := c
  have e : tapeW f ([d] ++ bs) (m, c', σ) es =
      flatOf (f (rvW d m c')) es.head? :: tapeW f bs σ es.tail := tapeW_cons f d bs m c' σ es
  rw [e]
  refine ⟨flat_sent hf d m c' _, ?_, flat_drawn hf d m c' _⟩
  show (flatOf (f (rvW d m c')) es.head?).drawn.headD OnBytes.zeroE = _
  rw [flat_drawn hf]
  rfl

/-- What is read off the tape at a masked sumcheck's place. -/
theorem IsTape.stage (hf : KeepsWords f) {dE : RDT} {vs bs : List RDT}
    {c : Tr (uLT (ckP .two) ((dE :: (vs ++ [dY, dV])) ++ bs))} {t : Tape}
    (h : IsTape f ((dE :: (vs ++ [dY, dV])) ++ bs) c t) (ws : List OnBytes.Psc.Weight)
    (hw : ws.length = vs.length) (w : OnBytes.Psc.Weight) :
    sentOf t = sentE dE (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).1 ∧
      tapeEps t = (drawnE dE (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.1).headD OnBytes.zeroE ∧
      (msOf ws (t.drop 1)).map (fun m => (m.2.1, m.2.2)) =
        midRs dY dV vs (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.2 ∧
      roundAt w (t.drop (vs.length + 1)) =
        (w, (midY dY dV vs (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.2).1,
          (midY dY dV vs (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.2).2) ∧
      sentOf (t.drop (vs.length + 2)) =
        midV dY dV vs (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.2 := by
  obtain ⟨es, rfl⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, _⟩ := stage_tape hf dE vs
    (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).1 (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.1
    (Maps.trL (dE :: (vs ++ [dY, dV])) bs c).2.2 es _ ws hw w
    (tapeW_app f (dE :: (vs ++ [dY, dV])) bs c es)
  exact ⟨a1, a2, a3, a4, a5⟩

end

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.tapeW_app
#print axioms OnBytes.Desc.First.P1.stage_tape
#print axioms OnBytes.Desc.First.P1.IsTape.right
#print axioms OnBytes.Desc.First.P1.IsTape.one
#print axioms OnBytes.Desc.First.P1.IsTape.stage
