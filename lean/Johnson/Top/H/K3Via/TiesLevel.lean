-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/TiesLevel.lean: the kind "lookup" (K3): the hearing on a view's rounds against
the flat text: the grand product on a view's rounds (Johnson/Desc/First/ProdV/Level.lean) against
the grand product on a tape (Johnson/Desc/First/Prod/Level.lean): a level, a turn, a run. Theorems.

How. The level on a view's rounds says yes only where `levelH` does, a text of two pieces of
Johnson/Desc/First/Look/Via/Rounds.lean (sumV, then drawV) with the same value (`level_le`); these
two go together with wholeStandIn and Fl.answer (Johnson/Top/H/K3Via/TiesSum.lean,
Johnson/Top/H/K3Via/Ties.lean); so the level goes together with the one on a tape (`ties_level`). A
turn and a run follow (`ties_turn`, `ties_run`).
Premise, public: a level's order has as many members as the level has variables.

Limits. One way, as `Ties` is. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.TiesSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Heard callOf ReadsFirst whole roundOf)
open VerifiableInference.Desc.First.Prod (Whole wholeStandIn)
open First.ProdV (elementsAlone)

/-! ## A text that says yes only where another does -/

theorem Ties.of_le {α β : Type} {R : α → β → Prop} {es : List Fmt.Entry} {x x' : Hr α} {y : Fl β}
    (hle : ∀ F rs r, x' F rs = some r → x F rs = some r) (h : Ties R es x y) : Ties R es x' y := by
  intro hs F G rs rest a e
  exact h hs F G rs rest a (hle F rs _ e)

/-! ## Lists -/

theorem take_succ_of_drop {α : Type} :
    ∀ (k : Nat) (l : List α) (x : α) (rest : List α), l.drop k = x :: rest →
    l.take (k + 1) = l.take k ++ [x]
  | 0, l, x, rest, h => by
    have h' : l = x :: rest := h
    subst h'
    rfl
  | k + 1, [], x, rest, h => by
    have h' : ([] : List α) = x :: rest := h
    cases h'
  | k + 1, a :: l, x, rest, h => by
    have h' : l.drop k = x :: rest := h
    show a :: l.take (k + 1) = a :: (l.take k ++ [x])
    rw [take_succ_of_drop k l x rest h']

theorem alone_append (a b : List Fmt.RoundView) :
    elementsAlone (a ++ b) = (elementsAlone a && elementsAlone b) := by
  unfold First.ProdV.elementsAlone
  rw [List.all_append]

/-! ## The two pieces return -/

theorem sum_mk {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs : List Fmt.RoundView} {h : Heard}
    {row : Aff} (ha : elementsAlone (rs.take (roundsOf k)) = true)
    (hw : whole C k endTerm F (rs.take (roundsOf k)) = some (h, row, G))
      (hz : isZeroE (h.r.getLastD zeroE) = false) :
    sumV C k endTerm F rs = some ((h, row), G, rs.drop (roundsOf k)) := by
  unfold sumV
  rw [ha, hw]
  show (if isZeroE (h.r.getLastD zeroE) then none else some ((h, row), G, rs.drop (roundsOf k))) = _
  rw [hz]
  rfl

theorem draw_mk {F : Fork} {r : Fmt.RoundView} {rest : List Fmt.RoundView} {s : List E} {xi : E}
    (ha : elementsAlone [r] = true)
    (hr : roundOf 0 1 r = some (s, [xi])) : drawV F (r :: rest) = some (xi, F, rest) := by
  have hd : drawsV 1 F (r :: rest) = some (#[xi], F, rest) := by
    show (if elementsAlone [r] then (roundOf 0 1 r).map (fun x => (x.2.toArray, F, rest)) else
      none) = _
    rw [ha, hr]
    rfl
  unfold drawV
  rw [hd]
  rfl

/-! ## A level -/

/-- The coordinates at which a level's variables are summed, in the order of the rounds. -/
abbrev levelZs (m : Nat) (z : Array E) (order : List Nat) : List E := order.map fun b =>
    z.getD (m - 1 - b) zeroE

/-- A level's end term. -/
abbrev levelEnd : List E → E := fun v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)

theorem levelEnd_reads : ReadsFirst 2 levelEnd := by
  intro l l' h
  show mulE (l.getD 0 zeroE) (l.getD 1 zeroE) = mulE (l'.getD 0 zeroE) (l'.getD 1 zeroE)
  rw [h 0 (by omega), h 1 (by omega)]

theorem levelCall_eq (m : Nat) (z : Array E) (order : List Nat) :
    ({ lead := 0, vs := First.ProdV.levelVars m z order, ends := some First.ProdV.levelEnds } :
      MaskedSum.Call) =
      callOf (levelZs m z order) 2 2 := by
  unfold First.ProdV.levelVars callOf levelZs First.ProdV.levelEnds
  rw [List.map_map]
  rfl

/-- What a level hands back. -/
def outV (m : Nat) (order : List Nat) (h : Heard) (xi : E) (row : Aff) : First.ProdV.LevelOut :=
  { r := First.ProdV.layBack m order (h.r.take m), sL := h.sEnd, sR := h.sEnd + 1, xi := xi,
    row := row }

/-- A level, of two pieces of the hearing. -/
def levelH (m : Nat) (z : Array E) (order : List Nat) (C : Aff) : Hr First.ProdV.LevelOut := do
  let a ← sumV C (callOf (levelZs m z order) 2 2) fun _ v => levelEnd v
  let xi ← drawV
  pure (outV m order a.1 xi a.2)

/-- **Form 5's level says yes only where the two pieces do, with the same value.** -/
theorem level_le {m : Nat} {z : Array E} {order : List Nat} {C : Aff} (hlen : order.length = m)
    (F : Fork)
    (rs : List Fmt.RoundView) (r : First.ProdV.LevelOut × Fork × List Fmt.RoundView)
    (h : First.ProdV.level m z order C F rs = some r) : levelH m z order C F rs = some r := by
  unfold First.ProdV.level at h
  rw [levelCall_eq] at h
  have hn : roundsOf (callOf (levelZs m z order) 2 2) = m + 3 := by
    show (levelZs m z order |>.map fun z => MaskedSum.Var.point z 3).length + 3 = m + 3
    rw [List.length_map, List.length_map, hlen]
  cases ha : elementsAlone (rs.take (m + 4)) with
  | false =>
    rw [ha] at h
    have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h
    cases h'
  | true =>
    rw [ha] at h
    cases hw : whole C (callOf (levelZs m z order) 2 2)
      (fun _ v => mulE (v.getD 0 zeroE) (v.getD 1 zeroE)) F
        (rs.take (m + 3)) with
    | none =>
      rw [hw] at h
      have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h
      cases h'
    | some y =>
      obtain ⟨h0, row, G⟩ := y
      rw [hw] at h
      cases hd : rs.drop (m + 3) with
      | nil =>
        rw [hd] at h
        have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h
        cases h'
      | cons line rest =>
        rw [hd] at h
        have ht : rs.take (m + 4) = rs.take (m + 3) ++ [line] :=
          take_succ_of_drop (m + 3) rs line rest hd
        rw [ht, alone_append, Bool.and_eq_true] at ha
        have h2 : (match roundOf 0 1 line with
          | some (_, [xi]) => if isZeroE (h0.r.getLastD zeroE) then none else some
              (outV m order h0 xi row, G, rest)
          | _ => none) = some r := h
        cases hr : roundOf 0 1 line with
        | none =>
          rw [hr] at h2
          have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h2
          cases h'
        | some sd =>
          obtain ⟨s0, d⟩ := sd
          rw [hr] at h2
          match d, hr, h2 with
          | [], _, h2 =>
            have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h2
            cases h'
          | _ :: _ :: _, _, h2 =>
            have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h2
            cases h'
          | [xi], hr, h2 =>
            have h1 : (if isZeroE (h0.r.getLastD zeroE) then none else some
              (outV m order h0 xi row, G, rest)) =
                some r := h2
            cases hz : isZeroE (h0.r.getLastD zeroE) with
            | true =>
              rw [hz] at h1
              have h' : (none : Option (First.ProdV.LevelOut × Fork × List Fmt.RoundView)) = some r := h1
              cases h'
            | false =>
              rw [hz] at h1
              have h' : some (outV m order h0 xi row, G, rest) = some r := h1
              cases h'
              have k1 : sumV C (callOf (levelZs m z order) 2 2) (fun _ v => levelEnd v) F rs =
                  some ((h0, row), G, line :: rest) := by
                rw [← hd, ← hn]
                exact sum_mk (by rw [hn]; exact ha.1) (by rw [hn]; exact hw) hz
              have k2 : drawV G (line :: rest) = some (xi, G, rest) := draw_mk ha.2 hr
              show Hr.andThen _ _ F rs = _
              unfold Hr.andThen
              rw [k1]
              show Hr.andThen _ _ G (line :: rest) = _
              unfold Hr.andThen
              rw [k2]
              rfl

/-- A level's entries, by its number of variables. -/
def levelE (m : Nat) : List Fmt.Entry :=
    sumE m 2 2 ++ ([drawEntry Model.RoundName.line.name 1] ++ [])

/-- The record of a level on a tape, with the values of the level on a view's rounds. -/
def Ro (o : First.ProdV.LevelOut) (o' : First.Prod.LevelOut) : Prop :=
    o' = ⟨o.r, o.sL, o.sR, o.xi, o.row⟩

/-- **A level.** -/
theorem ties_level (m : Nat) (z : Array E) (order : List Nat) (C : Aff) (hlen : order.length = m) :
    Ties Ro (levelE m) (Hr.of (First.ProdV.level m z order C)) (First.Prod.level m z order C) := by
  refine Ties.of_le (x := levelH m z order C) (level_le hlen) ?_
  unfold levelH First.Prod.level levelE
  refine Ties.bind (ties_sum C (levelZs m z order) m 2 2 levelEnd
    (by rw [List.length_map]; exact hlen) levelEnd_reads)
    fun a w hw => ?_
  subst hw
  refine Ties.bind (ties_draw .line) fun xi xi' hx => ?_
  subst hx
  exact Ties.pure rfl

/-! ## A turn, a run -/

/-- The carried record on a tape, with the values of the one on a view's rounds. -/
def Rc (s : First.ProdV.Carried) (s' : First.Prod.Carried) : Prop := s' = ⟨s.rows, s.point, s.form⟩

theorem turn_eq (order : List Nat) (s : First.ProdV.Carried) (m : Nat) :
    Hr.of (First.ProdV.turn order s m) =
      (Hr.of (First.ProdV.level m s.point order s.form) >>= fun o =>
        (pure ({ rows := s.rows.push o.row, point := (First.ProdV.stepDown o).1,
                 form := (First.ProdV.stepDown o).2 } :
          First.ProdV.Carried) : Hr First.ProdV.Carried)) := by
  funext F rs
  show (First.ProdV.level m s.point order s.form F rs).map _ = Hr.andThen _ _ F rs
  unfold Hr.andThen Hr.of
  cases First.ProdV.level m s.point order s.form F rs with
  | none => rfl
  | some y =>
    obtain ⟨o, G, rest⟩ := y
    rfl

/-- **A turn.** -/
theorem ties_turn (order : List Nat) (s : First.ProdV.Carried) (s' : First.Prod.Carried) (m : Nat)
    (hs : Rc s s')
    (hlen : order.length = m) :
    Ties Rc (levelE m ++ []) (Hr.of (First.ProdV.turn order s m)) (First.Prod.turn order s' m) := by
  have hs' : s' = ⟨s.rows, s.point, s.form⟩ := hs
  subst hs'
  rw [turn_eq]
  unfold First.Prod.turn
  refine Ties.bind (ties_level m s.point order s.form hlen) fun o o' ho => ?_
  have ho' : o' = ⟨o.r, o.sL, o.sR, o.xi, o.row⟩ := ho
  subst ho'
  exact Ties.pure rfl

/-- Form 5's run over a list of levels, as a text that hears. -/
def runL (m0 : Nat) (orders : Nat → List Nat) (l : List Nat) (s : First.ProdV.Carried) :
    Hr First.ProdV.Carried :=
  fun F rs => l.foldlM
    (fun (x : First.ProdV.Carried × Fork × List Fmt.RoundView) i =>
      First.ProdV.turn (orders (m0 + i)) x.1 (m0 + i) x.2.1 x.2.2)
    (s, F, rs)

theorem runL_cons (m0 : Nat) (orders : Nat → List Nat) (i : Nat) (l : List Nat)
    (s : First.ProdV.Carried) :
    runL m0 orders (i :: l) s =
      (Hr.of (First.ProdV.turn (orders (m0 + i)) s (m0 + i)) >>= fun s1 =>
        runL m0 orders l s1) := by
  funext F rs
  show (i :: l).foldlM _ (s, F, rs) = Hr.andThen _ _ F rs
  rw [List.foldlM_cons]
  unfold Hr.andThen Hr.of
  cases First.ProdV.turn (orders (m0 + i)) s (m0 + i) F rs with
  | none => rfl
  | some y =>
    obtain ⟨a, G, rest⟩ := y
    rfl

theorem ties_runL (m0 : Nat) (orders : Nat → List Nat) : ∀ (l : List Nat) (s : First.ProdV.Carried)
    (s' : First.Prod.Carried), Rc s s' → (∀ i ∈ l, (orders (m0 + i)).length = m0 + i) →
    Ties Rc (l.flatMap fun i => levelE (m0 + i) ++ []) (runL m0 orders l s)
      (l.foldlM (fun s i => First.Prod.turn (orders (m0 + i)) s (m0 + i)) s')
  | [], s, s', h, _ => by
    rw [List.foldlM_nil]
    exact Ties.pure (a := s) h
  | i :: l, s, s', h, ho => by
    rw [runL_cons, List.foldlM_cons, List.flatMap_cons]
    exact Ties.bind (ties_turn _ s s' _ h (ho i (by simp)))
      (fun a b hab => ties_runL m0 orders l a b hab (fun j hj => ho j (List.mem_cons_of_mem _ hj)))

/-- A run's entries, by numbers. -/
def runE (m0 n : Nat) : List Fmt.Entry := (List.range n).flatMap fun i => levelE (m0 + i) ++ []

/-- **A run of n levels.** -/
theorem ties_run (m0 n : Nat) (orders : Nat → List Nat) (s : First.ProdV.Carried)
    (s' : First.Prod.Carried) (h : Rc s s')
    (ho : ∀ i, i < n → (orders (m0 + i)).length = m0 + i) :
    Ties Rc (runE m0 n) (Hr.of (First.ProdV.run m0 n orders s)) (First.Prod.run m0 n orders s') :=
  ties_runL m0 orders (List.range n) s s' h (fun i hi => ho i (List.mem_range.1 hi))

end VerifiableInference.Desc.K3
