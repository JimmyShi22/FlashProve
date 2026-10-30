-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Via/Bridge.lean: the kind "lookup" (K3): the hearing on a view's rounds
(`messagesV`, Johnson/Desc/First/Look/Via/Rounds.lean) against the general text on a tape
(`messagesG`, Johnson/Desc/First/Look/K3LookupGeneral.lean). Theorems.

Main theorems:
  `ties_messages`: the two go together (Johnson/Top/H/K3Via/Ties.lean), piece by piece, in the order
    of the two texts' lines.
  `hearV_flRun`: where hearV says yes, the strict tape of the rounds is made at the entries `esMsg
    f`, and the general text says yes on it, takes all of it, and leaves the same ledger and
    `toHeardG` of what hearV heard: as machine words.

Premises: (1) `(esMsg f).all staticT`: the strict reading's tests that read the entry alone, at the
hearing's own entries: public, a function of the face; no view is read. (2) None on words. Face.ok
is asked by hearV itself; of it the proof spends that each level's order has as many members as the
level has variables.
`esMsg f` is written as the binds lay it, one list behind the other. That it is `entriesV f`
(Johnson/Desc/First/Look/Via/Rounds.lean), and that the strict maker does not read an entry's work
bits, stand in Johnson/Top/H/K3Via/BridgeEntries.lean.

Limits. One way. Not here: from messagesG at faceOf h to K3.lean's messages h
(Johnson/Top/H/K3Via/BridgeProof.lean). A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.TiesLevel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc eqTab orderDefault)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Heard callOf opts ReadsFirst)
open VerifiableInference.Desc.First.Prod (Whole wholeStandIn)
open VerifiableInference.Desc.First.Tape (tapeT flRun)

/-! ## Two flat steps for one piece -/

theorem Ties.bindTwo {α β β' γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {es1 es2 : List Fmt.Entry} {x : Hr α}
    {y1 : Fl β'} {y2 : β' → Fl β} {f : α → Hr γ} {g : β → Fl δ} (h1 : Ties R es1 x (y1 >>= y2))
    (h2 : ∀ a b, R a b → Ties S es2 (f a) (g b)) :
      Ties S (es1 ++ es2) (x >>= f) (y1 >>= fun p => y2 p >>= g) := by
  have e : (y1 >>= fun p => y2 p >>= g) = ((y1 >>= y2) >>= g) := (bind_assoc y1 y2 g).symm
  rw [e]
  exact Ties.bind h1 h2

/-- A draw or none, then one text for both: as Lean lays «let x ← if c then … else …» (a join
point). -/
theorem Ties.jp {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {e1 e2 rest : List Fmt.Entry}
    (c : Bool)
    {x1 x2 : Hr α} {y1 y2 : Fl β} {jv : α → Hr γ} {jg : β → Fl δ} (h1 : Ties R e1 x1 y1)
      (h2 : Ties R e2 x2 y2)
    (hj : ∀ a b, R a b → Ties S rest (jv a) (jg b)) :
    Ties S ((if c then e1 else e2) ++ rest) (if c then x1 >>= jv else x2 >>= jv)
      (if c then y1 >>= jg else y2 >>= jg) := by
  cases c with
  | true => exact Ties.bind h1 hj
  | false => exact Ties.bind h2 hj

/-! ## A flat text run off the strict tape -/

theorem flRun_mk {α : Type} {rule : First.Tape.TapeRule} {f : Fl α} {es : List Fmt.Entry}
    {F G : Fork} {rs : List Fmt.RoundView}
    {t : Tape} {a : α} (h1 : tapeT rule rs es = some t) (h2 : f F t = some (a, G, [])) :
    flRun rule f es F rs = some (a, G) := by
  unfold First.Tape.flRun
  simp only [h1, h2]

theorem flRun_some {α : Type} {rule : First.Tape.TapeRule} {f : Fl α} {es : List Fmt.Entry}
    {F G : Fork}
    {rs : List Fmt.RoundView} {a : α} (h : flRun rule f es F rs = some (a, G)) :
    ∃ t, tapeT rule rs es = some t ∧ f F t = some (a, G, []) := by
  unfold First.Tape.flRun at h
  cases hT : tapeT rule rs es with
  | none => simp [hT] at h
  | some t =>
    cases hf : f F t with
    | none => simp [hT, hf] at h
    | some x =>
      obtain ⟨b, G0, rest⟩ := x
      cases rest with
      | cons _ _ => simp [hT, hf] at h
      | nil =>
        simp only [hT, hf, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨t, rfl, hf⟩

/-! ## The end terms read their first values alone -/

theorem reads33 (a : E) : ReadsFirst 3 fun v =>
    subE (v.getD 0 zeroE)
      (mulE a (mulE (mulE (v.getD 1 zeroE) (v.getD 1 zeroE)) (v.getD 2 zeroE))) := by
  intro l l' h
  show subE (l.getD 0 zeroE) (mulE a
    (mulE (mulE (l.getD 1 zeroE) (l.getD 1 zeroE)) (l.getD 2 zeroE))) =
    subE (l'.getD 0 zeroE)
      (mulE a (mulE (mulE (l'.getD 1 zeroE) (l'.getD 1 zeroE)) (l'.getD 2 zeroE)))
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega)]

theorem reads32 : ReadsFirst 2 fun v =>
    mulE (mulE (v.getD 0 zeroE) (v.getD 0 zeroE)) (v.getD 1 zeroE) := by
  intro l l' h
  show mulE (mulE (l.getD 0 zeroE) (l.getD 0 zeroE)) (l.getD 1 zeroE) =
    mulE (mulE (l'.getD 0 zeroE) (l'.getD 0 zeroE)) (l'.getD 1 zeroE)
  rw [h 0 (by omega), h 1 (by omega)]

theorem reads11 : ReadsFirst 1 fun x =>
    subE (mulE (x.getD 0 zeroE) (x.getD 0 zeroE)) (x.getD 0 zeroE) := by
  intro l l' h
  show subE (mulE (l.getD 0 zeroE) (l.getD 0 zeroE)) (l.getD 0 zeroE) =
    subE (mulE (l'.getD 0 zeroE) (l'.getD 0 zeroE)) (l'.getD 0 zeroE)
  rw [h 0 (by omega)]

/-! ## The tie of the two sides' roots -/

def tieE (w : Nat) : List Fmt.Entry :=
  sumE 0 3 3 ++ ((List.range (w - 2)).flatMap (fun _ => sumE 0 3 2 ++ []) ++ [])

theorem ties_tie (w : Nat) (a : E) : Ties (fun x y => y = x) (tieE w) (tieV w a) (tieG w a) := by
  unfold tieV tieG tieE
  refine Ties.bind (ties_sum _ [] 0 3 3 _ rfl (reads33 a)) fun x x' hx => ?_
  subst hx
  refine Ties.bind (Ties.fold (R := fun (s s' : Array Aff × Nat × Array Nat) => s' = s)
    (fun _ => sumE 0 3 2 ++ []) _ _
    (fun _ s s' hs => ?_) _ _ _ rfl) fun s s' hs => ?_
  · subst hs
    refine Ties.bind (ties_sum _ [] 0 3 2 _ rfl reads32) fun y y' hy => ?_
    subst hy
    exact Ties.pure rfl
  · subst hs
    exact Ties.pure rfl

/-! ## From the product of the parts' roots to each -/

def partsE : Nat → List Fmt.Entry
  | 0 => []
  | n + 1 => sumE 0 2 2 ++ (partsE n ++ [])

theorem ties_parts : ∀ (n : Nat) (rows : Array Aff) (C : Aff),
    Ties (fun (x y : Array Aff × List Aff) => y = x ∧ x.2.length = n + 1) (partsE n)
      (partsV n rows C) (partsG n rows C)
  | 0, rows, C => Ties.pure (a := (rows, [C])) (b := (rows, [C])) ⟨rfl, rfl⟩
  | n + 1, rows, C => by
    unfold partsV partsG partsE
    refine Ties.bind (ties_sum C [] 0 2 2 _ rfl levelEnd_reads) fun w w' hw => ?_
    subst hw
    refine Ties.bind (ties_parts n _ _) fun x x' hx => ?_
    obtain ⟨hx1, hx2⟩ := hx
    subst hx1
    exact Ties.pure ⟨rfl, by simpa using hx2⟩

/-! ## The parts' key trees -/

def keysE : List (Nat × Nat) → List Fmt.Entry
  | [] => []
  | x :: xs => runE 0 x.1 ++ (keysE xs ++ [])

theorem ties_keys (f : Face) : ∀ (xs : List (Nat × Nat)) (Cs : List Aff) (rows : Array Aff),
    Cs.length = xs.length →
    (∀ x ∈ xs, ∀ i, i < x.1 → (f.orders x.2 (0 + i)).length = 0 + i) →
    Ties (fun (x y : Array Aff × List (Array E × Aff)) => y = x) (keysE xs) (keysV f xs Cs rows)
      (keysG f xs Cs rows)
  | [], [], rows, _, _ => Ties.pure (a := (rows, [])) (b := (rows, [])) rfl
  | x :: xs, C :: Cs, rows, hl, ho => by
    unfold keysV keysG keysE
    refine Ties.bind (ties_run 0 x.1 (f.orders x.2) _ _ rfl (ho x (by simp))) fun k k' hk => ?_
    have hk' : k' = ⟨k.rows, k.point, k.form⟩ := hk
    subst hk'
    refine Ties.bind (ties_keys f xs Cs k.rows (Nat.succ.inj hl)
      (fun y hy => ho y (List.mem_cons_of_mem _ hy)))
      fun y y' hy => ?_
    subst hy
    exact Ties.pure rfl
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-! ## The orders -/

theorem orderDefault_len (m : Nat) : (orderDefault m).length = m := by
  unfold OnBytes.Model.orderDefault
  simp

theorem runOk_len {m0 n zLen : Nat} {orders : Nat → List Nat}
    (h : First.Prod.runOk m0 n zLen orders = true) (i : Nat)
    (hi : i < n) : (orders (m0 + i)).length = m0 + i := by
  unfold First.Prod.runOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have k := h.2 i (List.mem_range.2 hi)
  unfold First.Prod.orderOk at k
  rw [Bool.and_eq_true, Bool.and_eq_true] at k
  exact beq_iff_eq.1 k.1.1

theorem ok_orders {f : Face} (h : f.ok = true) :
    ∀ x ∈ f.parts.zipIdx, ∀ i, i < x.1 → (f.orders x.2 (0 + i)).length = 0 + i := by
  unfold Face.ok at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro x hx i hi
  exact runOk_len (h.2 x hx) i hi

theorem ok_parts {f : Face} (h : f.ok = true) : f.parts ≠ [] := by
  unfold Face.ok at h
  simp only [Bool.and_eq_true] at h
  intro e
  have k := h.1.1.1.1.2
  rw [e] at k
  simp at k

/-! ## The leaves' call -/

/-- The leaves' variables as the flat text has them: a coordinate and a degree. -/
abbrev leafZs (f : Face) (z : Array E) : List (E × Nat) :=
  (List.range (f.mu + f.d)).map fun j => (z.getD j zeroE, if j < f.d then 2 else 1)

/-- The leaves' degrees. -/
abbrev leafDs (f : Face) : List Nat := (List.range (f.mu + f.d)).map fun j =>
    if j < f.d then 2 else 1

theorem leafVars_eq (f : Face) (z : Array E) : leafVars f z = opts (leafZs f z) := by
  unfold leafVars opts leafZs
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  by_cases hj : j < f.d
  · simp [hj]
  · simp [hj]

theorem leafDs_eq (f : Face) (z : Array E) : (leafZs f z).map (·.2) = leafDs f := by
  unfold leafZs leafDs
  rw [List.map_map]
  rfl

theorem toPsc_eq (h : Heard) : toPsc h = h.psc false := by
  have e : weightOf = MaskedSum.Var.weight := by
    funext v
    cases v <;> rfl
  unfold toPsc MaskedSum.Heard.psc
  rw [e]

/-! ## The whole hearing -/

/-- The entries of the lookup's rounds, as the binds lay them. -/
def esMsg (f : Face) : List Fmt.Entry :=
  [] ++ ([] ++
    ([] ++ ([] ++ ((if f.shifted then [drawEntry Model.RoundName.lkpShift.name 1] else []) ++
    ([drawEntry Model.RoundName.lkp.name 1] ++ (tieE f.planes ++ (partsE (f.parts.length - 1) ++
    ([drawEntry Model.RoundName.lkpPlanes.name f.mu] ++
      (keysE f.parts.zipIdx ++ ([] ++ (runE f.mu f.d ++ ([] ++
    (openE (leafDs f) ++ ([drawEntry Model.RoundName.zero.name (f.mu + f.d)] ++
      (sumE (f.mu + f.d) 2 1 ++
    ([] ++ ([] ++ [])))))))))))))))))

/-- A round of draws, with the number drawn. -/
theorem ties_draws' (rn : Model.RoundName) (n : Nat) :
    Ties (fun a b => b = a ∧ a.size = n) [drawEntry rn.name n] (drawsV n) (Fl.point rn n) := by
  intro hs F G rs rest a h
  obtain ⟨u, t, b, q1, q2, q3, q4⟩ := ties_draws rn n hs F G rs rest a h
  obtain ⟨r, -, -, e3, e4, -⟩ := draws_some h
  refine ⟨u, t, b, q1, q2, ⟨q3, ?_⟩, q4⟩
  rw [e3, List.size_toArray, List.length_map]
  exact e4

/-- **The lookup's rounds: the hearing on a view's rounds and the general text on the tape go
together.** -/
theorem ties_messages (f : Face) (hok : f.ok = true) :
    Ties (fun g g' => g' = toHeardG g) (esMsg f) (messagesV f) (messagesG f) := by
  unfold messagesV messagesG esMsg
  refine Ties.bind ties_slot fun _ slot0 e => ?_
  subst e
  refine Ties.bind (ties_owe _) fun _ o1 e => ?_
  subst e
  refine Ties.bind (ties_owe _) fun _ o2 e => ?_
  subst e
  refine Ties.bind (ties_owe _) fun _ o3 e => ?_
  subst e
  refine Ties.jp f.shifted (ties_draw .lkpShift) (Ties.pure (a := zeroE) (b := zeroE) rfl) fun _
    theta e => ?_
  subst e
  refine Ties.bind (ties_draw .lkp) fun _ alpha e => ?_
  subst e
  refine Ties.bind (ties_tie f.planes _) fun _ x e => ?_
  subst e
  obtain ⟨rows, sZ, sG⟩ := x
  refine Ties.bind (ties_parts (f.parts.length - 1) rows (Aff.slot sZ)) fun _ x e => ?_
  obtain ⟨e1, e2⟩ := e
  subst e1
  obtain ⟨rows1, roots⟩ := x
  refine Ties.bind (ties_draws .lkpPlanes f.mu) fun _ y e => ?_
  subst e
  have hroots : roots.length = f.parts.zipIdx.length := by
    have e2' : roots.length = f.parts.length - 1 + 1 := e2
    have hp : 0 < f.parts.length := List.length_pos_iff.2 (ok_parts hok)
    rw [List.length_zipIdx, e2']
    omega
  refine Ties.bind (ties_keys f f.parts.zipIdx roots rows1 hroots (ok_orders hok)) fun _ x e => ?_
  subst e
  obtain ⟨rows2, keys⟩ := x
  refine Ties.bind (ties_must _) fun _ _ _ => ?_
  refine Ties.bind (ties_run f.mu f.d orderDefault _ _ rfl (fun i _ => orderDefault_len _)) fun
    table table' e => ?_
  have e' : table' = ⟨table.rows, table.point, table.form⟩ := e
  subst e'
  refine Ties.bind (ties_must _) fun _ _ _ => ?_
  rw [leafVars_eq]
  refine Ties.bindTwo (ties_open table.form (leafZs f table.point) (leafDs f)
    (leafDs_eq f table.point)) fun leaves x e => ?_
  subst e
  refine Ties.bind (ties_draws' .zero (f.mu + f.d)) fun _ y5 e => ?_
  obtain ⟨e1, e2⟩ := e
  subst e1
  refine Ties.bind (ties_sum _ y5.reverse.toList (f.mu + f.d) 2 1 _
    (by rw [Array.length_toList, Array.size_reverse]; exact e2) reads11) fun bits bits' e => ?_
  subst e
  refine Ties.bind ties_slot fun _ s1 e => ?_
  subst e
  refine Ties.bind (ties_must _) fun _ _ _ => ?_
  refine Ties.pure ?_
  unfold toHeardG
  rw [toPsc_eq]

/-- **Where hearV says yes, the strict tape is made and the general text says yes on it: the same
ledger, the same values.** -/
theorem hearV_flRun {f : Face} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    (hst : (esMsg f).all staticT = true)
    (h : hearV f F rs = some (g, G)) :
      flRun {} (messagesG f) (esMsg f) F rs = some (toHeardG g, G) := by
  unfold hearV at h
  cases hok : f.ok with
  | false =>
    rw [hok] at h
    have h' : (none : Option (HeardV × Fork)) = some (g, G) := h
    cases h'
  | true =>
    rw [hok] at h
    cases hm : messagesV f F rs with
    | none =>
      rw [hm] at h
      have h' : (none : Option (HeardV × Fork)) = some (g, G) := h
      cases h'
    | some y =>
      obtain ⟨g0, G0, rest⟩ := y
      rw [hm] at h
      cases rest with
      | cons _ _ =>
        have h' : (none : Option (HeardV × Fork)) = some (g, G) := h
        cases h'
      | nil =>
        have h' : some (g0, G0) = some (g, G) := h
        cases h'
        obtain ⟨used, t, b, q1, q2, q3, q4⟩ := ties_messages f hok hst F G rs [] g hm
        rw [List.append_nil] at q1
        subst q1 q3
        have q5 := q4 []
        rw [List.append_nil] at q5
        exact flRun_mk q2 q5

end VerifiableInference.Desc.K3

#print axioms VerifiableInference.Desc.K3.ties_messages
#print axioms VerifiableInference.Desc.K3.hearV_flRun
