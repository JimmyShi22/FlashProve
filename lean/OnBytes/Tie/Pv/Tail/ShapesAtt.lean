-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/ShapesAtt.lean: the shapes of the tables of attention's sub-proof (of each table
its matrix, the rows in a block and the first entry in the vector of reads) are a term of the
sub-proof's shape; so the tables of every run have the shapes of the dry run on zeros. It does for
attention what ShapesLay.lean and ShapesHead.lean do for the layers and the head.

By the verifier's text (`placeAll`, `add`, OnBytes/Model/AttentionTables.lean) each table is placed
behind those before it, at a matrix, a block and a number of entries that are public numbers of the
shape S. One thing is not public by the text alone: `placeAll` places one table, and later two more,
for each member of the list of the units of the scores, which is heard. By the text of `scores`
(OnBytes/Model/AttentionScores.lean) that list gets one member for each unit of the calls of one
kind, and the list of these units is a plain function of S.

Main names (namespace OnBytes.Tie.Pv.Tail.Closed):
  `nScores S`: the number of these units. `scoreUnits_ret`, `hear_ret`: every success of `hear P`
    returns `nScores P.S` units of the scores. `ret_bind'`, `ret_blk`: two more laws of `Ret`.
  `total`, `place`, `rep`: the entries and the shapes of a list of tables placed one behind the
    other; a list k times.
  `Laid l t t'`: from the state t of the placing to t' exactly the tables l were placed.
  `Lays x l`: every success of the placing routine x, from every state and context, places exactly
    l. Its laws: `lays_bind`, `lays_bind0`, `lays_pure`, `lays_bind_pure`, `lays_lift`, `lays_up`,
    `lays_map`, `lays_forM`, `lays_mapM`, `lays_mapMA`; at the routines: `lays_weights`,
    `lays_getAs`, `lays_add`, `lays_placed`, `lays_total`, `lays_addAs`, `lays_addRow`, `lays_lng`,
    `lays_addLong`.
  `asPart S`, `attAsks S k`, `attShapes S k`: the term, at k units of the scores.
  `LaysF`, `laysF_placeAll`: `placeAll` places `attAsks S scores.size` and returns the list of all
    tables placed.
  `tables_shapes`: every success of `tables`, in a dry run or on a view, lays out tables with the
    shapes `attShapes S scores.size`, in the third vector. No hypothesis but the success.
  `shAt_att`: the dry run on zeros, where it returns, has the shapes `attShapes a.S (nScores a.S)`.
  `run_shapes_att`: at attention's link of a chain whose dry run returns: after every success of
    `hear` at a plan with the link's shape, every success of `tables` at that shape and the heard
    units of the scores: its tables have the shapes `shAt c n`, and they are `funsOf (shAt c n)` at
    their own weights. `att_same`: so `SameShapes (recAt c n) T.funs`.
The hypotheses of the last three: hA: the link's kind is "A"; ha: its record has the plan a; h: the
dry run returns. Besides, in the last two: hS: the plan P of the run has a's shape; hf, hT: the two
successes. The matrices, the planned length, what the lookup stored, the plane claims and the other
heard values of `tables` are free: the shapes read none of them.

Limits: those of ShapesLay.lean, word for word, on the weights, on the link's record, on the first
columns and the drawn matrix. That the list of scores at which the verifier calls `tables` is the
one that `hear` returned is by its text (`run`, OnBytes/Model/Attention.lean), not shown here: hT
names `f.scores`. That `attAsks` is the list of `placeAll` is checked where this file compiles: each
step of `laysF_placeAll` must meet the next piece of the list.

-/
import OnBytes.Tie.Pv.Tail.ShapesHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Closed
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail Cb.Pv.Tail OnBytes.L5
open OnBytes.Attention (PlaceM Placed)

/-! ## The number of the units of the scores -/

/-- The number of the units of the scores: a term of the shape. -/
def nScores (S : Attention.Shape) : Nat :=
  (Attention.unitsOf S Attention.Table.kfd [Attention.Seg.fm, Attention.Seg.fd]).length

/-- One routine after another, where the first one's values have a property. -/
theorem ret_bind' {α β : Type} {P : α → Prop} {Q : β → Prop} {x : SubM α} {f : α → SubM β}
    (hx : Ret P x) (hf : ∀ a, P a → Ret Q (f a)) : Ret Q (x >>= f) := by
  intro F c b F' c' hr
  obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok x f F c _).1 hr
  exact hf a (hx F c a F1 c1 h1) F1 c1 b F' c' h2

/-- Each unit adds one member to the list of scores. -/
theorem scoreUnits_ret (S : Attention.Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × Attention.ACall × Attention.Seg)) (planes : Array Attention.PlaneClaim)
      (stored : Array Attention.Score),
      Ret (fun r : Array Attention.PlaneClaim × Array Attention.Score =>
          r.2.size = stored.size + us.length) (Attention.scoreUnits S zk us planes stored)
  | [], planes, stored => by
    unfold Attention.scoreUnits
    exact ret_pure _ rfl
  | u :: us, planes, stored => by
    unfold Attention.scoreUnits
    refine ret_bind _ _ fun x => ?_
    intro F c r F' c' hr
    have h := scoreUnits_ret S zk us (planes.push x.1) (stored.push x.2) F c r F' c' hr
    rw [h, Array.size_push, List.length_cons]
    omega

/-- Every success of hear has as many units of the scores as the shape says. -/
theorem hear_ret (P : Attention.Plan) :
    Ret (fun f : Attention.First => f.scores.size = nScores P.S) (Attention.hear P) := by
  unfold Attention.hear
  refine ret_bind _ _ fun g => ?_
  refine ret_bind' (P := fun r : Array Attention.PlaneClaim × Array Attention.Score =>
    r.2.size = nScores P.S) ?_ ?_
  · unfold Attention.scores
    refine ret_bind _ _ fun planes => ?_
    intro F c r F' c' hr
    have h := scoreUnits_ret P.S g.zk _ planes #[] F c r F' c' hr
    rw [h]
    exact Nat.zero_add _
  · rintro ⟨planes, scores⟩ h
    refine ret_bind _ _ fun d => ?_
    refine ret_bind _ _ fun x => ?_
    exact ret_pure _ h

/-! ## Lists of tables that are placed one behind the other -/

/-- The entries of a list of tables, each given by its matrix, its rows in a block and its number of
entries. -/
def total : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | a :: l => a.2.2 + total l

/-- Their shapes, from entry p on. -/
def place : List (Nat × Nat × Nat) → Nat → List Tab
  | [], _ => []
  | a :: l, p => ⟨a.1, a.2.1, p⟩ :: place l (p + a.2.2)

/-- A list k times. -/
def rep : Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | 0, _ => []
  | k + 1, l => l ++ rep k l

/-- The entries of two lists. -/
theorem total_append : ∀ l l' : List (Nat × Nat × Nat), total (l ++ l') = total l + total l'
  | [], l' => (Nat.zero_add _).symm
  | a :: l, l' => by
    show a.2.2 + total (l ++ l') = a.2.2 + total l + total l'
    rw [total_append l l', Nat.add_assoc]

/-- The shapes of two lists, the second behind the first. -/
theorem place_append : ∀ (l l' : List (Nat × Nat × Nat)) (p : Nat),
    place (l ++ l') p = place l p ++ place l' (p + total l)
  | [], _, _ => rfl
  | a :: l, l', p => by
    show _ :: place (l ++ l') (p + a.2.2) =
      _ :: (place l (p + a.2.2) ++ place l' (p + (a.2.2 + total l)))
    rw [place_append l l', Nat.add_assoc]

/-- From the state t of the placing to the state t' exactly the tables l were placed. -/
structure Laid (l : List (Nat × Nat × Nat)) (t t' : Placed) : Prop where
  shapes : shapesOf t'.funs = shapesOf t.funs ++ place l t.next
  next : t'.next = t.next + total l
  tree : (∀ Fn ∈ t.funs.toList, Fn.tree = 2) → ∀ Fn ∈ t'.funs.toList, Fn.tree = 2

/-- Nothing placed. -/
theorem Laid.none (t : Placed) : Laid [] t t := ⟨(List.append_nil _).symm, rfl, id⟩

/-- One list placed, then another. -/
theorem Laid.then {l l' : List (Nat × Nat × Nat)} {t t1 t' : Placed} (h : Laid l t t1)
    (h' : Laid l' t1 t') : Laid (l ++ l') t t' := by
  refine ⟨?_, ?_, fun k => h'.tree (h.tree k)⟩
  · rw [h'.shapes, h.shapes, h.next, place_append, List.append_assoc]
  · rw [h'.next, h.next, total_append, Nat.add_assoc]

/-- Every success of x places exactly the tables l. -/
def Lays {α : Type} (x : PlaceM α) (l : List (Nat × Nat × Nat)) : Prop :=
  ∀ (t : Placed) (c : Ctx) (a : α) (t' : Placed) (c' : Ctx), x t c = .ok ((a, t'), c') → Laid l t t'

/-- One routine after another. -/
theorem lays_bind {α β : Type} {x : PlaceM α} {f : α → PlaceM β} {l l' : List (Nat × Nat × Nat)}
    (hx : Lays x l) (hf : ∀ a, Lays (f a) l') : Lays (x >>= f) (l ++ l') := by
  intro t c b t' c' hr
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind (m := PlaceM) (s := (t, c)) (s' := (t', c')) hr
  exact (hx t c a s1.1 s1.2 h1).then (hf a s1.1 s1.2 b t' c' h2)

/-- The same where the first places nothing. -/
theorem lays_bind0 {α β : Type} {x : PlaceM α} {f : α → PlaceM β} {l : List (Nat × Nat × Nat)}
    (hx : Lays x []) (hf : ∀ a, Lays (f a) l) : Lays (x >>= f) l := lays_bind hx hf

/-- A routine that only returns a value places nothing. -/
theorem lays_pure {α : Type} (a : α) : Lays (pure a : PlaceM α) [] := by
  intro t c b t' c' hr
  have e := (HasRuns.runs_pure (m := PlaceM) (a := a) (b := b) (s := (t, c)) (s' := (t', c')) hr).2
  have e' : t' = t := congrArg Prod.fst e
  rw [e']
  exact Laid.none t

/-- A routine whose value is changed. -/
theorem lays_bind_pure {α β : Type} {x : PlaceM α} {l : List (Nat × Nat × Nat)} (hx : Lays x l)
    (g : α → β) : Lays (x >>= fun a => pure (g a)) l := by
  have h := lays_bind hx fun a => lays_pure (g a)
  rwa [List.append_nil] at h

/-- A block places nothing. -/
theorem lays_lift {α : Type} (b : Blk α) : Lays (StateT.lift b : PlaceM α) [] := by
  intro t c a t' c' hr
  have e : t' = t :=
    (runs_lift (m := Blk) (σ := Placed) (x := b) (s := (t, c)) (s' := (t', c')) hr).2
  rw [e]
  exact Laid.none t

/-- The same for the lift that Lean puts in by itself. -/
theorem lays_up {α : Type} (b : Blk α) : Lays (liftM b : PlaceM α) [] := lays_lift b

/-- Such a block leaves the state of the placing. -/
theorem lays_up_state {α : Type} {b : Blk α} {s s' : HasRuns.St PlaceM} {a : α}
    (h : Runs (liftM b : PlaceM α) s a s') : s'.1 = s.1 :=
  (runs_lift (m := Blk) (σ := Placed) (x := b) h).2

/-- A routine under a map. -/
theorem lays_map {α β : Type} {x : PlaceM α} {l : List (Nat × Nat × Nat)} (hx : Lays x l)
    (g : α → β) : Lays (g <$> x) l := by
  rw [map_eq_pure_bind]
  exact lays_bind_pure hx g

/-- A loop over a list of numbers. -/
theorem lays_forM {f : Nat → PlaceM PUnit} {g : Nat → List (Nat × Nat × Nat)}
    (h : ∀ q, Lays (f q) (g q)) : ∀ qs : List Nat, Lays (qs.forM f) (qs.flatMap g)
  | [] => lays_pure _
  | q :: qs => by
    rw [List.flatMap_cons]
    exact lays_bind (h q) fun _ => lays_forM h qs

/-- A routine at each member of a list: the same tables each time. -/
theorem lays_mapM {α β : Type} {f : α → PlaceM β} {l : List (Nat × Nat × Nat)}
    (h : ∀ a, Lays (f a) l) : ∀ as : List α, Lays (as.mapM f) (rep as.length l)
  | [] => by
    rw [List.mapM_nil]
    exact lays_pure _
  | a :: as => by
    rw [List.mapM_cons]
    exact lays_bind (h a) fun b => lays_bind_pure (lays_mapM h as) _

/-- The same over an array. -/
theorem lays_mapMA {α β : Type} {f : α → PlaceM β} {l : List (Nat × Nat × Nat)}
    (h : ∀ a, Lays (f a) l) (as : Array α) : Lays (as.mapM f) (rep as.size l) := by
  rw [Array.mapM_eq_mapM_toList, ← Array.length_toList]
  exact lays_map (lays_mapM h as.toList) _

/-! ## The routines that place -/

/-- Weights place nothing. -/
theorem lays_weights (len : Nat) (f : Unit → Array E) : Lays (PlaceM.weights len f) [] :=
  lays_lift _

/-- A value that must be there places nothing. -/
theorem lays_getAs {α : Type} (name : String) (x : Option α) : Lays (PlaceM.getAs name x) [] := by
  cases x with
  | none => exact lays_lift _
  | some a => exact lays_pure a

/-- One table. -/
theorem lays_add (mats : Array TMat) (mat len : Nat) (phi : Array E) (elems : Nat) :
    Lays (Attention.add mats mat len phi elems) [(mat, len, elems)] := by
  intro t c a t' c' hr
  unfold Attention.add at hr
  obtain ⟨_, c1, _, h2⟩ := HasRuns.runs_bind (m := Blk) (s := c) (s' := c') hr
  obtain ⟨_, rfl⟩ := Prod.mk.inj (HasRuns.runs_pure (m := Blk) (s := c1) (s' := c') h2).1
  refine ⟨shapesOf_push _ _, rfl, fun k Fn hFn => ?_⟩
  rw [Array.toList_push, List.mem_append] at hFn
  rcases hFn with h1 | h1
  · exact k Fn h1
  · rw [List.mem_singleton.1 h1]

/-- Reading the state places nothing. -/
theorem lays_placed : Lays PlaceM.placed [] := by
  intro t c a t' c' hr
  have e := (HasRuns.runs_pure (m := Blk) (a := (t, t)) (b := (a, t')) (s := c) (s' := c') hr).1
  have e' : t' = t := congrArg Prod.snd e
  rw [e']
  exact Laid.none t

/-- Storing a length places nothing. -/
theorem lays_total (start : Nat) : Lays (PlaceM.total start) [] := by
  intro t c a t' c' hr
  unfold Attention.PlaceM.total at hr
  obtain ⟨_, rfl⟩ := Prod.mk.inj (HasRuns.runs_pure (m := Blk) (s := c) (s' := c') hr).1
  exact ⟨(List.append_nil _).symm, rfl, id⟩

/-- The parts of the matrix `as`. -/
def asPart (S : Attention.Shape) : List (Nat × Nat × Nat) :=
  (List.range S.cf.NAs).flatMap fun q => [(q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs)]

/-- A table on `as`: one for each part. -/
theorem lays_addAs (S : Attention.Shape) (mats : Array TMat) (phi : Unit → Array E) :
    Lays (Attention.addAs S mats phi) (asPart S) := by
  unfold Attention.addAs
  refine lays_bind0 (lays_weights _ _) fun w => ?_
  refine lays_bind0 lays_placed fun t0 => ?_
  have h := lays_bind (lays_forM (f := fun q =>
      discard (Attention.add mats q (2 ^ S.cf.lmS) w (S.kAs / S.cf.NAs)))
      (g := fun q => [(q, 2 ^ S.cf.lmS, S.kAs / S.cf.NAs)])
      (fun q => lays_map (lays_add _ _ _ _ _) _) (List.range S.cf.NAs))
    (fun _ => lays_bind0 (lays_total t0.next) fun _ => lays_pure t0.next)
  rwa [List.append_nil] at h

/-- A table on ah. -/
theorem lays_addRow (S : Attention.Shape) (mats : Array TMat) (psi : Unit → Array E) :
    Lays (Attention.addRow S mats psi) [(S.cf.NAs, S.T, S.fillH)] := by
  unfold Attention.addRow
  exact lays_bind0 (lays_weights _ _) fun _ => lays_add _ _ _ _ _

/-- The weights of a block of features place nothing. -/
theorem lays_lng (S : Attention.Shape) (zc : Array E) (ptk : Unit → Array E) :
    Lays (Attention.lng S zc ptk) [] := by
  unfold Attention.lng
  refine lays_bind0 (lays_weights _ _) fun _ => ?_
  refine lays_bind0 (lays_up _) fun _ => ?_
  refine lays_bind0 (lays_getAs _ _) fun _ => ?_
  exact lays_weights _ _

/-- A table on blocks of features. -/
theorem lays_addLong (S : Attention.Shape) (mats : Array TMat) (mat : Nat) (zc : Array E)
    (ptk : Unit → Array E) (elems : Nat) :
    Lays (Attention.addLong S mats mat zc ptk elems) [(mat, 2 ^ S.cf.la, elems)] := by
  unfold Attention.addLong
  exact lays_bind0 (lays_lng _ _ _) fun _ => lays_add _ _ _ _ _

/-! ## All tables -/

/-- Attention's tables at k units of the scores: of each its matrix, its rows in a block and its
number of entries, in the order of the vector of reads. -/
def attAsks (S : Attention.Shape) (k : Nat) : List (Nat × Nat × Nat) :=
  let row := (S.cf.NAs, S.T, S.fillH)
  let q := (S.cf.NAs + 3, 2 ^ S.cf.la, S.fillQ * S.T / 2 ^ S.cf.la)
  let b := (S.cf.NAs + 2, 2 ^ S.cf.lmb, S.kbA)
  asPart S ++ (asPart S ++ (asPart S ++ (rep k [row] ++ ([row] ++ ([row] ++ ([row] ++ ([row] ++
    ([row] ++ ([row] ++ ([(S.cf.NAs + 1, 2 ^ S.cf.la, S.fillO * S.T / 2 ^ S.cf.la)] ++
    (rep k ([q] ++ [q]) ++ ([q] ++ ([q] ++ ([q] ++ ([q] ++ ([q] ++ ([b] ++ ([b] ++
    ([b] ++ [])))))))))))))))))))

/-- The shapes of attention's tables: a term of the shape and of the number of score units. -/
def attShapes (S : Attention.Shape) (k : Nat) : List Tab := place (attAsks S k) 0

/-- Every success of x places exactly the tables l and returns the list of all tables placed. -/
def LaysF (x : PlaceM Attention.Tables) (l : List (Nat × Nat × Nat)) : Prop :=
  ∀ (t : Placed) (c : Ctx) (T : Attention.Tables) (t' : Placed) (c' : Ctx),
    x t c = .ok ((T, t'), c') → Laid l t t' ∧ T.funs = t'.funs

/-- One routine, then one that returns the list. -/
theorem laysF_bind {α : Type} {x : PlaceM α} {f : α → PlaceM Attention.Tables}
    {l l' : List (Nat × Nat × Nat)} (hx : Lays x l) (hf : ∀ a, LaysF (f a) l') :
    LaysF (x >>= f) (l ++ l') := by
  intro t c b t' c' hr
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind (m := PlaceM) (s := (t, c)) (s' := (t', c')) hr
  obtain ⟨k1, k2⟩ := hf a s1.1 s1.2 b t' c' h2
  exact ⟨(hx t c a s1.1 s1.2 h1).then k1, k2⟩

/-- The same where the first places nothing. -/
theorem laysF_bind0 {α : Type} {x : PlaceM α} {f : α → PlaceM Attention.Tables}
    {l : List (Nat × Nat × Nat)} (hx : Lays x []) (hf : ∀ a, LaysF (f a) l) :
    LaysF (x >>= f) l := laysF_bind hx hf

/-- The routine that places all tables. -/
theorem laysF_placeAll (S : Attention.Shape) (mats : Array TMat) (nW : Nat) (g : Forest.Heard)
    (planes : Array Attention.PlaneClaim) (scores : Array Attention.Score) (d : Attention.Divide)
    (x : Attention.Attain) :
    LaysF (Attention.placeAll S mats nW g planes scores d x) (attAsks S scores.size) := by
  unfold Attention.placeAll attAsks
  refine laysF_bind0 (lays_up _) fun _ => ?_
  refine laysF_bind (lays_addAs _ _ _) fun _ => ?_
  refine laysF_bind (lays_addAs _ _ _) fun _ => ?_
  refine laysF_bind (lays_addAs _ _ _) fun _ => ?_
  refine laysF_bind (lays_mapMA (fun _ => lays_addRow _ _ _) scores) fun _ => ?_
  refine laysF_bind (lays_addRow _ _ _) fun _ => ?_
  refine laysF_bind (lays_addRow _ _ _) fun _ => ?_
  refine laysF_bind (lays_addRow _ _ _) fun _ => ?_
  refine laysF_bind (lays_addRow _ _ _) fun _ => ?_
  refine laysF_bind (lays_addRow _ _ _) fun _ => ?_
  refine laysF_bind (lays_addRow _ _ _) fun _ => ?_
  refine laysF_bind0 (lays_up _) fun _ => ?_
  refine laysF_bind (lays_addLong _ _ _ _ _ _) fun _ => ?_
  refine laysF_bind (lays_mapMA (fun _ => lays_bind (lays_addLong _ _ _ _ _ _) fun _ =>
    lays_bind_pure (lays_addLong _ _ _ _ _ _) _) scores) fun _ => ?_
  refine laysF_bind (lays_addLong _ _ _ _ _ _) fun _ => ?_
  refine laysF_bind (lays_addLong _ _ _ _ _ _) fun _ => ?_
  refine laysF_bind (lays_addLong _ _ _ _ _ _) fun _ => ?_
  refine laysF_bind (lays_addLong _ _ _ _ _ _) fun _ => ?_
  refine laysF_bind (lays_addLong _ _ _ _ _ _) fun _ => ?_
  refine laysF_bind0 (lays_up _) fun _ => ?_
  refine laysF_bind0 (lays_weights _ _) fun _ => ?_
  refine laysF_bind (lays_add _ _ _ _ _) fun _ => ?_
  refine laysF_bind0 (lays_weights _ _) fun _ => ?_
  refine laysF_bind (lays_add _ _ _ _ _) fun _ => ?_
  refine laysF_bind0 (lays_weights _ _) fun _ => ?_
  refine laysF_bind (lays_add _ _ _ _ _) fun _ => ?_
  intro t c T t' c' hr
  obtain ⟨t0, s1, h1, h2⟩ := HasRuns.runs_bind (m := PlaceM) (s := (t, c)) (s' := (t', c')) hr
  obtain ⟨_, s2, h3, h4⟩ := HasRuns.runs_bind (m := PlaceM) (s := s1) (s' := (t', c')) h2
  have e1 := (HasRuns.runs_pure (m := Blk) (a := (t, t)) (b := (t0, s1.1)) (s := c) (s' := s1.2)
    h1).1
  have a1 : t0 = t := congrArg Prod.fst e1
  have a2 : s1.1 = t := congrArg Prod.snd e1
  have a3 : s2.1 = s1.1 := (lays_up_state h3)
  obtain ⟨b1, b2⟩ := HasRuns.runs_pure (m := PlaceM) (s := s2) (s' := (t', c')) h4
  have a4 : t' = s2.1 := congrArg Prod.fst b2
  have a5 : t' = t := a4.trans (a3.trans a2)
  rw [a5, b1, a1]
  exact ⟨Laid.none t, rfl⟩

/-- Every success of tables, dry or on a view, lays out tables with the term's shapes. -/
theorem tables_shapes {S : Attention.Shape} {mats : Array TMat} {nW : Nat} {g : Forest.Heard}
    {planes : Array Attention.PlaneClaim} {scores : Array Attention.Score} {d : Attention.Divide}
    {x : Attention.Attain} {c c' : Ctx} {T : Attention.Tables}
    (h : Attention.tables S mats nW g planes scores d x c = .ok (T, c')) :
    shapesOf T.funs = attShapes S scores.size ∧ ∀ Fn ∈ T.funs.toList, Fn.tree = 2 := by
  unfold Attention.tables at h
  obtain ⟨r, c1, h1, h2⟩ := HasRuns.runs_bind (m := Blk) (s := c) (s' := c') h
  have e := (HasRuns.runs_pure (m := Blk) (s := c1) (s' := c') h2).1
  obtain ⟨k1, k2⟩ := laysF_placeAll S mats nW g planes scores d x {} c r.1 r.2 c1 h1
  rw [e, k2]
  exact ⟨k1.shapes, k1.tree fun _ k => absurd k List.not_mem_nil⟩

/-! ## The dry run on zeros, and the debt -/

/-- Behind a block whose values have a property. -/
theorem ret_blk {α β : Type} {P : α → Prop} {Q : β → Prop} {b : Blk α} {f : α → SubM β}
    (hb : ∀ c a c', b c = .ok (a, c') → P a) (hf : ∀ a, P a → Ret Q (f a)) :
    Ret Q ((liftM b : SubM α) >>= f) := by
  intro F c y F' c' hr
  obtain ⟨a, F1, c1, h1, h2⟩ := (Port.bind_ok _ f F c _).1 hr
  exact hf a (hb c a c1 ((Port.lift_ok b F F1 c c1 a).1 h1).1) F1 c1 y F' c' h2

/-- The dry run on zeros, where it returns, has the term's shapes. -/
theorem shAt_att {c : Plan.Chain1} {n : Plan.LinkNums} {a : Attention.Plan} {x : Array HFun × Nat}
    (hA : (n.kind == "A") = true) (ha : n.att = some a) (h : Plan.funsOf c n = .ok x) :
    shAt c n = attShapes a.S (nScores a.S) := by
  rw [shAt_ok h]
  unfold Plan.funsOf at h
  simp only [hA, ha, if_true] at h
  have q : Ret (fun f : Array HFun => shapesOf f = attShapes a.S (nScores a.S))
      (do
        let f ← Attention.hear a
        let t ← (Attention.tables a.S a.mats a.nW f.g f.planes f.scores f.d f.x :
          Blk Attention.Tables)
        pure t.funs) := by
    refine ret_bind' (hear_ret a) fun f hf => ?_
    refine ret_blk (P := fun T : Attention.Tables => shapesOf T.funs = attShapes a.S (nScores a.S))
      (fun d T d' hT => by rw [← hf]; exact (tables_shapes hT).1) fun T hT => ?_
    exact ret_pure _ hT
  exact dry_ret q h

/-- At attention's link of a chain whose dry run returns: after every success of hear at a plan of
the link's shape, every success of tables at that shape and the heard units of the scores lays out
tables with the dry run's shapes. -/
theorem run_shapes_att {c : Plan.Chain1} {n : Plan.LinkNums} {a : Attention.Plan}
    {x : Array HFun × Nat} (hA : (n.kind == "A") = true) (ha : n.att = some a)
    (h : Plan.funsOf c n = .ok x) {P : Attention.Plan} (hS : P.S = a.S) {F F' : Fork} {d d' : Ctx}
    {f : Attention.First} (hf : Attention.hear P F d = .ok ((f, F'), d')) {mats : Array TMat}
    {nW : Nat} {g : Forest.Heard} {planes : Array Attention.PlaneClaim} {dv : Attention.Divide}
    {y : Attention.Attain} {e e' : Ctx} {T : Attention.Tables}
    (hT : Attention.tables a.S mats nW g planes f.scores dv y e = .ok (T, e')) :
    shapesOf T.funs = shAt c n ∧
      T.funs = funsOf (shAt c n) fun k => (T.funs.toList.getD k {}).phi := by
  obtain ⟨s1, s2⟩ := tables_shapes hT
  have k : f.scores.size = nScores a.S := hS ▸ hear_ret P F d f F' d' hf
  have e0 : shapesOf T.funs = shAt c n := by rw [s1, k, shAt_att hA ha h]
  exact ⟨e0, by rw [← e0]; exact (funsOf_self T.funs s2).symm⟩

/-- So the run's tables have the closed record's shapes. -/
theorem att_same {c : Plan.Chain1} {n : Plan.LinkNums} {a : Attention.Plan}
    {x : Array HFun × Nat} (hA : (n.kind == "A") = true) (ha : n.att = some a)
    (h : Plan.funsOf c n = .ok x) {P : Attention.Plan} (hS : P.S = a.S) {F F' : Fork} {d d' : Ctx}
    {f : Attention.First} (hf : Attention.hear P F d = .ok ((f, F'), d')) {mats : Array TMat}
    {nW : Nat} {g : Forest.Heard} {planes : Array Attention.PlaneClaim} {dv : Attention.Divide}
    {y : Attention.Attain} {e e' : Ctx} {T : Attention.Tables}
    (hT : Attention.tables a.S mats nW g planes f.scores dv y e = .ok (T, e')) :
    SameShapes (recAt c n) T.funs :=
  (run_shapes_att hA ha h hS hf hT).1.trans (funsL_shapes (shAt c n) _).symm

end OnBytes.Tie.Pv.Tail.Closed

#print axioms OnBytes.Tie.Pv.Tail.Closed.scoreUnits_ret
#print axioms OnBytes.Tie.Pv.Tail.Closed.hear_ret
#print axioms OnBytes.Tie.Pv.Tail.Closed.laysF_placeAll
#print axioms OnBytes.Tie.Pv.Tail.Closed.tables_shapes
#print axioms OnBytes.Tie.Pv.Tail.Closed.shAt_att
#print axioms OnBytes.Tie.Pv.Tail.Closed.run_shapes_att
#print axioms OnBytes.Tie.Pv.Tail.Closed.att_same
