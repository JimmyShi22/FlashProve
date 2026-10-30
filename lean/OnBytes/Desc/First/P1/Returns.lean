-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/Returns.lean: THE OTHER DIRECTION: on a tape of the form that FlTape.lean
names, and a ledger with room, the plain functions that hear a masked sumcheck
(OnBytes/K/Kc/Flat.lean) DO RETURN. Statements and proofs.

Why. The laws over these functions begin "wherever the function returns". If it returned on no tape
they would say nothing.

  `recvN_returns`, `closeOne_returns`, `emptyOn_returns`: the steps on the tape.
  `hide_returns`, `hideRun_returns`: a run of values is put under slots that are there and free.
  `pscBegin_returns`, `pscRound_returns`, `roundIn_eq2_returns`, `pscEnds_returns`,
    `pscRow_returns`.
  `rd`: a sumcheck's round as a round of the tape.
  `levelRounds_returns`, `levelIn_returns`: a layer of a product tree: for EVERY mu0, eps, rounds
    with two sent elements each, further round, two end values and tau, if the order has mu
    variables that pass the program's test, the claimed form's public part is there, and the ledger
    has arrays of the right sizes (`Sized`) and 2 mu + 5 free slots from its next slot on.

What is not shown. That the returned layer's row is worth 0 in some world, or that any condition of
`level_law` holds of the return: this is the shape's half of "the conditions can be met", not the
values' half.
-/
import OnBytes.Desc.First.P1.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.PscRun (Sized Filled hideRun_ok hide_ok)

variable {α β : Type}

theorem bind_eq {x : Fl α} {f : α → Fl β} {F G : Fork} {t u : Tape} {a : α}
    {r : β × Fork × Tape} (h1 : x F t = some (a, G, u)) (h2 : f a G u = some r) :
    (x >>= f) F t = some r := bind_some.mpr ⟨a, G, u, h1, h2⟩

/-! ### The steps on the tape -/

theorem recv_cons (nm : Option String) (z w : Nat) (x : E) (s d : List E) (u : Tape) :
    recv (⟨nm, z, w, x :: s, d⟩ :: u) = some (x, ⟨nm, z, w, s, d⟩ :: u) := rfl

theorem recvLoop_returns (nm : Option String) (z w : Nat) (d : List E) (u : Tape) :
    ∀ (s s' : List E) (a : Array E),
    recvLoop s.length a (⟨nm, z, w, s ++ s', d⟩ :: u) =
      some ((a.toList ++ s).toArray, ⟨nm, z, w, s', d⟩ :: u)
  | [], s', a => by
    show (some (a, ⟨nm, z, w, s', d⟩ :: u) : Option (Array E × Tape)) = _
    simp
  | x :: s, s', a => by
    show recvLoop (s.length + 1) a (⟨nm, z, w, x :: (s ++ s'), d⟩ :: u) = _
    rw [recvLoop_succ, recv_cons]
    show recvLoop s.length (a.push x) (⟨nm, z, w, s ++ s', d⟩ :: u) = _
    rw [recvLoop_returns nm z w d u s s' (a.push x)]
    simp

theorem recvN_returns (nm : Option String) (z w : Nat) (s d : List E) (u : Tape) :
    recvN s.length (⟨nm, z, w, s, d⟩ :: u) = some (s.toArray, ⟨nm, z, w, [], d⟩ :: u) := by
  have e := recvLoop_returns nm z w d u s [] (Array.emptyWithCapacity s.length)
  rw [List.append_nil] at e
  exact e

theorem closeOne_returns (name : String) (nz w : Nat) (x : E) (u : Tape) :
    closeOne name nz (⟨some name, nz, w, [], [x]⟩ :: u) = some (x, u) := by
  simp [closeOne]

theorem emptyOn_returns (name : String) (w : Nat) (u : Tape) :
    Fl.emptyOn name (⟨some name, 0, w, [], []⟩ :: u) = some ((), u) := by
  simp [Fl.emptyOn, closeN]

/-! ### The ledger -/

theorem hide_returns {F : Fork} {j : Nat} (y factor : E) (hF : Sized F) (hj : j < F.ns)
    (hf : ¬ Filled F j) : ∃ G, F.hide j y factor = some G := by
  obtain ⟨_, _, h3⟩ := hF
  have hs : j < F.gotF.size := by rw [h3]; exact hj
  have e : F.gotF.getD j true = F.gotF.getD j false := by
    simp [Array.getD_eq_getD_getElem?, hs]
  have hfalse : F.gotF.getD j true = false := by
    rw [e]
    unfold Filled at hf
    simpa using hf
  unfold Fork.hide
  rw [if_pos (by simp [hj, h3, hfalse])]
  exact ⟨_, rfl⟩

theorem hideSteps_returns (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork), Sized F →
    (∀ i, i < l.length → first + i < F.ns ∧ ¬ Filled F (first + i)) →
    ∃ x, l.foldlM (Fork.hideStep factor) (first, F) = some x
  | [], first, F, _, _ => ⟨(first, F), rfl⟩
  | y :: l, first, F, hF, h => by
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    obtain ⟨G, hG⟩ := hide_returns y factor hF h0.1 h0.2
    obtain ⟨_, _, hSame, hS, _, _, _, hoth⟩ := hide_ok F G first y factor hF hG
    obtain ⟨x, hx⟩ := hideSteps_returns factor l (first + 1) G hS (by
      intro i hi
      have hi' := h (i + 1) (by simpa using hi)
      have e : first + (i + 1) = first + 1 + i := by omega
      rw [e] at hi'
      refine ⟨by rw [hSame.ns]; exact hi'.1, fun hc => hi'.2 ?_⟩
      exact ((hoth (first + 1 + i) (by omega)).2.2).mp hc)
    refine ⟨x, ?_⟩
    rw [List.foldlM_cons]
    show (Fork.hideStep factor (first, F) y).bind _ = some x
    have e : Fork.hideStep factor (first, F) y = some (first + 1, G) := by
      show (F.hide first y factor).map _ = _
      rw [hG]
      rfl
    rw [e]
    exact hx

/-- A run of values is put under slots that are there and free. -/
theorem hideRun_returns {F : Fork} {first : Nat} (v : Array E) (factor : E) (hF : Sized F)
    (h : ∀ i, i < v.size → first + i < F.ns ∧ ¬ Filled F (first + i)) :
    ∃ G, F.hideRun first v factor = some G := by
  obtain ⟨x, hx⟩ := hideSteps_returns factor v.toList first F hF h
  refine ⟨x.2, ?_⟩
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, hx]

/-! ### Single steps, with what they return -/

theorem must_eq {b : Bool} (h : b = true) (F : Fork) (t : Tape) :
    Fl.must b F t = some ((), F, t) := must_some.mpr ⟨h, rfl, rfl⟩

theorem onTape_eq {g : Tape → Option (α × Tape)} {t u : Tape} {a : α} (h : g t = some (a, u))
    (F : Fork) : Fl.onTape g F t = some (a, F, u) := onTape_some.mpr ⟨h, rfl⟩

theorem take_eq (n : Nat) (F : Fork) (t : Tape) :
    Fl.takeSlots n F t = some (F.next, { F with next := F.next + n }, t) :=
  takeSlots_some.mpr ⟨rfl, rfl, rfl⟩

theorem ask_eq {f : Fork → Option α} {F : Fork} {a : α} (h : f F = some a) (t : Tape) :
    Fl.ask f F t = some (a, F, t) := ask_some.mpr ⟨h, rfl, rfl⟩

theorem need_eq {x : Option α} {a : α} (h : x = some a) (F : Fork) (t : Tape) :
    Fl.need x F t = some (a, F, t) := need_some.mpr ⟨h, rfl, rfl⟩

theorem change_eq {f : Fork → Option Fork} {F G : Fork} (h : f F = some G) (t : Tape) :
    Fl.change f F t = some ((), G, t) := change_some.mpr ⟨h, rfl⟩

/-! ### The sumcheck's functions -/

theorem pscBeginAt_returns (T mu eps : E) (w : Nat) (F : Fork) (u : Tape) :
    Fl.pscBeginAt T F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: u) =
      some ({ target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T) },
        { F with next := F.next + 1 }, u) := by
  unfold Fl.pscBeginAt
  refine bind_eq (take_eq 1 F _) ?_
  refine bind_eq (onTape_eq (recv_cons _ _ _ _ _ _ _) _) ?_
  refine bind_eq (onTape_eq (closeOne_returns _ _ _ _ _) _) ?_
  rfl

theorem pscBegin_returns {C : Aff} {F : Fork} {T : E} (hT : F.publicPart C = some T) (mu eps : E)
    (w : Nat) (u : Tape) :
    Fl.pscBegin C F (⟨some Model.RoundName.pscEpsilon.name, 0, w, [mu], [eps]⟩ :: u) =
      some ({ target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T), start := C,
              started := true }, { F with next := F.next + 1 }, u) := by
  unfold Fl.pscBegin
  refine bind_eq (ask_eq hT _) ?_
  refine bind_eq (pscBeginAt_returns T mu eps w F u) ?_
  rfl

theorem pscRound_returns (p : Psc) {w : OnBytes.Psc.Weight} (hw : Held w) (name : String)
    (nz k : Nat) {sent : List E} (hl : sent.length + 1 = w.d) (r : E) (F : Fork) (u : Tape) :
    Fl.pscRound p w (closeOne name nz) F (⟨some name, nz, k, sent, [r]⟩ :: u) =
      some ((r, stepP p (w, sent, r)), { F with next := F.next + (w.d - 1) }, u) := by
  have hn : w.d - 1 = sent.length := by omega
  unfold Fl.pscRound
  refine bind_eq (must_eq (Bool.and_eq_true_iff.mpr hw) _ _) ?_
  refine bind_eq (onTape_eq (by rw [hn]; exact recvN_returns _ _ _ _ _ _) _) ?_
  refine bind_eq (must_eq (by simp [hl]) _ _) ?_
  refine bind_eq (onTape_eq (closeOne_returns _ _ _ _ _) _) ?_
  refine bind_eq (take_eq _ _ _) ?_
  rfl

theorem roundIn_eq2_returns {p : Psc} (hp : p.ended = false) (z : E) (k : Nat) {sent : List E}
    (hl : sent.length = 2) (r : E) (F : Fork) (u : Tape) :
    Fl.roundIn .eq2 p z 0 F (⟨some Model.RoundName.pscRound.name, 0, k, sent, [r]⟩ :: u) =
      some ((r, stepP p (OnBytes.Psc.Weight.equality z 3, sent, r)),
        { F with next := F.next + 2 }, u) := by
  unfold Fl.roundIn
  refine bind_eq (must_eq (by rw [hp]; rfl) _ _) ?_
  refine bind_eq (need_eq (a := OnBytes.Psc.Weight.equality z 3) rfl _ _) ?_
  exact pscRound_returns p (held_equality z 3 (by omega)) _ 0 k
    (by show sent.length + 1 = 3; omega) r F u

theorem pscEnds_returns {p : Psc} (hp : p.ended = false) {dY n : Nat} (hd : 1 ≤ dY) (hn : 1 ≤ n)
    (k k' : Nat) {sent : List E} (hl : sent.length = dY) (beta : E) {v : Array E}
    (hv : v.size = n) {F G : Fork} (u : Tape)
    (hG : ({ F with next := F.next + dY + n } : Fork).hideRun (F.next + dY) v beta = some G) :
    Fl.pscEnds p dY n F (⟨some Model.RoundName.pscY.name, 1, k, sent, [beta]⟩ ::
        ⟨some Model.RoundName.pscValues.name, 0, k', v.toList, []⟩ :: u) =
      some ((F.next + dY,
        { stepP p (OnBytes.Psc.Weight.atZero (dY + 1), sent, beta) with ended := true }),
        G, u) := by
  have hvl : v.toList.length = n := hv
  have hread : recvN n (⟨some Model.RoundName.pscValues.name, 0, k', v.toList, []⟩ :: u) =
      some (v, ⟨some Model.RoundName.pscValues.name, 0, k', [], []⟩ :: u) := by
    have e := recvN_returns (some Model.RoundName.pscValues.name) 0 k' v.toList [] u
    rw [hvl, Array.toArray_toList] at e
    exact e
  unfold Fl.pscEnds
  refine bind_eq (must_eq (by simp [hp, hd, hn]) _ _) ?_
  refine bind_eq (pscRound_returns p (held_atZero (dY + 1) (by omega)) _ 1 k
    (by show sent.length + 1 = dY + 1; omega) beta F _) ?_
  refine bind_eq (onTape_eq hread _) ?_
  refine bind_eq (must_eq (by simp [hv]) _ _) ?_
  refine bind_eq (onTape_eq (emptyOn_returns _ _ _) _) ?_
  refine bind_eq (take_eq _ _ _) ?_
  refine bind_eq (change_eq (G := G) hG _) ?_
  rfl

theorem pscRow_returns {p : Psc} (h1 : p.rowMade = false) (h2 : p.started = true)
    (h3 : p.vars.isEmpty = false) (h4 : p.r.size = p.vars.size) (S0 : E) (kept : Aff)
    {F G : Fork} (t : Tape)
    (hG : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    Fl.pscRow p S0 kept F t = some ((p.rowForm S0 kept, { p with rowMade := true }), G, t) := by
  unfold Fl.pscRow
  refine bind_eq (must_eq (by simp [h1, h2, h3, h4]) _ _) ?_
  refine bind_eq (change_eq hG _) ?_
  rfl

/-! ### A layer of a product tree -/

/-- A sumcheck's round as a round of the tape: the number of batched rows, what is sent, what is
drawn. -/
def rd (x : Nat × List E × E) : FlatRound :=
  ⟨some Model.RoundName.pscRound.name, 0, x.1, x.2.1, [x.2.2]⟩

theorem stepP_ended (p : Psc) (m : Rnd) : (stepP p m).ended = p.ended := rfl

theorem runP_marks : ∀ (ms : List Rnd) (p : Psc),
    (runP p ms).ended = p.ended ∧ (runP p ms).rowMade = p.rowMade ∧
      (runP p ms).started = p.started
  | [], _ => ⟨rfl, rfl, rfl⟩
  | m :: ms, p => runP_marks ms (stepP p m)

theorem levelRounds_returns {mu : Nat} {rho : Array E} : ∀ (order : List Nat)
    (xs : List (Nat × List E × E)) (r : Array E) (p : Psc) (F : Fork) (u : Tape),
    xs.length = order.length → (∀ x ∈ xs, x.2.1.length = 2) →
    (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) → p.ended = false →
    Fl.levelRounds mu rho order r p F (xs.map rd ++ u) =
      some ((levelR mu order (xs.map (·.2.2)) r,
        runP p (msOf (levelWs mu rho order) (xs.map rd))),
        { F with next := F.next + 2 * order.length }, u)
  | [], [], r, p, F, u, _, _, _, _ => by
    unfold Fl.levelRounds
    rfl
  | [], _ :: _, _, _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, _, h, _, _, _ => by simp at h
  | v :: order, x :: xs, r, p, F, u, hl, hx, ht, hp => by
    have hl' : xs.length = order.length := by simpa using hl
    have hv := ht v (by simp)
    have ih := levelRounds_returns order xs (r.set! (mu - 1 - v) x.2.2)
      (stepP p (OnBytes.Psc.Weight.equality (rho.getD (mu - 1 - v) zeroE) 3, x.2.1, x.2.2))
      { F with next := F.next + 2 } u hl' (fun y hy => hx y (by simp [hy]))
      (fun w hw => ht w (by simp [hw])) ((stepP_ended p _).trans hp)
    have e : F.next + 2 + 2 * order.length = F.next + 2 * (v :: order).length := by
      rw [List.length_cons]
      omega
    unfold Fl.levelRounds
    refine bind_eq (must_eq (by simp [hv.1, hv.2]) _ _) ?_
    refine bind_eq (roundIn_eq2_returns hp (rho.getD (mu - 1 - v) zeroE) x.1 (hx x (by simp))
      x.2.2 F (xs.map rd ++ u)) ?_
    have hA : levelR mu (v :: order) ((x :: xs).map (·.2.2)) r =
        levelR mu order (xs.map (·.2.2)) (r.set! (mu - 1 - v) x.2.2) := rfl
    have hB : msOf (levelWs mu rho (v :: order)) ((x :: xs).map rd) =
        (OnBytes.Psc.Weight.equality (rho.getD (mu - 1 - v) zeroE) 3, x.2.1, x.2.2) ::
          msOf (levelWs mu rho order) (xs.map rd) := rfl
    rw [hA, hB, runP_cons, ← e]
    exact ih

theorem msOf_fst : ∀ (ws : List OnBytes.Psc.Weight) (rs : List FlatRound),
    ws.length = rs.length → (msOf ws rs).map (·.1) = ws
  | [], rs, _ => by simp [msOf_nil]
  | _ :: _, [], h => by simp at h
  | w :: ws, r :: rs, h => by
    have h' : ws.length = rs.length := by simpa using h
    rw [msOf_cons, List.map_cons, msOf_fst ws rs h']

theorem sum_level (mu : Nat) (rho : Array E) : ∀ order : List Nat,
    ((levelWs mu rho order).map fun w => w.d - 1).sum = 2 * order.length
  | [] => rfl
  | v :: order => by
    show 2 + ((levelWs mu rho order).map fun w => w.d - 1).sum = 2 * (order.length + 1)
    rw [sum_level mu rho order]
    omega

theorem entries_level (mu : Nat) (rho : Array E) (order : List Nat) :
    OnBytes.Psc.hidingEntries (levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3]) =
      1 + 2 * order.length + 2 := by
  unfold OnBytes.Psc.hidingEntries
  rw [List.map_append, List.sum_append, sum_level]
  rfl

theorem shown_returns {G : Fork} {j : Nat} (h1 : j < G.ns) (h2 : Filled G j) :
    G.shown j = some (G.vp.getD j zeroE) := by
  have h2' : G.gotF.getD j false = true := h2
  unfold Fork.shown
  rw [if_pos (by simp [h1, h2'])]

theorem endP_row_ready (p0 : Psc) (ms : List Rnd) (y : Rnd) (h1 : p0.rowMade = false)
    (h2 : p0.started = true) (h3 : p0.r.size = p0.vars.size) :
    (endP p0 ms y).rowMade = false ∧ (endP p0 ms y).started = true ∧
      (endP p0 ms y).vars.isEmpty = false ∧ (endP p0 ms y).r.size = (endP p0 ms y).vars.size := by
  obtain ⟨_, f2, f3⟩ := runP_marks ms p0
  obtain ⟨e1, e2, _⟩ := endP_spec p0 ms y
  refine ⟨f2.trans h1, f3.trans h2, by simp [endP, stepP], ?_⟩
  show (endP p0 ms y).r.toList.length = (endP p0 ms y).vars.toList.length
  rw [e1, e2, List.length_append, List.length_append, List.length_map, List.length_map]
  show p0.r.size + _ = p0.vars.size + _
  rw [h3]

/-- **A layer returns**, for every choice of what is sent and drawn in the shape that `levelIn_tape`
names: if the order has mu variables that pass the program's test, the form's public part is
there, and the ledger has arrays of the right sizes and 2 mu + 5 free slots from its next slot
on. -/
theorem levelIn_returns {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F : Fork} {T : E}
    (hom : order.length = mu) (ht : ∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size)
    (hT : F.publicPart C = some T) (hF : Sized F)
    (hroom : ∀ i, i < 2 * mu + 5 → F.next + i < F.ns ∧ ¬ Filled F (F.next + i))
    (mu0 eps : E) (w0 : Nat) (xs : List (Nat × List E × E)) (hxl : xs.length = mu)
    (hx : ∀ x ∈ xs, x.2.1.length = 2) (wY : Nat) (sentY : List E) (hsY : sentY.length = 2)
    (beta : E) (wV : Nat) (v : Array E) (hv : v.size = 2) (wT : Nat) (tau : E) (u : Tape) :
    ∃ (L : Level) (G : Fork), Fl.levelIn mu rho C order F
      (⟨some Model.RoundName.pscEpsilon.name, 0, w0, [mu0], [eps]⟩ ::
        (xs.map rd ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, wV, v.toList, []⟩ ::
          ⟨some Model.RoundName.line.name, 0, wT, [], [tau]⟩ :: u)) = some (L, G, u) := by
  subst hom
  have hwl0 : (levelWs order.length rho order).length = (xs.map rd).length := by
    rw [levelWs, List.length_map, List.length_map, hxl]
  have a1 := msOf_fst _ _ hwl0
  -- the record behind the rounds
  obtain ⟨e1, e2, _, _, _, _, e7⟩ := endP_spec
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } (msOf (levelWs order.length rho order) (xs.map rd))
    (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta)
  obtain ⟨f1, _, _⟩ := runP_marks (msOf (levelWs order.length rho order) (xs.map rd))
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true }
  obtain ⟨g1, g2, g3, g4⟩ := endP_row_ready
    { target := T, first := F.next, eps := eps, claim := addE mu0 (mulE eps T), start := C,
      started := true } (msOf (levelWs order.length rho order) (xs.map rd))
    (OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta) rfl rfl rfl
  have hheld : ∀ m ∈ msOf (levelWs order.length rho order) (xs.map rd) ++
      [(OnBytes.Psc.Weight.atZero (2 + 1), sentY, beta)], Held m.1 := by
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact held_level _ _ _ m.1 (by rw [← a1]; exact List.mem_map_of_mem hm)
    · rw [List.mem_singleton] at hm
      rw [hm]
      exact held_atZero 3 (by omega)
  have hwalk := walk_length (by simp) e1 e2 hheld
  rw [List.map_append, a1, List.map_singleton] at hwalk
  have hwalk' := hwalk.trans (entries_level order.length rho order)
  -- the two end values are put under their slots
  have hFa : Sized ({ F with next := F.next + 1 + 2 * order.length + 2 + 2 } : Fork) := hF
  obtain ⟨G1, hG1⟩ := hideRun_returns
    (F := { F with next := F.next + 1 + 2 * order.length + 2 + 2 })
    (first := F.next + 1 + 2 * order.length + 2) v beta hFa (by
      intro i hi
      have h := hroom (1 + 2 * order.length + 2 + i) (by omega)
      have e : F.next + (1 + 2 * order.length + 2 + i) =
          F.next + 1 + 2 * order.length + 2 + i := by omega
      rw [e] at h
      exact h)
  obtain ⟨hSame1, hS1, hin1, hout1⟩ := hideRun_ok _ G1 _ v beta hFa hG1
  have k0 := hin1 0 (by omega)
  have k1 := hin1 1 (by omega)
  rw [Nat.add_zero] at k0
  have hns : G1.ns = F.ns := hSame1.ns
  have hsh0 := shown_returns (G := G1) (by rw [hns]; exact k0.1) k0.2.2.1
  have hsh1 := shown_returns (G := G1) (by rw [hns]; exact k1.1) k1.2.2.1
  -- the sumcheck's own slots
  obtain ⟨G, hG⟩ := hideRun_returns (F := G1) (first := F.next)
    (Array.replicate (1 + 2 * order.length + 2) zeroE) (subE zeroE oneE) hS1 (by
      intro i hi
      rw [Array.size_replicate] at hi
      have h := hroom i (by omega)
      have ho := hout1 (F.next + i) (Or.inl (by omega))
      exact ⟨by rw [hns]; exact h.1, fun hc => h.2 (ho.2.2.mp hc)⟩)
  rw [← hwalk'] at hG
  have e7' : (endP _ _ _).first = F.next := e7
  have hG' := (congrArg (fun j => G1.hideRun j (Array.replicate _ zeroE) (subE zeroE oneE))
    e7').trans hG
  -- the function, step by step
  refine ⟨?_, G, ?_⟩
  rotate_left
  unfold Fl.levelIn
  refine bind_eq (must_eq (by simp) _ _) ?_
  refine bind_eq (pscBegin_returns hT mu0 eps w0 _) ?_
  refine bind_eq (levelRounds_returns order xs _ _ _ _ hxl hx ht rfl) ?_
  refine bind_eq (pscEnds_returns f1 (by omega) (by omega) wY wV hsY beta hv _ hG1) ?_
  refine bind_eq (onTape_eq (closeOne_returns _ _ _ _ _) _) ?_
  refine bind_eq (ask_eq hsh0 _) ?_
  refine bind_eq (ask_eq hsh1 _) ?_
  refine bind_eq (pscRow_returns g1 g2 g3 g4 _ _ _ hG') ?_
  rfl

end OnBytes.Desc.First.P1
