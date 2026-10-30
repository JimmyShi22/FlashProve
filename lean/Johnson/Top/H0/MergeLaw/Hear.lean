-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Hear.lean: the closed form of what the merge hears. Theorems with their
proofs, on the running text alone: where `mergeHear` (Johnson/Desc/First/Fork/MergeKind.lean) says
yes on a tape, the tape begins with just the merge's rounds, and what is handed on is a written
function of what the tape holds. General in the number of claims.

Main names:
  `recv_inv`, `recvLoop_closed`, `closeOne_inv`, `closeN_inv`, `closeRows_inv`: the tape's
  functions.
  `bind_inv`, `must_inv`, `onTape_inv`, `takeSlots_inv`, `ret_inv`, `need_inv`, `ask_inv`,
    `change_inv`: a step of the flat text (OnBytes/K/Kc/Flat.lean).
  `pscRound_inv`: one round of the masked sumcheck. `After`: the sumcheck's state behind some
  rounds.
  `wsForkRounds_inv`, `pscBeginAt_inv`, `pscEnds_inv`, `batch_inv`, `pscRow_inv`: the parts.
  `mergeHear_inv`: the whole, with the rows that leave for the committed matrix (`recs`).

The library has the like for verify-on-bytes's routine wsForkMerge, in that routine's own monad
(OnBytes/Tie/Pv/Lay/MergeTie.lean: merge_seam); it does not treat `recs`.

Limits: "if it says yes, then": nothing where it refuses, and not that it ever says yes. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Psc)

/-! ### the tape's four functions -/

theorem recv_inv {t u : Tape} {x : E} (h : recv t = some (x, u)) :
    ∃ nm z w s d t0, t = ⟨nm, z, w, x :: s, d⟩ :: t0 ∧ u = ⟨nm, z, w, s, d⟩ :: t0 := by
  match t, h with
  | ⟨nm, z, w, y :: s, d⟩ :: t0, h =>
    simp only [recv, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨nm, z, w, s, d, t0, rfl, rfl⟩
  | [], h => simp [recv] at h
  | ⟨_, _, _, [], _⟩ :: _, h => simp [recv] at h

/-- n elements are taken, and behind them the message is used up: then the message was just these.
-/
theorem recvLoop_closed : ∀ (n : Nat) (a b : Array E) (t u t' : Tape) (nm : Option String) (z w :
    Nat) (d : List E),
    recvLoop n a t = some (b, u) → u = ⟨nm, z, w, [], d⟩ :: t' →
    ∃ xs : List E, xs.length = n ∧ b.toList = a.toList ++ xs ∧ t = ⟨nm, z, w, xs, d⟩ :: t'
  | 0, a, b, t, u, t', nm, z, w, d, h, hu => by
    simp only [recvLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, by simp, hu⟩
  | n + 1, a, b, t, u, t', nm, z, w, d, h, hu => by
    unfold recvLoop at h
    split at h
    · rename_i x v hx
      obtain ⟨nm0, z0, w0, s, d0, t0, rfl, rfl⟩ := recv_inv hx
      obtain ⟨xs, hl, hb, ht⟩ := recvLoop_closed n _ b _ u t' nm z w d h hu
      simp only [List.cons.injEq, FlatRound.mk.injEq] at ht
      obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := ht
      exact ⟨x :: s, by simp [hl], by simp [hb], rfl⟩
    · exact absurd h (by simp)

theorem closeOne_inv {name : String} {nz : Nat} {u t' : Tape} {x : E} (h : closeOne name nz u = some
    (x, t')) :
    ∃ w, u = ⟨some name, nz, w, [], [x]⟩ :: t' := by
  unfold closeOne at h
  split at h
  · rename_i nm z w y t
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨w, rfl⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem closeN_inv {name : String} {nz n : Nat} {u t' : Tape} {d : List E} (h : closeN name nz n u =
    some (d, t')) :
    ∃ w, u = ⟨some name, nz, w, [], d⟩ :: t' ∧ d.length = n := by
  unfold closeN at h
  split at h
  · rename_i nm z w d0 t
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, hn⟩ := hc
      exact ⟨w, rfl, hn⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem closeRows_inv {rows : Nat} {u t' : Tape} {x : E} (h : closeRows rows u = some (x, t')) :
    u = ⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: t' := by
  unfold closeRows at h
  split at h
  · rename_i nm z w y t
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      rfl
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ### a step of the flat text -/

theorem bind_inv {α β : Type} {x : Fl α} {f : α → Fl β} {F G : Fork} {t u : Tape} {b : β}
    (h : (x >>= f) F t = some (b, G, u)) : ∃ a F1 t1, x F t = some (a, F1, t1) ∧ f a F1 t1 = some
        (b, G, u) := by
  have h' : Fl.andThen x f F t = some (b, G, u) := h
  unfold Fl.andThen at h'
  split at h'
  · rename_i a F1 t1 hx
    exact ⟨a, F1, t1, hx, h'⟩
  · exact absurd h' (by simp)

theorem must_inv {b : Bool} {F G : Fork} {t u : Tape} {x : Unit} (h : Fl.must b F t = some (x, G,
    u)) :
    b = true ∧ G = F ∧ u = t := by
  unfold Fl.must at h
  split at h
  · rename_i hb
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hb, h.2.1.symm, h.2.2.symm⟩
  · exact absurd h (by simp)

theorem onTape_inv {α : Type} {g : Tape → Option (α × Tape)} {F G : Fork} {t u : Tape} {a : α}
    (h : Fl.onTape g F t = some (a, G, u)) : g t = some (a, u) ∧ G = F := by
  unfold Fl.onTape at h
  cases hg : g t with
  | none => simp [hg] at h
  | some y =>
    simp only [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨by rw [← h1, ← h3], h2.symm⟩

theorem takeSlots_inv {n : Nat} {F G : Fork} {t u : Tape} {a : Nat} (h : Fl.takeSlots n F t = some
    (a, G, u)) :
    a = F.next ∧ G = { F with next := F.next + n } ∧ u = t := by
  simp only [Fl.takeSlots, Fl.take, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem ret_inv {α : Type} {a b : α} {F G : Fork} {t u : Tape} (h : (pure a : Fl α) F t = some (b,
    G, u)) :
    b = a ∧ G = F ∧ u = t := by
  have h' : Fl.ret a F t = some (b, G, u) := h
  simp only [Fl.ret, Option.some.injEq, Prod.mk.injEq] at h'
  exact ⟨h'.1.symm, h'.2.1.symm, h'.2.2.symm⟩

/-- **One round of the masked sumcheck, closed by one drawn element.** -/
theorem pscRound_inv {p p' : Psc} {w : OnBytes.Psc.Weight} {name : String} {nz : Nat} {F F' : Fork}
    {t t' : Tape} {r : E}
    (h : Fl.pscRound p w (closeOne name nz) F t = some ((r, p'), F', t')) :
    ∃ (xs : List E) (rows : Nat), xs.length + 1 = w.d ∧ t = ⟨some name, nz, rows, xs, [r]⟩ :: t' ∧
      p' = { p with
        claim := OnBytes.Psc.polyAt (w.complete xs p.claim) r
        vars := p.vars.push w
        r := p.r.push r } ∧
      F' = { F with next := F.next + (w.d - 1) } := by
  unfold Fl.pscRound at h
  obtain ⟨_, F1, t1, a1, k1⟩ := bind_inv h
  obtain ⟨_, e1, e1'⟩ := must_inv a1
  obtain ⟨sent, F2, t2, a2, k2⟩ := bind_inv k1
  obtain ⟨b2, e2⟩ := onTape_inv a2
  obtain ⟨_, F3, t3, a3, k3⟩ := bind_inv k2
  obtain ⟨hs, e3, e3'⟩ := must_inv a3
  obtain ⟨r0, F4, t4, a4, k4⟩ := bind_inv k3
  obtain ⟨b4, e4⟩ := onTape_inv a4
  obtain ⟨_, F5, t5, a5, k5⟩ := bind_inv k4
  obtain ⟨_, e5, e5'⟩ := takeSlots_inv a5
  obtain ⟨hr, e6, e6'⟩ := ret_inv k5
  subst e1 e1' e2 e3 e3' e4 e5 e5' e6 e6'
  obtain ⟨rows, hu⟩ := closeOne_inv b4
  obtain ⟨xs, hl, hb, ht⟩ := recvLoop_closed _ _ _ _ _ _ _ _ _ _ b2 hu
  simp only [Prod.mk.injEq] at hr
  obtain ⟨hr1, hr2⟩ := hr
  subst hr1 hr2
  have hx : sent.toList = xs := by simpa using hb
  simp only [beq_iff_eq] at hs
  refine ⟨xs, rows, ?_, ht, by rw [hx], rfl⟩
  rw [← hs, ← hx]; simp

/-! ### the state of the sumcheck behind some rounds -/

/-- p' is p behind the rounds rs in variables summed by ws. -/
structure After (p p' : Psc) (ws : List OnBytes.Psc.Weight) (rs : List (List E × E)) : Prop where
  claim : p'.claim = OnBytes.Psc.claimAfter ws rs p.claim
  r : p'.r.toList = p.r.toList ++ rs.map (·.2)
  vars : p'.vars.toList = p.vars.toList ++ ws
  eps : p'.eps = p.eps
  target : p'.target = p.target
  first : p'.first = p.first
  start : p'.start = p.start
  started : p'.started = p.started
  ended : p'.ended = p.ended
  rowMade : p'.rowMade = p.rowMade

theorem After.refl (p : Psc) : After p p [] [] :=
  ⟨by simp [OnBytes.Psc.claimAfter], by simp, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem After.cons {p p' : Psc} {w : OnBytes.Psc.Weight} {q : List E} {g : E} {ws : List
    OnBytes.Psc.Weight}
    {rs : List (List E × E)}
    (h : After { p with
      claim := OnBytes.Psc.polyAt (w.complete q p.claim) g
      vars := p.vars.push w
      r := p.r.push g } p' ws rs) :
    After p p' (w :: ws) ((q, g) :: rs) :=
  ⟨by rw [h.claim, OnBytes.Psc.claimAfter], by rw [h.r]; simp, by rw [h.vars]; simp, h.eps,
      h.target, h.first, h.start,
    h.started, h.ended, h.rowMade⟩

theorem claimAfter_snoc : ∀ (ws : List OnBytes.Psc.Weight) (rs : List (List E × E)) (w :
    OnBytes.Psc.Weight) (q : List E)
    (g R : E), ws.length = rs.length →
    OnBytes.Psc.claimAfter (ws ++ [w]) (rs ++ [(q, g)]) R =
      OnBytes.Psc.polyAt (w.complete q (OnBytes.Psc.claimAfter ws rs R)) g
  | [], [], w, q, g, R, _ => by simp [OnBytes.Psc.claimAfter]
  | v :: ws, (q0, g0) :: rs, w, q, g, R, h => by
    simp only [List.cons_append, OnBytes.Psc.claimAfter]
    exact claimAfter_snoc ws rs w q g _ (by simpa using h)
  | [], _ :: _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h

/-- The weight of a round of the merge's sumcheck. -/
theorem sum2_weight : Model.RoundForm.weight .sum2 zeroE 0 = some (OnBytes.Psc.Weight.plain 3) :=
    rfl

theorem need_inv {α : Type} {x : Option α} {F G : Fork} {t u : Tape} {a : α} (h : Fl.need x F t =
    some (a, G, u)) :
    x = some a ∧ G = F ∧ u = t := by
  unfold Fl.need at h
  cases x with
  | none => simp at h
  | some y =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.1], h.2.1.symm, h.2.2.symm⟩

/-- A round as the tape holds it. -/
def rd (name : String) (nz : Nat) (q : Nat × List E × E) : FlatRound := ⟨some name, nz, q.1, q.2.1,
    [q.2.2]⟩

/-- **The rounds in the column bits.** -/
theorem wsForkRounds_inv : ∀ (n : Nat) (rm rm' : Array E) (p p' : Psc) (F F' : Fork) (t t' : Tape),
    Fl.wsForkRounds n rm p F t = some ((rm', p'), F', t') →
    ∃ qs : List (Nat × List E × E), qs.length = n ∧ (∀ q ∈ qs, q.2.1.length = 2) ∧
      t = qs.map (rd Model.RoundName.pscRound.name 0) ++ t' ∧
      rm'.toList = rm.toList ++ qs.map (·.2.2) ∧
      After p p' (List.replicate n (OnBytes.Psc.Weight.plain 3)) (qs.map fun q => (q.2.1, q.2.2)) ∧
      F' = { F with next := F.next + 2 * n }
  | 0, rm, rm', p, p', F, F', t, t', h => by
    unfold Fl.wsForkRounds at h
    obtain ⟨hr, rfl, rfl⟩ := ret_inv h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨[], rfl, by simp, by simp, by simp, After.refl _, by simp⟩
  | n + 1, rm, rm', p, p', F, F', t, t', h => by
    unfold Fl.wsForkRounds at h
    obtain ⟨⟨r, p1⟩, F1, t1, a1, k1⟩ := bind_inv h
    unfold Fl.roundIn at a1
    obtain ⟨_, F2, t2, a2, k2⟩ := bind_inv a1
    obtain ⟨_, e2, e2'⟩ := must_inv a2
    obtain ⟨w, F3, t3, a3, k3⟩ := bind_inv k2
    obtain ⟨hw, e3, e3'⟩ := need_inv a3
    subst e2 e2' e3 e3'
    replace hw : some (OnBytes.Psc.Weight.plain 3) = some w := hw
    simp only [Option.some.injEq] at hw
    subst hw
    obtain ⟨xs, rows, hl, et, ep, eF⟩ := pscRound_inv k3
    subst et ep eF
    obtain ⟨qs, hn, hq, et, hrm, ha, eF⟩ := wsForkRounds_inv n _ _ _ _ _ _ _ _ k1
    subst et eF
    refine ⟨(rows, xs, r) :: qs, by simp [hn], ?_, by simp [rd], by rw [hrm]; simp, ?_, ?_⟩
    · intro q hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · have : xs.length + 1 = 3 := hl
        simpa using this
      · exact hq q hq'
    · simpa [List.replicate_succ] using After.cons ha
    · have : (OnBytes.Psc.Weight.plain 3).d - 1 = 2 := rfl
      simp only [this]
      congr 1
      omega

/-! ### the beginning, the end, the whole -/

theorem ask_inv {α : Type} {f : Fork → Option α} {F G : Fork} {t u : Tape} {a : α} (h : Fl.ask f F t
    = some (a, G, u)) :
    f F = some a ∧ G = F ∧ u = t := by
  unfold Fl.ask at h
  cases hf : f F with
  | none => simp [hf] at h
  | some y =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.1], h.2.1.symm, h.2.2.symm⟩

theorem change_inv {f : Fork → Option Fork} {F G : Fork} {t u : Tape} {a : Unit} (h : Fl.change f F
    t = some (a, G, u)) :
    f F = some G ∧ u = t := by
  unfold Fl.change at h
  cases hf : f F with
  | none => simp [hf] at h
  | some y =>
    simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.2.1], h.2.2.symm⟩

theorem emptyOn_inv {name : String} {t u : Tape} {a : Unit} (h : Fl.emptyOn name t = some (a, u)) :
    ∃ w, t = ⟨some name, 0, w, [], []⟩ :: u := by
  unfold Fl.emptyOn at h
  cases hc : closeN name 0 0 t with
  | none => simp [hc] at h
  | some y =>
    obtain ⟨d, v⟩ := y
    simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
    subst h
    obtain ⟨w, hu, hd⟩ := closeN_inv hc
    have hd' : d = [] := List.length_eq_zero_iff.1 hd
    subst hd'
    exact ⟨w, hu⟩

/-- **The beginning of the masked sumcheck.** -/
theorem pscBeginAt_inv {T : E} {p : Psc} {F F' : Fork} {t t' : Tape} (h : Fl.pscBeginAt T F t = some
    (p, F', t')) :
    ∃ (mu eps : E) (rows : Nat), t = ⟨some Model.RoundName.pscEpsilon.name, 0, rows, [mu], [eps]⟩ ::
        t' ∧
      p = { target := T, first := F.next, eps := eps, claim := addE mu (mulE eps T) } ∧
      F' = { F with next := F.next + 1 } := by
  unfold Fl.pscBeginAt at h
  obtain ⟨first, F1, t1, a1, k1⟩ := bind_inv h
  obtain ⟨e0, e1, e1'⟩ := takeSlots_inv a1
  obtain ⟨mu, F2, t2, a2, k2⟩ := bind_inv k1
  obtain ⟨b2, e2⟩ := onTape_inv a2
  obtain ⟨eps, F3, t3, a3, k3⟩ := bind_inv k2
  obtain ⟨b3, e3⟩ := onTape_inv a3
  obtain ⟨hp, e4, e4'⟩ := ret_inv k3
  subst e0 e1 e1' e2 e3 e4 e4' hp
  obtain ⟨rows, hu⟩ := closeOne_inv b3
  obtain ⟨nm, z, w, s, d, t0, ht, hu'⟩ := recv_inv b2
  rw [hu'] at hu
  simp only [List.cons.injEq, FlatRound.mk.injEq] at hu
  obtain ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := hu
  exact ⟨mu, eps, w, ht, rfl, rfl⟩

/-- **The round in the further variable and the one end value.** -/
theorem pscEnds_inv {p p' : Psc} {F F' : Fork} {t t' : Tape} {e : Nat} (h : Fl.pscEnds p 1 1 F t =
    some ((e, p'), F', t')) :
    ∃ (c beta v : E) (rY rV : Nat),
      t = ⟨some Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ :: ⟨some
          Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: t' ∧
      p' = { p with
        claim := OnBytes.Psc.polyAt ((OnBytes.Psc.Weight.atZero 2).complete [c] p.claim) beta
        vars := p.vars.push (OnBytes.Psc.Weight.atZero 2)
        r := p.r.push beta
        ended := true } ∧
      e = F.next + 1 ∧ ({ F with next := F.next + 2 } : Fork).hideRun e #[v] beta = some F' := by
  unfold Fl.pscEnds at h
  obtain ⟨_, F1, t1, a1, k1⟩ := bind_inv h
  obtain ⟨_, e1, e1'⟩ := must_inv a1
  obtain ⟨⟨beta, p1⟩, F2, t2, a2, k2⟩ := bind_inv k1
  dsimp only at k2
  obtain ⟨vs, F3, t3, a3, k3⟩ := bind_inv k2
  obtain ⟨b3, e3⟩ := onTape_inv a3
  obtain ⟨_, F4, t4, a4, k4⟩ := bind_inv k3
  obtain ⟨hs, e4, e4'⟩ := must_inv a4
  obtain ⟨_, F5, t5, a5, k5⟩ := bind_inv k4
  obtain ⟨b5, e5⟩ := onTape_inv a5
  obtain ⟨e', F6, t6, a6, k6⟩ := bind_inv k5
  obtain ⟨e6, e6', e6''⟩ := takeSlots_inv a6
  obtain ⟨_, F7, t7, a7, k7⟩ := bind_inv k6
  obtain ⟨b7, e7⟩ := change_inv a7
  obtain ⟨hr, e8, e8'⟩ := ret_inv k7
  subst e1 e1' e3 e4 e4' e5 e6 e6' e6'' e7 e8 e8'
  obtain ⟨xs, rY, hl, et, ep, eF⟩ := pscRound_inv a2
  subst et ep eF
  simp only [Prod.mk.injEq] at hr
  obtain ⟨hr1, hr2⟩ := hr
  subst hr1 hr2
  have hl' : xs.length = 1 := by
    have : xs.length + 1 = 2 := hl
    omega
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.1 hl'
  obtain ⟨rV, hu⟩ := emptyOn_inv b5
  obtain ⟨ys, hy, hb, ht⟩ := recvLoop_closed _ _ _ _ _ _ _ _ _ _ b3 hu
  obtain ⟨v, rfl⟩ := List.length_eq_one_iff.1 hy
  have hv : vs = #[v] := by
    apply Array.ext'
    simpa using hb
  subst hv
  refine ⟨c, beta, v, rY, rV, by rw [ht], rfl, rfl, ?_⟩
  have h2 : (OnBytes.Psc.Weight.atZero (1 + 1)).d - 1 = 1 := rfl
  simpa [h2, Nat.add_assoc] using b7

/-- **The claim that a sumcheck leaves**: its form is `Psc.rowForm`; the ledger gets the pairs (0,
-1) under the slots of the
hiding polynomial's coefficients; the tape is not touched. -/
theorem pscRow_inv {p p' : Psc} {S0 : E} {kept form : Model.Aff} {F F' : Fork} {t t' : Tape}
    (h : Fl.pscRow p S0 kept F t = some ((form, p'), F', t')) :
    form = p.rowForm S0 kept ∧ p' = { p with rowMade := true } ∧ t' = t ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some F' ∧
      (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true := by
  unfold Fl.pscRow at h
  obtain ⟨_, F1, t1, a1, k1⟩ := bind_inv h
  obtain ⟨hg, e1, e1'⟩ := must_inv a1
  obtain ⟨_, F2, t2, a2, k2⟩ := bind_inv k1
  obtain ⟨b2, e2⟩ := change_inv a2
  obtain ⟨hr, e3, e3'⟩ := ret_inv k2
  subst e1 e1' e2 e3 e3'
  simp only [Prod.mk.injEq] at hr
  exact ⟨hr.1, hr.2, rfl, b2, hg⟩

/-! ### the whole of what is heard -/

theorem ebind_inv {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} (h : (x >>=
    f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

theorem need_ok {nm : String} {b : Bool} {u : Unit} (h : VerifiableInference.Desc.need nm b = .ok u)
    : b = true := by
  unfold VerifiableInference.Desc.need at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem named_ok {α : Type} {nm : String} {x : Option α} {a : α} (h : VerifiableInference.Desc.named
    nm x = .ok a) :
    x = some a := by
  cases x with
  | none => exact absurd h (by simp [VerifiableInference.Desc.named])
  | some y =>
    simp only [VerifiableInference.Desc.named, Except.ok.injEq] at h
    rw [h]

theorem batch_inv {rows : Nat} {rho : Array E} {F G : Fork} {t u : Tape} (h : Fl.batch rows F t =
    some (rho, G, u)) :
    ∃ x, t = ⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u ∧ rho = Model.powers x rows
        ∧ G = F := by
  obtain ⟨b, e⟩ := onTape_inv h
  unfold Fl.batchOn at b
  split at b
  · cases hc : closeRows rows t with
    | none => simp [hc] at b
    | some y =>
      obtain ⟨x, v⟩ := y
      simp only [hc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at b
      obtain ⟨b1, b2⟩ := b
      subst b2
      exact ⟨x, closeRows_inv hc, b1.symm, e⟩
  · exact absurd b (by simp)

open Johnson.Desc.First.ForkMerge (mergeHear) in
open OnBytes.Model (WsLay WsClaim WsForkOut wsForkStart wsRowPart wsEpsT) in
/-- **The closed form of what the merge hears.** Where `mergeHear` says yes: the tape begins with
just lk + 4 rounds of the merge's shape, and what is handed on is written out. -/
theorem mergeHear_inv {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' :
    Tape} {wo : WsForkOut}
    (h : mergeHear lay cl sv F t = .ok (wo, F', t')) :
    ∃ (x mu eps c beta v T : E) (r1 rY rV : Nat) (qs : List (Nat × List E × E)),
      qs.length = lay.lk ∧ (∀ q ∈ qs, q.2.1.length = 2) ∧
      t = ⟨some Model.RoundName.batSigma.name, 0, sv.size, [], [x]⟩ ::
          ⟨some Model.RoundName.pscEpsilon.name, 0, r1, [mu], [eps]⟩ ::
          (qs.map (rd Model.RoundName.pscRound.name 0) ++
            ⟨some Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
            ⟨some Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: t') ∧
      F.publicPart (wsForkStart sv (Model.powers x sv.size)) = some T ∧
      wo.p.eps = eps ∧ wo.p.target = T ∧
      wo.p.claim = OnBytes.Psc.claimAfter (List.replicate lay.lk (OnBytes.Psc.Weight.plain 3) ++
          [OnBytes.Psc.Weight.atZero 2])
        (qs.map (fun q => (q.2.1, q.2.2)) ++ [([c], beta)]) (addE mu (mulE eps T)) ∧
      wo.rm.toList = qs.map (·.2.2) ∧ wo.beta = beta ∧ wo.p.r.toList = qs.map (·.2.2) ++ [beta] ∧
      wo.sFv = F.next + 1 + 2 * lay.lk + 1 ∧
      ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork).hideRun wo.sFv #[v] beta = some F' ∧
      F'.shown wo.sFv = some wo.fvp ∧
      wo.recs = (cl.zip (Model.powers x sv.size)).toList.map (fun y =>
        wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))) ∧
      wo.p.vars.toList =
        List.replicate lay.lk (OnBytes.Psc.Weight.plain 3) ++ [OnBytes.Psc.Weight.atZero 2] ∧
      wo.p.first = F.next ∧ wo.p.start = wsForkStart sv (Model.powers x sv.size) ∧
      wo.p.started = true ∧ wo.p.rowMade = false ∧ wo.p.ended = true := by
  unfold mergeHear at h
  obtain ⟨_, a1, k1⟩ := ebind_inv h
  obtain ⟨_, a2, k2⟩ := ebind_inv k1
  obtain ⟨_, a3, k3⟩ := ebind_inv k2
  obtain ⟨⟨rho, F1, t1⟩, a4, k4⟩ := ebind_inv k3
  dsimp only at k4
  obtain ⟨⟨T, F2, t2⟩, a5, k5⟩ := ebind_inv k4
  dsimp only at k5
  obtain ⟨⟨p, F3, t3⟩, a6, k6⟩ := ebind_inv k5
  dsimp only at k6
  obtain ⟨⟨⟨rm, p1⟩, F4, t4⟩, a7, k7⟩ := ebind_inv k6
  dsimp only at k7
  obtain ⟨⟨⟨sFv, p2⟩, F5, t5⟩, a8, k8⟩ := ebind_inv k7
  dsimp only at k8
  obtain ⟨⟨fvp, F6, t6⟩, a9, k9⟩ := ebind_inv k8
  dsimp only at k9
  obtain ⟨x, et, erho, eF1⟩ := batch_inv (named_ok a4)
  obtain ⟨hT, eF2, et2⟩ := ask_inv (named_ok a5)
  obtain ⟨mu, eps, r1, et3, ep, eF3⟩ := pscBeginAt_inv (named_ok a6)
  obtain ⟨qs, hn, hq, et4, hrm, ha, eF4⟩ := wsForkRounds_inv _ _ _ _ _ _ _ _ _ (named_ok a7)
  obtain ⟨c, beta, v, rY, rV, et5, ep2, esFv, hh⟩ := pscEnds_inv (named_ok a8)
  obtain ⟨hs, eF6, et6⟩ := ask_inv (named_ok a9)
  clear a1 a2 a3 a4 a5 a6 a7 a8 a9 k1 k2 k3 k4 k5 k6 k7 k8 h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at k9
  obtain ⟨ewo, eF', et'⟩ := k9
  have wp : wo.p = p2 := by rw [← ewo]
  have wrm : wo.rm = rm := by rw [← ewo]
  have wbeta : wo.beta = p2.r.back?.getD zeroE := by rw [← ewo]
  have wsFv : wo.sFv = sFv := by rw [← ewo]
  have wfvp : wo.fvp = fvp := by rw [← ewo]
  have wrecs : wo.recs = (cl.zip rho).toList.map (fun y =>
      wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 rm))) := by rw [← ewo]
  clear ewo
  have p2eps : p2.eps = p1.eps := by rw [ep2]
  have p2target : p2.target = p1.target := by rw [ep2]
  have p2claim : p2.claim = OnBytes.Psc.polyAt ((OnBytes.Psc.Weight.atZero 2).complete [c] p1.claim)
      beta := by rw [ep2]
  have p2r : p2.r = p1.r.push beta := by rw [ep2]
  have p2vars : p2.vars = p1.vars.push (OnBytes.Psc.Weight.atZero 2) := by rw [ep2]
  have p2first : p2.first = p1.first := by rw [ep2]
  have p2start : p2.start = p1.start := by rw [ep2]
  have p2started : p2.started = p1.started := by rw [ep2]
  have p2rowMade : p2.rowMade = p1.rowMade := by rw [ep2]
  have p2ended : p2.ended = true := by rw [ep2]
  clear ep2
  have h0eps : p1.eps = eps := by rw [ha.eps, ep]
  have h0target : p1.target = T := by rw [ha.target, ep]
  have h0claim : p1.claim = OnBytes.Psc.claimAfter (List.replicate lay.lk (OnBytes.Psc.Weight.plain
      3))
      (qs.map fun q => (q.2.1, q.2.2)) (addE mu (mulE eps T)) := by rw [ha.claim, ep]
  have h0r : p1.r.toList = qs.map (·.2.2) := by rw [ha.r, ep]; simp
  have h0vars : p1.vars.toList = List.replicate lay.lk (OnBytes.Psc.Weight.plain 3) := by
    rw [ha.vars, ep]; simp
  have h0first : p1.first = F2.next := by rw [ha.first, ep]
  have h0start : p1.start = wsForkStart sv rho := by rw [ha.start]
  have h0started : p1.started = true := by rw [ha.started]
  have h0rowMade : p1.rowMade = false := by rw [ha.rowMade, ep]
  clear ha ep
  subst eF' et' eF6 et6 eF1 eF2 et2
  refine ⟨x, mu, eps, c, beta, v, T, r1, rY, rV, qs, hn, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [et, et3, et4, et5]
  · rw [← erho]; exact hT
  · rw [wp, p2eps, h0eps]
  · rw [wp, p2target, h0target]
  · rw [wp, p2claim, h0claim, claimAfter_snoc _ _ _ _ _ _ (by simp [hn])]
  · rw [wrm, hrm]; simp
  · rw [wbeta, p2r]; simp
  · rw [wp, p2r]; simp [h0r]
  · rw [wsFv, esFv, eF4, eF3]
  · rw [wsFv]; rw [eF4, eF3] at hh; exact hh
  · rw [wsFv, wfvp]; exact hs
  · rw [wrecs, wrm, erho]
  · rw [wp, p2vars]; simp [h0vars]
  · rw [wp, p2first, h0first]
  · rw [wp, p2start, h0start, erho]
  · rw [wp, p2started, h0started]
  · rw [wp, p2rowMade, h0rowMade]
  · rw [wp, p2ended]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.mergeHear_inv
