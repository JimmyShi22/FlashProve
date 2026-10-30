-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/Tie3.lean: the tie of the two texts of the masked sumcheck, third part: a
sumcheck that is left open, both ways; the strict maker's tape is such a tape; and from what the
premise `Named` follows. Theorems.

Main theorems:
  `hear_open : Spec.hear_open`, `open_hear : Spec.open_hear` (Johnson/Top/H/P1Tie/Stmt.lean).
  `tape_is : Spec.tape_is`.
  `named_of_tapeT`: `Named` holds of the strict maker's tape of one call's own rounds, at entries
    that are that call's own but for the work bits.

The converse goes as in Johnson/Top/H/P1Tie/Tie2.lean: the tape's shape from the flat steps' return;
the part reads; the first direction on the same tape; a function has one value. As machine words; no
premise on words.

Limits. `named_of_tapeT` does not show that its two premises are met at a proof file. `entriesFit`
(Johnson/Desc/First/Look/Via/Rounds.lean) speaks of a whole lookup's list of entries; that this list
and the strict maker's tape cut into the calls' stretches is not shown in this file. A tie: it has
no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.P1Tie.Tie2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Fork Psc RoundForm)
open VerifiableInference.Desc.K3Cut (bindM bindS pureS stepR roundsIn_def)

/-- The variables of a sumcheck that is left open. -/
abbrev opts (zs : List (E × Nat)) : List Var := zs.map fun x => Var.point x.1 (x.2 + 1)

/-- The degrees add up. -/
abbrev degs (zs : List (E × Nat)) : Nat := (zs.map (·.2)).sum

/-! ## Small things -/

theorem P1Tie.hideRun_nil (F : Fork) (first : Nat) (factor : E) :
    F.hideRun first ([] : List E).toArray factor = some F := by
  unfold Fork.hideRun
  rw [← Array.foldlM_toList]
  rfl

theorem slots_opts : ∀ (zs : List (E × Nat)) (a : Nat),
    (opts zs).foldl (fun n v => n + (v.d - 1)) a = a + degs zs
  | [], a => rfl
  | x :: zs, a => by
    show (opts zs).foldl (fun n v => n + (v.d - 1)) (a + (x.2 + 1 - 1)) = a + (x.2 + degs zs)
    rw [slots_opts zs]
    omega

theorem keys_openCall (zs : List (E × Nat)) :
    ((entries (openCall zs)).map fun e => (some e.name, e.drawNZ)) =
      ((some "PSC epsilon", 0) : Option String × Nat) ::
        ((zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ++ []) := by
  show (([entry "PSC epsilon" (0 + 1) 1 0] ++
    ((opts zs).map fun (v : Var) => entry "PSC round" (v.d - 1) 1 0)) ++
      ([] : List Fmt.Entry)).map (fun (e : Fmt.Entry) => (some e.name, e.drawNZ)) = _
  rw [List.map_append, List.map_append, List.map_map, List.map_map]
  rfl

theorem bounds_openCall {zs : List (E × Nat)} (h : shapeOk (openCall zs) = true) :
    (∀ x ∈ zs, 1 ≤ x.2 ∧ x.2 ≤ 64) ∧ zs ≠ [] := by
  have h' : ((opts zs).all (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) && !(opts zs).isEmpty) =
    true := h
  rw [Bool.and_eq_true, List.all_eq_true] at h'
  refine ⟨fun x hx => ?_, ?_⟩
  · have k := h'.1 (Var.point x.1 (x.2 + 1)) (List.mem_map.2 ⟨x, hx, rfl⟩)
    have k' : (decide (2 ≤ x.2 + 1) && decide (x.2 + 1 ≤ 65)) = true := k
    simp only [Bool.and_eq_true, decide_eq_true_eq] at k'
    omega
  · intro e
    subst e
    have k : (!([] : List Var).isEmpty) = true := h'.2
    simp at k

theorem shapeOk_openCall {zs : List (E × Nat)} (h1 : ∀ x ∈ zs, 1 ≤ x.2 ∧ x.2 ≤ 64) (h2 : zs ≠ []) :
    shapeOk (openCall zs) = true := by
  show ((opts zs).all (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) && !(opts zs).isEmpty) = true
  have a : (opts zs).all (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) = true := by
    rw [List.all_eq_true]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
    obtain ⟨b1, b2⟩ := h1 x hx
    show (decide (2 ≤ x.2 + 1) && decide (x.2 + 1 ≤ 65)) = true
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have b : (!(opts zs).isEmpty) = true := by
    cases zs with
    | nil => exact absurd rfl h2
    | cons x zs => rfl
  rw [a, b]
  rfl

theorem readAll_open_some {vs : List Var} {rs : List Fmt.RoundView} {x : Read}
    (h : readAll ⟨0, vs, none⟩ rs = some x) :
    ∃ r0 rest, rs = r0 :: rest ∧ roundOf 1 1 r0 = some ([x.mu], [x.eps]) ∧ varRounds vs rest =
      some (x.rounds, []) ∧
      x.values = [] := by
  cases rs with
  | nil =>
    have h' : (none : Option Read) = some x := h
    cases h'
  | cons r0 rest =>
    cases h1 : firstRound ⟨0, vs, none⟩ r0 with
    | none => simp [readAll, h1] at h
    | some a =>
      obtain ⟨mu, eps, ea, h1'⟩ := firstRound_some0 h1
      subst ea
      cases h2 : varRounds (Call.all ⟨0, vs, none⟩) rest with
      | none => simp [readAll, h1, h2] at h
      | some y =>
        obtain ⟨l, R⟩ := y
        match R, h2 with
        | _ :: _, h2 => simp [readAll, h1, h2] at h
        | [], h2 =>
          simp only [readAll, h1, h2] at h
          have h' : some (⟨mu, eps, l, []⟩ : Read) = some x := h
          cases h'
          exact ⟨r0, rest, rfl, h1', h2, rfl⟩

theorem readAll_open_mk {vs : List Var} {r0 : Fmt.RoundView} {rest : List Fmt.RoundView} {mu eps : E}
    {l : List (List E × E)}
    (h1 : roundOf 1 1 r0 = some ([mu], [eps])) (h2 : varRounds vs rest = some (l, [])) :
    readAll ⟨0, vs, none⟩ (r0 :: rest) = some ⟨mu, eps, l, []⟩ := by
  have hf : firstRound ⟨0, vs, none⟩ r0 = some ([], [mu], [eps]) := by
    have h1' : roundOf (0 + 1) 1 r0 = some ([mu], [eps]) := h1
    simp only [firstRound, h1', Option.map_some]
    rfl
  have hall : varRounds (Call.all ⟨0, vs, none⟩) rest = some (l, []) := h2
  simp only [readAll, hf, hall]

/-! ## (3a) -/

theorem stepR_mk (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r acc : List E) (c z : E)
    (deg : Nat)
    (h1 : 1 ≤ deg) (h2 : deg ≤ 64) (w : Nat) (sent : List E) (x : E) (t : Tape) (F : Fork)
      (hs : sent.length = deg) :
    stepR .eq (acc.toArray, pscAt C T eps first vs r c false) (z, deg) F
      (⟨some "PSC round", 0, w, sent, [x]⟩ :: t) =
      some (((acc ++ [x]).toArray, pscAt C T eps first (vs ++ [Var.point z (deg + 1)]) (r ++ [x])
        (valueAt (complete (.point z (deg + 1)) sent c) x) false), tk F deg, t) := by
  unfold stepR
  refine bindM (roundIn_mk .eq deg C T eps first vs r c z (deg + 1) (by omega)
    (weight_eq z deg h1 h2) w sent x t F
    (by omega)) ?_
  show some ((acc.toArray.push x, _), _, t) = _
  rw [List.push_toArray]
  rfl

/-- No variable: nothing is heard. -/
theorem opens_nil (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r acc : List E) (c : E)
    (F : Fork) (t : Tape) :
    ([] : List (E × Nat)).foldlM (stepR .eq) (acc.toArray, pscAt C T eps first vs r c false) F t =
      some (((acc ++ ([] : List (List E × E)).map (·.2)).toArray,
        pscAt C T eps first (vs ++ opts []) (r ++ ([] : List (List E × E)).map (·.2))
          (after (opts []) [] c) false),
        tk F (degs []), t) := by
  have e1 : vs ++ opts [] = vs := List.append_nil vs
  have e2 : r ++ ([] : List (List E × E)).map (·.2) = r := List.append_nil r
  have e5 : acc ++ ([] : List (List E × E)).map (·.2) = acc := List.append_nil acc
  have e3 : after (opts []) [] c = c := rfl
  have e4 : degs [] = 0 := rfl
  rw [e1, e2, e5, e3, e4, tk_zero, List.foldlM_nil]
  rfl

/-- One variable more, in front. -/
theorem opens_step (C : Aff) (T eps : E) (first : Nat) (z : E) (deg : Nat) (d1 : 1 ≤ deg)
    (d2 : deg ≤ 64)
    (zs : List (E × Nat)) (vs : List Var) (r acc : List E) (c : E) (w : Nat) (sent : List E) (g : E)
      (t t' : Tape) (F : Fork)
    (l' : List (List E × E)) (a3 : sent.length = deg)
    (b3 : zs.foldlM (stepR .eq) ((acc ++ [g]).toArray,
      pscAt C T eps first (vs ++ [Var.point z (deg + 1)]) (r ++ [g])
        (valueAt (complete (.point z (deg + 1)) sent c) g) false) (tk F deg) t =
      some ((((acc ++ [g]) ++ l'.map (·.2)).toArray,
        pscAt C T eps first ((vs ++ [Var.point z (deg + 1)]) ++ opts zs)
          ((r ++ [g]) ++ l'.map (·.2))
          (after (opts zs) l' (valueAt (complete (.point z (deg + 1)) sent c) g)) false),
            tk (tk F deg) (degs zs), t')) :
    ((z, deg) :: zs).foldlM (stepR .eq) (acc.toArray, pscAt C T eps first vs r c false) F
        (⟨some "PSC round", 0, w, sent, [g]⟩ :: t) =
      some (((acc ++ ((sent, g) :: l').map (·.2)).toArray,
        pscAt C T eps first (vs ++ opts ((z, deg) :: zs)) (r ++ ((sent, g) :: l').map (·.2))
          (after (opts ((z, deg) :: zs)) ((sent, g) :: l') c) false), tk F (degs ((z, deg) :: zs)),
            t') := by
  have e1 : vs ++ opts ((z, deg) :: zs) = (vs ++ [Var.point z (deg + 1)]) ++ opts zs := by
    simp [opts]
  have e2 : r ++ (((sent, g) :: l').map (·.2)) = (r ++ [g]) ++ l'.map (·.2) := by simp
  have e5 : acc ++ (((sent, g) :: l').map (·.2)) = (acc ++ [g]) ++ l'.map (·.2) := by simp
  have e3 : degs ((z, deg) :: zs) = deg + degs zs := rfl
  have e4 : after (opts ((z, deg) :: zs)) ((sent, g) :: l') c =
      after (opts zs) l' (valueAt (complete (.point z (deg + 1)) sent c) g) :=
    after_cons (Var.point z (deg + 1)) (opts zs) sent g l' c
  rw [e1, e2, e5, e3, e4, ← tk_tk, List.foldlM_cons]
  exact bindM (stepR_mk C T eps first vs r acc c z deg d1 d2 w sent g t F a3) b3

theorem opens_cut (C : Aff) (T eps : E) (first : Nat) (zs : List (E × Nat)) :
    (∀ x ∈ zs, 1 ≤ x.2 ∧ x.2 ≤ 64) →
    ∀ (rs : List Fmt.RoundView) (t : Tape) (ks : List (Option String × Nat)) (l : List (List E × E))
      (rest : List Fmt.RoundView)
      (vs : List Var) (r acc : List E) (c : E) (F : Fork),
    varRounds (opts zs) rs = some (l, rest) → IsTape rs t →
    t.map keyOf = (zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ++ ks →
    ∃ t', IsTape rest t' ∧ t'.map keyOf = ks ∧ ∀ u : Tape,
      zs.foldlM (stepR .eq) (acc.toArray, pscAt C T eps first vs r c false) F (t ++ u) =
        some (((acc ++ l.map (·.2)).toArray,
          pscAt C T eps first (vs ++ opts zs) (r ++ l.map (·.2)) (after (opts zs) l c) false),
            tk F (degs zs), t' ++ u) := by
  induction zs with
  | nil =>
    intro _ rs t ks l rest vs r acc c F hv ht hk
    have hv' : varRounds [] rs = some (l, rest) := hv
    rw [varRounds_nil] at hv'
    have e := Option.some.inj hv'
    cases e
    exact ⟨t, ht, hk, fun u => opens_nil C T eps first vs r acc c F (t ++ u)⟩
  | cons y zs ih =>
    intro hb rs t ks l rest vs r acc c F hv ht hk
    obtain ⟨z, deg⟩ := y
    obtain ⟨d1, d2⟩ := hb (z, deg) (by simp)
    cases rs with
    | nil =>
      have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l, rest) := hv
      cases h'
    | cons r0 rs =>
      cases t with
      | nil => exact ht.elim
      | cons x t =>
        obtain ⟨s, g, l', h1, h2, e⟩ := varRounds_cons_some (v := Var.point z (deg + 1))
          (vs := opts zs) hv
        subst e
        have ht' : IsRound r0 x ∧ IsTape rs t := ht
        obtain ⟨a1, a2, a3, -⟩ := isRound_of ht'.1 h1
        obtain ⟨nm, nz, w, sent, drawn⟩ := x
        have a1' : sent = s := a1
        have a2' : drawn = [g] := a2
        subst a1' a2'
        rw [List.map_cons, List.map_cons, List.cons_append] at hk
        obtain ⟨k1, k2⟩ := List.cons.inj hk
        have k3 : nm = some "PSC round" := congrArg Prod.fst k1
        have k4 : nz = 0 := congrArg Prod.snd k1
        subst k3 k4
        have a3' : sent.length = deg := by
          have a4 : sent.length = deg + 1 - 1 := a3
          omega
        obtain ⟨t', b1, b2, b3⟩ := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx)) rs t ks l' rest
          (vs ++ [Var.point z (deg + 1)]) (r ++ [g]) (acc ++ [g])
            (valueAt (complete (.point z (deg + 1)) sent c) g)
          (tk F deg) h2 ht'.2 k2
        exact ⟨t', b1, b2, fun u =>
          opens_step C T eps first z deg d1 d2 zs vs r acc c w sent g (t ++ u) (t' ++ u) F l' a3'
            (b3 u)⟩

/-- **(3a) A sumcheck left open: the part's yes gives the flat beginning and rounds.** -/
theorem hear_open : Spec.hear_open := by
  intro C zs F G rs h t u hh ht hn
  obtain ⟨hk, T, x, hT, hR, hG, hrec⟩ := hear_some hh
  obtain ⟨mu, eps, rounds, values⟩ := x
  obtain ⟨r0, rest, ers, q0, qv, qe⟩ := readAll_open_some (vs := opts zs) hR
  subst ers
  have qe' : values = [] := qe
  subst qe'
  obtain ⟨hb, -⟩ := bounds_openCall hk
  cases t with
  | nil => exact ht.elim
  | cons x0 t1 =>
    have ht' : IsRound r0 x0 ∧ IsTape rest t1 := ht
    have hn' : (x0 :: t1).map keyOf = _ := hn
    rw [keys_openCall, List.map_cons] at hn'
    obtain ⟨n0, n1⟩ := List.cons.inj hn'
    obtain ⟨a1, a2, -, -⟩ := isRound_of ht'.1 q0
    obtain ⟨nm, nz, w, sent, drawn⟩ := x0
    have a1' : sent = [mu] := a1
    have a2' : drawn = [eps] := a2
    subst a1' a2'
    have n0' : (nm, nz) = ((some "PSC epsilon", 0) : Option String × Nat) := n0
    cases n0'
    obtain ⟨t', b1, -, b3⟩ := opens_cut C T eps F.next zs hb rest t1 [] rounds [] [] [] []
      (addE mu (mulE eps T)) (tk F 1) qv ht'.2 n1
    cases t' with
    | cons _ _ => exact b1.elim
    | nil =>
      -- the ledger: the slots are counted; nothing is laid
      have o1 : ownSlots (openCall zs).all = 1 + degs zs := slots_opts zs 1
      have hG' : ({ F with next := F.next + ownSlots (openCall zs).all + ([] : List E).length } :
        Fork).hideRun
          (F.next + ownSlots (openCall zs).all) ([] : List E).toArray
            ((rounds.map (·.2)).getLastD zeroE) = some G := hG
      rw [P1Tie.hideRun_nil, o1] at hG'
      have eG : tk (tk F 1) (degs zs) = G := by
        rw [tk_tk]
        exact Option.some.inj hG'
      refine ⟨_, _, _, pscBegin_mk mu eps w (t1 ++ u) hT, ?_⟩
      rw [roundsIn_def]
      refine (b3 u).trans ?_
      rw [eG, hrec]
      rfl

/-! ## (3b) -/

theorem weight_eq_inv {z : E} {deg : Nat} {w : OnBytes.Psc.Weight}
    (h : RoundForm.eq.weight z deg = some w) :
    1 ≤ deg ∧ deg ≤ 64 ∧ w = OnBytes.Psc.Weight.equality z (deg + 1) := by
  cases hd : RoundForm.eq.degreeOK deg with
  | false =>
    unfold RoundForm.weight at h
    rw [hd] at h
    simp at h
  | true =>
    have hd' : (!(RoundForm.eq == RoundForm.nodes || RoundForm.eq == RoundForm.eq) ||
        (decide (1 ≤ deg) && decide (deg ≤ 64))) = true := hd
    have hb : 1 ≤ deg ∧ deg ≤ 64 := by
      simpa using hd'
    refine ⟨hb.1, hb.2, ?_⟩
    have e := (weight_eq z deg hb.1 hb.2).symm.trans h
    exact (Option.some.inj e).symm

theorem stepR_inv {s s' : Array E × Psc} {z : E} {deg : Nat} {F F' : Fork} {c c' : Tape}
    (h : stepR .eq s (z, deg) F c = some (s', F', c')) :
    ∃ w sent x, c = ⟨some "PSC round", 0, w, sent, [x]⟩ :: c' ∧ sent.length = deg ∧ 1 ≤ deg ∧ deg ≤
      64 := by
  unfold stepR at h
  obtain ⟨⟨x, q⟩, F1, c1, h1, h2⟩ := bindS h
  obtain ⟨-, e2, e3⟩ := pureS h2
  subst e2 e3
  obtain ⟨wt, sent, -, hw, -, -, hev, -, -⟩ := Fo.Tp.roundIn_ok .eq s.2 z deg F F' c c' x q h1
  obtain ⟨d1, d2, rfl⟩ := weight_eq_inv hw
  obtain ⟨c1, g1, c2, g2, e⟩ := hev
  have e' : c' = c2 := e
  subst e'
  have g1' : recvN (deg + 1 - 1) c = some (sent, c1) := g1
  have g2' : closeOne Model.RoundName.pscRound.name 0 c1 = some (x, c') := g2
  obtain ⟨w, rfl⟩ := closeOne_inv g2'
  obtain ⟨k1, k2⟩ := Fo.Tp.recvN_some g1' rfl
  refine ⟨w, sent.toList, x, k2, ?_, d1, d2⟩
  rw [Array.length_toList]
  omega

theorem foldR_inv : ∀ (zs : List (E × Nat)) (s : Array E × Psc) (F : Fork) (c : Tape)
    (s1 : Array E × Psc) (F1 : Fork)
    (c1 : Tape), zs.foldlM (stepR .eq) s F c = some (s1, F1, c1) →
    ∃ tv : Tape, c = tv ++ c1 ∧ tv.map keyOf =
      (zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ∧
      tv.map (fun y => (y.sent.length, y.drawn.length)) = zs.map (fun x => (x.2, 1)) ∧
        (∀ x ∈ zs, 1 ≤ x.2 ∧ x.2 ≤ 64)
  | [], s, F, c, s1, F1, c1, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨-, -, e3⟩ := pureS h
    subst e3
    exact ⟨[], rfl, rfl, rfl, fun x hx => by simp at hx⟩
  | (z, deg) :: zs, s, F, c, s1, F1, c1, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨q, F2, c2, h1, h2⟩ := bindS h
    obtain ⟨w, sent, x, e1, e2, d1, d2⟩ := stepR_inv h1
    obtain ⟨tv, g1, g3, g4, g5⟩ := foldR_inv zs q F2 c2 s1 F1 c1 h2
    refine ⟨⟨some "PSC round", 0, w, sent, [x]⟩ :: tv, ?_, ?_, ?_, ?_⟩
    · rw [e1, g1]
      rfl
    · rw [List.map_cons, List.map_cons, g3]
      rfl
    · rw [List.map_cons, List.map_cons, g4]
      show (sent.length, 1) :: _ = (deg, 1) :: _
      rw [e2]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨d1, d2⟩
      · exact g5 y hy

theorem opens_read : ∀ (zs : List (E × Nat)) (tv : Tape) (rs : List Fmt.RoundView), IsTape rs tv →
    tv.map (fun y => (y.sent.length, y.drawn.length)) = zs.map (fun x => (x.2, 1)) →
    ∃ l, varRounds (opts zs) rs = some (l, [])
  | [], [], [], _, _ => ⟨[], rfl⟩
  | [], [], _ :: _, ht, _ => ht.elim
  | x :: zs, y :: tv, [], ht, _ => ht.elim
  | x :: zs, y :: tv, r0 :: rs, ht, hl => by
    rw [List.map_cons, List.map_cons] at hl
    obtain ⟨k1, k2⟩ := List.cons.inj hl
    have k1' : (y.sent.length, y.drawn.length) = (x.2, 1) := k1
    have s1 : y.sent.length = x.2 := congrArg Prod.fst k1'
    have s2 : y.drawn.length = 1 := congrArg Prod.snd k1'
    obtain ⟨l, h1⟩ := opens_read zs tv rs ht.2 k2
    obtain ⟨g, eg⟩ := one_of_length y.drawn s2
    have hr : roundOf ((Var.point x.1 (x.2 + 1)).d - 1) 1 r0 = some (y.sent, [g]) := by
      rw [← eg]
      exact roundOf_tape ht.1 (by show y.sent.length = x.2 + 1 - 1; omega) s2
    exact ⟨(y.sent, g) :: l, varRounds_cons_mk (v := Var.point x.1 (x.2 + 1)) (vs := opts zs) hr h1⟩
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl

/-- **(3b) The flat beginning and rounds give the part's yes.** -/
theorem open_hear : Spec.open_hear := by
  intro C zs F G rs t u p0 F0 t0 r p hz ht k0 k1
  obtain ⟨T, mu, eps, w0, hT, c0, -⟩ := begin_inv k0
  have k1' := k1
  rw [roundsIn_def] at k1'
  obtain ⟨tv, g1, g3, g4, g5⟩ := foldR_inv zs _ F0 t0 _ G u k1'
  have et : t = ⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ :: tv := by
    apply List.append_cancel_right (bs := u)
    rw [c0, g1]
    rfl
  subst et
  have hN : Named (openCall zs) (⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ :: tv) := by
    show (_ :: tv).map keyOf = _
    rw [keys_openCall, List.map_cons, g3, List.append_nil]
    rfl
  cases rs with
  | nil => exact ht.elim
  | cons r0 rest =>
    have ht' : IsRound r0 ⟨some "PSC epsilon", 0, w0, [mu], [eps]⟩ ∧ IsTape rest tv := ht
    have q0 : roundOf 1 1 r0 = some ([mu], [eps]) := roundOf_tape ht'.1 rfl rfl
    obtain ⟨l, v1⟩ := opens_read zs tv rest ht'.2 g4
    have hR : readAll (openCall zs) (r0 :: rest) = some ⟨mu, eps, l, []⟩ :=
      readAll_open_mk (vs := opts zs) q0 v1
    have hL : ledgerOf (openCall zs) F ⟨mu, eps, l, []⟩ =
        some { F with next := F.next + ownSlots (openCall zs).all + ([] : List E).length } :=
          P1Tie.hideRun_nil _ _ _
    have hh := hear_mk (shapeOk_openCall g5 hz) hT hR hL
    obtain ⟨p0', F0', t0', k0', k1''⟩ := hear_open C zs F _ (r0 :: rest) _ _ u hh ht hN
    have e0 := Option.some.inj (k0.symm.trans k0')
    cases e0
    have e1 := Option.some.inj (k1.symm.trans k1'')
    have e2 : r = (P1Tie.heardOf C (openCall zs) F T ⟨mu, eps, l, []⟩).r.toArray :=
      congrArg (fun x => x.1.1) e1
    have e3 : p = (P1Tie.heardOf C (openCall zs) F T ⟨mu, eps, l, []⟩).psc false :=
      congrArg (fun x => x.1.2) e1
    have e4 : G = { F with next := F.next + ownSlots (openCall zs).all + ([] : List E).length } :=
      congrArg (fun x => x.2.1) e1
    subst e2 e3 e4
    exact ⟨_, hh, rfl, rfl⟩

/-! ## The strict maker's tape -/

theorem elemsOf_eq : ∀ (l : List Fmt.ItemValue), First.Tape.elemsOf l = scalars l
  | [] => rfl
  | .e x :: l => by
    show (First.Tape.elemsOf l).map (E.ofTriple x :: ·) = (scalars l).map (E.ofTriple x :: ·)
    rw [elemsOf_eq l]
  | .f _ :: _ => rfl
  | .word _ :: _ => rfl
  | .root _ :: _ => rfl
  | .answer _ :: _ => rfl

theorem roundT_is {rule : First.Tape.TapeRule} {r : Fmt.RoundView} {e : Fmt.Entry} {x : FlatRound}
    (h : First.Tape.roundT rule r e = some x) :
      IsRound r x ∧ keyOf x = (some e.name, e.drawNZ) := by
  cases hs : First.Tape.elemsOf r.vals with
  | none => simp [First.Tape.roundT, hs] at h
  | some sent =>
    simp only [First.Tape.roundT, hs] at h
    split at h
    · have e1 := Option.some.inj h
      subst e1
      exact ⟨⟨by rw [← elemsOf_eq]; exact hs, rfl⟩, rfl⟩
    · cases h

/-- **The strict maker's tape is such a tape**, and bears its entries' names and numbers. -/
theorem tape_is : Spec.tape_is := by
  intro rule rs
  induction rs with
  | nil =>
    intro es t h
    cases es with
    | nil =>
      have h' : some ([] : Tape) = some t := h
      cases h'
      exact ⟨trivial, rfl⟩
    | cons e es => simp [First.Tape.tapeT] at h
  | cons r rs ih =>
    intro es t h
    cases es with
    | nil => simp [First.Tape.tapeT] at h
    | cons e es =>
      simp only [First.Tape.tapeT] at h
      cases hx : First.Tape.roundT rule r e with
      | none => simp [hx] at h
      | some x =>
        cases ht : First.Tape.tapeT rule rs es with
        | none => simp [hx, ht] at h
        | some t' =>
          simp only [hx, ht, Option.some.injEq] at h
          subst h
          obtain ⟨a1, a2⟩ := roundT_is hx
          obtain ⟨b1, b2⟩ := ih es t' ht
          refine ⟨⟨a1, b1⟩, ?_⟩
          rw [List.map_cons, List.map_cons, a2, b2]

/-- **From what the premise `Named` follows**: the strict maker's tape of one call's own rounds, at
entries that are that call's own but for the work bits, is the tape of these rounds and bears the
call's names. It moves the question to these two premises; that they are met at a call inside a
lookup of a proof file is not shown here: `entriesFit` speaks of the whole lookup's list. -/
theorem named_of_tapeT {rule : First.Tape.TapeRule} {rs : List Fmt.RoundView} {es : List Fmt.Entry}
    {t : Tape} {k : Call}
    (h : First.Tape.tapeT rule rs es = some t)
      (he : (es.map fun e => { e with work := 0 }) = entries k) :
    IsTape rs t ∧ Named k t := by
  obtain ⟨a, b⟩ := tape_is rule rs es t h
  refine ⟨a, ?_⟩
  show t.map keyOf = (entries k).map fun e => (some e.name, e.drawNZ)
  rw [b, ← he, List.map_map]
  rfl

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_open
#print axioms VerifiableInference.Desc.Part.MaskedSum.open_hear
#print axioms VerifiableInference.Desc.Part.MaskedSum.tape_is
#print axioms VerifiableInference.Desc.Part.MaskedSum.named_of_tapeT
