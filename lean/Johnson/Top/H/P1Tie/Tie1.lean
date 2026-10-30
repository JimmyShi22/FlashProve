-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/P1Tie/Tie1.lean: the tie of the two texts of the masked sumcheck, first half: from the
part's yes to the flat course. Theorems.

Main theorems:
  `heard_cut`: the hearing with ends: `Fl.pscBegin`, the fold of `stepW` and `Fl.pscEnds` return,
    with the verifier program's record of what was heard and the same ledger.
  `whole_cut : Spec.whole_cut` (Johnson/Top/H/P1Tie/Stmt.lean).
As machine words; no premise on words (Johnson/Top/H/P1Tie/Words.lean).

Limits. Those of Johnson/Top/H/P1Tie/Stmt.lean's head. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.P1Tie.Stmt
import Johnson.Top.H.P1Tie.FlatMk
import Johnson.Top.H.P1Tie.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Aff Fork Psc RoundForm)
open VerifiableInference.Desc.First.Prod (Whole)
open VerifiableInference.Desc.K3Cut (WholeCut bindM mustM stepW shown_at)

/-! ## Small things -/

/-- The ledger with n more slots counted. -/
def tk (F : Fork) (n : Nat) : Fork := { F with next := F.next + n }

theorem tk_tk (F : Fork) (a b : Nat) : tk (tk F a) b = tk F (a + b) := by
  show ({ F with next := F.next + a + b } : Fork) = { F with next := F.next + (a + b) }
  rw [Nat.add_assoc]

/-- What a read round says of the tape's round. -/
theorem isRound_of {n k : Nat} {r : Fmt.RoundView} {x : FlatRound} {s d : List E} (hx : IsRound r x)
    (h : roundOf n k r = some (s, d)) : x.sent = s ∧ x.drawn = d ∧ s.length = n ∧ d.length = k := by
  obtain ⟨a1, a2, a3, a4⟩ := roundOf_some h
  obtain ⟨b1, b2⟩ := hx
  refine ⟨Option.some.inj (b1.symm.trans a1), b2.trans a4.symm, a2, ?_⟩
  rw [a4, List.length_map]
  exact a3

/-- The point-variables of the stand-in. -/
abbrev pts (zs : List E) : List Var := zs.map fun z => Var.point z 3

/-- The further variable. -/
abbrev varY (dY : Nat) : Var := Var.point zeroE (dY + 1)

theorem slots_pts (dY : Nat) : ∀ (zs : List E) (a : Nat),
    (pts zs ++ [varY dY]).foldl (fun n v => n + (v.d - 1)) a = a + 2 * zs.length + dY
  | [], a => by
    show a + (dY + 1 - 1) = a + 2 * 0 + dY
    omega
  | z :: zs, a => by
    show (pts zs ++ [varY dY]).foldl (fun n v => n + (v.d - 1)) (a + (3 - 1)) = _
    rw [slots_pts dY zs]
    simp only [List.length_cons]
    omega

/-! ## Reading all rounds of a call with ends and no lead -/

theorem firstRound_some0 {vs : List Var} {en : Option Ends} {r0 : Fmt.RoundView}
    {a : List E × List E × List E}
    (h : firstRound ⟨0, vs, en⟩ r0 = some a) :
    ∃ mu eps, a = ([], [mu], [eps]) ∧ roundOf 1 1 r0 = some ([mu], [eps]) := by
  unfold firstRound at h
  cases h1 : roundOf (0 + 1) 1 r0 with
  | none =>
    have h2 : ((roundOf (0 + 1) 1 r0).map fun x => (x.1.take 0, x.1.drop 0, x.2)) = some a := h
    rw [h1] at h2
    have h' : (none : Option (List E × List E × List E)) = some a := h2
    cases h'
  | some sd =>
    obtain ⟨s, d⟩ := sd
    have h2 : ((roundOf (0 + 1) 1 r0).map fun x => (x.1.take 0, x.1.drop 0, x.2)) = some a := h
    rw [h1] at h2
    have h' : some (s.take 0, s.drop 0, d) = some a := h2
    obtain ⟨_, b2, b3, b4⟩ := roundOf_some h1
    obtain ⟨mu, e1⟩ := one_of_length s b2
    obtain ⟨eps, e2⟩ := one_of_length d (by rw [b4, List.length_map]; exact b3)
    subst e1 e2
    cases h'
    exact ⟨mu, eps, rfl, rfl⟩

theorem readAll_ends_some {vs : List Var} {e : Ends} {rs : List Fmt.RoundView} {x : Read}
    (h : readAll ⟨0, vs, some e⟩ rs = some x) :
    ∃ r0 rest rv d, rs = r0 :: rest ∧ roundOf 1 1 r0 = some ([x.mu], [x.eps]) ∧
      varRounds (vs ++ [varY e.dY]) rest = some (x.rounds, [rv]) ∧ roundOf e.n 0 rv =
        some (x.values, d) := by
  cases rs with
  | nil =>
    have h' : (none : Option Read) = some x := h
    cases h'
  | cons r0 rest =>
    cases h1 : firstRound ⟨0, vs, some e⟩ r0 with
    | none => simp [readAll, h1] at h
    | some a =>
      obtain ⟨mu, eps, ea, h1'⟩ := firstRound_some0 h1
      subst ea
      cases h2 : varRounds (Call.all ⟨0, vs, some e⟩) rest with
      | none => simp [readAll, h1, h2] at h
      | some y =>
        obtain ⟨l, R⟩ := y
        match R, h2 with
        | [], h2 => simp [readAll, h1, h2] at h
        | _ :: _ :: _, h2 => simp [readAll, h1, h2] at h
        | [rv], h2 =>
          simp only [readAll, h1, h2] at h
          cases h3 : roundOf e.n 0 rv with
          | none =>
            rw [h3] at h
            have h' : (none : Option Read) = some x := h
            cases h'
          | some sd =>
            obtain ⟨s, d⟩ := sd
            rw [h3] at h
            have h' : some (⟨mu, eps, l, s⟩ : Read) = some x := h
            cases h'
            exact ⟨r0, rest, rv, d, rfl, h1', h2, h3⟩

/-! ## The names -/

theorem keys_callOf (zs : List E) (dY n : Nat) :
    ((entries (callOf zs dY n)).map fun e => (some e.name, e.drawNZ)) =
      ((some "PSC epsilon", 0) : Option String × Nat) ::
        ((zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ++
          [(some "PSC Y", 1), (some "PSC values", 0)]) := by
  show (([entry "PSC epsilon" (0 + 1) 1 0] ++
    ((pts zs).map fun v => entry "PSC round" (v.d - 1) 1 0)) ++
      [entry "PSC Y" dY 1 1, entry "PSC values" n 0 0]).map (fun e => (some e.name, e.drawNZ)) = _
  rw [List.map_append, List.map_append, List.map_map, List.map_map]
  rfl

/-! ## The variables -/

theorem stepW_mk (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r : List E) (c z : E)
    (w : Nat) (sent : List E)
    (x : E) (t : Tape) (F : Fork) (hs : sent.length = 2) :
    stepW (pscAt C T eps first vs r c false) z F (⟨some "PSC round", 0, w, sent, [x]⟩ :: t) =
      some (pscAt C T eps first (vs ++ [Var.point z 3]) (r ++ [x])
        (valueAt (complete (.point z 3) sent c) x) false,
        tk F 2, t) := by
  unfold stepW
  exact bindM (roundIn_mk .eq2 0 C T eps first vs r c z 3 (by omega) (weight_eq2 z) w sent x t F
    (by omega)) rfl

theorem after_cons (v : Var) (vs : List Var) (s : List E) (g : E) (l : List (List E × E)) (c : E) :
    after (v :: vs) ((s, g) :: l) c = after vs l (valueAt (complete v s c) g) := rfl

theorem tk_zero (F : Fork) : tk F 0 = F := rfl

/-- No variable: nothing is heard. -/
theorem vars_nil (C : Aff) (T eps : E) (first : Nat) (vs : List Var) (r : List E) (c : E) (F : Fork)
    (t : Tape) :
    ([] : List E).foldlM stepW (pscAt C T eps first vs r c false) F t =
      some (pscAt C T eps first (vs ++ pts []) (r ++ ([] : List (List E × E)).map (·.2))
        (after (pts []) [] c) false,
        tk F (2 * ([] : List E).length), t) := by
  have e1 : vs ++ pts [] = vs := List.append_nil vs
  have e2 : r ++ ([] : List (List E × E)).map (·.2) = r := List.append_nil r
  have e3 : after (pts []) [] c = c := rfl
  have e4 : 2 * ([] : List E).length = 0 := rfl
  rw [e1, e2, e3, e4, tk_zero, List.foldlM_nil]
  rfl

/-- One variable more, in front. -/
theorem vars_step (C : Aff) (T eps : E) (first : Nat) (z : E) (zs : List E) (vs : List Var)
    (r : List E) (c : E) (w : Nat)
    (sent : List E) (g : E) (t t' : Tape) (F : Fork) (l' : List (List E × E)) (a3 : sent.length = 2)
    (b3 : zs.foldlM stepW (pscAt C T eps first (vs ++ [Var.point z 3]) (r ++ [g])
        (valueAt (complete (.point z 3) sent c) g) false) (tk F 2) t =
      some (pscAt C T eps first ((vs ++ [Var.point z 3]) ++ pts zs) ((r ++ [g]) ++ l'.map (·.2))
        (after (pts zs) l' (valueAt (complete (.point z 3) sent c) g)) false,
          tk (tk F 2) (2 * zs.length), t')) :
    (z :: zs).foldlM stepW (pscAt C T eps first vs r c false) F
      (⟨some "PSC round", 0, w, sent, [g]⟩ :: t) =
      some (pscAt C T eps first (vs ++ pts (z :: zs)) (r ++ ((sent, g) :: l').map (·.2))
        (after (pts (z :: zs)) ((sent, g) :: l') c) false, tk F (2 * (z :: zs).length), t') := by
  have e1 : vs ++ pts (z :: zs) = (vs ++ [Var.point z 3]) ++ pts zs := by simp [pts]
  have e2 : r ++ (((sent, g) :: l').map (·.2)) = (r ++ [g]) ++ l'.map (·.2) := by simp
  have e3 : 2 * (z :: zs).length = 2 + 2 * zs.length := by
    simp only [List.length_cons]
    omega
  have e4 : after (pts (z :: zs)) ((sent, g) :: l') c =
    after (pts zs) l' (valueAt (complete (.point z 3) sent c) g) :=
    after_cons (Var.point z 3) (pts zs) sent g l' c
  rw [e1, e2, e3, e4, ← tk_tk, List.foldlM_cons]
  exact bindM (stepW_mk C T eps first vs r c z w sent g t F a3) b3

/-- **The variables' rounds, read by the part, are heard by the fold of the flat rounds.** ks: the
names behind. -/
theorem vars_cut (C : Aff) (T eps : E) (first : Nat) (zs : List E) : ∀ (rs : List Fmt.RoundView) (t : Tape)
    (ks : List (Option String × Nat)) (l : List (List E × E)) (rest : List Fmt.RoundView) (vs : List Var)
      (r : List E) (c : E)
    (F : Fork),
    varRounds (pts zs) rs = some (l, rest) → IsTape rs t →
    t.map keyOf = (zs.map fun _ => ((some "PSC round", 0) : Option String × Nat)) ++ ks →
    ∃ t', IsTape rest t' ∧ t'.map keyOf = ks ∧ ∀ u : Tape,
      zs.foldlM stepW (pscAt C T eps first vs r c false) F (t ++ u) =
        some (pscAt C T eps first (vs ++ pts zs) (r ++ l.map (·.2)) (after (pts zs) l c) false,
          tk F (2 * zs.length), t' ++ u) := by
  induction zs with
  | nil =>
    intro rs t ks l rest vs r c F hv ht hk
    have hv' : varRounds [] rs = some (l, rest) := hv
    rw [varRounds_nil] at hv'
    have e := Option.some.inj hv'
    cases e
    exact ⟨t, ht, hk, fun u => vars_nil C T eps first vs r c F (t ++ u)⟩
  | cons z zs ih =>
    intro rs t ks l rest vs r c F hv ht hk
    cases rs with
    | nil =>
      have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l, rest) := hv
      cases h'
    | cons r0 rs =>
      cases t with
      | nil => exact ht.elim
      | cons x t =>
        obtain ⟨s, g, l', h1, h2, e⟩ := varRounds_cons_some (v := Var.point z 3) (vs := pts zs) hv
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
        obtain ⟨t', b1, b2, b3⟩ := ih rs t ks l' rest (vs ++ [Var.point z 3]) (r ++ [g])
          (valueAt (complete (.point z 3) sent c) g) (tk F 2) h2 ht'.2 k2
        exact ⟨t', b1, b2, fun u => vars_step C T eps first z zs vs r c w sent g (t ++ u) (t' ++ u)
          F l' a3 (b3 u)⟩

/-! ## The hearing -/

/-- **The hearing with ends: the flat beginning, rounds and ends return**, with `verify-on-bytes`'s
record of what was heard and the same ledger. -/
theorem heard_cut {C : Aff} {zs : List E} {dY n : Nat} {F G0 : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {t : Tape}
    (hh : hear C (callOf zs dY n) F rs = some (h, G0)) (ht : IsTape rs t)
      (hn : Named (callOf zs dY n) t) (u : Tape) :
    ∃ (p0 : Psc) (F0 : Fork) (t0 : Tape) (p1 : Psc) (F1 : Fork) (t1 : Tape),
      Fl.pscBegin C F (t ++ u) = some (p0, F0, t0) ∧ zs.foldlM stepW p0 F0 t0 = some (p1, F1, t1) ∧
      Fl.pscEnds p1 dY n F1 t1 = some ((h.sEnd, h.psc true), G0, u) ∧
      (∀ v ∈ h.vars, v.isPoint = true) ∧ h.vars ≠ [] ∧ h.r.length = h.vars.length := by
  obtain ⟨hk, T, x, hT, hR, hG, hrec⟩ := hear_some hh
  obtain ⟨mu, eps, rounds, values⟩ := x
  obtain ⟨r0, rest, rv, d, ers, q0, qv, qe⟩ := readAll_ends_some (vs := pts zs) (e := ⟨dY, n⟩) hR
  subst ers
  obtain ⟨l1, mid, l2, v1, v2, el, ell⟩ :=
    varRounds_append_some (pts zs) [varY dY] rest [rv] rounds qv
  have el' : rounds = l1 ++ l2 := el
  subst el'
  -- the round of the further variable
  cases mid with
  | nil =>
    have h' : (none : Option (List (List E × E) × List Fmt.RoundView)) = some (l2, [rv]) := v2
    cases h'
  | cons rY mid' =>
    obtain ⟨sY, beta, l', w1, w2, e2⟩ := varRounds_cons_some v2
    rw [varRounds_nil] at w2
    have e3 := Option.some.inj w2
    cases e3
    subst e2
    -- the shape's two bounds
    have hb : 1 ≤ dY ∧ 1 ≤ n := by
      have hk' : ((pts zs).all (fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) &&
          (decide (1 ≤ dY) && decide (1 ≤ n))) = true := hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk'
      exact hk'.2
    -- the tape, round by round
    cases t with
    | nil => exact ht.elim
    | cons x0 t1 =>
      have hn' : (x0 :: t1).map keyOf = _ := hn
      rw [keys_callOf, List.map_cons] at hn'
      obtain ⟨n0, n1⟩ := List.cons.inj hn'
      obtain ⟨a1, a2, -, -⟩ := isRound_of ht.1 q0
      obtain ⟨nm, nz, w, sent, drawn⟩ := x0
      have a1' : sent = [mu] := a1
      have a2' : drawn = [eps] := a2
      subst a1' a2'
      have n0' : (nm, nz) = ((some "PSC epsilon", 0) : Option String × Nat) := n0
      cases n0'
      obtain ⟨t', b1, b2, b3⟩ := vars_cut C T eps F.next zs rest t1 _ l1 (rY :: [rv]) [] []
        (addE mu (mulE eps T)) (tk F 1) v1 ht.2 n1
      match t', b1, b2, b3 with
      | [], b1, _, _ => exact b1.elim
      | [_], b1, _, _ => exact b1.2.elim
      | _ :: _ :: _ :: _, b1, _, _ => exact b1.2.2.elim
      | [xY, xV], b1, b2, b3 =>
        obtain ⟨c1, c2, c3, -⟩ := isRound_of b1.1 w1
        obtain ⟨d1, d2, d3, d4⟩ := isRound_of b1.2.1 qe
        obtain ⟨nmY, nzY, wY, sentY, drawnY⟩ := xY
        obtain ⟨nmV, nzV, wV, sentV, drawnV⟩ := xV
        have c1' : sentY = sY := c1
        have c2' : drawnY = [beta] := c2
        have d1' : sentV = values := d1
        have d2' : drawnV = d := d2
        subst c1' c2' d1' d2'
        have d5 : drawnV = [] := List.eq_nil_of_length_eq_zero d4
        subst d5
        have b2' : [(nmY, nzY), (nmV, nzV)] =
            ([(some "PSC Y", 1), (some "PSC values", 0)] : List (Option String × Nat)) := b2
        cases b2'
        -- the ledger
        have o1 : ownSlots (callOf zs dY n).all = 1 + 2 * zs.length + dY := slots_pts dY zs 1
        have o3 : ((l1 ++ [(sentY, beta)]).map (·.2)).getLastD zeroE = beta := by simp
        have hG' : ({ F with next := F.next + ownSlots (callOf zs dY n).all + sentV.length } :
          Fork).hideRun
            (F.next + ownSlots (callOf zs dY n).all) sentV.toArray
            (((l1 ++ [(sentY, beta)]).map (·.2)).getLastD zeroE) = some G0 := hG
        have a5 : F.next + (1 + 2 * zs.length + dY) = F.next + 1 + 2 * zs.length + dY := by omega
        rw [o1, o3, d3, a5] at hG'
        have c3' : sentY.length = dY := c3
        have hE := pscEnds_mk C T eps F.next ([] ++ pts zs) ([] ++ l1.map (·.2))
          (after (pts zs) l1 (addE mu (mulE eps T)))
          dY n hb.1 hb.2 wY wV sentY sentV beta u (tk (tk F 1) (2 * zs.length)) G0 c3' d3 hG'
        -- the record
        have hp : pscAt C T eps F.next ([] ++ pts zs ++ [varY dY]) ([] ++ l1.map (·.2) ++ [beta])
            (valueAt (complete (varY dY) sentY (after (pts zs) l1 (addE mu (mulE eps T)))) beta)
              true = h.psc true := by
          rw [hrec, psc_eq]
          show _ = pscAt C T eps F.next (pts zs ++ [varY dY]) ((l1 ++ [(sentY, beta)]).map (·.2))
            (after (pts zs ++ [varY dY]) (l1 ++ [(sentY, beta)]) (addE mu (mulE eps T))) true
          rw [List.map_append, after_append _ _ _ _ _ ell]
          rfl
        have hsE : F.next + 1 + 2 * zs.length + dY = h.sEnd := by
          rw [hrec]
          show _ = F.next + ownSlots (callOf zs dY n).all
          rw [o1]
          omega
        refine ⟨_, _, _, _, _, _, pscBegin_mk mu eps w (t1 ++ u) hT, b3 u, ?_, ?_, ?_, ?_⟩
        · rw [← hp, ← hsE]
          exact hE
        · intro v hv
          rw [hrec] at hv
          have hv' : v ∈ pts zs ++ [varY dY] := hv
          rw [List.mem_append] at hv'
          rcases hv' with hv' | hv'
          · obtain ⟨z, _, rfl⟩ := List.mem_map.1 hv'
            rfl
          · rw [List.mem_singleton] at hv'
            subst hv'
            rfl
        · rw [hrec]
          show pts zs ++ [varY dY] ≠ []
          simp
        · rw [hrec]
          show ((l1 ++ [(sentY, beta)]).map (·.2)).length = (pts zs ++ [varY dY]).length
          simp [ell]

/-- **(1) The part's yes gives the flat course.** -/
theorem whole_cut : Spec.whole_cut := by
  intro C zs dY n e F G rs h row t u hw ht hn
  obtain ⟨e0, G0, sh, he, hh, hs, hr⟩ := whole_some hw
  have he' : (⟨dY, n⟩ : Ends) = e0 := Option.some.inj he
  subst he'
  obtain ⟨p0, F0, t0, p1, F1, t1, k0, k1, k2, hp, hne, hl⟩ := heard_cut hh ht hn u
  obtain ⟨r1, r2⟩ := row_some hr
  subst r1
  have hsh : (List.range n).map (fun i => G0.shown (h.sEnd + i)) = sh.map some :=
    P1Tie.mapM_some _ _ _ hs
  exact ⟨p0, F0, t0, p1, F1, t1, h.psc true, G0, u, sh, _, k0, k1, k2, shown_at hsh,
    pscRow_mk h hp hne hl true (e sh) {} G0 G u r2, rfl⟩

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_cut
