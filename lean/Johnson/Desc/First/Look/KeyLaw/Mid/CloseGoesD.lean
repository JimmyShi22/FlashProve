-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CloseGoesD.lean: the course over the field goes with the plain
function of the described lookup at the test of the bits.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean). That the program's run, read in the field, is this
course is shown in files that are not in this library yet.

It imports CloseGoesB.lean. `Sim` is that of Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean,
`Goes` that of Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean, `cBits`, `pscC`, `heardF`, `slots`
those of Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean, `bitsRun` that of CloseRun.lean.
Main names:
  `fits_lk` flat rounds that fit k + 1 formats (2 scalars, one draw) are a list of pairs (scalars,
    challenge), written flat; the last pair is named.
  `heard_yes` what a sumcheck that shows one value reads of rounds that are written out.
  `finC_app` `Lev.finC k` reads the first k + 1 rounds alone.
  `bits_goes` `Goes` from seam 7 to seam 8, for `cBits` and `bitsRun`, under four conditions: the
    course's public record is that of the data; pl ≤ 2^mu; the place of the name i of the hiding
    polynomial of the test of the bits is the ledger's entry number own + ownAt 7 + `Cf.portIdx` i;
    the place cB is the entry number own + ownAt 7 + 1 + 2 (mu + d) + 2.
Limits: nothing on the program's blocks on machine words.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoesB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.Clo
open Lk6.PortSim Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

/-! ### the rounds -/

theorem fits_lk : ∀ (k : ℕ) (l : List (RV GE)),
    fitsAll (List.replicate k (⟨2, 1, false⟩ : Fm) ++ [⟨2, 1, true⟩]) l = true →
    ∃ (rs : List (List GE × GE)) (q : List GE) (b : GE),
      l = (rs ++ [(q, b)]).map (fun r => (r.1, [r.2])) ∧ rs.length = k ∧
      ∀ i : Fin (k + 1), ((rs ++ [(q, b)]).getD i.val ([], 0)).1.length = 2
  | 0, l, h => by
    obtain ⟨v, l', rfl, hv, hl⟩ := fits_cons (x := ⟨2, 1, true⟩) (a := []) h
    obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 hv
    obtain rfl := fits_nil hl
    refine ⟨[], v.1, v.2.headD 0, ?_, rfl, fun i => ?_⟩
    · show [v] = [(v.1, [v.2.headD 0])]
      rw [← len_one h2]
    · exact Fin.cases h1 (fun i => i.elim0) i
  | k + 1, l, h => by
    obtain ⟨v, l', rfl, hv, hl⟩ := fits_cons (x := ⟨2, 1, false⟩)
      (a := List.replicate k (⟨2, 1, false⟩ : Fm) ++ [⟨2, 1, true⟩])
      (show fitsAll ((⟨2, 1, false⟩ : Fm) ::
        (List.replicate k (⟨2, 1, false⟩ : Fm) ++ [⟨2, 1, true⟩])) l = true from h)
    obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ v).1 hv
    obtain ⟨rs, q, b, rfl, hk, hq⟩ := fits_lk k l' hl
    refine ⟨(v.1, v.2.headD 0) :: rs, q, b, ?_, by rw [List.length_cons, hk], fun i => ?_⟩
    · show v :: _ = (v.1, [v.2.headD 0]) :: _
      rw [← len_one h2]
      rfl
    · refine Fin.cases h1 (fun i => ?_) i
      exact hq i

theorem fits_val {l : List (RV GE)} (h : fitsAll [(⟨1, 0, false⟩ : Fm)] l = true) :
    ∃ v, l = [([v], [])] := by
  obtain ⟨w, l', rfl, hw, hl⟩ := fits_cons h
  obtain ⟨h1, h2, _⟩ := (Fm.fits_iff _ w).1 hw
  obtain rfl := fits_nil hl
  refine ⟨w.1.headD 0, ?_⟩
  rw [← len_one h1, nil_of_length w.2 h2]

theorem heard_yes (k : ℕ) (m e v : GE) (rs : List (List GE × GE)) (rest : List (RV GE))
    (h : rs.length = k + 1) :
    heardF k true (([m], [e]) :: ((rs.map (fun r => (r.1, [r.2])) ++ [([v], [])]) ++ rest)) =
      ⟨m, e, rs, [v]⟩ := by
  have hl : (rs.map fun r : List GE × GE => ((r.1, [r.2]) : RV GE)).length = k + 1 := by
    rw [List.length_map, h]
  have e1 : ((fun r : RV GE => (r.1, r.2.headD 0)) ∘ fun r : List GE × GE => (r.1, [r.2])) = id :=
    funext fun _ => rfl
  have e2 : (((rs.map (fun r : List GE × GE => ((r.1, [r.2]) : RV GE)) ++ [([v], [])]) ++
      rest).take (k + 1)).map
      (fun r : RV GE => (r.1, r.2.headD 0)) = rs := by
    rw [List.append_assoc, List.take_left' hl, List.map_map, e1, List.map_id]
  have e3 : ((([m], [e]) : RV GE) ::
      ((rs.map (fun r : List GE × GE => ((r.1, [r.2]) : RV GE)) ++ [([v], [])]) ++ rest)).getD
      (k + 2) ([], []) = ([v], []) := by
    show ((rs.map (fun r : List GE × GE => ((r.1, [r.2]) : RV GE)) ++ [([v], [])]) ++
      rest).getD (k + 1) ([], []) = _
    rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]), hl,
      Nat.sub_self]
    rfl
  show (⟨m, e, (((rs.map (fun r : List GE × GE => ((r.1, [r.2]) : RV GE)) ++ [([v], [])]) ++
      rest).take (k + 1)).map
    (fun r : RV GE => (r.1, r.2.headD 0)),
    (((([m], [e]) : RV GE) ::
      ((rs.map (fun r : List GE × GE => ((r.1, [r.2]) : RV GE)) ++ [([v], [])]) ++ rest)).getD
      (k + 2) ([], [])).1⟩ : PscF.Heard) = _
  rw [e2, e3]

theorem finC_app : ∀ (k : ℕ) (z : Fin k → GE) (σ : GE) (l ex : List (RV GE)), l.length = k + 1 →
    Lev.finC k z σ (l ++ ex) = Lev.finC k z σ l
  | 0, _, _, [_], _, _ => rfl
  | 0, _, _, [], _, h => absurd h (by simp)
  | 0, _, _, _ :: _ :: _, _, h => absurd h (by simp)
  | _ + 1, _, _, [], _, h => absurd h (by simp)
  | k + 1, z, σ, a :: l, ex, h => finC_app k (fun i => z i.succ) _ l ex (by simpa using h)

theorem chC_map_app : ∀ (rs : List (List GE × GE)) (ex : List (RV GE)) (i : ℕ), i < rs.length →
    Lev.chC (rs.map (fun r => (r.1, [r.2])) ++ ex) i = (rs.map (·.2)).getD i 0
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: rs, ex, i + 1, h => chC_map_app rs ex i (Nat.lt_of_succ_lt_succ h)

theorem snt_last : ∀ (rs : List (List GE × GE)) (v : GE) (n : ℕ), rs.length = n →
    Lev.snt (([], []) :: (rs.map (fun r => (r.1, [r.2])) ++ [([v], [])])) (n + 1) 0 = v
  | [], _, 0, _ => rfl
  | [], _, _ + 1, h => absurd h (by simp)
  | _ :: _, _, 0, h => absurd h (by simp)
  | _ :: rs, v, n + 1, h => snt_last rs v n (by simpa using h)

/-! ### one sumcheck of the course that shows one value -/

theorem pscC_bits (D : Dt) (V : List PscF.Weight) (k : ℕ) (hV : V.length = k)
    (place : List GE → List GE) (s : Cs) (m e v : GE) (rs : List (List GE × GE))
    (rest : List (RV GE))
    (hs : s.rounds = ([m], [e]) :: ((rs.map (fun r => (r.1, [r.2])) ++ [([v], [])]) ++ rest))
    (hrk : rs.length = k + 1) :
    pscC D ⟨V, [], 0⟩ sBits false 0 place s =
      ({ PscF.outOf ⟨V, [], 0⟩ sBits (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits))
            ⟨m, e, rs, [v]⟩ with
          point := place (PscF.outOf ⟨V, [], 0⟩ sBits
            (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits)) ⟨m, e, rs, [v]⟩).point
          ends := (PscF.outOf ⟨V, [], 0⟩ sBits
            (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits)) ⟨m, e, rs, [v]⟩).ends.map
              fun c => { c with point := place c.point } },
        { s with
          rounds := rest
          own := s.own + PscF.masksOf ⟨V, [], 0⟩ sBits
          idx := s.idx + 0
          rows := s.rows ++
            [⟨(PscF.outOf ⟨V, [], 0⟩ sBits (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits))
                ⟨m, e, rs, [v]⟩).rowMasks, [],
              (PscF.outOf ⟨V, [], 0⟩ sBits (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits))
                ⟨m, e, rs, [v]⟩).rowTarget⟩] }) := by
  have key : ∀ (kk : ℕ) (H : PscF.Heard) (rr : List (RV GE)), kk = V.length →
      H = heardF kk true s.rounds → rr = s.rounds.drop (kk + 3) →
      pscC D ⟨V, [], 0⟩ sBits false 0 place s =
      ({ PscF.outOf ⟨V, [], 0⟩ sBits (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits)) H with
          point := place (PscF.outOf ⟨V, [], 0⟩ sBits
            (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits)) H).point
          ends := (PscF.outOf ⟨V, [], 0⟩ sBits
            (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits)) H).ends.map
              fun c => { c with point := place c.point } },
        { s with
          rounds := rr
          own := s.own + PscF.masksOf ⟨V, [], 0⟩ sBits
          idx := s.idx + 0
          rows := s.rows ++
            [⟨(PscF.outOf ⟨V, [], 0⟩ sBits (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits))
                H).rowMasks, [],
              (PscF.outOf ⟨V, [], 0⟩ sBits (slots D.ms s.own (PscF.masksOf ⟨V, [], 0⟩ sBits))
                H).rowTarget⟩] }) := by
    rintro _ _ _ rfl rfl rfl
    rfl
  refine key k _ _ hV.symm (by rw [hs, heard_yes k m e v rs rest hrk]) ?_
  rw [hs, List.drop_succ_cons, List.drop_left' (by
    rw [List.length_append, List.length_map, hrk]
    rfl)]

theorem slots_drop (e : ℕ → Slot) (first a : ℕ) :
    (slots e first (a + 1)).drop a = [e (first + a)] := by
  unfold slots
  rw [List.range_succ, List.map_append, List.drop_left' (by simp)]
  rfl

theorem map_two {α β : Type} (f : α → β) (l : List α) (a b : α) :
    ((l ++ [a]) ++ [b]).map f = l.map f ++ [f a, f b] := by simp

theorem sum_two (k : ℕ) : ∑ _i : Fin (k + 1), 2 = 2 * k + 2 := by
  simp
  omega

theorem ownAt_8 (S : Pub) : ownAt S 8 = ownAt S 7 + (1 + 2 * (S.mu + S.d) + 2 + 1) := by
  first | rfl | simp [ownAt]

/-! ### the test of the bits -/

variable (A : Dat GE) (sl : Slot → A.J) (st : A.St) (own idx : ℕ)

theorem bits_goes (P : ClPl A) (D : Dt) (hD : D.S = A.toPub) (hr : A.pl ≤ 2 ^ A.mu)
    (hP : ∀ i, P.wB i = sl (D.ms (own + ownAt A.toPub 7 + Cf.portIdx (Lev.lk GE (A.mu + A.d)) i)))
    (hB : P.cB = sl (D.ms (own + ownAt A.toPub 7 + (1 + 2 * (A.mu + A.d) + 2)))) :
    Goes (Sim A sl st own idx 7) (Sim A sl st own idx 8) (cBits D) (A.bitsRun P) A.fmBits := by
  intro s x h hf
  have hlen : A.fmBits.length = A.mu + A.d + 3 := by simp [Dat.fmBits]
  rw [hlen] at hf ⊢
  obtain ⟨m, e, l', hl, hl'⟩ := fits_head
    (a := (List.replicate (A.mu + A.d) (⟨2, 1, false⟩ : Fm) ++ [(⟨2, 1, true⟩ : Fm)]) ++
      [(⟨1, 0, false⟩ : Fm)])
    (show fitsAll ((⟨1, 1, false⟩ : Fm) ::
      ((List.replicate (A.mu + A.d) (⟨2, 1, false⟩ : Fm) ++ [(⟨2, 1, true⟩ : Fm)]) ++
        [(⟨1, 0, false⟩ : Fm)])) (s.rounds.take (A.mu + A.d + 3)) = true from hf)
  obtain ⟨h1, h2⟩ := fitsAll_app _ _ l' hl'
  obtain ⟨rs0, q, b, hr0, hk0, hq⟩ := fits_lk _ _ h1
  obtain ⟨v, hv⟩ := fits_val h2
  have hl2 : l' = (rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++ [([v], [])] := by
    rw [← hr0, ← hv, List.take_append_drop]
  subst hl2
  have hrk : (rs0 ++ [(q, b)]).length = A.mu + A.d + 1 := by
    rw [List.length_append, hk0]
    rfl
  have hs : s.rounds = ([m], [e]) :: (((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++
      [([v], [])]) ++ s.rounds.drop (A.mu + A.d + 3)) := by
    rw [← List.cons_append, ← hl, List.take_append_drop]
  obtain ⟨hzl, hzt⟩ := h.zt rfl
  -- the weights
  obtain ⟨L, hLd⟩ : ∃ L : List GE, L = List.ofFn fun i : Fin (A.mu + A.d) =>
    x.zt (ordC (A.mu + A.d) i) := ⟨_, rfl⟩
  have hLl : L.length = A.mu + A.d := by rw [hLd, List.length_ofFn]
  have hLz : (fun i : Fin (A.mu + A.d) => x.zt (ordC (A.mu + A.d) i)) =
      fun i => L.getD i.val 0 := funext fun i => by rw [hLd, getD_ofFn]
  have hvars : (ordDown (A.mu + A.d)).map (fun t => PscF.Weight.equality (s.zt.getD t 0) 3) =
      L.map fun a => PscF.Weight.equality a 3 := by
    have e0 : ordDown (A.mu + A.d) =
        List.ofFn fun i : Fin (A.mu + A.d) => ((ordC (A.mu + A.d) i : Fin (A.mu + A.d)) : ℕ) :=
      (ordC_default _).symm
    rw [e0, hLd, List.map_ofFn, List.map_ofFn]
    refine congrArg List.ofFn (funext fun i => ?_)
    show PscF.Weight.equality (s.zt.getD (ordC (A.mu + A.d) i).val 0) 3 = _
    rw [← hzt _ (ordC (A.mu + A.d) i).isLt]
    rfl
  have hW := ofFn_snoc0 (A.mu + A.d) L hLl
  have hn : PscF.masksOf ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits =
      2 * (A.mu + A.d) + 3 + 1 := by
    show 1 + ((L.map (fun a => PscF.Weight.equality a 3) ++ [PscF.Weight.atZero 3]).map
      fun w => w.d - 1).sum + 1 = _
    rw [← hW, List.map_ofFn, List.sum_ofFn]
    show 1 + ∑ _i : Fin (A.mu + A.d + 1), 2 + 1 = _
    rw [sum_two]
    omega
  have hc : cBits D s =
      { (pscC D ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits false 0
          (byVarF · (ordDown (A.mu + A.d))) s).2 with
        bit := (pscC D ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits false 0
          (byVarF · (ordDown (A.mu + A.d))) s).1.ends.getD 0 noClaim
        rows := (pscC D ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits false 0
            (byVarF · (ordDown (A.mu + A.d))) s).2.rows ++
          [⟨((pscC D ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits false 0
              (byVarF · (ordDown (A.mu + A.d))) s).1.ends.getD 0 noClaim).masks,
            [(1, eqPairsF ((pscC D ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits false 0
              (byVarF · (ordDown (A.mu + A.d))) s).1.ends.getD 0 noClaim).point)],
            ((pscC D ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits false 0
              (byVarF · (ordDown (A.mu + A.d))) s).1.ends.getD 0 noClaim).value⟩] } := by
    rw [← hvars]
    show cBits D s = _
    unfold cBits
    rw [hD]
  rw [hc, pscC_bits D _ (A.mu + A.d) (by rw [List.length_map, hLl]) _ s m e v _ _ hs hrk, hl, hn]
  -- the challenges
  obtain ⟨cs0, hcs0⟩ : ∃ cs0 : List GE, cs0 = rs0.map (·.2) := ⟨_, rfl⟩
  have hcs : (rs0 ++ [(q, b)]).map (·.2) = cs0 ++ [b] := by rw [List.map_append, hcs0]; rfl
  have hcl : cs0.length = A.mu + A.d := by rw [hcs0, List.length_map, hk0]
  have hchA : ∀ i, i < A.mu + A.d + 1 →
      Lev.chC (([m], [e]) :: ((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++ [([v], [])]))
        (i + 1) = (cs0 ++ [b]).getD i 0 := fun i hi =>
    (chC_map_app (rs0 ++ [(q, b)]) _ i (by rw [hrk]; exact hi)).trans (by rw [hcs])
  have hv' : Lev.snt (([m], [e]) :: ((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++
      [([v], [])])) (A.mu + A.d + 2) 0 = v := snt_last (rs0 ++ [(q, b)]) v _ hrk
  have hE : PscF.hidingEntries (L.map (fun a => PscF.Weight.equality a 3) ++
      [PscF.Weight.atZero 3]) = 2 * (A.mu + A.d) + 3 := by
    have h0 : PscF.hidingEntries (L.map (fun a => PscF.Weight.equality a 3) ++
      [PscF.Weight.atZero 3]) + 1 = 2 * (A.mu + A.d) + 3 + 1 := hn
    omega
  have hwl : (PscF.hidingWalk ((L.map (fun a => PscF.Weight.equality a 3) ++
      [PscF.Weight.atZero 3]).zip (cs0 ++ [b]))).1.length = 2 * (A.mu + A.d) + 3 := by
    rw [PscF.hidingWalk_length _ _ (by simp) (by simp [hLl, hcl]) (fun w hw => by
      rw [← hW] at hw
      obtain ⟨i, hi⟩ := (List.mem_ofFn' _ _).1 hw
      rw [← hi]
      exact Nat.le_add_left 1 2), hE]
  have hfl : ∀ n, n < 2 * (A.mu + A.d) + 3 + 1 →
      sl ((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).getD n default) =
        sl (D.ms (own + ownAt A.toPub 7 + n)) := fun n hn' => by
    rw [slots_getD _ _ _ _ hn', h.own]
  have hlt : ∀ i : PIdx (Lev.lk GE (A.mu + A.d)),
      Cf.portIdx (Lev.lk GE (A.mu + A.d)) i < 2 * (A.mu + A.d) + 3 + 1 := fun i => by
    have h0 := Cf.portIdx_lt (Lev.lk GE (A.mu + A.d)) i
    have h1 : ((Lev.lk GE (A.mu + A.d)).map fun f => f.n).sum = 2 * (A.mu + A.d) + 2 := by
      simp [Lev.lk, pfCube, pDummy]
      omega
    omega
  have hb0 : byVarF cs0 (ordDown (A.mu + A.d)) = cs0.reverse := by
    rw [← hcl]
    exact byVarF_down _
  have hπ : List.ofFn (fun t : Fin (A.mu + A.d) =>
      Lev.chC (([m], [e]) :: ((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++ [([v], [])]))
        (t.rev.val + 1)) = cs0.reverse := by
    have e0 : (fun t : Fin (A.mu + A.d) =>
        Lev.chC (([m], [e]) :: ((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++ [([v], [])]))
          (t.rev.val + 1)) =
        fun t => (fun i : Fin (A.mu + A.d) => cs0.getD i.val 0) t.rev :=
      funext fun t => by
        rw [hchA _ (Nat.lt_succ_of_lt t.rev.isLt), List.getD_append _ _ _ _ (by
          rw [hcl]
          exact t.rev.isLt)]
    rw [e0, ofFn_rev (A.mu + A.d) fun i : Fin (A.mu + A.d) => cs0.getD i.val 0,
      ofFn_getD _ _ hcl]
  have hβ : Lev.chC (([m], [e]) :: ((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++
      [([v], [])])) (A.mu + A.d + 1) = b := by
    rw [hchA _ (Nat.lt_succ_self _), List.getD_append_right _ _ _ _ (by rw [hcl]), hcl,
      Nat.sub_self]
    rfl
  have hends : (PscF.outOf ⟨L.map fun a => PscF.Weight.equality a 3, [], 0⟩ sBits
      (slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)) ⟨m, e, rs0 ++ [(q, b)], [v]⟩).ends =
      [⟨cs0, [(D.ms (s.own + (2 * (A.mu + A.d) + 3)), b)], v⟩] := by
    show (((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).drop (PscF.hidingWalk
      ((L.map (fun a => PscF.Weight.equality a 3) ++ [PscF.Weight.atZero 3]).zip
        ((rs0 ++ [(q, b)]).map (·.2)))).1.length).zip [v]).map (fun p =>
      (⟨((rs0 ++ [(q, b)]).map (·.2)).take (L.map fun a => PscF.Weight.equality a 3).length,
        [(p.1, (((rs0 ++ [(q, b)]).map (·.2)).getLast?).getD 0)], p.2⟩ : PscF.PointClaim)) = _
    rw [hcs, hwl, slots_drop, List.length_map, hLl, List.take_left' hcl]
    simp
  refine ⟨⟨h.st, h.al, ?_, ?_, h.idx, fun a => absurd a (by decide), fun a => absurd a (by decide),
    fun _ a => absurd a (by decide), fun _ a => absurd a (by decide), fun _ => h.cls (by decide),
    fun a => absurd a (by decide)⟩, rfl⟩
  · show x.rows ++ [_, _] = ((s.rows ++ [_]) ++ [_]).map (rdRow A sl)
    rw [map_two, h.rows]
    refine congrArg (List.map (rdRow A sl) s.rows ++ ·) (congrArg₂ (fun r r' => [r, r']) ?_ ?_)
    · refine congrArg₂ LdLkp.Row.mk (funext fun j => ?_) ?_
      · show _ = rdMF sl ((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).zip (PscF.hidingWalk
          ((L.map (fun a => PscF.Weight.equality a 3) ++ [PscF.Weight.atZero 3]).zip
            ((rs0 ++ [(q, b)]).map (·.2)))).1 ++ []) j + 0
        rw [List.append_nil, add_zero, ← hW, hcs,
          walk_hidM sl j (A.mu + A.d) (fun _ => 2) _ (cs0 ++ [b]) _
            (fun i => sl ((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).getD
              (Cf.portIdx (pfMix GE (A.mu + A.d + 1) fun _ => 2) i) default))
            (by rw [List.length_append, hcl]; rfl)
            (by rw [slots_length, sum_two]; omega) (fun _ => rfl),
          hidM_rowF j (A.mu + A.d)
            (fun n => sl ((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).getD n default))]
        have e1 : (fun r t => P.wB (Lev.nmV GE (A.mu + A.d) r t)) = fun r t =>
            sl ((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).getD
              (Cf.portIdx (Lev.lk GE (A.mu + A.d)) (Lev.nmV GE (A.mu + A.d) r t)) default) :=
          funext fun r => funext fun t => by rw [hfl _ (hlt _), hP]
        have e2 : P.wB (Lev.nmC GE (A.mu + A.d)) =
            sl ((slots D.ms s.own (2 * (A.mu + A.d) + 3 + 1)).getD
              (Cf.portIdx (Lev.lk GE (A.mu + A.d)) (Lev.nmC GE (A.mu + A.d))) default) := by
          rw [hfl _ (hlt _), hP]
        show Lev.rowF (A.mu + A.d) (fun r t => P.wB (Lev.nmV GE (A.mu + A.d) r t))
          (P.wB (Lev.nmC GE (A.mu + A.d))) _ j = _
        rw [e1, e2]
        exact congrFun (rowF_congr (A.mu + A.d) _ _ _ _ fun i hi =>
          hchA i (Nat.lt_succ_of_le hi)) j
      · show Lev.finC (A.mu + A.d) (fun i => x.zt (ordC (A.mu + A.d) i)) (m + e * 0)
            ((rs0 ++ [(q, b)]).map (fun r => (r.1, [r.2])) ++ [([v], [])]) - e * (_ * (_ - 1)) =
          PscF.claimAfter (L.map (fun a => PscF.Weight.equality a 3) ++ [PscF.Weight.atZero 3])
            (rs0 ++ [(q, b)]) (m + e * 0) - e * (v * v - v)
        rw [hv', ← hW, claim_finM (A.mu + A.d + 1) (fun _ => 2) _ _ _ hrk hq,
          finM_finC (A.mu + A.d) L hLl, finC_app _ _ _ _ _ (by rw [List.length_map, hrk]), hLz]
        ring
    · rw [hends]
      refine congrArg₂ LdLkp.Row.mk (funext fun j => ?_) hv'
      show A.cellW _ j + Lev.one P.cB _ j =
        rdMF sl [(D.ms (s.own + (2 * (A.mu + A.d) + 3)), b)] j +
          (1 * onCell A (eqPairsF (byVarF cs0 (ordDown (A.mu + A.d)))) j + 0)
      rw [hβ, cellW_onCell A hr, hπ, hb0, rdMF_cons, rdMF_nil, hB, h.own]
      have e3 : own + ownAt A.toPub 7 + (1 + 2 * (A.mu + A.d) + 2) =
          own + ownAt A.toPub 7 + (2 * (A.mu + A.d) + 3) := by omega
      rw [e3]
      show _ + Parts.one _ b j = _
      ring
  · show s.own + (2 * (A.mu + A.d) + 3 + 1) = _
    rw [h.own, ownAt_8]
    show _ = own + (ownAt A.toPub 7 + (1 + 2 * (A.mu + A.d) + 2 + 1))
    omega

end Lk6.Mid.Clo

#print axioms Lk6.Mid.Clo.bits_goes
#print axioms Lk6.Mid.Clo.fits_lk
#print axioms Lk6.Mid.Clo.heard_yes
#print axioms Lk6.Mid.Clo.finC_app
