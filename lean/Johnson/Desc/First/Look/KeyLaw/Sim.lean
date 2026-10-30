-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Sim.lean: one masked sumcheck of the kind "lookup", where it returns,
against one sumcheck of the course over the field (pscC, Mid/Course.lean): the row that the first
leaves has in every later ledger the value of the row that the second adds; the end slots read as
the end claims; both have taken the same rounds and the same mask entries.

Main names:
  shK, flatK: a round's key as a shape, and read in the field.
  wF zd: equality weights over the field. ran_read: the running claim and the hiding polynomial's
    linear form of a sumcheck's state, read.
  heardF_y: what the course hears of the rounds of a sumcheck that shows values.
  sum_dot: the hiding coefficients' share of a row.
  Base F t s: the ledger has its sizes, and the course's rounds left are the tape, read.
  whole_sim: THE STEP.

Limits. One world W of mask entries; where the flat function returns.

-/
import Johnson.Desc.First.Look.KeyLaw.Read
import Johnson.Desc.First.Look.KeyLaw.Whole
import Johnson.Desc.First.Look.KeyLaw.Mid.AtTypedData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole)
open Lk6.PortSim (noClaim)
open Lk6.Mid (Dt Cs RowF pscC heardF slots eqPairsF)

/-- A key's shape. -/
def shK (k : Key) : Shape := (k.1.getD "", k.2.2.1.length, k.2.2.2.length, k.2.1)

/-- Keys, read in the field. -/
def flatK (ks : List Key) : List (Lk6.Flat.RV GE) :=
  ks.map fun k => (k.2.2.1.map readE, k.2.2.2.map readE)

theorem flatK_append (a b : List Key) : flatK (a ++ b) = flatK a ++ flatK b := List.map_append

/-- Equality weights over the field. -/
def wF (zd : List (E × ℕ)) : List PscF.Weight :=
  zd.map fun p => PscF.Weight.equality (readE p.1) p.2

theorem eqW_read (zd : List (E × ℕ)) : (PscTie.eqW zd).map readW = wF zd := by
  unfold PscTie.eqW wF
  rw [List.map_map]
  exact List.map_congr_left fun p _ => readW_equality p.1 p.2

/-- A sumcheck's state, read. -/
theorem ran_read {p : Psc} {first : ℕ} {mu eps : E} {zd : List (E × ℕ)} {rs : List (List E × E)}
    (h : Ran p first mu eps zd rs) :
    readE p.claim = PscF.claimAfter (wF zd) (rs.map readRound)
        (readE mu + readE eps * readE p.target) ∧
      (p.walk.1.map readE, readE p.walk.2) =
        PscF.hidingWalk ((wF zd).zip ((rs.map readRound).map (·.2))) := by
  constructor
  · rw [h.claim_eq, read_claimAfter, eqW_read, readE_add, readE_mul]
  · unfold Psc.walk
    rw [zipT_eq, h.vars_eq, h.r_eq, read_hidingWalk, read_challenges, ← eqW_read, zip_read]
    rfl

/-- What the course hears of a sumcheck that shows values. -/
theorem heardF_y (k : ℕ) (m e : GE) (rs : List (List GE × GE)) (vals : List GE)
    (rest : List (Lk6.Flat.RV GE)) (h : rs.length = k + 1) :
    heardF k true (([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++ (vals, []) :: rest)) =
      ⟨m, e, rs, vals⟩ := by
  have e1 : ((([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++
      (vals, []) :: rest) : List (Lk6.Flat.RV GE)).drop 1).take (k + 1) =
      rs.map (fun r => (r.1, [r.2])) := by
    rw [List.drop_succ_cons, List.drop_zero]
    exact List.take_left' (by rw [List.length_map, h])
  have e2 : (([m], [e]) :: (rs.map (fun r => (r.1, [r.2])) ++
      (vals, []) :: rest) : List (Lk6.Flat.RV GE)).getD (k + 2) ([], []) = (vals, []) := by
    rw [List.getD_cons_succ, List.getD_append_right _ _ _ _ (by rw [List.length_map, h])]
    simp [h]
  unfold heardF
  simp only [if_true, e1, e2, List.headD_cons, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id rs]
  exact List.map_congr_left fun r _ => rfl

theorem drop_y (k : ℕ) (x : Lk6.Flat.RV GE) (A : List (Lk6.Flat.RV GE)) (y : Lk6.Flat.RV GE)
    (rest : List (Lk6.Flat.RV GE)) (h : A.length = k + 1) :
    (x :: (A ++ y :: rest)).drop (k + 3) = rest := by
  rw [List.drop_succ_cons, show k + 2 = A.length + 1 by omega, ← List.drop_drop,
    List.drop_left, List.drop_succ_cons, List.drop_zero]

variable (W : PscF.World) (home : ℕ → Slot)

/-- The hiding coefficients' share of a row: the slots from first on hold mask entries. -/
theorem sum_dot (sv : ℕ → GE) : ∀ (l : List E) (first N : ℕ), l.length ≤ N →
    (∀ i < l.length, sv (first + i) = W.mask (home (first + i))) →
    Model.sumFrom (fun j x => rho.val x * sv j) first l =
      PscF.dot (l.map readE) (((List.range' first N).map home).map W.mask)
  | [], _, _, _, _ => by simp [Model.sumFrom, PscF.dot_nil_left]
  | x :: l, first, 0, h, _ => by simp at h
  | x :: l, first, N + 1, h, hs => by
    rw [List.range'_succ, List.map_cons, List.map_cons, List.map_cons, PscF.dot_cons]
    show rho.val x * sv first + Model.sumFrom _ (first + 1) l = _
    rw [sum_dot sv l (first + 1) N (by simpa using h) fun i hi => by
      have := hs (i + 1) (by simpa using hi)
      rwa [show first + (i + 1) = first + 1 + i by omega] at this]
    have h0 := hs 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    rfl

/-- The ledger has its sizes; the course's rounds left are the tape's, read. -/
structure Base (F : Fork) (t : Tape) (s : Cs) : Prop where
  sized : Sized F
  rounds : s.rounds = flatK (t.map key)


/-! ## The course's sumcheck, written out -/

variable (D : Dt)

/-- The fresh mask entries of a sumcheck that takes n. -/
def freshOf (keys : Bool) (n : ℕ) (s : Cs) : List Slot :=
  if keys then slots D.ms s.own (n - 2) ++ slots D.ix s.idx 2 else slots D.ms s.own n

/-- What the course's sumcheck hands on, before the point is put back. -/
def oOf (c : PscF.Claim) (S : PscF.Summand) (keys : Bool) (s : Cs) : PscF.Out :=
  PscF.outOf c S (freshOf D keys (PscF.masksOf c S) s)
    (heardF c.vars.length (S.shown != 0) s.rounds)

theorem pscC_eq (c : PscF.Claim) (S : PscF.Summand) (keys : Bool) (kept : ℕ)
    (place : List GE → List GE) (s : Cs) :
    pscC D c S keys kept place s =
      ({ oOf D c S keys s with
          point := place (oOf D c S keys s).point
          ends := (oOf D c S keys s).ends.map fun e => { e with point := place e.point } },
        { s with
          rounds := s.rounds.drop (if (S.shown != 0) = true then c.vars.length + 3
            else c.vars.length + 1)
          own := s.own + (if keys = true then PscF.masksOf c S - 2 else PscF.masksOf c S)
          idx := s.idx + (if keys = true then 2 else 0)
          rows := s.rows ++ [⟨(oOf D c S keys s).rowMasks,
            ((oOf D c S keys s).rowMaps.take kept).map fun a =>
              (a, eqPairsF (place (oOf D c S keys s).point)), (oOf D c S keys s).rowTarget⟩] }) :=
  rfl

theorem sum_const {α : Type} (c : ℕ) : ∀ l : List α, (l.map fun _ => c).sum = l.length * c
  | [] => by simp
  | _ :: l => by rw [List.map_cons, List.sum_cons, sum_const c l, List.length_cons]; ring

theorem entries_wF (zd : List (E × ℕ)) :
    PscF.hidingEntries (wF zd) = 1 + (zd.map fun p => p.2 - 1).sum := by
  unfold PscF.hidingEntries wF
  rw [List.map_map]
  rfl

/-- An end claim of a sumcheck over the field. -/
theorem outOf_end (c : PscF.Claim) (S : PscF.Summand) (fresh : List Slot) (Hd : PscF.Heard) (i : ℕ)
    (a : Slot) (b : GE)
    (h1 : (fresh.drop (PscF.hidingWalk ((PscF.varsOf c S).zip
      (Hd.rounds.map (·.2)))).1.length)[i]? = some a) (h2 : Hd.values[i]? = some b) :
    (PscF.outOf c S fresh Hd).ends[i]? = some ⟨(PscF.outOf c S fresh Hd).point,
      [(a, (PscF.outOf c S fresh Hd).beta.getD 0)], b⟩ := by
  show (((fresh.drop _).zip Hd.values).map _)[i]? = _
  rw [List.getElem?_map, (List.getElem?_zip_eq_some (z := (a, b))).2 ⟨h1, h2⟩]
  rfl

theorem map_getD_some {α β : Type} (l : List α) (g : α → β) (i : ℕ) (x : α) (d : β)
    (h : l[i]? = some x) : (l.map g).getD i d = g x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

theorem range'_get : ∀ (N a i : ℕ), i < N → (List.range' a N)[i]? = some (a + i)
  | 0, _, _, h => by omega
  | N + 1, a, 0, _ => by rw [List.range'_succ]; rfl
  | N + 1, a, i + 1, h => by
    rw [List.range'_succ, List.getElem?_cons_succ, range'_get N (a + 1) i (by omega)]
    congr 1; omega

theorem zipmap_getD {α β γ : Type} (f : α × β → γ) (l1 : List α) (l2 : List β) (i : ℕ) (a : α)
    (b : β) (d : γ) (h1 : l1[i]? = some a) (h2 : l2[i]? = some b) :
    ((l1.zip l2).map f).getD i d = f (a, b) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    (List.getElem?_zip_eq_some (z := (a, b))).2 ⟨h1, h2⟩]
  rfl

/-- The keys of a sumcheck's rounds have the sumcheck's shape. -/
theorem pscKeys_shape (mu eps : E) (rs : List (List E × E)) (L : List ℕ)
    (h : rs.map (fun r => r.1.length) = L) (y : Option ((List E × E) × List E)) :
    (pscKeys mu eps rs y).map shK =
      pscShape L (y.map fun x => (x.1.1.length, x.2.length)) := by
  subst h
  unfold pscKeys pscShape
  rw [List.map_append, List.map_cons, List.map_map, List.map_map]
  congr 1
  cases y with
  | none => rfl
  | some x => rfl

variable {W home}

/-- **THE STEP.** -/
theorem whole_sim {C : Aff} {zs : List E} {dY n : ℕ} {endTerm : List E → E} {F G : Fork}
    {t u : Tape} {w : Whole} {s : Cs} {c : PscF.Claim} {S : PscF.Summand}
    {keys : Bool} {place : List GE → List GE}
    (h : wholeStandIn C zs dY n endTerm F t = some (w, G, u)) (hb : Base F t s)
    (hcv : c.vars = zs.map fun z => PscF.Weight.equality (readE z) 3)
    (hC : Reads W home F C c.masks c.target) (hS1 : S.shown = n) (hS2 : S.degree = dY) (hn : 1 ≤ n)
    (hS3 : ∀ pt (y : List E), (S.coeffs pt (y.map readE)).headD 0 = readE (endTerm y))
    (hfr : freshOf D keys (1 + 2 * zs.length + dY + n) s =
      (List.range' F.next (1 + 2 * zs.length + dY + n)).map home) :
    ∃ (o : PscF.Out) (row : RowF) (beta : GE) (val : ℕ → GE),
      pscC D c S keys 0 place s =
        (o, { s with
          rounds := flatK (u.map key)
          own := s.own + (if keys = true then 1 + 2 * zs.length + dY + n - 2
            else 1 + 2 * zs.length + dY + n)
          idx := s.idx + (if keys = true then 2 else 0)
          rows := s.rows ++ [row] }) ∧
      o.point = place ((w.challenges.take zs.length).map readE) ∧
      w.challenges.length = zs.length + 1 ∧
      (∀ i < n, o.ends.getD i noClaim = ⟨o.point, [(home (w.sEnd + i), beta)], val i⟩ ∧
        Reads W home G (Aff.slot (w.sEnd + i)) [(home (w.sEnd + i), beta)] (val i)) ∧
      row.maps = [] ∧ NoEnt w.row ∧
      (∀ H, Later G H → hidV W home H w.row = W.form row.masks - row.target) ∧
      Adv F G (1 + 2 * zs.length + dY + n) ∧ Sized G ∧
      ∃ ks, t.map key = ks ++ u.map key ∧
        ks.map shK = pscShape (List.replicate zs.length 2) (some (dY, n)) := by
  obtain ⟨τ, mu, eps, rs, ry, vv, p, G1, G2, hτ, hl, hl2, hly, hk, hR, hps, hpt, hvn, hch, hse,
      hrow,
    a1, hh1, hh2⟩ := whole_fl hb.sized h
  obtain ⟨hcl, hwk⟩ := ran_read hR
  obtain ⟨-, hτv⟩ := public_reads hτ
  have hS1' : Sized G1 := a1.later.sized hb.sized
  obtain ⟨f1, f2, f3, -⟩ := PscRun.hideRun_ok _ _ _ _ _ hS1' hh1
  obtain ⟨g1, g2, g3, -⟩ := PscRun.hideRun_ok _ _ _ _ _ f2 hh2
  have a2 : Adv G1 G2 0 := adv_hide hS1' hh1
  have a3 : Adv G2 G 0 := adv_hide f2 hh2
  have hy : (S.shown != 0) = true := by
    rw [hS1]; simp; omega
  have hy' : (S.shown == 0) = false := by
    rw [hS1]; simp; omega
  -- the claim, its variables, the number of mask entries
  have hvars : PscF.varsOf c S =
      wF (zs.map (·, 3) ++ [(zeroE, dY + 1)]) := by
    unfold PscF.varsOf wF
    rw [hy', hS2, hcv, List.map_append, List.map_map, List.map_cons, List.map_nil, readE_zero]
    rfl
  have hent : PscF.hidingEntries (wF (zs.map (·, 3) ++ [(zeroE, dY + 1)])) =
      1 + 2 * zs.length + dY := by
    rw [entries_wF, List.map_append, List.map_map, List.sum_append]
    have e : (zs.map ((fun p : E × ℕ => p.2 - 1) ∘ fun x => (x, 3))).sum = zs.length * 2 :=
      sum_const 2 zs
    rw [e]
    show 1 + (zs.length * 2 + (dY + 1 - 1 + 0)) = _
    omega
  have hN : PscF.masksOf c S =
      1 + 2 * zs.length + dY + n := by
    unfold PscF.masksOf
    rw [hvars, hent, hS1]
  -- the rounds
  have hrd : s.rounds = ([readE mu], [readE eps]) ::
      (((rs ++ [ry]).map readRound).map (fun r => (r.1, [r.2])) ++
        (vv.toList.map readE, []) :: flatK (u.map key)) := by
    rw [hb.rounds, hk, flatK_append]
    simp [flatK, pscKeys, kr, readRound]
  have hlen : ((rs ++ [ry]).map readRound).length = zs.length + 1 := by simp [hl]
  have hdrop : s.rounds.drop (c.vars.length + 3) = flatK (u.map key) := by
    rw [hrd, hcv, List.length_map]
    exact drop_y _ _ _ _ _ (by rw [List.length_map, hlen])
  have ho : oOf D c S keys s =
      PscF.outOf c S
        ((List.range' F.next (1 + 2 * zs.length + dY + n)).map home)
        ⟨readE mu, readE eps, (rs ++ [ry]).map readRound, vv.toList.map readE⟩ := by
    unfold oOf
    rw [hN, hfr, hy, hrd, hcv, List.length_map, heardF_y _ _ _ _ _ _ hlen]
  -- the hiding polynomial's linear form
  have hw1 : (PscF.hidingWalk ((wF (zs.map (·, 3) ++ [(zeroE, dY + 1)])).zip
      (((rs ++ [ry]).map readRound).map (·.2)))).1 = p.walk.1.map readE :=
    (congrArg Prod.fst hwk).symm
  have hw2 : (PscF.hidingWalk ((wF (zs.map (·, 3) ++ [(zeroE, dY + 1)])).zip
      (((rs ++ [ry]).map readRound).map (·.2)))).2 = 1 := by
    rw [← congrArg Prod.snd hwk]
    exact (PscRun.ran_walk rho hR).2
  have hwl : p.walk.1.length = 1 + 2 * zs.length + dY := by
    have := PscF.hidingWalk_length (wF (zs.map (·, 3) ++ [(zeroE, dY + 1)]))
      (((rs ++ [ry]).map readRound).map (·.2)) (by simp [wF]) (by simp [wF, hl])
      (fun w hw => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
        rcases List.mem_append.1 hq with hq | hq
        · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hq
          exact (by decide : 1 ≤ 3)
        · obtain rfl : q = (zeroE, dY + 1) := by simpa using hq
          exact Nat.le_add_left 1 dY)
    rw [hw1, List.length_map, hent] at this
    exact this
  have hFG : Later F G := (a1.later.trans a2.later).trans a3.later
  have htg : readE p.target = c.target := by rw [hpt, hτv, hC.pub]
  have hbeta : (PscF.outOf c S ((List.range' F.next (1 + 2 * zs.length + dY + n)).map home)
      ⟨readE mu, readE eps, (rs ++ [ry]).map readRound, vv.toList.map readE⟩).beta =
      some (readE ry.2) := by
    show (if (S.shown == 0) = true then none
      else (((rs ++ [ry]).map readRound).map (·.2)).getLast?) = _
    rw [hy']
    simp [readRound]
  refine ⟨(pscC D c S keys 0 place s).1,
    ⟨(oOf D c S keys s).rowMasks, [], (oOf D c S keys s).rowTarget⟩, readE ry.2,
    fun i => readE (vv.getD i zeroE), ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, g2, ⟨_, hk, ?_⟩⟩
  · refine Prod.ext rfl ?_
    rw [pscC_eq]
    show ({ s with
      rounds := s.rounds.drop (if (S.shown != 0) = true then c.vars.length + 3
        else c.vars.length + 1)
      own := s.own + (if keys = true then PscF.masksOf c S - 2 else PscF.masksOf c S)
      idx := s.idx + (if keys = true then 2 else 0)
      rows := s.rows ++ [⟨(oOf D c S keys s).rowMasks, [], (oOf D c S keys s).rowTarget⟩] } : Cs) =
          _
    rw [if_pos hy, hdrop, hN]
  · show place (oOf D c S keys s).point = _
    rw [ho]
    show place ((((rs ++ [ry]).map readRound).map (·.2)).take c.vars.length) = _
    rw [hch, read_challenges, List.map_take, hcv, List.length_map]
  · rw [hch]; simp [hl]
  · intro i hi
    have hi' : i < vv.size := hvn ▸ hi
    constructor
    · show ((oOf D c S keys s).ends.map fun e => { e with point := place e.point }).getD i noClaim =
        ⟨place (oOf D c S keys s).point, _, _⟩
      rw [ho]
      rw [map_getD_some _ _ i _ _ (outOf_end c S _ _ i (home (w.sEnd + i))
        (readE (vv.getD i zeroE)) ?_ ?_), hbeta]
      · rfl
      · show (((List.range' F.next (1 + 2 * zs.length + dY + n)).map home).drop
          (PscF.hidingWalk ((PscF.varsOf c S).zip
            (((rs ++ [ry]).map readRound).map (·.2)))).1.length)[i]? = _
        rw [hvars, hw1, List.length_map, hwl, List.getElem?_drop, List.getElem?_map,
          range'_get _ _ _ (by omega), hse]
        exact congrArg (fun j => some (home j)) (by omega)
      · show (vv.toList.map readE)[i]? = _
        simp [hi', Array.getD]
    · obtain ⟨b1, -, b3, b4, b5⟩ := f3 i hi'
      have := (Reads.slot (W := W) (home := home) (F := G2) (j := w.sEnd + i)
        (by rw [f1.ns]; exact b1) b3).later a3.later
      rwa [b4, b5] at this
  · rw [hrow]
    exact NoEnt.rowForm (hps ▸ hC.ne) _
  · intro H hH
    have hCH : C.value rho (hidW W home H) = c.target - W.form c.masks :=
      (hC.later (hFG.trans hH)).hid
    have hsum := sum_dot W home (hidW W home H).slot p.walk.1 F.next
      (1 + 2 * zs.length + dY + n) (by omega) (fun i hi => by
        obtain ⟨-, -, c3, c4, c5⟩ := g3 i (by simpa using hi)
        rw [hR.first_eq] at c3 c4 c5
        obtain ⟨-, k2, k3⟩ := hH.keep _ c3
        show readE (H.vp.getD _ zeroE) - readE (H.mf.getD _ zeroE) * W.mask (home _) = _
        rw [k2, k3, c4, c5, readE_sub, readE_zero, readE_one]
        have : (Array.replicate p.walk.1.length zeroE).getD i zeroE = zeroE := by
          simp [Array.getD]
        rw [this, readE_zero]
        ring)
    show (w.row).value rho (hidW W home H) =
      W.form (oOf D c S keys s).rowMasks - (oOf D c S keys s).rowTarget
    rw [hrow, PscRun.ran_row rho hR (hidW W home H), hps, Aff.value_empty, hsum, hCH, ho]
    show _ = W.form (((List.range' F.next (1 + 2 * zs.length + dY + n)).map home).zip
        (PscF.hidingWalk ((PscF.varsOf c S).zip (((rs ++ [ry]).map readRound).map (·.2)))).1 ++
        PscF.scaleForm (readE eps * (PscF.hidingWalk ((PscF.varsOf c S).zip
          (((rs ++ [ry]).map readRound).map (·.2)))).2) c.masks) -
      (PscF.claimAfter (PscF.varsOf c S) ((rs ++ [ry]).map readRound)
          (readE mu + readE eps * c.target) -
        readE eps * (S.coeffs _ (vv.toList.map readE)).headD 0)
    rw [hvars, hw1, hw2, PscF.World.form_append, PscF.World.form_zip, PscF.World.form_scale, hS3,
      ← htg, ← hcl]
    simp only [rho_val]
    ring
  · exact ((a1.trans a2).trans a3).cast (by omega)
  · rw [pscKeys_shape mu eps rs _ hl2]
    show pscShape _ (some (ry.1.length, vv.toList.length)) = _
    have hvl : vv.toList.length = n := by simpa using hvn
    rw [hly, hvl]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.whole_sim
#print axioms VerifiableInference.Desc.K3.KeyLaw.ran_read
#print axioms VerifiableInference.Desc.K3.KeyLaw.heardF_y
#print axioms VerifiableInference.Desc.K3.KeyLaw.sum_dot
