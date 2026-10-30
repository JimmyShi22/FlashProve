-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookTrace.lean

"TwV.traceOfFlat" reads the trace "trT" off the rounds "rsT" of a lookup.

Johnson/HonestTrace/LookDefs.lean defines, for the data D of a lookup (the public numbers of
Cb/Pv/Lookup/Out/TwV.lean, a joint key vector, bits, the point of comparison), a reading μ of the
mask entries and challenges C as arguments: "rsT D μ C", for each round the scalars sent and the
elements drawn; and "trT D μ C", a value of "TwV.Trace". "TwV.traceOfFlat" is TwV's function from
rounds to a trace: the draw of the point of comparison; n + 1 steps of the tie; the draw of the
planes' point; the levels of the keys' tree and of the table's tree, each a sumcheck and a line's
draw; the leaves' sumcheck (TwV's "closing": the field cls of TwV.Trace, and clsE, clsX of Chal);
the draw of the bits' point; the bits' sumcheck. This file walks that function over "rsT", one
sumcheck at a time, by "takeSc_job" (Johnson/HonestTrace/LookSum.lean).

Why a walk is needed. But for tie step 0 and the bits' sumcheck, whose target is 0, a sumcheck's
target is made of SHOWN values of sumchecks in front: one of them (the tie; key level 0), two joined
on a line (the later levels, the leaves), or all planes' roots joined at a point (table level 0):
"tieTg", "keyTg", "tabTg". And each level's point is made of the challenges in front ("keyPt",
"tabPt"). "traceOfFlat" computes both as it goes. The walk shows that what it computes are these
terms.

Main theorems:
* "trace_hon": under "PremT D μ C", traceOfFlat D.N (rsT D μ C) = trT D μ C.
* "trace_of_lawful": the walk itself: under "PremT D μ C", if every tie step's job, every level's
  job at its point, the leaves' job and the bits' job are lawful, then traceOfFlat D.N (rsT D μ C) =
  trT D μ C.
* "tieGo_jobs", "lvGo_jobs": "TwV.tieGo" and "TwV.lvGo" on the rounds of any families of lawful jobs
  whose targets and points follow each other as TwV's functions compute them.
* "traceOfFlat_eq": "traceOfFlat" from the results of its eight steps.
Helpers: "scJob_xs", "scJob_vals", "takeSc_some", "takeSc_none", "tie_getD", "tie_v",
"keyPt_length", "tabPt_length".

Limits. Of "PremT" the walk "trace_of_lawful" reads the number of planes (n + 2 = 2^w), the LENGTHS
of the four kinds of orders and the lengths of the challenges' lists; that the jobs are lawful is
its premise, in five clauses. "trace_hon" pays these from Johnson/HonestTrace/LookCube.lean and
LookJobs.lean, which read that the orders are permutations and, for the tie, the relation
"Data.Mid". The clause of "PremT" on the bits' places is read by neither. Whether "PremT" can be met
is not a matter of this file. K is any field; masks and challenges are arguments. The statement is
an equation of two values of plain data: it says nothing of the rows that TwV makes of a trace.

Not claimed: anything on soundness, completeness or what the masks conceal.

-/
import Johnson.HonestTrace.LookSum
import Johnson.HonestTrace.LookJobs

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open TwV

section
variable {K : Type} [Field K] {P : Type}

/-! ## What scJob holds -/

/-- "scJob" keeps the challenges. -/
theorem scJob_xs (L : Led P) (μ : P → K) (J : Job K) (eps tg : K) (xs : List K) :
    (scJob L μ J eps tg xs).xs = xs := by
  unfold scJob
  cases J.dY <;> rfl

/-- At a job with end values the shown values of "scJob" are "shownOf". -/
theorem scJob_vals (L : Led P) (μ : P → K) (J : Job K) (eps tg : K) (xs : List K)
    (h : J.dY.isSome) : (scJob L μ J eps tg xs).vals = shownOf L μ J xs := by
  unfold scJob
  cases hY : J.dY with
  | none => rw [hY] at h; cases h
  | some _ => rfl

/-- "takeSc_job" at a job with end values: a lawful J with as many degrees as points, one challenge
more than it has points, any target and any rest. -/
theorem takeSc_some (L : Led P) (μ : P → K) (J : Job K) (hJ : J.Lawful)
    (hd : J.dg.length = J.zs.length) (hY : J.dY.isSome) (eps tg : K) (xs : List K)
    (hx : xs.length = J.zs.length + 1) (rest : Rounds K) :
    takeSc (runJob L μ J eps xs ++ rest) tg (J.zs ++ [0]) true =
      (scJob L μ J eps tg xs, rest) := by
  have t := takeSc_job L μ J hJ hd eps tg xs (by rw [if_pos hY]; exact hx) rest
  rw [if_pos hY, hY] at t
  exact t

/-- "takeSc_job" at a job without end values: a lawful J with as many degrees as points, as many
challenges as points, any target and any rest. -/
theorem takeSc_none (L : Led P) (μ : P → K) (J : Job K) (hJ : J.Lawful)
    (hd : J.dg.length = J.zs.length) (hY : J.dY = none) (eps tg : K) (xs : List K)
    (hx : xs.length = J.zs.length) (rest : Rounds K) :
    takeSc (runJob L μ J eps xs ++ rest) tg J.zs false = (scJob L μ J eps tg xs, rest) := by
  have t := takeSc_job L μ J hJ hd eps tg xs (by rw [hY]; simpa using hx) rest
  rw [hY] at t
  simpa using t

/-! ## The tie -/

/-- **c steps of the tie from step l on.** For a family J of jobs of which those from l to l + c - 1
are lawful, have no variable but Y, and whose targets follow each other (the target of step i + 1 is
shown value number "nxAt i" of step i): "TwV.tieGo" from the target of step l, on these jobs' rounds
followed by any rest, returns their values "scJob" at these targets, and the rest. -/
theorem tieGo_jobs (led : ℕ → Led P) (μ : P → K) (J : ℕ → Job K) (tg E B : ℕ → K) :
    ∀ (c l : ℕ) (rest : Rounds K),
    (∀ i, l ≤ i → i < l + c → (J i).Lawful ∧ (J i).zs = [] ∧ (J i).dg = [] ∧ (J i).dY.isSome ∧
      tg (i + 1) = (shownOf (led i) μ (J i) [B i]).getD (nxAt i) 0) →
    tieGo c l (tg l)
        ((List.range' l c).flatMap (fun s => runJob (led s) μ (J s) (E s) [B s]) ++ rest) =
      ((List.range' l c).map fun s => scJob (led s) μ (J s) (E s) (tg s) [B s], rest)
  | 0, l, rest, _ => rfl
  | c + 1, l, rest, H => by
    obtain ⟨hL, hz, hd, hY, ht⟩ := H l (Nat.le_refl l) (by omega)
    have ih := tieGo_jobs led μ J tg E B c (l + 1) rest fun i h1 h2 => H i (by omega) (by omega)
    have t := takeSc_some (led l) μ (J l) hL (by rw [hz, hd]; rfl) hY (E l) (tg l) [B l]
      (by rw [hz]; rfl)
      ((List.range' (l + 1) c).flatMap (fun s => runJob (led s) μ (J s) (E s) [B s]) ++ rest)
    rw [hz] at t
    have e : (List.range' l (c + 1)).flatMap (fun s => runJob (led s) μ (J s) (E s) [B s]) ++ rest =
        runJob (led l) μ (J l) (E l) [B l] ++
          ((List.range' (l + 1) c).flatMap (fun s => runJob (led s) μ (J s) (E s) [B s]) ++
            rest) := by
      rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    rw [e]
    unfold tieGo
    simp only
    rw [show ([] : List K) ++ [0] = [0] from rfl] at t
    rw [t]
    simp only
    have ev : (scJob (led l) μ (J l) (E l) (tg l) [B l]).v (nxAt l) = tg (l + 1) := by
      unfold Sc.v
      rw [scJob_vals _ _ _ _ _ _ hY, ht]
    rw [ev, ih, List.range'_succ, List.map_cons]

/-! ## A tree -/

/-- **c levels of a tree from level l on.** For a family J of jobs of which those from l to l + c -
1 are lawful, have end values, as many degrees as points, the points "inRounds (o i) (pt i)" and one
challenge more than points, and whose targets and points follow each other (the next target is
"lineTg" of the level's "scJob" at the line's draw; the next point is the level's challenges by
coordinate, then the draw): "TwV.lvGo" from the target and the point of level l, on these jobs'
rounds, each followed by its line's draw, and then any rest, returns the levels' "scJob" with their
draws, the target and the point of level l + c, and the rest. -/
theorem lvGo_jobs (o : ℕ → List ℕ) (led : ℕ → Led P) (μ : P → K) (J : ℕ → Job K)
    (pt : ℕ → List K) (tg E : ℕ → K) (X : ℕ → List K) (R : ℕ → K) :
    ∀ (c l : ℕ) (rest : Rounds K),
    (∀ i, l ≤ i → i < l + c → (J i).Lawful ∧ (J i).dg.length = (J i).zs.length ∧
      (J i).dY.isSome ∧ (J i).zs = inRounds (o i) (pt i) ∧ (X i).length = (J i).zs.length + 1 ∧
      tg (i + 1) = lineTg (scJob (led i) μ (J i) (E i) (tg i) (X i)) (R i) ∧
      pt (i + 1) = byVar (o i) (X i) ++ [R i]) →
    lvGo o c l (tg l) (pt l)
        ((List.range' l c).flatMap
          (fun s => runJob (led s) μ (J s) (E s) (X s) ++ [([], [R s])]) ++ rest) =
      ((List.range' l c).map fun s => (scJob (led s) μ (J s) (E s) (tg s) (X s), R s),
        tg (l + c), pt (l + c), rest)
  | 0, l, rest, _ => rfl
  | c + 1, l, rest, H => by
    obtain ⟨hL, hd, hY, hz, hx, ht, hp⟩ := H l (Nat.le_refl l) (by omega)
    have ih := lvGo_jobs o led μ J pt tg E X R c (l + 1) rest
      fun i h1 h2 => H i (by omega) (by omega)
    have t := takeSc_some (led l) μ (J l) hL hd hY (E l) (tg l) (X l) hx
      (([], [R l]) :: ((List.range' (l + 1) c).flatMap
        (fun s => runJob (led s) μ (J s) (E s) (X s) ++ [([], [R s])]) ++ rest))
    rw [hz] at t
    have e : (List.range' l (c + 1)).flatMap
          (fun s => runJob (led s) μ (J s) (E s) (X s) ++ [([], [R s])]) ++ rest =
        runJob (led l) μ (J l) (E l) (X l) ++
          (([], [R l]) :: ((List.range' (l + 1) c).flatMap
            (fun s => runJob (led s) μ (J s) (E s) (X s) ++ [([], [R s])]) ++ rest)) := by
      rw [List.range'_succ, List.flatMap_cons, List.append_assoc, List.append_assoc]
      rfl
    rw [e]
    unfold lvGo
    simp only
    rw [t]
    simp only [List.headD_cons, List.tail_cons]
    rw [scJob_xs, ← ht, ← hp, ih, List.range'_succ, List.map_cons,
      show l + 1 + c = l + (c + 1) by omega]

/-! ## TwV.traceOfFlat, step by step -/

/-- "TwV.traceOfFlat" on a list of rounds r0 :: rt, from the results of its eight steps: if each
step, at what the steps in front returned, returns what h1 to h8 say, the trace is made of these
results. -/
theorem traceOfFlat_eq (N : Nums P K) (r0 : List K × List K) (rt r1 r2 r3 r4 r5 : Rounds K)
    (lam kT tT : K)
    (tie : List (Sc K)) (join kp tp zero : List K) (keys tabl : List (Sc K × K)) (cls bits : Sc K)
    (h1 : r0.2.headD 0 = lam)
    (h2 : tieGo (N.n + 1) 0 0 rt = (tie, r1))
    (h3 : (r1.headD ([], [])).2 = join)
    (h4 : lvGo N.oK (N.v' + 1) 0 (tK ⟨lam, tie, join, [], 0, [], Sc.zero, [], Sc.zero⟩) [] r1.tail =
      (keys, kT, kp, r2))
    (h5 : lvGo N.oT N.d 0 (tgT0 N ⟨lam, tie, join, [], 0, [], Sc.zero, [], Sc.zero⟩) join r2 =
      (tabl, tT, tp, r3))
    (h6 : takeSc r3 tT (inRounds N.oE tp) false = (cls, r4))
    (h7 : (r4.headD ([], [])).2 = zero)
    (h8 : takeSc r4.tail 0 (inRounds N.oB zero ++ [0]) true = (bits, r5)) :
    traceOfFlat N (r0 :: rt) = ⟨lam, tie, join, keys, kT, tabl, cls, zero, bits⟩ := by
  unfold traceOfFlat
  simp only [List.headD_cons, List.tail_cons, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## The honest rounds -/

variable (D : Data P K) (μ : P → K) (C : Chal K)

/-- Member number th of the list of the tie's steps in "trT", for th ≤ n, is "scJob" of step th. -/
theorem tie_getD {th : ℕ} (h : th < D.N.n + 1) :
    ((List.range' 0 (D.N.n + 1)).map fun s =>
      scJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) (tieTg D μ C s) [C.tieB s]).getD th Sc.zero =
      scJob (D.N.ledTie th) μ (tieJob D th) (C.tieE th) (tieTg D μ C th) [C.tieB th] := by
  rw [← List.range_eq_range', List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h]
  rfl

/-- Shown value number a of the tie's step s in "trT" is "tieShown". It holds by unfolding. -/
theorem tie_v (s a : ℕ) :
    (scJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) (tieTg D μ C s) [C.tieB s]).v a =
      tieShown D μ C s a := rfl

/-- **"TwV.traceOfFlat" reads "trT" off "rsT", if the jobs are lawful.** Under "PremT D μ C", if the
job of every tie step s ≤ n, of every key level l < v at "keyPt", of every table level l < d at
"tabPt", the leaves' job at "tabPt d" and the bits' job at the drawn point are lawful:
traceOfFlat D.N (rsT D μ C) = trT D μ C. -/
theorem trace_of_lawful (H : PremT D μ C) (hTie : ∀ s ≤ D.N.n, (tieJob D s).Lawful)
    (hKey : ∀ l < D.v, (keyJob D l (keyPt D C l)).Lawful)
    (hTab : ∀ l < D.N.d, (tabJob D l (tabPt D C l)).Lawful)
    (hCls : (leavesJob D (tabPt D C D.N.d)).Lawful) (hBit : (bitsJob D C.zero).Lawful) :
    traceOfFlat D.N (rsT D μ C) = trT D μ C := by
  -- the rounds, bracketed to the right
  have hrs : rsT D μ C = ([], [D.al]) ::
      ((List.range' 0 (D.N.n + 1)).flatMap (fun s =>
          runJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) [C.tieB s]) ++
        (([], C.join) ::
          ((List.range' 0 D.v).flatMap (fun l =>
              runJob (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyE l) (C.keyX l) ++
                [([], [C.keyR l])]) ++
            ((List.range' 0 D.N.d).flatMap (fun l =>
                runJob (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabE l) (C.tabX l) ++
                  [([], [C.tabR l])]) ++
              (runJob D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) C.clsE C.clsX ++
                (([], C.zero) ::
                  (runJob D.N.ledB μ (bitsJob D C.zero) C.bitE C.bitX ++ []))))))) := by
    unfold rsT
    simp only [List.range_eq_range', List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil]
  have lK : ∀ l < D.v, (D.N.oK l).length = l := fun l hl => by
    rw [(H.oK l hl).length_eq, List.length_range]
  have lT : ∀ l < D.N.d, (D.N.oT l).length = D.N.w + l := fun l hl => by
    rw [(H.oT l hl).length_eq, List.length_range]
  have lE : D.N.oE.length = D.N.w + D.N.d := by rw [H.oE.length_eq, List.length_range]
  have lB : D.N.oB.length = D.N.w + D.N.d := by rw [H.oB.length_eq, List.length_range]
  have t2 := tieGo_jobs D.N.ledTie μ (tieJob D) (tieTg D μ C) C.tieE C.tieB (D.N.n + 1) 0
    (([], C.join) ::
      ((List.range' 0 D.v).flatMap (fun l =>
          runJob (D.N.ledK l) μ (keyJob D l (keyPt D C l)) (C.keyE l) (C.keyX l) ++
            [([], [C.keyR l])]) ++
        ((List.range' 0 D.N.d).flatMap (fun l =>
            runJob (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabE l) (C.tabX l) ++
              [([], [C.tabR l])]) ++
          (runJob D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) C.clsE C.clsX ++
            (([], C.zero) :: (runJob D.N.ledB μ (bitsJob D C.zero) C.bitE C.bitX ++ []))))))
    (fun i _ hi => ⟨hTie i (by omega), rfl, rfl, rfl, by
      show (if i + 1 = 0 then (0 : K) else _) = _
      rw [if_neg (Nat.succ_ne_zero i)]
      rfl⟩)
  have t4 := lvGo_jobs D.N.oK D.N.ledK μ (fun l => keyJob D l (keyPt D C l)) (keyPt D C)
    (keyTg D μ C) C.keyE C.keyX C.keyR D.v 0
    ((List.range' 0 D.N.d).flatMap (fun l =>
        runJob (D.N.ledT l) μ (tabJob D l (tabPt D C l)) (C.tabE l) (C.tabX l) ++
          [([], [C.tabR l])]) ++
      (runJob D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) C.clsE C.clsX ++
        (([], C.zero) :: (runJob D.N.ledB μ (bitsJob D C.zero) C.bitE C.bitX ++ []))))
    (fun i _ hi => by
      have hi' : i < D.v := by omega
      refine ⟨hKey i hi', ?_, rfl, rfl, ?_, rfl, rfl⟩
      · show (List.replicate i 2).length = (inRounds (D.N.oK i) (keyPt D C i)).length
        unfold inRounds
        rw [List.length_replicate, List.length_map, lK i hi']
      · show (C.keyX i).length = (inRounds (D.N.oK i) (keyPt D C i)).length + 1
        unfold inRounds
        rw [List.length_map, lK i hi', H.chal.keyX i hi'])
  have t5 := lvGo_jobs D.N.oT D.N.ledT μ (fun l => tabJob D l (tabPt D C l)) (tabPt D C)
    (tabTg D μ C) C.tabE C.tabX C.tabR D.N.d 0
    (runJob D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) C.clsE C.clsX ++
      (([], C.zero) :: (runJob D.N.ledB μ (bitsJob D C.zero) C.bitE C.bitX ++ [])))
    (fun i _ hi => by
      have hi' : i < D.N.d := by omega
      refine ⟨hTab i hi', ?_, rfl, rfl, ?_, rfl, rfl⟩
      · show (List.replicate (D.N.w + i) 2).length = (inRounds (D.N.oT i) (tabPt D C i)).length
        unfold inRounds
        rw [List.length_replicate, List.length_map, lT i hi']
      · show (C.tabX i).length = (inRounds (D.N.oT i) (tabPt D C i)).length + 1
        unfold inRounds
        rw [List.length_map, lT i hi', H.chal.tabX i hi'])
  rw [Nat.zero_add] at t4 t5
  rw [show tieTg D μ C 0 = 0 from if_pos rfl] at t2
  have t6 := takeSc_none D.N.ledE μ (leavesJob D (tabPt D C D.N.d)) hCls
    (by
      show (dgE D.N).length = (inRounds D.N.oE (tabPt D C D.N.d)).length
      unfold dgE inRounds
      rw [List.length_map, List.length_map])
    rfl C.clsE (tabTg D μ C D.N.d) C.clsX
    (by
      show C.clsX.length = (inRounds D.N.oE (tabPt D C D.N.d)).length
      unfold inRounds
      rw [List.length_map, lE, H.chal.clsX])
    (([], C.zero) :: (runJob D.N.ledB μ (bitsJob D C.zero) C.bitE C.bitX ++ []))
  have t8 := takeSc_some D.N.ledB μ (bitsJob D C.zero) hBit
    (by
      show (List.replicate (D.N.w + D.N.d) 2).length = (inRounds D.N.oB C.zero).length
      unfold inRounds
      rw [List.length_replicate, List.length_map, lB])
    rfl C.bitE 0 C.bitX
    (by
      show C.bitX.length = (inRounds D.N.oB C.zero).length + 1
      unfold inRounds
      rw [List.length_map, lB, H.chal.bitX])
    []
  -- the table's first target
  have e5 : tgT0 D.N ⟨D.al, (List.range' 0 (D.N.n + 1)).map fun s =>
        scJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) (tieTg D μ C s) [C.tieB s], C.join, [], 0,
        [], Sc.zero, [], Sc.zero⟩ = tabTg D μ C 0 := by
    show ((List.range (2 ^ D.N.w)).map fun th => eqN C.join th * tgtT D.N _ th).sum =
      ((List.range (2 ^ D.N.w)).map fun j => eqN C.join j * gShown D μ C j).sum
    refine congrArg List.sum (List.map_congr_left fun th hth => ?_)
    have hth' : th < D.N.n + 2 := by
      rw [H.planes]
      exact List.mem_range.1 hth
    congr 1
    unfold tgtT gShown
    by_cases c : th < D.N.n + 1
    · rw [if_pos c, if_pos c]
      show (List.getD _ th Sc.zero).v (TwV.ptAt th) = _
      rw [tie_getD D μ C c, tie_v]
    · rw [if_neg c, if_neg c, if_pos (by omega)]
      show (List.getD _ D.N.n Sc.zero).v (nxAt D.N.n) = _
      rw [tie_getD D μ C (Nat.lt_succ_self _), tie_v]
  have e4 : tK ⟨D.al, (List.range' 0 (D.N.n + 1)).map fun s =>
        scJob (D.N.ledTie s) μ (tieJob D s) (C.tieE s) (tieTg D μ C s) [C.tieB s], C.join, [], 0,
        [], Sc.zero, [], Sc.zero⟩ = keyTg D μ C 0 := by
    show (List.getD _ 0 Sc.zero).v 0 = _
    rw [tie_getD D μ C (Nat.succ_pos _), tie_v]
    rfl
  rw [hrs]
  rw [← e4] at t4
  rw [← e5] at t5
  refine (traceOfFlat_eq D.N ([], [D.al]) _ _ _ _ _ _ D.al _ _ _ C.join _ _ C.zero _ _ _ _ rfl t2
    rfl t4 t5 t6 rfl t8).trans ?_
  unfold trT
  simp only [List.range_eq_range']

/-- Under "PremT" the key side's point of level l ≤ v has l coordinates. -/
theorem keyPt_length (H : PremT D μ C) : ∀ l ≤ D.v, (keyPt D C l).length = l
  | 0, _ => rfl
  | l + 1, hl => by
    show (byVar (D.N.oK l) (C.keyX l) ++ [C.keyR l]).length = l + 1
    unfold byVar
    rw [List.length_append, List.length_map, List.length_range, (H.oK l hl).length_eq,
      List.length_range]
    rfl

/-- Under "PremT" the table side's point of level l ≤ d has w + l coordinates. -/
theorem tabPt_length (H : PremT D μ C) : ∀ l ≤ D.N.d, (tabPt D C l).length = D.N.w + l
  | 0, _ => H.chal.join
  | l + 1, hl => by
    show (byVar (D.N.oT l) (C.tabX l) ++ [C.tabR l]).length = D.N.w + (l + 1)
    unfold byVar
    rw [List.length_append, List.length_map, List.length_range, (H.oT l hl).length_eq,
      List.length_range]
    rfl

/-- **"TwV.traceOfFlat" reads "trT" off "rsT".** Under "PremT D μ C":
traceOfFlat D.N (rsT D μ C) = trT D μ C. The jobs are lawful by
Johnson/HonestTrace/LookCube.lean ("pj_lawful") and LookJobs.lean ("tieJob_lawful",
"leavesJob_lawful", "bitsJob_lawful"). -/
theorem trace_hon (H : PremT D μ C) : traceOfFlat D.N (rsT D μ C) = trT D μ C :=
  trace_of_lawful D μ C H (fun _ hs => tieJob_lawful D H.mid hs)
    (fun l hl => pj_lawful l 0 _ _ (D.N.oK l) (keyPt D C l) (H.oK l hl)
      (keyPt_length D μ C H l (Nat.le_of_lt hl)))
    (fun l hl => pj_lawful (D.N.w + l) 0 _ _ (D.N.oT l) (tabPt D C l) (H.oT l hl)
      (tabPt_length D μ C H l (Nat.le_of_lt hl)))
    (leavesJob_lawful D _ (tabPt_length D μ C H D.N.d (Nat.le_refl _)) H.oE)
    (bitsJob_lawful D C.zero H.chal.zero H.oB)

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.scJob_xs
#print axioms OnBytes.HonestTrace.Look.scJob_vals
#print axioms OnBytes.HonestTrace.Look.takeSc_some
#print axioms OnBytes.HonestTrace.Look.takeSc_none
#print axioms OnBytes.HonestTrace.Look.tieGo_jobs
#print axioms OnBytes.HonestTrace.Look.lvGo_jobs
#print axioms OnBytes.HonestTrace.Look.traceOfFlat_eq
#print axioms OnBytes.HonestTrace.Look.tie_getD
#print axioms OnBytes.HonestTrace.Look.tie_v
#print axioms OnBytes.HonestTrace.Look.trace_of_lawful
#print axioms OnBytes.HonestTrace.Look.keyPt_length
#print axioms OnBytes.HonestTrace.Look.tabPt_length
#print axioms OnBytes.HonestTrace.Look.trace_hon
