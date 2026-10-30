-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieOkMade.lean: two tests on the plan of a proximity test, `tieOk` (TieOk.lean)
and `ownTieOk` (OwnTie.lean), say yes wherever the block's own test on the plan does.

`writtenOf` (PubOk.lean) lays the trees as they are told, in turn, on the declared rounds that send
a root. MadeRounds.lean writes these rounds out: the first "FOLD epsilon" where the first fold sends
its own mask, and each "SEND seed". tieOk counts by kk = h + (k - h), which is k where h ≤ k;
`sizesOk` asks that. Statements and proofs.
Main names:
  `wr`, `layW_quiet`, `layW_root`, `layW_rep`: a declared round as it is written. `kBat` … `kBase`:
    the kinds of the seven names.
  `layW_stage`, `layW_base`: a stage but the last, and the base case, as they are written: every
    written round spelled out.
  `told_cons`, `next_opens`: what the next stage opens is the head of the lists that are left to it.
    `cutsW`, `told_shapes`, `laidB_fst`: tools.
  `tie_step`, `tie_later`: one stage; the walk. `ownTold N`: the own mask's tree as it is told,
    where the first fold sends it.
  `written_made`: at a place whose numbers give rounds, with as many lists of oracle messages, and h
    ≤ k at each stage: the written rounds are there (w0 :: w); behind "BAT" they are as many as the
    laid declared rounds; tieOk's walk says yes; the first of them sends the own mask's tree as it
    is told, or none; what the first switch opens is p.nums.first and then the own mask's tree; that
    tree's source is "own", number free.
  `tieOk_made`, `ownTieOk_made`; `tieOk_of_planOk`, `ownTieOk_of_planOk`: (proximityTestKind X p).planOk = true
    gives tieOk p = true and ownTieOk p = true, whatever the parts X.
What it means: tieOk and ownTieOk lean on one test of the place: sizesOk's h ≤ k at each stage.
Beyond that they hold the text that makes the rounds (roundsOfNums) against writtenOf's: no plan
whose numbers give rounds, with as many lists of oracle messages and h ≤ k, can fail them.
What it pays: the premises htie : tieOk p = true (AccKPlace.lean, AccKConst.lean, AccKOwn.lean and
what they call) and hown : ownTieOk p = true (AccKOwn.lean). Of AtPlace
(Johnson/Desc/K12/Coin/Sheet.lean) and AtPlaceOwn
(Johnson/Desc/K12/Coin/OwnArm.lean): the first half of the field like
(writtenOf π.nums = some (w0 :: l)), no whole field.
Limits: that planOk says yes at a real place is not shown here: it has been seen in runs only.
Nothing is said on which written round sends a tree beyond the two clauses above: Chain.Trees is not
shown here (TreesMade.lean). No soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.EntriesMade
import Johnson.Desc.K12.Law.TieOk
import Johnson.Desc.K12.Law.OwnTie

set_option autoImplicit false
namespace H2K.Made
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Fmt.M1 (rEps rTwo rSeed rCs rLambda rBase laterRounds wMid)
open H2K.First
open H2K.Pub (WR writtenOf layW ownOf)

/-- A declared round as it is written. -/
def wr (r : Fmt.DeclaredRound) (k : Fmt.Kind) (t : Option Fmt.Shape) : WR :=
  ⟨r.entry, k, r.entry.cut, t, r.opens.filterMap ownOf⟩

theorem layW_quiet (r : Fmt.DeclaredRound) (rs : List Fmt.DeclaredRound) (sh : List Fmt.Shape)
    (k : Fmt.Kind) (hk : Fmt.kindOf r.entry.name = some k) (h0 : r.entry.roots = 0) :
    layW (r :: rs) sh = (layW rs sh).map (wr r k none :: ·) := by
  conv => lhs; unfold layW
  simp [hk, h0, wr]

theorem layW_root (r : Fmt.DeclaredRound) (rs : List Fmt.DeclaredRound) (s : Fmt.Shape)
    (t : List Fmt.Shape) (k : Fmt.Kind) (hk : Fmt.kindOf r.entry.name = some k)
    (h1 : r.entry.roots = 1) :
    layW (r :: rs) (s :: t) = (layW rs t).map (wr r k (some s) :: ·) := by
  conv => lhs; unfold layW
  simp [hk, h1, wr]

theorem layW_rep (r : Fmt.DeclaredRound) (k0 : Fmt.Kind) (hk : Fmt.kindOf r.entry.name = some k0)
    (h0 : r.entry.roots = 0) (rs : List Fmt.DeclaredRound) (sh : List Fmt.Shape) : ∀ k : Nat,
    layW (List.replicate k r ++ rs) sh = (layW rs sh).map (List.replicate k (wr r k0 none) ++ ·)
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, layW_quiet r _ sh k0 hk h0,
      layW_rep r k0 hk h0 rs sh k, Option.map_map]
    rfl

theorem kBat : Fmt.kindOf "BAT" = some .elems := by decide
theorem kEps : Fmt.kindOf "FOLD epsilon" = some .join := by decide
theorem kTwo : Fmt.kindOf "FOLD round" = some .elems := by decide
theorem kSeed : Fmt.kindOf "SEND seed" = some .seeds := by decide
theorem kCs : Fmt.kindOf "CS" = some .positions := by decide
theorem kLam : Fmt.kindOf "BASE lambda" = some .elems := by decide
theorem kBase : Fmt.kindOf "BASE" = some .positions := by decide

/-- A stage but the last, as it is written. pre: the own mask's shape, where this stage's fold sends
it. s: the shape of the tree that the switch sends. -/
theorem layW_stage (own seen : Bool) (work tree W : Nat) (cur nxt : Fmt.M1.Stage) (x : List Op)
    (R' : List Fmt.DeclaredRound) (pre : List Fmt.Shape) (s : Fmt.Shape) (S' : List Fmt.Shape)
    (hpre : ((own && !seen) = true ∧ ∃ s0, pre = [s0]) ∨ ((own && !seen) = false ∧ pre = [])) :
    layW ((⟨epsE own seen, [], []⟩ ::
        List.replicate cur.k (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        (⟨(rSeed nxt).entry, [], []⟩ :: ⟨(rCs work cur tree W).entry, [], x⟩ :: R'))
      (pre ++ s :: S') =
      (layW R' S').map fun w' => (wr ⟨epsE own seen, [], []⟩ .join pre.head? ::
        List.replicate cur.k (wr ⟨(rTwo "FOLD round").entry, [], []⟩ .elems none)) ++
        (wr ⟨(rSeed nxt).entry, [], []⟩ .seeds (some s) ::
          wr ⟨(rCs work cur tree W).entry, [], x⟩ .positions none :: w') := by
  have tail : layW (List.replicate cur.k (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound) ++
      (⟨(rSeed nxt).entry, [], []⟩ :: ⟨(rCs work cur tree W).entry, [], x⟩ :: R')) (s :: S') =
      (layW R' S').map fun w' =>
        List.replicate cur.k (wr ⟨(rTwo "FOLD round").entry, [], []⟩ .elems none) ++
        (wr ⟨(rSeed nxt).entry, [], []⟩ .seeds (some s) ::
          wr ⟨(rCs work cur tree W).entry, [], x⟩ .positions none :: w') := by
    rw [layW_rep _ .elems kTwo rfl, layW_root _ _ _ _ .seeds kSeed rfl,
      layW_quiet _ _ _ .positions kCs rfl, Option.map_map, Option.map_map]
    rfl
  rcases hpre with ⟨hc, s0, rfl⟩ | ⟨hc, rfl⟩
  · rw [List.cons_append, List.cons_append, List.nil_append,
      layW_root _ _ _ _ .join (by rw [epsE_name]; exact kEps) (by simp [epsE_roots, hc]), tail,
      Option.map_map]
    rfl
  · rw [List.cons_append, List.nil_append,
      layW_quiet _ _ _ .join (by rw [epsE_name]; exact kEps) (by simp [epsE_roots, hc]), tail,
      Option.map_map]
    rfl

/-- The base case, as it is written. -/
theorem layW_base (work tree : Nat) (cur : Fmt.M1.Stage) (x : List Op) :
    layW [⟨rLambda.entry, [], []⟩, ⟨(rBase work cur tree).entry, [], x⟩] [] =
      some [wr ⟨rLambda.entry, [], []⟩ .elems none,
        wr ⟨(rBase work cur tree).entry, [], x⟩ .positions none] := by
  rw [layW_quiet _ _ _ .elems kLam rfl, layW_quiet _ _ _ .positions kBase rfl]
  rfl

theorem told_cons (N : H2U.TestNums) (n : Nat) (x : List Op) (t : List (List Op))
    (h : ((told N).drop n).map ([·]) = x :: t) :
    ∃ a W, (told N).drop n = N.own a W (N.free + n) :: (told N).drop (n + 1) := by
  obtain ⟨a, W, _, rfl, rfl⟩ := told_drop N n x t h
  cases hd : (told N).drop n with
  | nil => rw [hd] at h; cases h
  | cons y ys =>
    rw [hd] at h
    have h1 : (told N).drop (n + 1) = ys := by
      have := congrArg (List.drop 1) hd
      simpa [List.drop_drop, Nat.add_comm] using this
    have h2 : [y] = [N.own a W (N.free + n)] := (List.cons.inj h).1
    exact ⟨a, W, by rw [h1, (List.cons.inj h2).1]⟩

/-- What the next stage opens is the head of the lists that are left to it. -/
theorem next_opens (own : Bool) (work tree W : Nat) (nxt : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (ls : List (List Op)) (R' : List Fmt.DeclaredRound) (l' : Laid)
    (h' : H2U.layOpens own true (laterRounds work tree W nxt rest) ls = some R')
    (hl' : l'.map (·.1) = R') :
    ∃ x t, ls = x :: t ∧ (cutN nxt rest l').flatMap (·.opens) = x := by
  cases rest with
  | nil =>
    obtain ⟨x, rfl, _, rfl⟩ := lay_base own work tree W nxt ls R' h'
    exact ⟨x, [], rfl, by simp [cutN, hl']⟩
  | cons n2 rest =>
    obtain ⟨x, t, R'', rfl, _, _, rfl⟩ := lay_stage own true work tree W nxt n2 rest ls R' h'
    obtain ⟨_, c2, _⟩ := cuts l' _ _ _ R'' nxt.k (by simp [Nat.add_comm]) hl'
    exact ⟨x, t, rfl, by simp [cutN, c2]⟩

theorem cutsW {α : Type} (A : List α) (S C : α) (R' : List α) (k : Nat) (hA : A.length = 1 + k) :
    (A ++ (S :: C :: R'))[1 + k]? = some S ∧ (A ++ (S :: C :: R')).drop (k + 3) = R' := by
  refine ⟨?_, ?_⟩
  · rw [List.getElem?_append_right (by omega), hA, Nat.sub_self]
    rfl
  · have e : k + 3 = (1 + k) + 2 := by omega
    rw [e, ← List.drop_drop, List.drop_left' hA]
    rfl

/-- One stage but the last. pre: the own mask's shape, where this stage's fold sends it. -/
theorem tie_step (p : P12) (own seen : Bool) (work tree W : Nat) (cur nxt : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (j : Nat) (l : Laid) (R : List Fmt.DeclaredRound) (x : List Op) (m : Nat)
    (pre : List Fmt.Shape)
    (hpre : ((own && !seen) = true ∧ ∃ s0, pre = [s0]) ∨ ((own && !seen) = false ∧ pre = []))
    (h : H2U.layOpens own seen (laterRounds work tree W cur (nxt :: rest))
      (x :: ((told p.nums).drop m).map ([·])) = some R)
    (hl : l.map (·.1) = R) (hk : cur.h ≤ cur.k)
    (IH : ∀ R' x', H2U.layOpens own true (laterRounds work (tree + 1) (wMid nxt) nxt rest)
        (x' :: ((told p.nums).drop (m + 1)).map ([·])) = some R' →
      (l.drop (cur.k + 3)).map (·.1) = R' →
      ∃ w', layW R' (((told p.nums).drop (m + 1)).map (·.1)) = some w' ∧
        w'.length = (l.drop (cur.k + 3)).length ∧
        ok (tieWalk (j + 1) nxt rest (l.drop (cur.k + 3)) w') = true) :
    ∃ w, layW R (pre ++ ((told p.nums).drop m).map (·.1)) = some w ∧ w.length = l.length ∧
      ok (tieWalk j cur (nxt :: rest) l w) = true ∧ (w[0]?).map (·.tree) = some pre.head? := by
  obtain ⟨x1, t, R', hx, _, h', rfl⟩ := lay_stage own seen work tree W cur nxt rest _ R h
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx
  obtain ⟨_, _, c3⟩ := cuts l _ _ _ R' cur.k (by simp [Nat.add_comm]) hl
  obtain ⟨x', t', hx', hcut⟩ := next_opens own work _ _ nxt rest _ R' _ h' c3
  obtain ⟨a, W', hd⟩ := told_cons _ _ _ _ hx'
  rw [hd, List.map_cons] at hx' h'
  obtain ⟨rfl, rfl⟩ := List.cons.inj hx'
  obtain ⟨w', hw', hlen', hok'⟩ := IH R' _ h' c3
  have hA : ((wr ⟨epsE own seen, [], []⟩ .join pre.head? ::
      List.replicate cur.k (wr ⟨(rTwo "FOLD round").entry, [], []⟩ .elems none)) : List WR).length
      = 1 + cur.k := by simp [Nat.add_comm]
  have hw : layW ((⟨epsE own seen, [], []⟩ ::
        List.replicate cur.k (⟨(rTwo "FOLD round").entry, [], []⟩ : Fmt.DeclaredRound)) ++
        (⟨(rSeed nxt).entry, [], []⟩ :: ⟨(rCs work cur tree W).entry, [], x⟩ :: R'))
      (pre ++ ((told p.nums).drop m).map (·.1)) =
      some ((wr ⟨epsE own seen, [], []⟩ .join pre.head? ::
        List.replicate cur.k (wr ⟨(rTwo "FOLD round").entry, [], []⟩ .elems none)) ++
        (wr ⟨(rSeed nxt).entry, [], []⟩ .seeds (some (p.nums.own a W' (p.nums.free + m)).1) ::
          wr ⟨(rCs work cur tree W).entry, [], x⟩ .positions none :: w')) := by
    rw [hd, List.map_cons, layW_stage own seen work tree W cur nxt x R' pre _ _ hpre, hw']
    rfl
  obtain ⟨g1, g2⟩ := cutsW _ (wr ⟨(rSeed nxt).entry, [], []⟩ .seeds
    (some (p.nums.own a W' (p.nums.free + m)).1))
    (wr ⟨(rCs work cur tree W).entry, [], x⟩ .positions none) w' cur.k hA
  have hkk : H2K.Pub.kk cur = cur.k := by unfold H2K.Pub.kk; omega
  refine ⟨_, hw, ?_, ?_, ?_⟩
  · have e1 := congrArg List.length hl
    have e3 := congrArg List.length c3
    simp only [List.length_map, List.length_append, List.length_cons, List.length_replicate]
      at e1 e3 ⊢
    omega
  · unfold tieWalk
    rw [hkk, g1, g2, hcut]
    simpa [ok, wr] using hok'
  · simp [wr]

/-- The walk from a stage behind the first "FOLD epsilon" on. -/
theorem tie_later (p : P12) (own : Bool) (work : Nat) : ∀ (rest : List Fmt.M1.Stage)
    (cur : Fmt.M1.Stage) (j tree W : Nat) (l : Laid) (R : List Fmt.DeclaredRound) (x : List Op)
    (m : Nat),
    H2U.layOpens own true (laterRounds work tree W cur rest)
      (x :: ((told p.nums).drop m).map ([·])) = some R →
    l.map (·.1) = R → (∀ s ∈ cur :: rest, s.h ≤ s.k) →
    ∃ w, layW R (((told p.nums).drop m).map (·.1)) = some w ∧ w.length = l.length ∧
      ok (tieWalk j cur rest l w) = true
  | [], cur, j, tree, W, l, R, x, m, h, hl, _ => by
    obtain ⟨x', hx, _, rfl⟩ := lay_base own work tree W cur _ R h
    have hn : (told p.nums).drop m = [] := by
      have := (List.cons.inj hx).2
      simpa using this
    refine ⟨[wr ⟨rLambda.entry, [], []⟩ .elems none,
      wr ⟨(rBase work cur tree).entry, [], x'⟩ .positions none], ?_, ?_, rfl⟩
    · rw [hn, List.map_nil, layW_base]
    · simpa using (congrArg List.length hl).symm
  | nxt :: rest, cur, j, tree, W, l, R, x, m, h, hl, hk => by
    obtain ⟨w, h1, h2, h3, _⟩ := tie_step p own true work tree W cur nxt rest j l R x m []
      (Or.inr ⟨by simp, rfl⟩) h hl (hk cur List.mem_cons_self)
      (fun R' x' hR' hl' => tie_later p own work rest nxt (j + 1) _ _ _ R' x' (m + 1) hR' hl'
        (fun s hs => hk s (List.mem_cons_of_mem _ hs)))
    exact ⟨w, by simpa using h1, h2, h3⟩

theorem told_shapes (N : H2U.TestNums) :
    (N.sent.zipIdx.map fun t => (N.own t.1.1 t.1.2 (N.free + t.2)).1) = (told N).map (·.1) := by
  unfold told
  rw [List.map_map]
  rfl

theorem laidB_fst (p : P12) (d0 : Fmt.DeclaredRound) (R : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some (d0 :: R)) (hlen : p.oracles.length = (d0 :: R).length) :
    (laidB p).map (·.1) = R := by
  unfold laidB
  rw [hr, Option.getD_some, List.map_drop, List.map_fst_zip (by omega)]
  rfl

/-- The own mask's tree as it is told, where the first fold sends it. -/
def ownTold (N : H2U.TestNums) : List Op := if N.ownMask then (told N).take 1 else []

/-- **The written rounds of a place, against its declared rounds.** -/
theorem written_made (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (hlen : p.oracles.length = rds.length)
    (hk : ∀ s ∈ p.nums.stages, s.h ≤ s.k) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (w : List WR),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: w) ∧
      w.length = (laidB p).length ∧ ok (tieWalk 0 a rest (laidB p) w) = true ∧
      (w[0]?).map (·.tree) = some ((ownTold p.nums).map (·.1)).head? ∧
      opensOf p a.k = p.nums.first ++ ownTold p.nums ∧
      (p.nums.ownMask = true → ∃ x W, ownTold p.nums = [p.nums.own x W p.nums.free]) := by
  obtain ⟨s, next, rest, R, hs, hR, rfl⟩ := rounds_top p.nums rds hr
  have hl := laidB_fst p _ R hr hlen
  have hopens : opensOf p s.k = p.nums.first ++ ownTold p.nums := by
    obtain ⟨x, t, R', hx, _, _, rfl⟩ := lay_stage _ _ _ _ _ _ _ _ _ R hR
    obtain ⟨_, c2, _⟩ := cuts (laidB p) _ _ _ R' s.k (by simp [Nat.add_comm]) hl
    have e : opensOf p s.k =
        ((((laidB p).drop (1 + s.k)).take 2).map (·.1)).flatMap (·.opens) := by
      unfold opensOf laidB
      rw [List.flatMap_map]
    rw [e, c2, ← (List.cons.inj hx).1]
    simp [ownTold]
  have key : ∃ (m : Nat) (pre : List Fmt.Shape),
      (if p.nums.ownMask then (told p.nums).drop 1 else told p.nums) = (told p.nums).drop m ∧
      (told p.nums).map (·.1) = pre ++ ((told p.nums).drop m).map (·.1) ∧
      pre = (ownTold p.nums).map (·.1) ∧
      (((p.nums.ownMask && !false) = true ∧ ∃ s0, pre = [s0]) ∨
        ((p.nums.ownMask && !false) = false ∧ pre = [])) ∧
      (p.nums.ownMask = true → ∃ x W, ownTold p.nums = [p.nums.own x W p.nums.free]) := by
    cases ho : p.nums.ownMask
    · exact ⟨0, [], by simp, by simp, by simp [ownTold, ho], Or.inr ⟨rfl, rfl⟩, by simp⟩
    · have h0 := told_at p.nums 0
      have hs0 : p.nums.sent[0]? = some (s.Z.a, 3 * 2 ^ s.h) := by
        unfold H2U.TestNums.sent
        rw [hs, ho]
        rfl
      rw [hs0] at h0
      cases ht : told p.nums with
      | nil => rw [ht] at h0; cases h0
      | cons y ys =>
        rw [ht] at h0
        have hy : y = p.nums.own s.Z.a (3 * 2 ^ s.h) (p.nums.free + 0) := Option.some.inj h0
        exact ⟨1, [y.1], by simp, by simp, by simp [ownTold, ho, ht], Or.inl ⟨rfl, y.1, rfl⟩,
          fun _ => ⟨s.Z.a, 3 * 2 ^ s.h, by simp [ownTold, ho, ht, hy]⟩⟩
  obtain ⟨m, pre, e1, e2, e3, hpre, hown⟩ := key
  rw [e1] at hR
  obtain ⟨w, h1, h2, h3, h4⟩ := tie_step p p.nums.ownMask false p.nums.work 0 0 s next rest 0
    (laidB p) R _ m pre hpre hR hl (hk s (by rw [hs]; exact List.mem_cons_self))
    (fun R' x' hR' hl' => tie_later p _ _ rest next 1 _ _ _ R' x' (m + 1) hR' hl'
      (fun x hx => hk x (by rw [hs]; exact List.mem_cons_of_mem _ hx)))
  refine ⟨s, next :: rest, wr ⟨{ Fmt.M1.rBat.entry with rows := p.nums.rows }, [], []⟩ .elems none,
    w, hs, ?_, h2, h3, by rw [h4, e3], hopens, hown⟩
  unfold writtenOf
  rw [hr, Option.bind_some, told_shapes, e2, layW_quiet _ _ _ .elems kBat rfl, h1]
  rfl

/-- **tieOk is a theorem.** -/
theorem tieOk_made (p : P12) (rds : List Fmt.DeclaredRound) (hr : H2U.roundsOfNums p.nums = some rds)
    (hlen : p.oracles.length = rds.length) (hk : ∀ s ∈ p.nums.stages, s.h ≤ s.k) :
    tieOk p = true := by
  obtain ⟨a, rest, w0, w, hs, hw, h2, h3, _⟩ := written_made p rds hr hlen hk
  obtain ⟨_, _, _, R, _, _, rfl⟩ := rounds_top p.nums rds hr
  have hb : (((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).take 1).map (·.1)) =
      [⟨{ Fmt.M1.rBat.entry with rows := p.nums.rows }, [], []⟩] := by
    rw [hr, Option.getD_some, List.map_take, List.map_fst_zip (by omega)]
    rfl
  unfold tieOk writtenB tieOn
  rw [hw, hs, hb]
  simp only [Option.isSome_some, Option.getD_some, List.drop_succ_cons, List.drop_zero,
    Bool.true_and]
  rw [ok_app]
  exact ⟨by simp [ok, nOpenB, h2], h3⟩

/-- **ownTieOk is a theorem.** -/
theorem ownTieOk_made (p : P12) (rds : List Fmt.DeclaredRound)
    (hr : H2U.roundsOfNums p.nums = some rds) (hlen : p.oracles.length = rds.length)
    (hk : ∀ s ∈ p.nums.stages, s.h ≤ s.k) : ownTieOk p = true := by
  obtain ⟨a, rest, w0, w, hs, hw, _, _, h4, h5, h6⟩ := written_made p rds hr hlen hk
  unfold ownTieOk writtenB ownTieOn
  rw [hw, hs]
  simp only [Option.getD_some, List.drop_succ_cons, List.drop_zero]
  cases hw0 : w[0]? with
  | none => rw [hw0] at h4; cases h4
  | some dE =>
    rw [hw0] at h4
    have h4' : dE.tree = ((ownTold p.nums).map (·.1)).head? := Option.some.inj h4
    cases ho : p.nums.ownMask
    · simp [ok, h4', ownTold, ho]
    · obtain ⟨x, W, hx⟩ := h6 ho
      rw [h5, hx]
      simp [ok, h4', hx, H2U.TestNums.own]

/-- **The block's test on the plan holds tieOk**, whatever the parts. -/
theorem tieOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : tieOk p = true := by
  obtain ⟨rds, hr, hl⟩ := rounds_of_planOk X p hp
  exact tieOk_made p rds hr hl fun s hs => (sizes_of_planOk X p hp s hs).2

/-- **The block's test on the plan holds ownTieOk**, whatever the parts. -/
theorem ownTieOk_of_planOk {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) : ownTieOk p = true := by
  obtain ⟨rds, hr, hl⟩ := rounds_of_planOk X p hp
  exact ownTieOk_made p rds hr hl fun s hs => (sizes_of_planOk X p hp s hs).2

end H2K.Made

#print axioms H2K.Made.written_made
#print axioms H2K.Made.tieOk_made
#print axioms H2K.Made.ownTieOk_made
#print axioms H2K.Made.tieOk_of_planOk
#print axioms H2K.Made.ownTieOk_of_planOk
