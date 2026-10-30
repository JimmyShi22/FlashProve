-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndLoops.lean: what all ties and all reads of the smallness test together add
to the sub-proof's one equation: the two loops of objectsF (OnBytes/Model/Tail.lean).

Definitions, statements and proofs. A loop in SubM whose body never breaks off is the runs of its
body, in order (as forIn_inv of OnBytes/Slice/BlkSendRun.lean says for Blk).
Main names:
  `RunFoldS`, `forInS_inv`, `forInS_inv_array`, `runFold_append`, `runFold_flat`, `runFold_mono`,
    `runFold_map`: loops.
  `Kept`: what the claims keep of a state. `colsU`: an array's number of columns.
  `tieBracket`, `readBracket`, `tieTerm`, `readTerm`: what a tie and a read add.
  `readsList`: the reads in the order in which objectsF adds them.
  `objectsF_total`: if objectsF returns, then behind the lookup's claims and weightsF the total
    grows by the sum of the ties' and the reads' terms.
Limits: of the lookup's claims nothing is said but that they ran. Of what objectsF tests of a table
only the number of its weights is carried out of the run. The marks on the tables' entries,
the tiling of the tables and the three counts that objectsF tests are not carried out of the run.

-/
import OnBytes.Tie.Pv.Tail.EndClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-! ## Loops in SubM -/

theorem pure_ok {α : Type} (a x : α) (F G : Fork) (c c' : Ctx) :
    (pure a : SubM α) F c = .ok ((x, G), c') ↔ x = a ∧ G = F ∧ c' = c := by
  show (Except.ok ((a, F), c) : Except Failure ((α × Fork) × Ctx)) = .ok ((x, G), c') ↔ _
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

/-- The runs of a loop's body on the entries of a list, one after the other. -/
def RunFoldS {α β : Type} (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop) :
    List α → β → Fork → Ctx → β → Fork → Ctx → Prop
  | [], b, F, c, b', F', c' => b' = b ∧ F' = F ∧ c' = c
  | a :: l, b, F, c, b', F', c' =>
    ∃ b1 F1 c1, step a b F c b1 F1 c1 ∧ RunFoldS step l b1 F1 c1 b' F' c'

/-- A run of a loop over a list whose body never breaks off is the runs of the body, in order. -/
theorem forInS_inv {α β : Type} (f : α → β → SubM (ForInStep β))
    (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop)
    (hf : ∀ a b F c r F1 c1, f a b F c = .ok ((r, F1), c1) →
      ∃ b1, r = .yield b1 ∧ step a b F c b1 F1 c1) :
    ∀ (l : List α) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      (forIn l b f) F c = .ok ((b', F'), c') → RunFoldS step l b F c b' F' c'
  | [], b, F, c, b', F', c', h => by
    rw [List.forIn_nil] at h
    exact (pure_ok _ _ _ _ _ _).1 h
  | a :: l, b, F, c, b', F', c', h => by
    rw [List.forIn_cons] at h
    obtain ⟨r, F1, c1, h1, h2⟩ := (bind_ok _ _ _ _ _).1 h
    obtain ⟨b1, rfl, hs⟩ := hf a b F c r F1 c1 h1
    exact ⟨b1, F1, c1, hs, forInS_inv f step hf l b1 F1 c1 b' F' c' h2⟩

/-- The same for a loop over an array. -/
theorem forInS_inv_array {α β : Type} (f : α → β → SubM (ForInStep β))
    (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop)
    (hf : ∀ a b F c r F1 c1, f a b F c = .ok ((r, F1), c1) →
      ∃ b1, r = .yield b1 ∧ step a b F c b1 F1 c1)
    (as : Array α) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx)
    (h : (forIn as b f) F c = .ok ((b', F'), c')) : RunFoldS step as.toList b F c b' F' c' := by
  rw [← Array.forIn_toList] at h
  exact forInS_inv f step hf _ _ _ _ _ _ _ h

theorem runFold_append {α β : Type} (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop) :
    ∀ (l1 l2 : List α) (b : β) (F : Fork) (c : Ctx) (b1 : β) (F1 : Fork) (c1 : Ctx) (b2 : β)
      (F2 : Fork) (c2 : Ctx),
      RunFoldS step l1 b F c b1 F1 c1 → RunFoldS step l2 b1 F1 c1 b2 F2 c2 →
      RunFoldS step (l1 ++ l2) b F c b2 F2 c2
  | [], l2, b, F, c, b1, F1, c1, b2, F2, c2, h1, h2 => by
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact h2
  | a :: l1, l2, b, F, c, b1, F1, c1, b2, F2, c2, h1, h2 => by
    obtain ⟨b0, F0, c0, hs, hr⟩ := h1
    exact ⟨b0, F0, c0, hs, runFold_append step l1 l2 _ _ _ _ _ _ _ _ _ hr h2⟩

/-- A loop whose body is itself a loop is one loop over the flattened list. -/
theorem runFold_flat {α γ β : Type} (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop)
    (g : γ → List α) :
    ∀ (l : List γ) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      RunFoldS (fun x => RunFoldS step (g x)) l b F c b' F' c' →
      RunFoldS step (l.flatMap g) b F c b' F' c'
  | [], b, F, c, b', F', c', h => h
  | x :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, hs, hr⟩ := h
    rw [List.flatMap_cons]
    exact runFold_append step _ _ _ _ _ _ _ _ _ _ _ hs (runFold_flat step g l _ _ _ _ _ _ hr)

theorem runFold_mono {α β : Type} (step step' : α → β → Fork → Ctx → β → Fork → Ctx → Prop)
    (hm : ∀ a b F c b1 F1 c1, step a b F c b1 F1 c1 → step' a b F c b1 F1 c1) :
    ∀ (l : List α) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      RunFoldS step l b F c b' F' c' → RunFoldS step' l b F c b' F' c'
  | [], b, F, c, b', F', c', h => h
  | a :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, hs, hr⟩ := h
    exact ⟨b1, F1, c1, hm _ _ _ _ _ _ _ hs, runFold_mono step step' hm l _ _ _ _ _ _ hr⟩

theorem runFold_map {α γ β : Type} (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop)
    (g : γ → α) :
    ∀ (l : List γ) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      RunFoldS (fun x => step (g x)) l b F c b' F' c' → RunFoldS step (l.map g) b F c b' F' c'
  | [], b, F, c, b', F', c', h => h
  | x :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, hs, hr⟩ := h
    exact ⟨b1, F1, c1, hs, runFold_map step g l _ _ _ _ _ _ hr⟩

/-! ## What a claim keeps -/

/-- t2Lin keeps the plan's number of claims. -/
theorem t2Lin_plan (a : Aff) (runs : Array Run2) (F G : Fork) (c c' : Ctx)
    (hs : F.LS.size = F.ns) (h : t2Lin a runs F c = .ok (((), G), c')) :
    G.planClaimsF = F.planClaimsF := by
  simp only [t2Lin, SubM.kap, SubM.push, SubM.change, SubM.take, bind, StateT.bind] at h
  cases h1 : F.kap with
  | none => simp [h1, liftOption_none, Except.bind] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    simp only [h1, Option.map_some, liftOption_some, Except.bind] at h
    cases h2 : F1.push k a with
    | none => simp [h2, liftOption_none] at h
    | some F2 =>
      simp only [h2, Option.map_some, liftOption_some] at h
      cases h3 : F2.pushRuns k runs with
      | none => simp [h3, liftOption_none] at h
      | some G' =>
        simp only [h3, Option.map_some, liftOption_some, Except.ok.injEq, Prod.mk.injEq,
          true_and] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k h1
        have hs1 : F1.LS.size = F1.ns := by rw [hF1]; exact hs
        obtain ⟨_, hF2, _, _⟩ :=
          Fork.push_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F1 F2 k a hs1 h2
        obtain ⟨_, hG, _⟩ :=
          Fork.pushRuns_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F2 G' k runs h3
        rw [hG, hF2, hF1]

/-- What the smallness test's claims keep of a state, against a state F0. -/
structure Kept (F0 F : Fork) : Prop where
  theta : F.theta = F0.theta
  plan : F.planClaimsF = F0.planClaimsF
  sized : F.LS.size = F.ns
  frame : treesFrame F.trees = treesFrame F0.trees

/-- The number of columns of array t. -/
def colsU (F : Fork) (t : Nat) : Nat := ((F.trees[t]?).map (·.K)).getD 0

theorem colsU_frame (F F0 : Fork) (h : treesFrame F.trees = treesFrame F0.trees) (t : Nat) :
    colsU F t = colsU F0 t := by
  have := congrArg (fun a => ((a[t]?).map (fun x => x.1.K)).getD 0) h
  simpa [treesFrame, HTree.frame, colsU, Array.getElem?_map, Option.map_map, Function.comp]
    using this

/-! ## The two brackets, as functions of the tail's state -/

/-- The bracket of the tie of matrix mu (linTie_total). -/
def tieBracket (tl : HTailF2) (mu : Nat) : K :=
  -((2 : K) ^ 17 * (ρ.val (sumE tl.vp) * ρ.val (sumE
      ((tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[]) (tl.loX.getD mu #[])).getD #[]))))
    + runSum (fun i => ρ.val (((tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[])
          (tl.loX.getD mu #[])).getD #[]).getD i zeroE)
        * W.entry tl.ix.ZZ tl.zzRowTies ((tl.zzCol mu 0 0).getD 0 + i)) (tl.shp.getD mu {}).m 0
    + (2 : K) ^ 10 * runSum (fun i => ρ.val (((tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[])
          (tl.loX.getD mu #[])).getD #[]).getD i zeroE)
        * W.entry tl.ix.ZZ tl.zzRowTies ((tl.zzCol mu 1 0).getD 0 + i)) (tl.shp.getD mu {}).m 0
    - runSum (fun p => ρ.val (((tieRight (tl.shp.getD mu {}) (tl.loX.getD mu #[])
          (tl.gamX.getD mu #[])).getD #[]).getD p zeroE) * W.entry (tl.gtTree.getD mu 0) 0 p)
        ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k) 0

/-- The bracket of the read of segment x.2 of table x.1 (linRead_total). F0 gives the number of
columns
of the vector's array. -/
def readBracket (tl : HTailF2) (F0 : Fork) (x : HFun × Nat) : K :=
  -((2 : K) ^ 17 * ρ.val (mulE (sumE x.1.phi) (sumE tl.vt)))
    - runSum (fun d => ρ.val ((tl.gamV.getD x.1.mat #[]).getD d zeroE)
        * W.entry ((tl.ix.U.getD x.1.tree none).getD 0)
            (posOf tl x.1 x.2 d / colsU F0 ((tl.ix.U.getD x.1.tree none).getD 0))
            (posOf tl x.1 x.2 d % colsU F0 ((tl.ix.U.getD x.1.tree none).getD 0)))
        (tl.mats.getD x.1.mat {}).k 0
    + runSum (fun j => ρ.val (x.1.phi.getD j zeroE)
        * W.entry tl.ix.ZZ tl.zzRowReads ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j))
      x.1.len 0
    + (2 : K) ^ 10 * runSum (fun j => ρ.val (x.1.phi.getD j zeroE)
        * W.entry tl.ix.ZZ tl.zzRowReads ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j))
      x.1.len 0

theorem linTie_plan (tl : HTailF2) (mu : Nat) (F G : Fork) (c c' : Ctx) (hs : F.LS.size = F.ns)
    (h : tl.linTie mu F c = .ok (((), G), c')) : G.planClaimsF = F.planClaimsF := by
  unfold HTailF2.linTie at h
  simp only [bind_ok, get_ok, ask_ok] at h
  obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, h⟩ := h
  exact t2Lin_plan _ _ _ _ _ _ hs h

theorem linRead_plan (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (sums : E) (F G : Fork)
    (c c' : Ctx) (hs : F.LS.size = F.ns) (h : tl.linRead Fn sg laid sums F c = .ok (((), G), c')) :
    G.planClaimsF = F.planClaimsF := by
  unfold HTailF2.linRead at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq] at h
  obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨rfl, rfl, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨ht, rfl⟩, h⟩ := h
  have := testAs_ctx _ _ _ _ _ ht
  subst this
  obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, h⟩ := h
  exact t2Lin_plan _ _ _ _ _ _ hs h

/-- One tie, as a step against F0. -/
theorem linTie_step (tl : HTailF2) (mu : Nat) (F0 F G : Fork) (c c' : Ctx)
    (h : tl.linTie mu F c = .ok (((), G), c')) :
    (F.LS.size = F.ns → c' = c) ∧ (Kept F0 F → Kept F0 G ∧ G.nClaim = F.nClaim + 1 ∧
      G.total ρ W = F.total ρ W
      + ρ.val F0.theta ^ (F0.planClaimsF + tl.eqFirst.getD mu 0) * tieBracket ρ W tl mu) := by
  refine ⟨fun hs => (linTie_total ρ W tl mu F G c c' hs h).1, fun hk => ?_⟩
  obtain ⟨_, wl, wr, c0, c1, hwl, hwr, hc0, hc1, ht, e3, e4, e5, e6, e7⟩ :=
    linTie_total ρ W tl mu F G c c' hk.sized h
  refine ⟨⟨e4.trans hk.theta, (linTie_plan tl mu F G c c' hk.sized h).trans hk.plan, e6,
    e7.trans hk.frame⟩, e3, ?_⟩
  rw [ht, hk.theta, hk.plan]
  simp only [tieBracket, hwl, hwr, hc0, hc1, Option.getD_some]

/-- One read, as a step against F0. -/
theorem linRead_step (tl : HTailF2) (Fn : HFun) (sg laid : Nat) (F0 F G : Fork) (c c' : Ctx)
    (h : tl.linRead Fn sg laid (mulE (sumE Fn.phi) (sumE tl.vt)) F c = .ok (((), G), c')) :
    (F.LS.size = F.ns → c' = c) ∧ (Kept F0 F → Kept F0 G ∧ G.nClaim = F.nClaim + 1 ∧
      G.total ρ W = F.total ρ W
      + ρ.val F0.theta ^ (F0.planClaimsF + (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF))
        * readBracket ρ W tl F0 (Fn, sg)) := by
  refine ⟨fun hs => (linRead_total ρ W tl Fn sg laid _ F G c c' hs h).1, fun hk => ?_⟩
  obtain ⟨_, tU, c0, c1, htU, hc0, hc1, ht, e3, e4, e5, e6, e7⟩ :=
    linRead_total ρ W tl Fn sg laid _ F G c c' hk.sized h
  refine ⟨⟨e4.trans hk.theta, (linRead_plan tl Fn sg laid _ F G c c' hk.sized h).trans hk.plan,
    e6, e7.trans hk.frame⟩, e3, ?_⟩
  have hcol : ((F.trees[tU]?).map (·.K)).getD 0 = colsU F0 tU := colsU_frame F F0 hk.frame tU
  rw [ht, hk.theta, hk.plan, hcol]
  simp only [readBracket, htU, hc0, hc1, Option.getD_some]

/-! ## Sums over a loop's runs -/

/-- From a state that has kept F0's fields: the context stays, the fields are kept, n claims are
added,
and the one equation grows by t. -/
def AddStep (F0 : Fork) (n : Nat) (t : K) (F : Fork) (c : Ctx) (F1 : Fork) (c1 : Ctx) : Prop :=
  Kept F0 F → c1 = c ∧ Kept F0 F1 ∧ F1.nClaim = F.nClaim + n ∧ F1.total ρ W = F.total ρ W + t

theorem runFold_adds {α β : Type} (F0 : Fork) (term : α → K) :
    ∀ (l : List α) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      RunFoldS (fun a (_ : β) F c (_ : β) F1 c1 => AddStep ρ W F0 1 (term a) F c F1 c1)
        l b F c b' F' c' →
      AddStep ρ W F0 l.length (l.map term).sum F c F' c'
  | [], b, F, c, b', F', c', h => by
    obtain ⟨_, rfl, rfl⟩ := h
    intro hk
    exact ⟨rfl, hk, rfl, by simp⟩
  | a :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, hs, hr⟩ := h
    intro hk
    obtain ⟨e1, k1, n1, t1⟩ := hs hk
    obtain ⟨e2, k2, n2, t2⟩ := runFold_adds F0 term l b1 F1 c1 b' F' c' hr k1
    refine ⟨e2.trans e1, k2, by rw [n2, n1, List.length_cons]; omega, ?_⟩
    rw [t2, t1, List.map_cons, List.sum_cons]
    ring

theorem runFold_counts {α β : Type} (F0 : Fork) (cnt : β → Nat) (term : Nat → α → K) :
    ∀ (l : List α) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      RunFoldS (fun a b F c b1 F1 c1 =>
        cnt b1 = cnt b + 1 ∧ AddStep ρ W F0 1 (term (cnt b) a) F c F1 c1) l b F c b' F' c' →
      cnt b' = cnt b + l.length ∧ AddStep ρ W F0 l.length (sumFrom term (cnt b) l) F c F' c'
  | [], b, F, c, b', F', c', h => by
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, fun hk => ⟨rfl, hk, rfl, by simp [sumFrom]⟩⟩
  | a :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, ⟨hc, hs⟩, hr⟩ := h
    obtain ⟨hc2, hs2⟩ := runFold_counts F0 cnt term l b1 F1 c1 b' F' c' hr
    refine ⟨by rw [hc2, hc, List.length_cons]; omega, fun hk => ?_⟩
    obtain ⟨e1, k1, n1, t1⟩ := hs hk
    obtain ⟨e2, k2, n2, t2⟩ := hs2 k1
    refine ⟨e2.trans e1, k2, by rw [n2, n1, List.length_cons]; omega, ?_⟩
    rw [t2, t1, hc, sumFrom]
    ring

/-! ## objectsF's two loops -/

/-- The segments of table Fn, if it lies on matrix mu and on vector un; else none. -/
def segsOf (tl : HTailF2) (mu un : Nat) (Fn : HFun) : List (HFun × Nat) :=
  if (Fn.mat == mu && Fn.tree == un) = true then
    (List.range ((tl.mats.getD mu {}).m / Fn.len)).map fun sg => (Fn, sg)
  else []

/-- The reads in the order in which objectsF lays them: matrix by matrix, U1's tables before U3's,
the
list's order, segment by segment. -/
def readsList (tl : HTailF2) (funs : Array HFun) : List (HFun × Nat) :=
  (List.range tl.NM).flatMap fun mu =>
    [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl mu un)

/-- What the tie of matrix mu adds. -/
def tieTerm (tl : HTailF2) (F0 : Fork) (mu : Nat) : K :=
  ρ.val F0.theta ^ (F0.planClaimsF + tl.eqFirst.getD mu 0) * tieBracket ρ W tl mu

/-- What read number q adds. -/
def readTerm (tl : HTailF2) (F0 : Fork) (q : Nat) (x : HFun × Nat) : K :=
  ρ.val F0.theta ^ (F0.planClaimsF + (tl.eqFirst.getD tl.NM 0 + q * tl.stepF))
    * readBracket ρ W tl F0 x

/-- The reads' loops, flattened: one step for each read. -/
def stepR (tl : HTailF2) (F0 : Fork) (x : HFun × Nat) (b : MProd Nat (Array (Array Bool)))
    (F : Fork) (c : Ctx) (b1 : MProd Nat (Array (Array Bool))) (F1 : Fork) (c1 : Ctx) : Prop :=
  b1.fst = b.fst + 1 ∧ AddStep ρ W F0 1 (readTerm ρ W tl F0 b.fst x) F c F1 c1

/-- A step of the reads' loops, with what objectsF has tested of the read's table. -/
@[reducible] def stepP (tl : HTailF2) (F0 : Fork) (x : HFun × Nat)
    (b : MProd Nat (Array (Array Bool))) (F : Fork) (c : Ctx)
    (b1 : MProd Nat (Array (Array Bool))) (F1 : Fork) (c1 : Ctx) : Prop :=
  x.1.phi.size = x.1.len ∧ stepR ρ W tl F0 x b F c b1 F1 c1

/-- A fact that stands beside each step holds of every member of the list. -/
theorem runFold_all {α β : Type} (P : α → Prop)
    (step : α → β → Fork → Ctx → β → Fork → Ctx → Prop) :
    ∀ (l : List α) (b : β) (F : Fork) (c : Ctx) (b' : β) (F' : Fork) (c' : Ctx),
      RunFoldS (fun a b F c b1 F1 c1 => P a ∧ step a b F c b1 F1 c1) l b F c b' F' c' →
      (∀ a ∈ l, P a) ∧ RunFoldS step l b F c b' F' c'
  | [], _, _, _, _, _, _, h => ⟨fun _ ha => absurd ha (List.not_mem_nil), h⟩
  | a :: l, b, F, c, b', F', c', h => by
    obtain ⟨b1, F1, c1, ⟨hp, hs⟩, hr⟩ := h
    obtain ⟨ha, hr'⟩ := runFold_all P step l b1 F1 c1 b' F' c' hr
    refine ⟨fun x hx => ?_, b1, F1, c1, hs, hr'⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hp
    · exact ha x hx

/-- The ties and reads of objectsF. If objectsF returns from F, then its run is: the lookup's claims
(Forest.objects), the join (linJoin9), the planes (linBits9) and weightsF, of whose effect nothing
is
said here but that they ran one after the other from F and c and left tl1, F1, c1; and then the two
loops. If F1 has one coefficient for each slot, then from F1 to the end the context stays, theta,
planClaims and the arrays' frame are kept, and the one equation grows by the sum over the matrices
of
theta^(planClaims + eqFirst mu) times the tie's bracket, and the sum over the reads, q counting from
0
in objectsF's order, of theta^(planClaims + eqFirst NM + q stepF) times the read's bracket; one
claim is
added for each tie and each read. nX4Laid is the number of reads; the test's state that objectsF
returns is tl1 but for four fields; the list given is the closed list (funsHeld); each read's table
has as many weights as its segments have rows. -/
theorem objectsF_total (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) :
    ∃ g Fa ca tla Fb cb tlb Fc cc tl1 F1 c1,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      tlb.weightsF Fc cc = .ok ((tl1, F1), c1) ∧
      tl'.nX4Laid = (readsList tl1 funs).length ∧
      tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid,
                       lsTail := tl'.lsTail } ∧
      tl.funsHeld funs = true ∧
      (∀ x ∈ readsList tl1 funs, x.1.phi.size = x.1.len) ∧
      (F1.LS.size = F1.ns → c' = c1 ∧ Kept F1 G ∧
        G.nClaim = F1.nClaim + tl1.NM + (readsList tl1 funs).length ∧
        G.total ρ W = F1.total ρ W + ((List.range tl1.NM).map (tieTerm ρ W tl1 F1)).sum
          + sumFrom (readTerm ρ W tl1 F1) 0 (readsList tl1 funs)) := by
  unfold HTailF2.objectsF at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq, SubM.claims] at h
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨hfh, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨ht, rfl⟩, h⟩ := h
  have := testAs_ctx _ _ _ _ _ ht
  subst this
  obtain ⟨g, _, _, ⟨hg, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, Fa, ca, hFo, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, tla, Fb, cb, hJ, tlb, Fc, cc, hB,
    _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, tl1, F1, c1, hWt, h⟩ := h
  obtain ⟨_, F1', c1', ⟨_, hF1, hc1⟩, bT, F2, c2, hT, bR, F3, c3, hR, h⟩ := h
  rw [hF1, hc1] at hT
  clear hF1 hc1 F1' c1'
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := (pure_ok _ _ _ _ _ _).1 h
  -- the ties
  have rT := forInS_inv _
    (fun mu (_ : MProd (Array Nat) (Array Nat)) F c (_ : MProd (Array Nat) (Array Nat)) F' c' =>
      AddStep ρ W F1 1 (tieTerm ρ W tl1 F1 mu) F c F' c')
    (by
      intro mu b F c r F' c' hb
      simp only [bind_ok, pure_ok, ask_ok, Option.some.injEq] at hb
      obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, Fx, cx, hl, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
      refine ⟨_, rfl, fun hk => ?_⟩
      obtain ⟨e1, e2⟩ := linTie_step ρ W tl1 mu F1 _ _ _ _ hl
      exact ⟨e1 hk.sized, (e2 hk).1, (e2 hk).2.1, (e2 hk).2.2⟩) _ _ _ _ _ _ _ hT
  have aT := runFold_adds ρ W F1 _ _ _ _ _ _ _ _ rT
  -- the reads: four loops, flattened
  have rR := forInS_inv _
    (fun mu => RunFoldS (fun un => RunFoldS (fun (Fn : HFun) => RunFoldS (stepP ρ W tl1 F1)
      (segsOf tl1 mu un Fn)) funs.toList) [0, 2])
    (by
      intro mu b F c r F' c' hb
      simp only [bind_ok, pure_ok] at hb
      obtain ⟨b2, Fx, cx, h2, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
      refine ⟨_, rfl, ?_⟩
      refine forInS_inv _ _ ?_ _ _ _ _ _ _ _ h2
      intro un b F c r F' c' hb
      simp only [bind_ok, pure_ok] at hb
      obtain ⟨b3, Fx, cx, h3, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
      refine ⟨_, rfl, ?_⟩
      refine forInS_inv_array _ _ ?_ _ _ _ _ _ _ _ h3
      intro Fn b F c r F' c' hb
      by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
      · rw [if_pos hc] at hb
        simp only [bind_ok, pure_ok, lift_ok, mustAs_ok] at hb
        obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨hsf, rfl⟩, rfl⟩, b4, Fx, cx, h4,
          _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hsf
        refine ⟨_, rfl, ?_⟩
        rw [segsOf, if_pos hc]
        apply runFold_map
        refine forInS_inv _ _ ?_ _ _ _ _ _ _ _ h4
        intro sg b F c r F' c' hb
        simp only [bind_ok, pure_ok, get_ok] at hb
        obtain ⟨rd, _, _, ⟨_, rfl, rfl⟩, _, Fy, cy, hl, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
        refine ⟨_, rfl, hsf.2, rfl, fun hk => ?_⟩
        obtain ⟨e1, e2⟩ := linRead_step ρ W tl1 Fn sg _ F1 _ _ _ _ hl
        exact ⟨e1 hk.sized, (e2 hk).1, (e2 hk).2.1, (e2 hk).2.2⟩
      · rw [if_neg hc] at hb
        simp only [bind_ok, pure_ok] at hb
        obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
        refine ⟨_, rfl, ?_⟩
        rw [segsOf, if_neg hc]
        exact ⟨rfl, rfl, rfl⟩) _ _ _ _ _ _ _ hR
  have s1 := runFold_mono _
    (fun mu => RunFoldS (fun un => RunFoldS (stepP ρ W tl1 F1)
      (funs.toList.flatMap (segsOf tl1 mu un))) [0, 2])
    (fun mu _ _ _ _ _ _ h2 => runFold_mono _
      (fun un => RunFoldS (stepP ρ W tl1 F1) (funs.toList.flatMap (segsOf tl1 mu un)))
      (fun un _ _ _ _ _ _ h3 => runFold_flat (stepP ρ W tl1 F1) (segsOf tl1 mu un) _ _ _ _ _ _ _ h3)
      _ _ _ _ _ _ _ h2) _ _ _ _ _ _ _ rR
  have s2 := runFold_mono _
    (fun mu => RunFoldS (stepP ρ W tl1 F1)
      ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)))
    (fun mu _ _ _ _ _ _ h2 => runFold_flat (stepP ρ W tl1 F1)
      (fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ _ _ h2) _ _ _ _ _ _ _ s1
  have fP := runFold_flat (stepP ρ W tl1 F1)
    (fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ _ _ s2
  obtain ⟨hall, fR⟩ := runFold_all (fun x : HFun × Nat => x.1.phi.size = x.1.len)
    (stepR ρ W tl1 F1) _ _ _ _ _ _ _ fP
  have cR := runFold_counts ρ W F1 (fun b : MProd Nat (Array (Array Bool)) => b.fst)
    (readTerm ρ W tl1 F1) _ _ _ _ _ _ _ fR
  refine ⟨g, _, _, tla, _, _, tlb, _, _, tl1, F1, c1, hg, hFo, hJ, hB, hWt, ?_, rfl, hfh, hall, ?_⟩
  · have := cR.1
    simpa [readsList] using this
  · intro hs
    obtain ⟨e1, k1, n1, t1⟩ := aT ⟨rfl, rfl, hs, rfl⟩
    obtain ⟨e2, k2, n2, t2⟩ := cR.2 k1
    refine ⟨e2.trans e1, k2, ?_, ?_⟩
    · rw [n2, n1, List.length_range]
      rfl
    · rw [t2, t1]
      rfl

#print axioms linTie_step
#print axioms linRead_step
#print axioms objectsF_total

end OnBytes.Tie.Pv.Tail.Port
