-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Own.lean: the own rounds of an attention sub-proof as one chain (Cb/Pv/Att/Chain.lean), at
letters. Fixed: the order, and of each stage whether it is a sumcheck, a draw, or scalars and a
draw. Which sumcheck stands at a place (`SumL.of3`, `SumL.ofD`), how many further scalars it has,
and all maps, weights, claims and linear claims are parameters.

Definitions, statements and proofs. The stages, in the order of the plan of rounds (the names say
what the programs run at each place): one sumcheck of products for each score unit; the sumcheck of
the denominator times the output; a draw of one element; the two sumchecks of the value product; a
draw of a point; a round with one scalar for each pair and a draw of one element; the sumcheck of
the score at the index; a draw of one element; the sumcheck by degrees of the key at the index; a
draw of one element; the sumcheck that the index's cells are bits. The plane values' scalars, which
the plan names first, are further scalars of the first sumcheck.

Main names:
  `SumL E M X`: the letters of one sumcheck at statements X: a plain sumcheck T with its conditions
    (`PlainSc`, Cb/Pv/Att/Plain.lean), the number n of further scalars, the claim cl, the reading
    msg, the linear claims L. `S.Nx`: the statements behind it. `SumL.of3`, `SumL.ofD`: from a
    sumcheck of products (`Sc3`) and from the sumcheck by degrees (`Scd`).
  `Ch.comap f c`: a chain on X read at statements X' through f : X' → X, with `Ch.todo_comap`,
    `Ch.ok_comap`, `Ch.nums_comap`, `Ch.sh_comap`.
  `Tail E M X`: the letters of the eleven stages behind the score units. `T.ch`: their chain.
    `T.Laws`: a bound on the bad draws at each of the five rounds that draw, and: what is owed at
    the end of the score's sumcheck, with the claim before the next draw, gives its output claims.
  `Seen E X`: the first statement with the further scalars of the score units so far, in order.
    `AttOwn E M X`: the score units' letters and a tail, all at statements `Seen E X`: so a unit's
    letters can name the further scalars of the units before it, and the tail's those of all units.
    `A.ch`: THE chain. `attOwn_ok`: its conditions, from `T.Laws`.
  `attOwn_knowAt`: `KnowAt` for `A.ch.R Ex`, from "`A.ch.Todo`" to `A.ch.Last`, under `T.Laws`
    alone.
  `attOwn_nums`: the list of its errors, in closed form.
  `law_pow`: a bound on the bad draws of a batch by the powers of one element, from `cnt_badPow`
    (Cb/G6/Johnson/Layers/Rounds.lean).

Limits: those of Cb/Pv/Att/Chain.lean. The errors are counts of draws, each among its own round's
draws: at the further variable's round among |E| - 1, at the draw of a point of nz coordinates among
|E|^nz (there the number is a parameter eZ of the tail), else among |E|. `T.Laws` speaks of all
messages m: its six clauses are laws on the letters, to be proved at a value. `T.Laws` does not ask
that pV, pZ, pF, pD, pH carry the later stages' claims: at letters that leave them out, `A.ch.Todo`
is silent on those stages. In Cb/Pv/Att/Gaps.lean these five are made so that they carry them. A
score unit's output is read by no later letter. That the letters at a value are the programs' maps,
weights and claims is not said here.

-/
import Cb.Pv.Att.Chain
import Cb.Pv.Att.Sc3
import Cb.Pv.Att.ScdProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-! ### A chain read through a map of statements -/

namespace Ch

/-- A chain on X, read at statements X' through f. -/
def comap : {X : Type} → Ch E M X → {X' : Type} → (X' → X) → Ch E M X'
  | _, .done _, X', _ => .done X'
  | _, .ride Y n F cl msg L Ow next, _, f =>
    .ride Y n F (fun x r => cl (f x) r) msg (fun x r m => L (f x) r m)
      (fun b m => Ow ((f b.1.1, b.1.2), b.2) m) (next.comap fun b => ((f b.1.1, b.1.2), b.2))
  | _, .draw D err P next, _, f =>
    .draw D err (fun x m => P (f x) m) (next.comap fun b => (f b.1, b.2))
  | _, .send n D err P L next, _, f =>
    .send n D err (fun x m => P (f x) m) (fun x s m => L (f x) s m)
      (next.comap fun b => ((f b.1.1, b.1.2), b.2))

theorem todo_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X) (x : X') (m : M),
    (c.comap f).Todo x m ↔ c.Todo (f x) m
  | _, .done _, _, _, _, _ => Iff.rfl
  | _, .ride _ _ _ _ _ _ _ next, _, f, x, m =>
    exists_congr fun r => and_congr Iff.rfl (and_congr Iff.rfl
      (exists_congr fun o => todo_comap next (fun b => ((f b.1.1, b.1.2), b.2)) ((x, r), o) m))
  | _, .draw _ _ _ _, _, _, _, _ => Iff.rfl
  | _, .send _ _ _ _ _ _, _, _, _, _ => Iff.rfl

theorem ok_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X), c.OK → (c.comap f).OK
  | _, .done _, _, _, _ => trivial
  | _, .ride _ _ _ _ _ _ _ next, _, f, h =>
    ⟨h.1, fun b m h1 h2 => h.2.1 ((f b.1.1, b.1.2), b.2) m h1 ((todo_comap next _ b m).1 h2),
      ok_comap next _ h.2.2⟩
  | _, .draw _ _ _ next, _, f, h =>
    ⟨fun x m hP => le_trans (cnt_mono fun β hβ => (todo_comap next _ (x, β) m).1 hβ)
      (h.1 (f x) m hP), ok_comap next _ h.2⟩
  | _, .send _ _ _ _ _ next, _, f, h =>
    ⟨fun x m hP s hL => le_trans (cnt_mono fun β hβ => (todo_comap next _ ((x, s), β) m).1 hβ)
      (h.1 (f x) m hP s hL), ok_comap next _ h.2⟩

theorem nums_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X),
    (c.comap f).nums = c.nums
  | _, .done _, _, _ => rfl
  | _, .ride Y _ _ _ _ _ _ next, _, _ =>
    congrArg ((1 :: (Y.fmt.map PFmt.n ++ [0])) ++ ·) (nums_comap next _)
  | _, .draw _ err _ next, _, _ => congrArg ([err] ++ ·) (nums_comap next _)
  | _, .send _ _ err _ _ next, _, _ => congrArg ([err] ++ ·) (nums_comap next _)

theorem sh_comap : ∀ {X : Type} (c : Ch E M X) {X' : Type} (f : X' → X), (c.comap f).sh = c.sh
  | _, .done _, _, _ => rfl
  | _, .ride Y n _ _ _ _ _ next, _, _ => congrArg (shapeRN Y n ++ ·) (sh_comap next _)
  | _, .draw D _ _ next, _, _ => congrArg ([drawRound D.D] ++ ·) (sh_comap next _)
  | _, .send n D _ _ _ next, _, _ =>
    congrArg ([Lay.sendRound E (Fin n) D.D] ++ ·) (sh_comap next _)

end Ch

/-! ### The letters of one sumcheck -/

/-- The letters of one sumcheck at statements X. -/
structure SumL (E : Type) [Field E] [Fintype E] (M X : Type) where
  T : PlainSc E
  ok : T.OK
  n : ℕ
  cl : X → (Fin n → E) → E × T.St
  msg : M → T.J → E
  L : X → (Fin n → E) → M → Prop

namespace SumL
variable {X : Type} (S : SumL E M X)

/-- The statements behind it. -/
abbrev Nx : Type := (X × (Fin S.n → E)) × S.T.our.par.Out

/-- All its output claims. -/
def Out (b : S.Nx) (m : M) : Prop := S.T.our.par.OutHolds b.2 (S.msg m)

/-- The stage, with what is owed at the chain's end as a parameter. -/
noncomputable def stage (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) : Ch E M X :=
  .ride S.T.our.par S.n S.T.fix S.cl S.msg S.L Ow next

/-- The list of its errors. -/
def nums : List ℕ := 1 :: (List.ofFn S.T.deg ++ [S.T.DY] ++ [0])

theorem stage_nums (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx) :
    (S.stage Ow next).nums = S.nums ++ next.nums := by
  show (1 :: (S.T.our.par.fmt.map PFmt.n ++ [0])) ++ next.nums = _
  rw [plain_degs]
  rfl

theorem stage_ok (Ow : S.Nx → M → Prop) (next : Ch E M S.Nx)
    (hO : ∀ b m, Ow b m → next.Todo b m → S.Out b m) (h : next.OK) : (S.stage Ow next).OK :=
  ⟨⟨plain_vars S.T S.ok, plain_deg S.T S.ok, plain_inj S.T⟩, hO, h⟩

/-- From a sumcheck of products. -/
def of3 (T : Sc3 E) (n : ℕ) (cl : X → (Fin n → E) → E × T.St) (msg : M → T.J → E)
    (L : X → (Fin n → E) → M → Prop) : SumL E M X := ⟨T.plain, sc3_ok T, n, cl, msg, L⟩

/-- From the sumcheck by degrees. -/
def ofD {s : ScdSize} (T : Scd E s) (n : ℕ) (cl : X → (Fin n → E) → E × T.St) (msg : M → T.J → E)
    (L : X → (Fin n → E) → M → Prop) : SumL E M X := ⟨T.plain, scd_ok T, n, cl, msg, L⟩

end SumL

/-! ### The eleven stages behind the score units -/

/-- One element of E. -/
abbrev drE (E : Type) [Field E] [Fintype E] : Dr := ⟨E⟩
/-- A point of nz coordinates. -/
abbrev drPt (E : Type) [Field E] [Fintype E] (nz : ℕ) : Dr := ⟨Fin nz → E⟩

/-- The letters of the eleven stages behind the score units. -/
structure Tail (E : Type) [Field E] [Fintype E] (M X : Type) where
  /-- the denominator times the output -/
  sE : SumL E M X
  /-- what is claimed before the draw for the value products -/
  pV : sE.Nx → M → Prop
  /-- the value product below the diagonal, and on it -/
  sVM : SumL E M (sE.Nx × E)
  sVD : SumL E M sVM.Nx
  /-- the point's coordinates; the bound on its bad draws; what is claimed before it -/
  nz : ℕ
  eZ : ℕ
  pZ : sVD.Nx → M → Prop
  /-- the pairs; what is claimed before their scalars; what is claimed of the scalars -/
  np : ℕ
  pF : sVD.Nx × (Fin nz → E) → M → Prop
  lF : sVD.Nx × (Fin nz → E) → (Fin np → E) → M → Prop
  /-- the score at the index; what of its output claims is owed at the end -/
  sF : SumL E M (((sVD.Nx × (Fin nz → E)) × (Fin np → E)) × E)
  owF : sF.Nx → M → Prop
  /-- what is claimed before the draw for the key at the index -/
  pD : sF.Nx → M → Prop
  sD : SumL E M (sF.Nx × E)
  /-- what is claimed before the draw for the bits -/
  pH : sD.Nx → M → Prop
  sH : SumL E M (sD.Nx × E)

namespace Tail
variable {X : Type} (T : Tail E M X)

/-- The stages from the draw for the bits on. -/
noncomputable def chH : Ch E M T.sD.Nx :=
  .draw (drE E) (T.np - 1) T.pH (T.sH.stage T.sH.Out (.done _))
/-- From the draw for the key at the index on. -/
noncomputable def chD : Ch E M T.sF.Nx :=
  .draw (drE E) (T.np - 1) T.pD (T.sD.stage T.sD.Out T.chH)
/-- From the pairs' scalars on. -/
noncomputable def chF : Ch E M (T.sVD.Nx × (Fin T.nz → E)) :=
  .send T.np (drE E) (T.np - 1) T.pF T.lF (T.sF.stage T.owF T.chD)
/-- From the draw of the point on. -/
noncomputable def chZ : Ch E M T.sVD.Nx := .draw (drPt E T.nz) T.eZ T.pZ T.chF
/-- From the draw for the value products on. -/
noncomputable def chV : Ch E M T.sE.Nx :=
  .draw (drE E) 1 T.pV (T.sVM.stage T.sVM.Out (T.sVD.stage T.sVD.Out T.chZ))
/-- The eleven stages. -/
noncomputable def ch : Ch E M X := T.sE.stage T.sE.Out T.chV

/-- The laws on the letters. -/
structure Laws : Prop where
  cV : ∀ x m, ¬ T.pV x m →
    cnt (fun β : E => (T.sVM.stage T.sVM.Out (T.sVD.stage T.sVD.Out T.chZ)).Todo (x, β) m) ≤ 1
  cZ : ∀ x m, ¬ T.pZ x m → cnt (fun p : Fin T.nz → E => T.pF (x, p) m) ≤ T.eZ
  cF : ∀ x m, ¬ T.pF x m → ∀ s, T.lF x s m →
    cnt (fun β : E => (T.sF.stage T.owF T.chD).Todo ((x, s), β) m) ≤ T.np - 1
  oF : ∀ b m, T.owF b m → T.pD b m → T.sF.Out b m
  cD : ∀ x m, ¬ T.pD x m →
    cnt (fun β : E => (T.sD.stage T.sD.Out T.chH).Todo (x, β) m) ≤ T.np - 1
  cH : ∀ x m, ¬ T.pH x m →
    cnt (fun β : E => (T.sH.stage T.sH.Out (.done _)).Todo (x, β) m) ≤ T.np - 1

theorem ch_ok (h : T.Laws) : T.ch.OK :=
  T.sE.stage_ok _ _ (fun _ _ h1 _ => h1)
    ⟨h.cV, T.sVM.stage_ok _ _ (fun _ _ h1 _ => h1) (T.sVD.stage_ok _ _ (fun _ _ h1 _ => h1)
      ⟨h.cZ, h.cF, T.sF.stage_ok _ _ h.oF
        ⟨h.cD, T.sD.stage_ok _ _ (fun _ _ h1 _ => h1)
          ⟨h.cH, T.sH.stage_ok _ _ (fun _ _ h1 _ => h1) trivial⟩⟩⟩)⟩

/-- The list of the eleven stages' errors. -/
def nums : List ℕ :=
  T.sE.nums ++ ([1] ++ (T.sVM.nums ++ (T.sVD.nums ++ ([T.eZ] ++ ([T.np - 1] ++ (T.sF.nums ++
    ([T.np - 1] ++ (T.sD.nums ++ ([T.np - 1] ++ (T.sH.nums ++ []))))))))))

theorem ch_nums : T.ch.nums = T.nums :=
  (T.sE.stage_nums _ _).trans <| congrArg (T.sE.nums ++ ·) <| congrArg ([1] ++ ·) <|
  (T.sVM.stage_nums _ _).trans <| congrArg (T.sVM.nums ++ ·) <|
  (T.sVD.stage_nums _ _).trans <| congrArg (T.sVD.nums ++ ·) <| congrArg ([T.eZ] ++ ·) <|
  congrArg ([T.np - 1] ++ ·) <| (T.sF.stage_nums _ _).trans <| congrArg (T.sF.nums ++ ·) <|
  congrArg ([T.np - 1] ++ ·) <| (T.sD.stage_nums _ _).trans <| congrArg (T.sD.nums ++ ·) <|
  congrArg ([T.np - 1] ++ ·) <| T.sH.stage_nums _ _

end Tail

/-! ### The whole -/

/-- The first statement, and the further scalars of the score units so far, in order. -/
abbrev Seen (E X : Type) : Type := X × List (List E)

/-- The score units, then a chain. Each reads the first statement and the further scalars of the
units before it. -/
noncomputable def unitsCh {X : Type} : List (SumL E M (Seen E X)) → {X' : Type} →
    (X' → Seen E X) → Ch E M (Seen E X) → Ch E M X'
  | [], _, pr, tail => tail.comap pr
  | u :: us, _, pr, tail =>
    .ride u.T.our.par u.n u.T.fix (fun x r => u.cl (pr x) r) u.msg (fun x r m => u.L (pr x) r m)
      (fun b m => u.T.our.par.OutHolds b.2 (u.msg m))
      (unitsCh us (fun b => ((pr b.1.1).1, (pr b.1.1).2 ++ [List.ofFn b.1.2])) tail)

theorem unitsCh_ok {X : Type} (tail : Ch E M (Seen E X)) (h : tail.OK) :
    ∀ (us : List (SumL E M (Seen E X))) {X' : Type} (pr : X' → Seen E X),
      (unitsCh us pr tail).OK
  | [], _, pr => Ch.ok_comap tail pr h
  | u :: us, _, _ =>
    ⟨⟨plain_vars u.T u.ok, plain_deg u.T u.ok, plain_inj u.T⟩, fun _ _ h1 _ => h1,
      unitsCh_ok tail h us _⟩

theorem unitsCh_nums {X : Type} (tail : Ch E M (Seen E X)) :
    ∀ (us : List (SumL E M (Seen E X))) {X' : Type} (pr : X' → Seen E X),
      (unitsCh us pr tail).nums = (us.map SumL.nums).flatten ++ tail.nums
  | [], _, pr => Ch.nums_comap tail pr
  | u :: us, _, pr => by
    show (1 :: (u.T.our.par.fmt.map PFmt.n ++ [0])) ++ (unitsCh us _ tail).nums = _
    rw [plain_degs, unitsCh_nums tail us, List.map_cons, List.flatten_cons]
    exact (List.append_assoc u.nums _ _).symm

/-- The letters of an attention sub-proof's own rounds. -/
structure AttOwn (E : Type) [Field E] [Fintype E] (M X : Type) where
  units : List (SumL E M (Seen E X))
  tail : Tail E M (Seen E X)

namespace AttOwn
variable {X : Type} (A : AttOwn E M X)

/-- THE chain. -/
noncomputable def ch : Ch E M X := unitsCh A.units (fun x => (x, [])) A.tail.ch

end AttOwn

theorem attOwn_ok {X : Type} (A : AttOwn E M X) (h : A.tail.Laws) : A.ch.OK :=
  unitsCh_ok A.tail.ch (A.tail.ch_ok h) A.units _

/-- Knowledge soundness of an attention sub-proof's own rounds. This is said under the hypotheses
that stand in the statement itself, which this comment does not list; it is no claim that they hold.
-/
theorem attOwn_knowAt {X Kc X0 Wp : Type} (A : AttOwn E M X) (h : A.tail.Laws) (Ex : ExtSpec)
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop) :
    KnowAt (A.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ A.ch.Todo x m)
      (jt A0 (fun e => pr (A.ch.back e)) (A.ch.Last Dn)) (fun _ _ _ wp => wp) (A.ch.eps Ex) :=
  Ch.knowAt Ex A0 A.ch pr Dn (attOwn_ok A h)

/-- The list of its errors. -/
theorem attOwn_nums {X : Type} (A : AttOwn E M X) (Ex : ExtSpec) :
    errList (A.ch.eps Ex) = (A.units.map SumL.nums).flatten ++ A.tail.nums := by
  rw [Ch.errList_eps]
  show (unitsCh A.units _ A.tail.ch).nums = _
  rw [unitsCh_nums, Tail.ch_nums]

/-- The errors of a sumcheck of products. -/
theorem nums_of3 {X : Type} (T : Sc3 E) (n : ℕ) (cl : X → (Fin n → E) → E × T.St)
    (msg : M → T.J → E) (L : X → (Fin n → E) → M → Prop) :
    (SumL.of3 T n cl msg L).nums = 1 :: (List.replicate T.nv 3 ++ [2] ++ [0]) := by
  show 1 :: (List.ofFn (fun _ : Fin T.nv => 3) ++ [2] ++ [0]) = _
  rw [List.ofFn_const]

/-! ### A law from a batch by powers -/

/-- If n gaps being 0 and Q give the claim before a draw of one element, and the claim behind it
gives that the gaps' batch by the element's powers is 0 and Q, then at most n - 1 draws are bad. -/
theorem law_pow {X : Type} (n : ℕ) (g : X → M → Fin n → E) (Q P : X → M → Prop)
    (T : X × E → M → Prop) (hP : ∀ x m, (∀ b, g x m b = 0) → Q x m → P x m)
    (hT : ∀ x β m, T (x, β) m → ∑ b : Fin n, β ^ (b : ℕ) * g x m b = 0 ∧ Q x m) (x : X) (m : M)
    (h : ¬ P x m) : cnt (fun β : E => T (x, β) m) ≤ n - 1 := by
  refine le_trans (cnt_mono fun β hβ => ?_) (cnt_badPow (g x m))
  obtain ⟨h1, h2⟩ := hT x β m hβ
  exact ⟨fun h0 => h (hP x m (fun b => congrFun h0 b) h2), h1⟩

end Cb.Pv.Att
