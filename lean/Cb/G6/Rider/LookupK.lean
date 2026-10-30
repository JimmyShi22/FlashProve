-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/LookupK.lean: the lookup that is assembled as the programs run it, over a sumcheck that
is a letter: which of its rounds draw the coordinates of the key side's last point, the read-off,
and that it hands its caller's state on.

Definitions, statements and proofs. No protocol of its own: no term of a reduction is added or
changed.

The term is `A.baseKS SK` (Cb/Pv/Lookup/Know/AsmK.lean) for a record `A : LkAsmH` and a letter
`SK : PscLtK`: the head, the planes' point, the keys' tree, the table's forest, the closing, the
test on bits, the read-out. Its output statement holds a claim on the keys whose point `pt` has
v' + 1 coordinates.

Main names:
  `Carries.seqU`: both blocks of a row bind. `draw_carries`: a draw from the whole field.
  `LetterCar SK`: what is asked of the letter. A letter lays no law on what its verifiers put out,
    so for a free letter there is no read-off. Asked: both forms hand the sumcheck's state on
    (`st`, `stC`); the form with the round of values has the bundle `Carries`
    (Cb/G6/Rider/Carrier.lean) for any placing of names on different rounds of variables of degree
    at least 1, at the letter's own counts (`β`, `car`).
  `gam_sg`: a level of a product tree binds its variables in the order `D.sg l`
    (Cb/Ld/LdLkpTreeP.lean): coordinate i of the point at which the level's sumcheck ended is the
    challenge of the round of variable number (sg l)⁻¹ i. `plS`: that number.
  `levKB`, `levK_carries`: the bundle of a level over the letter, for every order.
  `chnKB`, `chnK_carries`, `baseKS_carries`: the bundle of the whole term. `chnKB` writes out,
    along the term's own make, which round draws which coordinate: the rounds of the variables and
    the line of the last key level, and no other round (by its definition; `chnKB_vars`: the list of
    the names bound is that level's). The read-off: whatever the verifier outputs, `pt (v' - k)` is
    the challenge bound to k. The rider's list lies below the term's own list of counts.
  `baseKS_passes`: whatever the verifier outputs, its first component is the input statement.
  `letterCar₀`, `baseK₀_carries`, `baseK₀_passes`: at the named short sumcheck `V₀`, `V₀C`
    (Cb/G6/Pick.lean) no premise is left (from Cb/G6/Rider/Short.lean).

Limits: nothing on knowledge soundness (the rule that uses the bundle is `knowAt_cubes`,
Cb/G6/Rider/KnowAt.lean); nothing on whether what follows the lookup keeps the point; nothing on an
honest prover. Nothing here is computed by a verifier: the `Binds` and the readers serve the
analysis alone.

Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Lookup.Know.AsmKV
import Cb.G6.Rider.Short

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole

/-! ## 1. Two rules more for the bundle -/

namespace Carries
variable {E X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec}

/-- Both blocks of a row bind: the first the coordinates in T₁, the second those in T₂. Asked: the
second block binds no name of T₁ (hd) and hands the first's coordinates on (hp). -/
theorem seqU {R₁ : IOR X₁ E₁ X₂ E₂} {β₁ : Binds ℕ E R₁.shape} {ε₁ : Err R₁.shape} {T₁ : ℕ → Prop}
    {r₂ : X₂ → ℕ → E} (C₁ : Carries R₁ β₁ ε₁ T₁ r₂) {R₂ : IOR X₂ E₂ X₃ E₃}
    {β₂ : Binds ℕ E R₂.shape} {ε₂ : Err R₂.shape} {T₂ : ℕ → Prop} {r₃ : X₃ → ℕ → E}
    (C₂ : Carries R₂ β₂ ε₂ T₂ r₃) (hd : ∀ k, T₁ k → k ∉ β₂.vars)
    (hp : ∀ x y τ x', R₂.out x y τ = some x' → ∀ k, T₁ k → r₃ x' k = r₂ x k) :
    Carries (R₁.seq R₂) (Binds.app (s := R₁.shape) (t := R₂.shape) β₁ β₂) (Err.app ε₁ ε₂)
      (fun k => T₁ k ∨ T₂ k) r₃ where
  inj := Binds.Inj.app (s := R₁.shape) (t := R₂.shape) C₁.inj C₂.inj
  mem := fun k hk => by
    show k ∈ Binds.vars (s := R₁.shape ++ R₂.shape) (Binds.app β₁ β₂)
    rw [Binds.vars_app]
    exact hk.elim (fun h => List.mem_append_left _ (C₁.mem k h))
      fun h => List.mem_append_right _ (C₂.mem k h)
  rd := fun x y τ x' z h k hk => by
    obtain ⟨x₂, hx, hx'⟩ := Option.bind_eq_some_iff.1 ((IOR.seq_out R₁ R₂ x y τ).symm.trans h)
    show Binds.pt (s := R₁.shape ++ R₂.shape) (Binds.app β₁ β₂)
      (Tr.rho (s := R₁.shape ++ R₂.shape) τ) z k = r₃ x' k
    rw [Binds.pt_app, ← Tr.rho_fst, ← Tr.rho_snd]
    rcases hk with h1 | h2
    · rw [Binds.pt_of_notMem _ _ _ (hd k h1), C₁.rd x y _ x₂ z hx k h1, hp _ _ _ _ hx' k h1]
    · exact C₂.rd x₂ _ _ x' _ hx' k h2
  le := err_app_le _ (s := R₁.shape) (t := R₂.shape) _ _ C₁.le C₂.le

end Carries

section Draw
variable {E : Type} [Fintype E] [Nonempty E]

/-- A round that draws from all of E binds the name k. -/
def drawB (k : ℕ) : Binds ℕ E [IOR.drawRound E] := (some (k, fun c : E => c), ())

/-- A draw from all of E that the new statement holds at coordinate k, at any count e ≥ 1. -/
theorem draw_carries {X X' : Type} (nx : X → E → X') (Ex : ExtSpec) (k e : ℕ) (he : 1 ≤ e)
    (r : X' → ℕ → E) (hr : ∀ x c, r (nx x c) k = c) :
    Carries (IOR.draw E nx Ex) (drawB k) ((e, ()) : ℕ × Unit) (fun c => c = k) r where
  inj := ⟨fun _ _ h => h, trivial⟩
  mem := fun c hc => by
    rw [hc]
    exact List.mem_singleton.2 rfl
  rd := fun x y τ x' z h c hc => by
    obtain rfl := Option.some.inj (show some (nx x (IOR.drawn τ)) = some x' from h)
    rw [hc, hr]
    exact Function.update_self _ _ _
  le := ⟨he, trivial⟩

end Draw

variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-! ## 2. What is asked of the letter -/

/-- What the read-off asks of a letter. st, stC: both forms hand the sumcheck's state on. β, car:
for any placing pl of the names t < g on different rounds of variables of degree at least 1, the
form with the round of values has the bundle, at the letter's own counts: name t is coordinate pl t
of the point in its output statement. -/
structure LetterCar (SK : PscLtK E Ex) where
  st  : ∀ Y : PscPar E, (SK.full Y).R.Passes Prod.snd PscPar.Out.st
  stC : ∀ Y : PscPar E, (SK.core Y).R.Passes Prod.snd PscPar.Mid.st
  β   : (Y : PscPar E) → (g : ℕ) → (pl : ℕ → ℕ) → Binds ℕ E (SK.full Y).R.shape
  car : ∀ (Y : PscPar E) (g : ℕ) (pl : ℕ → ℕ), Y.ValInj →
    (∀ t < g, ∀ t' < g, pl t = pl t' → t = t') → (∀ t < g, pl t < Y.fmt.length) →
    (∀ t < g, ∀ φ, Y.fmt[pl t]? = some φ → 1 ≤ φ.n) →
    Carries (SK.full Y).R (β Y g pl) (SK.full Y).e (fun t => t < g)
      fun o t => ptAt Y.fmt o.pt (pl t)

/-! ## 3. A level of a product tree, for every order of its rounds -/

omit [Fintype E] in
/-- The library's reader of a point on a cube gives the coordinates in the order of the rounds. -/
private theorem hFnOf_iniK (f : PFmt E) : ∀ (k : ℕ) (d : PDats (List.replicate k f)) (fd : PFmt E)
    (e : PDat E fd) (γ : PPt (List.replicate k f ++ [fd])) (i : Fin k),
    hFnOf f k d (hInit (List.replicate k f) d fd e
      (pH (List.replicate k f ++ [fd]) (PDats.snoc (List.replicate k f) d fd e) γ)) i =
      ptAt (List.replicate k f ++ [fd]) γ i
  | 0, _, _, _, _, i => i.elim0
  | k + 1, d, fd, e, γ, i => by
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · exact hFnOf_iniK f k d.2 fd e γ.2 i

/-- Coordinate i of the point at which a level's sumcheck ended (the library's reader gam) is the
entry of the output statement's point at the variable number (sg l)⁻¹ i: it is drawn in that
variable's round. -/
theorem gam_sg (D : TreeP E) : ∀ (l : ℕ) (o : (D.lv l).T.par.Out) (i : Fin (D.g + l)),
    (D.lv l).gam o i = ptAt (D.lv l).T.par.fmt o.pt ((D.sg l).symm i)
  | 0, o, i => hFnOf_iniK (pfCube E 2) (D.g + 0) _ _ _ o.pt ((D.sg 0).symm i)
  | l + 1, o, i => hFnOf_iniK (pfCube E 2) (D.g + l + 1) _ _ _ o.pt ((D.sg (l + 1)).symm i)

private theorem fmt_lvK (D : TreeP E) : ∀ l, (D.lv l).T.fmt = List.replicate (D.g + l) (pfCube E 2)
  | 0 => rfl
  | _ + 1 => rfl

private theorem dy_lvK (D : TreeP E) : ∀ l, (D.lv l).T.DY = 2
  | 0 => rfl
  | _ + 1 => rfl

private theorem len_parK (D : TreeP E) (l : ℕ) : (D.lv l).T.par.fmt.length = D.g + l + 1 := by
  show ((D.lv l).T.fmt ++ [pDummy E (D.lv l).T.DY]).length = _
  rw [fmt_lvK]
  simp

private theorem deg_parK (D : TreeP E) (l : ℕ) : ∀ φ ∈ (D.lv l).T.par.fmt, 1 ≤ φ.n := by
  intro φ hφ
  have hφ' : φ ∈ (D.lv l).T.fmt ++ [pDummy E (D.lv l).T.DY] := hφ
  rw [fmt_lvK, dy_lvK] at hφ'
  rcases List.mem_append.1 hφ' with h | h
  · rw [List.eq_of_mem_replicate h]
    exact Nat.le_succ 1
  · rw [List.mem_singleton.1 h]
    exact Nat.le_succ 1

/-- The number of the variable that is coordinate t of level l. -/
def plS (D : TreeP E) (l t : ℕ) : ℕ := if h : t < D.g + l then ((D.sg l).symm ⟨t, h⟩ : ℕ) else t

theorem plS_of (D : TreeP E) (l : ℕ) {t : ℕ} (h : t < D.g + l) :
    plS D l t = ((D.sg l).symm ⟨t, h⟩ : ℕ) := dif_pos h

theorem plS_inj (D : TreeP E) (l : ℕ) : ∀ t < D.g + l, ∀ t' < D.g + l,
    plS D l t = plS D l t' → t = t' := by
  intro t ht t' ht' e
  rw [plS_of D l ht, plS_of D l ht'] at e
  exact congrArg Fin.val ((D.sg l).symm.injective (Fin.ext e))

theorem plS_lt (D : TreeP E) (l : ℕ) : ∀ t < D.g + l, plS D l t < D.g + l := by
  intro t ht
  rw [plS_of D l ht]
  exact ((D.sg l).symm ⟨t, ht⟩).isLt

section Level
variable {SK : PscLtK E Ex} (LC : LetterCar SK) (D : TreeP E) (l : ℕ)

/-- The Binds of a whole level over the letter (the sumcheck, then the line): in the sumcheck the
letter's own β for the placing plS, which lays the name k < D.g + l on the variable number (sg l)⁻¹
k (at letterCar₀ that variable's round binds k); the line's round binds D.g + l. -/
noncomputable def levKB : Binds ℕ E (D.levK SK l).R.shape :=
  Binds.app (s := (SK.full (D.lv l).T.par).R.shape) (t := [IOR.drawRound E])
    (LC.β (D.lv l).T.par (D.g + l) (plS D l)) (drawB (D.g + l))

/-- The level's bundle, for every order of its rounds: each coordinate k ≤ D.g + l of the point that
the level hands down (pnt of level l + 1) is the challenge of one round; 1 against the letter's own
count at a variable, 1 against 1 at the line. -/
theorem levK_carries :
    Carries (D.levK SK l).R (levKB LC D l) (D.levK SK l).e (fun k => k ≤ D.g + l)
      fun x' => nat ((D.lv (l + 1)).pnt x'.2) := by
  have C₁ := LC.car (D.lv l).T.par (D.g + l) (plS D l)
    ((psc_our_ok E (D.lv l).T).2 (ldLkpP_ok E D l).2.1) (plS_inj D l)
    (fun t ht => by rw [len_parK]; exact Nat.lt_succ_of_lt (plS_lt D l t ht))
    (fun t _ φ hφ => deg_parK D l φ (List.mem_of_getElem? hφ))
  have C₂ : Carries (E := E) (D.lineK Ex l).R (drawB (E := E) (D.g + l)) (D.lineK Ex l).e
      (fun c => c = D.g + l)
      fun x' : E × (D.lv (l + 1)).T.St => nat ((D.lv (l + 1)).pnt x'.2) :=
    draw_carries (E := E) (D.cube l).toLine.toIn.nxX Ex (D.g + l) 1 (Nat.le_refl 1) _ fun o c => by
      show nat (Fin.snoc ((D.lv l).gam o) c : Fin (D.g + l + 1) → E) (D.g + l) = c
      rw [show nat (Fin.snoc ((D.lv l).gam o) c : Fin (D.g + l + 1) → E) (D.g + l) =
        (Fin.snoc ((D.lv l).gam o) c : Fin (D.g + l + 1) → E) ⟨D.g + l, Nat.lt_succ_self _⟩
        from dif_pos (Nat.lt_succ_self _)]
      exact Fin.snoc_last (α := fun _ => E) c ((D.lv l).gam o)
  refine (C₁.seqU C₂ (fun k hk hm => absurd (List.mem_singleton.1 hm) (Nat.ne_of_lt hk)) ?_).mono
    fun k hk => (Nat.lt_or_eq_of_le hk)
  intro o y τ x' ho k hk
  obtain ⟨c, rfl⟩ : ∃ c : E, (D.cube l).toLine.toIn.nxX o c = x' :=
    ⟨IOR.drawn τ, Option.some.inj ho⟩
  show nat (Fin.snoc ((D.lv l).gam o) c : Fin (D.g + l + 1) → E) k = _
  rw [show nat (Fin.snoc ((D.lv l).gam o) c : Fin (D.g + l + 1) → E) k =
    (Fin.snoc ((D.lv l).gam o) c : Fin (D.g + l + 1) → E) ⟨k, Nat.lt_succ_of_lt hk⟩
    from dif_pos (Nat.lt_succ_of_lt hk), plS_of D l hk, ← gam_sg D l o ⟨k, hk⟩]
  exact Fin.snoc_castSucc (α := fun _ => E) c ((D.lv l).gam o) ⟨k, hk⟩

include LC in
/-- A level over the letter hands on the root state of its tree. -/
theorem pass_levK :
    (D.levK SK l).R.Passes (fun x => D.root l x.2) fun x => D.root (l + 1) x.2 :=
  (passes_map (LC.st (D.lv l).T.par) (D.root l)).seq (IOR.Passes.draw _ _ Ex _ _ fun _ _ => rfl)

end Level

/-! ## 4. A row of blocks: the last one binds -/

section Chain
omit [Field E] [Fintype E]
variable (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex)

/-- The blocks b 0, .., b n in a row: the last one binds by bd, the others bind nothing. -/
noncomputable def chainLastK : (n : ℕ) → Binds ℕ E (b n).R.shape →
    Binds ℕ E (BkK.chain X b n).R.shape
  | 0, bd => bd
  | n + 1, bd =>
    Binds.app (s := (BkK.chain X b n).R.shape) (t := (b (n + 1)).R.shape) (idle _) bd

theorem chainLastK_carries : ∀ (n : ℕ) (bd : Binds ℕ E (b n).R.shape) (T : ℕ → Prop)
    (r : X (n + 1) → ℕ → E), Carries (b n).R bd (b n).e T r →
    Carries (BkK.chain X b n).R (chainLastK X b n bd) (BkK.chain X b n).e T r
  | 0, _, _, _, h => h
  | n + 1, _, _, _, h => Carries.seqR (BkK.chain X b n).R (BkK.chain X b n).e h

theorem chainLastK_vars : ∀ (n : ℕ) (bd : Binds ℕ E (b n).R.shape),
    (chainLastK X b n bd).vars = bd.vars
  | 0, _ => rfl
  | n + 1, bd => by
    refine (Binds.vars_app (s := (BkK.chain X b n).R.shape) (t := (b (n + 1)).R.shape)
      (idle _) bd).trans ?_
    rw [idle_vars]
    rfl

/-- A row of blocks hands on what each of them hands on. -/
theorem passes_chainK {Rc : Type} (r : ∀ l, X l → Rc)
    (h : ∀ l, (b l).R.Passes (r l) (r (l + 1))) :
    ∀ n, (BkK.chain X b n).R.Passes (r 0) (r (n + 1))
  | 0 => h 0
  | n + 1 => (passes_chainK r h n).seq (h (n + 1))

end Chain

/-! ## 5. The assembled lookup -/

section Link
variable {SK : PscLtK E Ex} (LC : LetterCar SK) (A : LkAsmH E)

/-- The keys' tree of the assembled lookup. -/
noncomputable abbrev DKh : TreeP E := (A.IK.setV (A.v' + 1)).DK

/-- The reader behind the keys' side: the point that the last key level hands down, in pnt's
numbering. -/
noncomputable def rdKh (x : A.X4) : ℕ → E := nat (((DKh A).lv (A.v' + 1)).pnt x.2)

/-- The keys' side: its last level binds; the levels before it bind nothing. -/
noncomputable def keyKB : Binds ℕ E (segKK A.IK A.v' (fun x => A.tK (A.oR x)) SK).R.shape :=
  chainLastK (fun l => E × ((DKh A).lv l).T.St) ((DKh A).levK SK) A.v' (levKB LC (DKh A) A.v')

theorem keyK_carries :
    Carries (segKK A.IK A.v' (fun x => A.tK (A.oR x)) SK).R (keyKB LC A)
      (segKK A.IK A.v' (fun x => A.tK (A.oR x)) SK).e (fun k => k ≤ A.v') (rdKh A) :=
  Carries.pre (R := ((DKh A).treeK SK A.v').R)
    (chainLastK_carries _ _ A.v' _ _ _
      ((levK_carries LC (DKh A) A.v').mono fun k hk => by
        show k ≤ 0 + A.v'
        rw [Nat.zero_add]
        exact hk)) _ _

/-- The keys' side, then l levels of the table's forest, which bind nothing. -/
noncomputable def forestKB : (l : ℕ) → Binds ℕ E (A.forestK SK l).R.shape
  | 0 => keyKB LC A
  | l + 1 =>
    Binds.app (s := (A.forestK SK l).R.shape) (t := (A.D.levK SK l).R.shape) (forestKB l) (idle _)

theorem forestK_carries : ∀ l, Carries (A.forestK SK l).R (forestKB LC A l) (A.forestK SK l).e
    (fun k => k ≤ A.v') (fun x => rdKh A (A.D.root l x.2).1)
  | 0 => (keyK_carries LC A).post _ _ fun x x' e k _ => by
      obtain rfl := Option.some.inj e
      rfl
  | l + 1 => (forestK_carries l).seqL (A.D.levK SK l).R (A.D.levK SK l).e
      (passes_map (pass_levK LC A.D l) fun s => rdKh A s.1)

/-- The Binds of the whole chain, written out along its own make: head and planes' point bind
nothing; the keys' last level binds; the table's levels, the closing and the test on bits bind
nothing. -/
noncomputable def chnKB : Binds ℕ E (A.chnK SK).R.shape :=
  Binds.app
    (s := ((((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d)).seq (A.endK SK)).R.shape)
    (t := (A.bitK SK).R.shape)
    (Binds.app
      (s := (((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d)).R.shape)
      (t := (A.endK SK).R.shape)
      (Binds.app (s := ((A.H.headK SK).seq (A.rootK Ex)).R.shape)
        (t := (A.forestK SK A.d).R.shape) (idle _) (forestKB LC A A.d))
      (idle _))
    (idle _)

include LC in
/-- The test on bits over the letter hands on whatever is read off its state. -/
theorem pass_bitK {Rc : Type} (f : A.XE → Rc) :
    (A.bitK SK).R.Passes f fun o : A.XB => f o.st.1 :=
  (IOR.Passes.draw _ _ Ex f (fun x : E × A.Bt.zc.next.St => f x.2.1) fun _ _ => rfl).seq
    (passes_map (LC.st A.Bt.zc.next.par) fun s : A.Bt.zc.next.St => f s.1)

/-- The bundle of the chain, one rule for each stage: the point is read back out of the nested
states. -/
theorem chnK_carries :
    Carries (A.chnK SK).R (chnKB LC A) (A.chnK SK).e (fun k => k ≤ A.v')
      (fun o => rdKh A (A.oldT o)) :=
  ((Carries.seqR ((A.H.headK SK).seq (A.rootK Ex)).R ((A.H.headK SK).seq (A.rootK Ex)).e
        (forestK_carries LC A A.d)).seqL
      (A.endK SK).R (A.endK SK).e
      (passes_map (LC.stC A.En.par) fun s => rdKh A (A.D.root A.d s).1)).seqL
    (A.bitK SK).R (A.bitK SK).e
    (pass_bitK LC A fun z : A.XE => rdKh A (A.D.root A.d z.st).1)

/-- The claim's point is the handed-down point read backwards: coordinate v' - k of pt is coordinate
k of pnt. -/
theorem clK_rd (x : A.X4) {k : ℕ} (hk : k ≤ A.v') : (A.clK x).pt (A.v' - k) = rdKh A x k := by
  have h1 : A.v' - k < 0 + (A.v' + 1) := by omega
  have h2 : k < 0 + (A.v' + 1) := by omega
  have e1 : (A.clK x).pt (A.v' - k) =
      ((DKh A).lv (A.v' + 1)).pnt x.2 (Fin.rev ⟨A.v' - k, h1⟩) := dif_pos h1
  have e2 : rdKh A x k = ((DKh A).lv (A.v' + 1)).pnt x.2 ⟨k, h2⟩ := dif_pos h2
  rw [e1, e2]
  congr 1
  apply Fin.ext
  rw [Fin.val_rev]
  show 0 + (A.v' + 1) - (A.v' - k + 1) = k
  omega

/-- The lookup's bundle: the reader is the output statement's own point pt, read backwards: the name
k stands at pt (v' - k). So pt 0 is the line's challenge of the last key level, and pt (v' - k), k <
v', is the challenge of that level's variable number (oK v')⁻¹ k. -/
theorem baseKS_carries :
    Carries (A.baseKS SK).R (chnKB LC A) (A.baseKS SK).e (fun k => k ≤ A.v')
      (fun b k => b.2.1.pt (A.v' - k)) :=
  (chnK_carries LC A).post _ _ fun o b e k hk => by
    obtain rfl := Option.some.inj e
    exact clK_rd A (A.oldT o) hk

/-! ### which names are bound -/

theorem forestKB_vars : ∀ l, (forestKB LC A l).vars = (levKB LC (DKh A) A.v').vars
  | 0 => chainLastK_vars _ _ A.v' _
  | l + 1 => by
    refine (Binds.vars_app (s := (A.forestK SK l).R.shape) (t := (A.D.levK SK l).R.shape)
      (forestKB LC A l) (idle _)).trans ?_
    rw [idle_vars, List.append_nil]
    exact forestKB_vars l

/-- The names that the chain's rounds bind are those that the last key level's rounds bind (two
lists of names are equal). That no other round binds is chnKB's own definition. -/
theorem chnKB_vars : (chnKB LC A).vars = (levKB LC (DKh A) A.v').vars := by
  refine (Binds.vars_app
    (s := ((((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d)).seq (A.endK SK)).R.shape)
    (t := (A.bitK SK).R.shape) _ (idle _)).trans ?_
  rw [idle_vars, List.append_nil]
  refine (Binds.vars_app
    (s := (((A.H.headK SK).seq (A.rootK Ex)).seq (A.forestK SK A.d)).R.shape)
    (t := (A.endK SK).R.shape) _ (idle _)).trans ?_
  rw [idle_vars, List.append_nil]
  refine (Binds.vars_app (s := ((A.H.headK SK).seq (A.rootK Ex)).R.shape)
    (t := (A.forestK SK A.d).R.shape) (idle _) (forestKB LC A A.d)).trans ?_
  rw [idle_vars, List.nil_append]
  exact forestKB_vars LC A A.d

end Link

/-! ## 6. The caller's state is handed on -/

section Pass
variable {SK : PscLtK E Ex} (LC : LetterCar SK)
include LC

theorem tieK_passes (D : TieF E) (n : ℕ) :
    (D.tieK SK n).R.Passes (fun x => (D.lv 0).base x.2) fun x => (D.lv (n + 1)).base x.2 :=
  passes_chainK (fun l => E × (D.lv l).T.St) (D.stepK SK) (fun l x => (D.lv l).base x.2)
    (fun l => (passes_map (LC.st (D.lv l).T.par) (D.lv l).base).post _ _ fun o x' e => by
      obtain rfl := Option.some.inj e
      rfl) n

theorem headK_passes (H : LkHeadF E) :
    (H.headK SK).R.Passes id fun x => ((H.tie.lv (H.n + 1)).base x.2).1 :=
  (IOR.Passes.draw E Prod.mk Ex id Prod.fst fun _ _ => rfl).seq
    ((passes_map (tieK_passes LC H.tie H.n) Prod.fst).pre _ _ fun x x' e => by
      obtain rfl := Option.some.inj e
      rfl)

theorem treeK_passes (D : TreeP E) (n : ℕ) :
    (D.treeK SK n).R.Passes (fun x => D.root 0 x.2) fun x => D.root (n + 1) x.2 :=
  passes_chainK (fun l => E × (D.lv l).T.St) (D.levK SK) (fun l x => D.root l x.2)
    (fun l => pass_levK LC D l) n

theorem segKK_passes (I : LkInst E) (v' : ℕ) (tK : I.X → E) :
    (segKK I v' tK SK).R.Passes id (oldK I v') :=
  (passes_map (treeK_passes LC (I.setV (v' + 1)).DK v') Prod.fst).pre _ _ fun x x' e => by
    obtain rfl := Option.some.inj e
    rfl

variable (A : LkAsmH E)

theorem forestK_passes : ∀ l, (A.forestK SK l).R.Passes id fun x => A.o4 (A.D.root l x.2).1
  | 0 => (segKK_passes LC A.IK A.v' fun x => A.tK (A.oR x)).post _ _ fun x x' e => by
      obtain rfl := Option.some.inj e
      rfl
  | l + 1 => (forestK_passes l).seq (passes_map (pass_levK LC A.D l) fun s => A.o4 s.1)

theorem chnK_passes :
    (A.chnK SK).R.Passes id fun o => (A.b2 (A.oR (A.o4 (A.oldT o)))).1 :=
  (((((headK_passes LC A.H).seq
          (IOR.Passes.draw _ _ Ex (fun x : A.X2 => (A.b2 x).1)
            (fun x : A.XR => (A.b2 (A.oR x)).1) fun _ _ => rfl)).seq
        (passes_map (forestK_passes LC A A.d) fun x => (A.b2 (A.oR x)).1)).seq
      (passes_map (LC.stC A.En.par) fun s => (A.b2 (A.oR (A.o4 (A.D.root A.d s).1))).1)).seq
    (pass_bitK LC A fun z : A.XE => (A.b2 (A.oR (A.o4 (A.D.root A.d z.st).1))).1))

/-- The whole lookup hands its caller's state on. -/
theorem baseKS_passes : (A.baseKS SK).R.Passes id Prod.fst :=
  (chnK_passes LC A).post _ _ fun o b e => by
    obtain rfl := Option.some.inj e
    rfl

end Pass

/-! ## 7. The letter at the named short sumcheck -/

/-- The named short sumcheck has what is asked of a letter. -/
noncomputable def letterCar₀ (E : Type) [Field E] [Fintype E] (Ex : ExtSpec) :
    LetterCar (PscLtK.ofShort (E := E) V₀ V₀C Ex) where
  st := fun Y => short_passes Y Ex (F₀ Y)
  stC := fun Y => shortC_passes Y Ex (F₀ Y)
  β := fun Y g pl => shortB Y Ex (pscBinds Y Ex (selPl g pl))
  car := fun Y g pl hI hpl hlt hn => v0_carries Y Ex (psc_carries Y Ex hI g pl hpl hlt hn)

/-- The lookup over the named short sumcheck: no premise is left. -/
theorem baseK₀_carries (A : LkAsmH E) :
    Carries (A.baseK V₀ V₀C (Ex := Ex)).R (chnKB (letterCar₀ E Ex) A) (A.baseK V₀ V₀C (Ex := Ex)).e
      (fun k => k ≤ A.v') (fun b k => b.2.1.pt (A.v' - k)) :=
  baseKS_carries (letterCar₀ E Ex) A

theorem baseK₀_passes (A : LkAsmH E) : (A.baseK V₀ V₀C (Ex := Ex)).R.Passes id Prod.fst :=
  baseKS_passes (letterCar₀ E Ex) A

end Cb.Rider

#print axioms Cb.Rider.Carries.seqU
#print axioms Cb.Rider.draw_carries
#print axioms Cb.Rider.gam_sg
#print axioms Cb.Rider.levK_carries
#print axioms Cb.Rider.chnK_carries
#print axioms Cb.Rider.baseKS_carries
#print axioms Cb.Rider.baseK₀_carries
#print axioms Cb.Rider.chnKB_vars
#print axioms Cb.Rider.baseKS_passes
#print axioms Cb.Rider.baseK₀_passes
