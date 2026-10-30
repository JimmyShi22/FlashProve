-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CorePeel.lean: soundness of the written link is reduced to a statement on the rounds
after the fifth, by the library's theorems on its link protocol.

The chain of an entry file begins with five rounds (in the written protocol an empty round stands in
front of them): the fold point; the root of the tree with the two folded rows, and the seed of their
sample; the two answers; the positions of the columns of the two stored tables; the point of
comparison. The library's link protocol (Cb/Ld/LdLink.lean) begins with the same five rounds, in its
own types. This file carries the written rounds to the library's (OnBytes/Slice/Carry.lean,
Draws.lean, LinkAt.lean) and takes them off one block after another (OnBytes/Slice/Peel.lean,
CoreKnow.lean). To take a block off: to show that the prover has lost before it, given that it has
lost after it.

The result, `core_peel`. It holds for any rounds t after the five and any goal `bad`, a property of
full transcripts that is bad for the prover (in use: the verifier refuses). on0, on1: conditions on
the first table and on the copy, free here. Let the pair y of stored strings have no witness in the
relaxed relation of the link's first joint, enlarged by the statements outside its condition
(`.cf`): both conditions hold of y, and the relation (both tables decode, to messages that agree on
the compared entries) does not. Then the prover has lost at the start towards `bad`, if
 - `bad` holds wherever a round's test of work fails, and
 - after every transcript of the five rounds it has lost in t, provided that the statement that the
   library's verifier holds at that point (`st4`) has no witness in the relaxed relation of the
   link's last joint before the closing, enlarged in the same way. That relation says: the two
   folded rows decode with their samples to vectors that meet all rows that are left.
The second condition speaks of the batching and the proximity test alone. It is a hypothesis here.
No property of the written decision is used in this file.

Further hypotheses: a bound on the bad fold points; bounds on the lists of the two oracle messages,
and that two different members of a list have the same answers at no more than a counted number of
seeds; that the compared entries have different vertices; and `DrawsOK`: for each of the five rounds
the map from its typed values to the library's verifier message is injective, and its positions have
at most 64 bits.

Main definitions: `one`, `gVec`, `gSeed`, `gLoc`, `wordsOf`, `answOf`, `st4`, `DrawsOK`, `coreErr`.
Main theorems: `peel_peek`, `peel_send`, `core_peel`.
Not claimed. That the hypothesis on the rounds after the fifth holds. Nothing on the sizes of the
error counts.
-/
import OnBytes.Slice.Peel
import OnBytes.Slice.CoreKnow
import OnBytes.Slice.LinkAt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-! ## Maps of one round -/

/-- The maps of a single round that do not look at the past. -/
def one {r r' : Round} (fm : r.Msg → r'.Msg) (fc : r.Chal → Option r'.Chal) : Carry [r] [r'] :=
  (fm, fun _ => fc, fun _ _ => ())

theorem one_fib {r r' : Round} (fm : r.Msg → r'.Msg) (fc : r.Chal → Option r'.Chal) (w : ℕ)
    (h : ∀ c', cnt (fun c => fc c = some c') ≤ w) : (one fm fc).Fib ((w, ()) : ℕ × Unit) :=
  ⟨fun _ c' => h c', fun _ _ => trivial⟩

theorem one_tr {r r' : Round} (fm : r.Msg → r'.Msg) (fc : r.Chal → Option r'.Chal) (m : r.Msg)
    (c : r.Chal) : (one fm fc).tr (m, c, ()) = (fc c).map fun c' => (fm m, c', ()) := by
  show (fc c).bind (fun c' => (some ()).map fun τ' => (fm m, c', τ')) = _
  cases fc c <;> rfl

/-- The maps of two rounds that do not look at the past. -/
def two {r₁ r₂ r₁' r₂' : Round} (fm₁ : r₁.Msg → r₁'.Msg) (fc₁ : r₁.Chal → Option r₁'.Chal)
    (fm₂ : r₂.Msg → r₂'.Msg) (fc₂ : r₂.Chal → Option r₂'.Chal) : Carry [r₁, r₂] [r₁', r₂'] :=
  (fm₁, fun _ => fc₁, fun _ _ => one fm₂ fc₂)

theorem two_fib {r₁ r₂ r₁' r₂' : Round} (fm₁ : r₁.Msg → r₁'.Msg) (fc₁ : r₁.Chal → Option r₁'.Chal)
    (fm₂ : r₂.Msg → r₂'.Msg) (fc₂ : r₂.Chal → Option r₂'.Chal) (w₁ w₂ : ℕ)
    (h₁ : ∀ c', cnt (fun c => fc₁ c = some c') ≤ w₁)
    (h₂ : ∀ c', cnt (fun c => fc₂ c = some c') ≤ w₂) :
    (two fm₁ fc₁ fm₂ fc₂).Fib ((w₁, (w₂, ())) : ℕ × ℕ × Unit) :=
  ⟨fun _ c' => h₁ c', fun _ _ => one_fib fm₂ fc₂ w₂ h₂⟩

theorem two_tr {r₁ r₂ r₁' r₂' : Round} (fm₁ : r₁.Msg → r₁'.Msg) (fc₁ : r₁.Chal → Option r₁'.Chal)
    (fm₂ : r₂.Msg → r₂'.Msg) (fc₂ : r₂.Chal → Option r₂'.Chal) (m₁ : r₁.Msg) (c₁ : r₁.Chal)
    (m₂ : r₂.Msg) (c₂ : r₂.Chal) :
    (two fm₁ fc₁ fm₂ fc₂).tr (m₁, c₁, m₂, c₂, ()) =
      (fc₁ c₁).bind fun c₁' => (fc₂ c₂).map fun c₂' => (fm₁ m₁, c₁', fm₂ m₂, c₂', ()) := by
  show (fc₁ c₁).bind
    (fun c₁' => ((one fm₂ fc₂).tr (m₂, c₂, ())).map fun τ' => (fm₁ m₁, c₁', τ')) = _
  rw [one_tr]
  cases fc₁ c₁ <;> cases fc₂ c₂ <;> rfl

/-! ## Typed values as the library's verifier messages -/

/-- The first n elements among the typed values, as a vector; 0 where there are fewer. -/
def gVec (n : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) : Fin n → GE :=
  fun i => (elemsV ds v).getD i.val 0

theorem possV_nil (ds : List Fmt.Draw) (h : nP ds = 0) (v : Vals .two ds) : possV ds v = [] :=
  List.length_eq_zero_iff.1 ((possV_length ds v).trans h)

theorem elemsV_nil (ds : List Fmt.Draw) (h : nE ds = 0) (v : Vals .two ds) : elemsV ds v = [] :=
  List.length_eq_zero_iff.1 ((elemsV_length ds v).trans h)

theorem gVec_inj (n : ℕ) (ds : List Fmt.Draw) (hp : PlainDraws ds) (hE : nE ds = n)
    (hP : nP ds = 0) : Function.Injective (gVec n ds) := fun v w h =>
  vals_inj ds hp v w
    (list_ext_getD 0 ((elemsV_length ds v).trans (elemsV_length ds w).symm) fun i hi =>
      congrFun h ⟨i, by rw [← hE, ← elemsV_length ds v]; exact hi⟩)
    ((possV_nil ds hP v).trans (possV_nil ds hP w).symm)

/-- If a round draws nothing, its typed values have one value. -/
theorem gUnit_inj (ds : List Fmt.Draw) (hp : PlainDraws ds) (hE : nE ds = 0) (hP : nP ds = 0) :
    Function.Injective (fun _ : Vals .two ds => ()) := fun v w _ =>
  vals_inj ds hp v w ((elemsV_nil ds hE v).trans (elemsV_nil ds hE w).symm)
    ((possV_nil ds hP v).trans (possV_nil ds hP w).symm)

/-- An element other than 0 as a unit; 1 at 0. -/
def unitOf (x : GE) : GEˣ := if h : x ≠ 0 then Units.mk0 x h else 1

theorem unitOf_val {x : GE} (h : x ≠ 0) : (unitOf x).val = x := by
  unfold unitOf
  rw [dif_pos h]
  rfl

/-- A seed: c elements and a factor other than 0. -/
def gSeed (c : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) : (Fin c → GE) × GEˣ :=
  (gVec c ds v, unitOf ((elemsV ds v).getD c 0))

theorem gSeed_inj (c : ℕ) (ds : List Fmt.Draw) (hp : PlainDraws ds) (hE : nE ds = c + 1)
    (hP : nP ds = 0) (hz : IsNZ ds c) : Function.Injective (gSeed c ds) := fun v w h =>
  vals_inj ds hp v w
    (list_ext_getD 0 ((elemsV_length ds v).trans (elemsV_length ds w).symm) fun i hi => by
      have hi' : i < c + 1 := by rw [← hE, ← elemsV_length ds v]; exact hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h1 | rfl
      · exact congrFun (congrArg Prod.fst h) ⟨i, h1⟩
      · have h2 := congrArg (fun s : (Fin i → GE) × GEˣ => s.2.val) h
        simp only [gSeed] at h2
        rwa [unitOf_val (elemsV_nz ds i hz v), unitOf_val (elemsV_nz ds i hz w)] at h2)
    ((possV_nil ds hP v).trans (possV_nil ds hP w).symm)

/-- Two lists of positions: the first t0 draws, then t1. -/
def gLoc (a t0 t1 : ℕ) (ds : List Fmt.Draw) (v : Vals .two ds) :
    (Fin t0 → Fin (2 ^ a)) × (Fin t1 → Fin (2 ^ a)) :=
  (fun i => ⟨(possV ds v).getD i.val 0 % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩,
   fun i => ⟨(possV ds v).getD (t0 + i.val) 0 % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩)

theorem getD_lt (a : ℕ) (ds : List Fmt.Draw) (hA : AllPos a ds) (v : Vals .two ds) (i : ℕ) :
    (possV ds v).getD i 0 < 2 ^ a := by
  by_cases hi : i < (possV ds v).length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact possV_lt a ds hA v _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
    exact Nat.two_pow_pos a

theorem gLoc_inj (a t0 t1 : ℕ) (ds : List Fmt.Draw) (hp : PlainDraws ds) (hE : nE ds = 0)
    (hP : nP ds = t0 + t1) (hA : AllPos a ds) : Function.Injective (gLoc a t0 t1 ds) :=
  fun v w h =>
  vals_inj ds hp v w ((elemsV_nil ds hE v).trans (elemsV_nil ds hE w).symm)
    (list_ext_getD 0 ((possV_length ds v).trans (possV_length ds w).symm) fun i hi => by
      have hi' : i < t0 + t1 := by rw [← hP, ← possV_length ds v]; exact hi
      have key : (possV ds v).getD i 0 % 2 ^ a = (possV ds w).getD i 0 % 2 ^ a := by
        by_cases h1 : i < t0
        · exact congrArg Fin.val (congrFun (congrArg Prod.fst h) ⟨i, h1⟩)
        · have h2 := congrArg Fin.val (congrFun (congrArg Prod.snd h) ⟨i - t0, by omega⟩)
          simp only [gLoc] at h2
          rwa [Nat.add_sub_cancel' (Nat.le_of_not_lt h1)] at h2
      rwa [Nat.mod_eq_of_lt (getD_lt a ds hA v i), Nat.mod_eq_of_lt (getD_lt a ds hA w i)] at key)

theorem chalTo_some {C' : Type} (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → C')
    (c : (wRound d).Chal) (c' : C') (h : chalTo d g c = some c') : c' = g (valsOf d c) := by
  unfold chalTo at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-! ## A round in which the library's verifier only draws and reads -/

/-- **A round without a prover message in the library's protocol is taken off.** V: the library's
verifier of the round. g: the typed values of the written round as V's verifier message. -/
theorem peel_peek {Xi Xo Wi Wo : Type} {Ei Eo : ExtSpec} (V : IOR.PeekV Xi Ei Xo Eo)
    {RA : Xi × Ei.Str → Wi → Prop} {RB : Xo × Eo.Str → Wo → Prop}
    {ext : Xi × Ei.Str → Tr (IOR.peek V).red.shape → Wo → Wi} {e : ℕ}
    (hK : (IOR.peek V).red.Know (fun _ => True) RA RB ext ((e, ()) : ℕ × Unit))
    (d : PQ.RD) (g : Vals .two (Fmt.dsOf d.entry d.kind) → V.D) (hg : Function.Injective g)
    (hlog : d.entry.logN ≤ 64) (t : Shape) (εt : Err t) (a : Xi × Ei.Str) (hno : ∀ w, ¬ RA a w)
    (bad : Tr (wRound d :: t) → Prop)
    (hp : ∀ m c τ, GChal.pass (b := d.entry.work) c = false → bad (m, c, τ))
    (H : ∀ m c, (∀ w, ¬ RB (V.nx a.1 a.2 (g (valsOf d c)), V.g.map a.2) w) →
      Doomed t εt fun b => bad (m, c, b)) :
    Doomed (wRound d :: t) (e * (bsRound .two d.entry d.kind).w, εt) bad := by
  refine peel (s := [wRound d]) (t := t) (IOR.peek V).red hK a trivial hno
    (one (fun _ => ((), ())) (chalTo d g)) (((bsRound .two d.entry d.kind).w, ()) : ℕ × Unit)
    (one_fib _ _ _ (chalTo_fib d g hg hlog)) εt bad ?_ ?_
  · rintro ⟨m, c, ⟨⟩⟩ hτ0
    have hτ :=
      (one_tr (r' := IOR.drawRound V.D) (fun _ => ((), ())) (chalTo d g) m c).symm.trans hτ0
    have hc : chalTo d g c = none := by
      cases h : chalTo d g c with
      | none => rfl
      | some c' => rw [h] at hτ; cases hτ
    exact doomed_of_all _ _ _ fun b => hp m c b (chalTo_none d g c hc)
  · rintro ⟨m, c, ⟨⟩⟩ τ' hτ0 hno'
    have hτ :=
      (one_tr (r' := IOR.drawRound V.D) (fun _ => ((), ())) (chalTo d g) m c).symm.trans hτ0
    cases h : chalTo d g c with
    | none => rw [h] at hτ; cases hτ
    | some c' =>
      rw [h] at hτ
      obtain rfl : (((), ()), c', ()) = τ' := Option.some.inj hτ
      obtain rfl := chalTo_some d g c c' h
      exact H m c fun w => hno' _ w rfl

/-! ## The sending -/

/-- Word number j of the column at the position x of a written oracle; 0 outside. -/
def wordAt (d : PQ.RD) (o : (wRound d).Orc) (x j : ℕ) : UInt64 :=
  if hx : x < PQ.posN d.tree then if hj : j < PQ.colW d.tree then o ⟨x, hx⟩ ⟨j, hj⟩ else 0 else 0

/-- Symbol number i over the extension field of the column at x: three words. -/
def symAt (d : PQ.RD) (o : (wRound d).Orc) (x i : ℕ) : GE :=
  toE (wordAt d o x (3 * i), wordAt d o x (3 * i + 1), wordAt d o x (3 * i + 2))

/-- **The written oracle as the words of the two members.** A column holds the R symbols of the
first table's folded row, then the R symbols of the copy's (and then what this map does not
read). -/
def wordsOf (S : Sz) (d : PQ.RD) (o : (wRound d).Orc) : S.fam.ext.Str := fun a p =>
  match p with
  | .inl x => fun s => symAt d o x.val ((if a then S.P.R else 0) + s.1.val)
  | .inr _ => fun s => s.1.elim

/-- The elements of the extension field among the items of a written prover message. -/
def ansOf (d : PQ.RD) (m : (wRound d).Msg) : List GE :=
  (PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2)).filterMap fun g =>
    match g with
    | .e x => some (toE x)
    | .answer x => some (toE x)
    | _ => none

/-- **The two answers**: the first table's folded row's, then the copy's. -/
def answOf (S : Sz) (d : PQ.RD) (m : (wRound d).Msg) : S.fam.Answ :=
  fun a _ => (ansOf d m).getD (if a then 1 else 0) 0

theorem seeds_fair (S : Sz) : S.seeds.Fair := fun _ ρ => le_of_eq (cnt_eq_const ρ)

/-- The statement after the sending. -/
def st2 (S : Sz) (d2 d3 : PQ.RD) (a : S.lk.X1 × S.lk.E0.Str) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) : S.lk.X2 × S.lk.E2.Str :=
  ((a.1, fun b => (gSeed (S.P.aR + S.P.aP) _ (valsOf d2 c2), answOf S d3 m3 b)),
    (a.2, wordsOf S d2 m2.1))

/-- **The two rounds of the sending are taken off.** -/
theorem peel_send (S : Sz) (on0 on1 : (S.lk.D.X.Row → S.Pos → GE) → S.lk.D.X.Rec → Prop)
    (L : Bool → ℕ) (hlist : ∀ a, (S.lk.N.om a).ListLE (L a)) (hev : ∀ a, (S.lk.N.om a).Evades)
    (d2 d3 : PQ.RD)
    (hg2 : Function.Injective (gSeed (S.P.aR + S.P.aP) (Fmt.dsOf d2.entry d2.kind)))
    (hg3 : Function.Injective (fun _ : Vals .two (Fmt.dsOf d3.entry d3.kind) => ()))
    (hlog2 : d2.entry.logN ≤ 64) (hlog3 : d3.entry.logN ≤ 64) (t : Shape) (εt : Err t)
    (a : S.lk.X1 × S.lk.E0.Str) (hno : ∀ w, ¬ (S.lk.j1 on0 on1).cf.relR a w)
    (bad : Tr (wRound d2 :: wRound d3 :: t) → Prop)
    (hp2 : ∀ m c τ, GChal.pass (b := d2.entry.work) c = false → bad (m, c, τ))
    (hp3 : ∀ m2 c2 m c τ, GChal.pass (b := d3.entry.work) c = false → bad (m2, c2, m, c, τ))
    (H : ∀ m2 c2 m3 c3, (∀ w, ¬ (S.lk.j2 on0 on1).cf.relR (st2 S d2 d3 a m2 c2 m3) w) →
      Doomed t εt fun b => bad (m2, c2, m3, c3, b)) :
    Doomed (wRound d2 :: wRound d3 :: t)
      (ldSendFamErr S.lk.N S.seeds L * (bsRound .two d2.entry d2.kind).w,
        (0 * (bsRound .two d3.entry d3.kind).w, εt)) bad := by
  refine peel (s := [wRound d2, wRound d3]) (t := t) (ldSendFam S.lk.N S.seeds S.lk.X1 S.lk.E0).red
    (know_snd S.lk on0 on1 S.seeds L (seeds_fair S) hlist hev) a trivial hno
    (two (r₁' := S.fam.sendRound S.seeds) (r₂' := Blocks.plainRound S.fam.Answ Unit fun _ _ => 0)
      (fun m => (wordsOf S d2 m.1, ())) (chalTo d2 (gSeed (S.P.aR + S.P.aP) _))
      (fun m => ((), answOf S d3 m)) (chalTo d3 fun _ => ()))
    (((bsRound .two d2.entry d2.kind).w, ((bsRound .two d3.entry d3.kind).w, ())) : ℕ × ℕ × Unit)
    (two_fib _ _ _ _ _ _ (chalTo_fib d2 _ hg2 hlog2) (chalTo_fib d3 _ hg3 hlog3)) εt bad ?_ ?_
  · rintro ⟨m2, c2, m3, c3, ⟨⟩⟩ hτ0
    have hτ := (two_tr (r₁' := S.fam.sendRound S.seeds)
      (r₂' := Blocks.plainRound S.fam.Answ Unit fun _ _ => 0)
      (fun m => (wordsOf S d2 m.1, ())) (chalTo d2 (gSeed (S.P.aR + S.P.aP) _))
      (fun m => ((), answOf S d3 m)) (chalTo d3 fun _ => ()) m2 c2 m3 c3).symm.trans hτ0
    cases h2 : chalTo d2 (gSeed (S.P.aR + S.P.aP) _) c2 with
    | none => exact doomed_of_all _ _ _ fun b => hp2 m2 c2 _ (chalTo_none d2 _ c2 h2)
    | some s =>
      cases h3 : chalTo d3 (fun _ => ()) c3 with
      | none => exact doomed_of_all _ _ _ fun b => hp3 m2 c2 m3 c3 b (chalTo_none d3 _ c3 h3)
      | some u =>
        rw [h2, h3] at hτ
        cases hτ
  · rintro ⟨m2, c2, m3, c3, ⟨⟩⟩ τ' hτ0 hno'
    have hτ := (two_tr (r₁' := S.fam.sendRound S.seeds)
      (r₂' := Blocks.plainRound S.fam.Answ Unit fun _ _ => 0)
      (fun m => (wordsOf S d2 m.1, ())) (chalTo d2 (gSeed (S.P.aR + S.P.aP) _))
      (fun m => ((), answOf S d3 m)) (chalTo d3 fun _ => ()) m2 c2 m3 c3).symm.trans hτ0
    cases h2 : chalTo d2 (gSeed (S.P.aR + S.P.aP) _) c2 with
    | none =>
      rw [h2] at hτ
      cases hτ
    | some s =>
      cases h3 : chalTo d3 (fun _ => ()) c3 with
      | none =>
        rw [h2, h3] at hτ
        cases hτ
      | some u =>
        rw [h2, h3] at hτ
        obtain rfl := Option.some.inj hτ
        obtain rfl := chalTo_some d2 _ c2 s h2
        exact H m2 c2 m3 c3 fun w => hno' _ w rfl

/-! ## The five rounds -/

section Core
variable (S : Sz) (d1 d2 d3 d4 d5 : PQ.RD)

/-- **The statement that the library's verifier holds after the five rounds**, as a function of the
two stored strings and of the written messages. -/
def st4 (y : S.lk.E0.Str) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
    (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c4 : (wRound d4).Chal)
    (c5 : (wRound d5).Chal) : S.lk.X4 × S.lk.E3.Str :=
  let a1 : S.lk.X1 × S.lk.E0.Str :=
    (S.lk.vGam.nx (S.rec0, S.rec0) y (gVec S.P.v _ (valsOf d1 c1)), S.lk.vGam.g.map y)
  let a2 := st2 S d2 d3 a1 m2 c2 m3
  let a3 : S.lk.X3 × S.lk.E3.Str :=
    (S.lk.vLoc.nx a2.1 a2.2 (gLoc S.P.T.a S.P.nu0 S.P.nuj _ (valsOf d4 c4)), S.lk.vLoc.g.map a2.2)
  (S.lk.vPhi.nx a3.1 a3.2 (gVec S.P.aPhi _ (valsOf d5 c5)), S.lk.vPhi.g.map a3.2)

/-- For each of the five rounds: the map from its typed values to the library's verifier message is
injective, and its positions have at most 64 bits. -/
structure DrawsOK : Prop where
  g1 : Function.Injective (gVec S.P.v (Fmt.dsOf d1.entry d1.kind))
  g2 : Function.Injective (gSeed (S.P.aR + S.P.aP) (Fmt.dsOf d2.entry d2.kind))
  g3 : Function.Injective (fun _ : Vals .two (Fmt.dsOf d3.entry d3.kind) => ())
  g4 : Function.Injective (gLoc S.P.T.a S.P.nu0 S.P.nuj (Fmt.dsOf d4.entry d4.kind))
  g5 : Function.Injective (gVec S.P.aPhi (Fmt.dsOf d5.entry d5.kind))
  l1 : d1.entry.logN ≤ 64
  l2 : d2.entry.logN ≤ 64
  l3 : d3.entry.logN ≤ 64
  l4 : d4.entry.logN ≤ 64
  l5 : d5.entry.logN ≤ 64

/-- The error counts of the five written rounds: the library's, each times w, the sampler's bound on
how many strings of the round's hash blocks give one tuple of drawn values. -/
def coreErr (ε₀ ε₁ : ℕ) (L : Bool → ℕ) {t : Shape} (εt : Err t) :
    Err (wRound d1 :: wRound d2 :: wRound d3 :: wRound d4 :: wRound d5 :: t) :=
  (S.lk.errGam ε₀ ε₁ * (bsRound .two d1.entry d1.kind).w,
    (ldSendFamErr S.lk.N S.seeds L * (bsRound .two d2.entry d2.kind).w,
      (0 * (bsRound .two d3.entry d3.kind).w,
        (S.lk.errLoc * (bsRound .two d4.entry d4.kind).w,
          (S.lk.errPhi * (bsRound .two d5.entry d5.kind).w, εt)))))

/-- **The link's five rounds are taken off.** The head tells the statement. -/
theorem core_peel (on0 on1 : (S.lk.D.X.Row → S.Pos → GE) → S.lk.D.X.Rec → Prop) (ε₀ ε₁ : ℕ)
    (L : Bool → ℕ) (hFold : S.lk.FoldErr on0 on1 ε₀ ε₁) (hpl : Function.Injective S.lk.D.pl)
    (hlist : ∀ a, (S.lk.N.om a).ListLE (L a)) (hev : ∀ a, (S.lk.N.om a).Evades)
    (hd : DrawsOK S d1 d2 d3 d4 d5) (t : Shape) (εt : Err t) (y : S.lk.E0.Str)
    (hy : ∀ w, ¬ (S.lk.j0 on0 on1).cf.relR ((S.rec0, S.rec0), y) w)
    (bad : Tr (wRound d1 :: wRound d2 :: wRound d3 :: wRound d4 :: wRound d5 :: t) → Prop)
    (hp1 : ∀ m1 c1 τ, GChal.pass (b := d1.entry.work) c1 = false → bad (m1, c1, τ))
    (hp2 : ∀ m1 c1 m2 c2 τ, GChal.pass (b := d2.entry.work) c2 = false → bad (m1, c1, m2, c2, τ))
    (hp3 : ∀ m1 c1 m2 c2 m3 c3 τ, GChal.pass (b := d3.entry.work) c3 = false →
      bad (m1, c1, m2, c2, m3, c3, τ))
    (hp4 : ∀ m1 c1 m2 c2 m3 c3 m4 c4 τ, GChal.pass (b := d4.entry.work) c4 = false →
      bad (m1, c1, m2, c2, m3, c3, m4, c4, τ))
    (hp5 : ∀ m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 τ, GChal.pass (b := d5.entry.work) c5 = false →
      bad (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, τ))
    (H : ∀ m1 c1 m2 c2 m3 c3 m4 c4 m5 c5,
      (∀ w, ¬ S.lk.j4.cf.relR (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5) w) →
      Doomed t εt fun b => bad (m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, b)) :
    Doomed _ (coreErr S d1 d2 d3 d4 d5 ε₀ ε₁ L εt) bad :=
  peel_peek S.lk.vGam (know_gam S.lk on0 on1 ε₀ ε₁ hFold) d1 _ hd.g1 hd.l1 _ _
    ((S.rec0, S.rec0), y) hy bad hp1 fun m1 c1 h1 =>
  peel_send S on0 on1 L hlist hev d2 d3 hd.g2 hd.g3 hd.l2 hd.l3 _ _ _ h1 _ (hp2 m1 c1)
    (hp3 m1 c1) fun m2 c2 m3 c3 h2 =>
  peel_peek S.lk.vLoc (know_loc S.lk on0 on1 S.seeds) d4 _ hd.g4 hd.l4 _ _ _ h2 _
    (hp4 m1 c1 m2 c2 m3 c3) fun m4 c4 h3 =>
  peel_peek S.lk.vPhi (know_phi S.lk hpl) d5 _ hd.g5 hd.l5 t εt _ h3 _
    (hp5 m1 c1 m2 c2 m3 c3 m4 c4) fun m5 c5 h4 => H m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 h4

end Core

end OnBytes.Slice

#print axioms OnBytes.Slice.core_peel
#print axioms OnBytes.Slice.peel_send
#print axioms OnBytes.Slice.gSeed_inj
#print axioms OnBytes.Slice.gLoc_inj
#print axioms OnBytes.Slice.peel_peek
