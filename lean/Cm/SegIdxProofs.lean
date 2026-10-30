-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxProofs.lean: the proofs of `Spec.ofBits_ok` and `Spec.ofBits_vtx` of Cm/SegIdx.lean: under
the hypotheses of their statements, the generic constructor `ofBits` gives an index atom, and what
that atom reads at a vertex.

An index atom (`IdxAtom` with its law `IdxAtom.OK`, Cb/Req/ReqSpec.lean) is a vector on the
vertices of a cube, linear in the index matrix, whose multilinear extension at every point is a
tensor form: through such atoms the model's conditions read the weights. A source (`Src`,
Cm/SegIdx.lean) says where a bit comes from: a variable of the cube, its negation, or a constant.

Main names:
  `AffIn f u`: f is affine in the coordinate u of its point, for all fixed values of the others;
    `Indep f u`: f does not read it.
  `ext_glue`: a function that is affine in each of the first v coordinates is, at every point, the
    multilinear extension of its values at the vertices (the coordinates from v on are left as they
    are).

Why, if no variable is named twice in cs ++ rs (`Src.OK`), the tensor form of `ofBits` is affine in
every variable: eq(the point of a list of sources, c) is a product with one factor for each source:
it is affine in a variable that is named once, and does not read a variable that is not named; and
then a variable that a column source names is read by no row source, and the reverse.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegIdx
import Blocks.EqN

set_option autoImplicit false

namespace Cm
open Cb Blocks Finset

variable {E : Type} [Field E]

/-! ## 1. Affine in each variable -/

def AffIn (f : (ℕ → E) → E) (u : ℕ) : Prop :=
  ∀ q, ∃ α β : E, ∀ t, f (Function.update q u t) = α + β * t
def Indep (f : (ℕ → E) → E) (u : ℕ) : Prop := ∀ q t, f (Function.update q u t) = f q

theorem Indep.affIn {f : (ℕ → E) → E} {u : ℕ} (h : Indep f u) : AffIn f u := fun q =>
  ⟨f q, 0, fun t => by rw [h q t, zero_mul, add_zero]⟩

omit [Field E] in
theorem indep_const (c : E) (u : ℕ) : Indep (fun _ => c) u := fun _ _ => rfl

theorem Indep.mul {f g : (ℕ → E) → E} {u : ℕ} (hf : Indep f u) (hg : Indep g u) :
    Indep (fun q => f q * g q) u := fun q t => by
  show f _ * g _ = _
  rw [hf q t, hg q t]

theorem AffIn.mul_indep {f g : (ℕ → E) → E} {u : ℕ} (hf : AffIn f u) (hg : Indep g u) :
    AffIn (fun q => f q * g q) u := fun q => by
  obtain ⟨α, β, h⟩ := hf q
  refine ⟨α * g q, β * g q, fun t => ?_⟩
  show f _ * g _ = _
  rw [h t, hg q t]
  ring

theorem AffIn.indep_mul {f g : (ℕ → E) → E} {u : ℕ} (hf : Indep f u) (hg : AffIn g u) :
    AffIn (fun q => f q * g q) u := fun q => by
  obtain ⟨α, β, h⟩ := hg q
  refine ⟨f q * α, f q * β, fun t => ?_⟩
  show f _ * g _ = _
  rw [h t, hf q t]
  ring

theorem AffIn.sum {J : Type} (s : Finset J) {f : J → (ℕ → E) → E}
    {u : ℕ} (h : ∀ j ∈ s, AffIn (f j) u) :
    AffIn (fun q => ∑ j ∈ s, f j q) u := by
  classical
  induction s using Finset.induction_on with
  | empty => exact fun _ => ⟨0, 0, fun _ => by simp⟩
  | insert a s ha ih =>
    intro q
    obtain ⟨α, β, h1⟩ := h a (mem_insert_self a s) q
    obtain ⟨α', β', h2⟩ := ih (fun j hj => h j (mem_insert_of_mem hj)) q
    refine ⟨α + α', β + β', fun t => ?_⟩
    have h2' : ∑ j ∈ s, f j (Function.update q u t) = α' + β' * t := h2 t
    show ∑ j ∈ insert a s, f j (Function.update q u t) = _
    rw [sum_insert ha, h1 t, h2']
    ring

theorem Indep.sum {J : Type} (s : Finset J) {f : J → (ℕ → E) → E}
    {u : ℕ} (h : ∀ j ∈ s, Indep (f j) u) :
    Indep (fun q => ∑ j ∈ s, f j q) u :=
  fun q t => sum_congr rfl fun j hj => h j hj q t

/-! ## 2. A function that is affine in each variable is the extension of its values at the
vertices -/

/-- the first v coordinates of a, the others of q -/
def glue (v : ℕ) (a q : ℕ → E) : ℕ → E := fun t => if t < v then a t else q t

theorem eqN_one_zero (off : ℕ) (a : ℕ → E) : eqN 1 off a 0 = 1 - a off := by simp [eqN]
theorem eqN_one_one (off : ℕ) (a : ℕ → E) : eqN 1 off a 1 = a off := by simp [eqN]

theorem vtx_succ (v X : ℕ) (β : ℕ) (hβ : β < 2) (q : ℕ → E) :
    glue (v + 1) (vtx (v + 1) (X * 2 + β)) q =
      Function.update (glue v (vtx v X) q) v (if β = 1 then 1 else 0) := by
  funext t
  unfold glue vtx
  rcases Nat.lt_trichotomy t v with h | h | h
  · have e : v + 1 - 1 - t = (v - 1 - t) + 1 := by omega
    have e2 : (X * 2 + β) / 2 = X := by omega
    rw [Function.update_of_ne (Nat.ne_of_lt h), if_pos (by omega), if_pos h,
      e, Nat.testBit_succ, e2]
    simp [h, Nat.lt_succ_of_lt h]
  · subst h
    rw [Function.update_self, if_pos (Nat.lt_succ_self t)]
    have e : t + 1 - 1 - t = 0 := by omega
    rw [e, Nat.testBit_zero]
    have : (X * 2 + β) % 2 = β := by omega
    simp [this]
  · rw [Function.update_of_ne (Nat.ne_of_gt h), if_neg (by omega), if_neg (by omega)]

theorem ext_glue :
    ∀ (v : ℕ) (f : (ℕ → E) → E),
      (∀ u < v, AffIn f u) → ∀ q, ∑ X ∈ range (2 ^ v), eqN v 0 q X * f (glue v (vtx v X) q) = f q
  | 0, f, _, q => by
      have e : glue 0 (vtx 0 0) q = q := by funext t; simp [glue]
      simp [eqN, e]
  | v + 1, f, hf, q => by
      rw [pow_succ, Alg.sum_range_mul_add,
        ← ext_glue v f (fun u hu => hf u (Nat.lt_succ_of_lt hu)) q]
      refine sum_congr rfl fun X _ => ?_
      obtain ⟨α, β, h⟩ := hf v (Nat.lt_succ_self v) (glue v (vtx v X) q)
      have hq : glue v (vtx v X) q v = q v := if_neg (Nat.lt_irrefl v)
      have h0 : f (glue v (vtx v X) q) = α + β * q v := by
        rw [← h (q v), ← hq, Function.update_eq_self]
      have a0 := eqN_append' v 1 0 q X (z' := 0) (by norm_num)
      have a1 := eqN_append' v 1 0 q X (z' := 1) (by norm_num)
      rw [pow_one, Nat.zero_add, eqN_one_zero] at a0
      rw [pow_one, Nat.zero_add, eqN_one_one] at a1
      rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add, a0, a1,
        vtx_succ v X 0 (by norm_num), vtx_succ v X 1 (by norm_num), h0]
      rw [if_neg (by norm_num : ¬ (0 : ℕ) = 1), if_pos (rfl : (1 : ℕ) = 1), h, h]
      ring

/-! ## 3. The point of a list of sources -/

theorem Src.pt_congr {q q' : ℕ → E} :
    ∀ l : List Src, (∀ u ∈ Src.vars l, q u = q' u) → Src.pt l q = Src.pt l q'
  | [], _ => rfl
  | .var u :: l, h => by
      funext t
      cases t with
      | zero => exact h u (List.mem_cons_self)
      | succ t => exact congrFun (Src.pt_congr l fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) t
  | .nvar u :: l, h => by
      funext t
      cases t with
      | zero => exact congrArg (fun z => 1 - z) (h u (List.mem_cons_self))
      | succ t => exact congrFun (Src.pt_congr l fun u' hu' => h u' (List.mem_cons_of_mem _ hu')) t
  | .bit β :: l, h => by
      funext t
      cases t with
      | zero => rfl
      | succ t => exact congrFun (Src.pt_congr l h) t

/-- eq of the point of a list: one factor for the first source. -/
theorem eqN_cons (s : Src) (l : List Src) (q : ℕ → E) (c : ℕ) :
    eqN (s :: l).length 0 (Src.pt (s :: l) q) c =
      (if (c / 2 ^ l.length).testBit 0 then s.eval q else 1 - s.eval q) *
        eqN l.length 0 (Src.pt l q) (c % 2 ^ l.length) := by
  have h := eqN_append 1 l.length 0 (Src.pt (s :: l) q) (c / 2 ^ l.length)
    (Nat.mod_lt c (Nat.two_pow_pos l.length))
  rw [Nat.div_add_mod] at h
  have e1 : (s :: l).length = 1 + l.length := by rw [List.length_cons, Nat.add_comm]
  rw [e1, h]
  congr 1
  · simp [eqN, Src.pt]
  · rw [eqN_eq, eqN_eq]
    congr 1
    funext t
    show Src.pt (s :: l) q (0 + 1 + t.val) = Src.pt l q (0 + t.val)
    rw [Nat.zero_add, Nat.zero_add, Nat.add_comm]
    rfl

theorem indep_eval {s : Src} {u : ℕ} (h : u ∉ Src.vars [s]) :
    Indep (fun q : ℕ → E => s.eval q) u := fun q t => by
  cases s with
  | var u' =>
    have : u' ≠ u := fun e => h (by rw [e]; exact List.mem_cons_self)
    exact Function.update_of_ne this _ _
  | nvar u' =>
    have : u' ≠ u := fun e => h (by rw [e]; exact List.mem_cons_self)
    exact congrArg (fun z => 1 - z) (Function.update_of_ne this _ _)
  | bit β => rfl

theorem affIn_eval (s : Src) (u : ℕ) : AffIn (fun q : ℕ → E => s.eval q) u := fun q => by
  cases s with
  | var u' =>
    by_cases e : u' = u
    · subst e
      exact ⟨0, 1, fun t => by show Function.update q u' t u' = _; rw [Function.update_self]; ring⟩
    · exact ⟨q u', 0,
        fun t => by show Function.update q u t u' = _; rw [Function.update_of_ne e]; ring⟩
  | nvar u' =>
    by_cases e : u' = u
    · subst e
      exact ⟨1, -1,
        fun t => by show 1 - Function.update q u' t u' = _; rw [Function.update_self]; ring⟩
    · exact ⟨1 - q u', 0,
        fun t => by show 1 - Function.update q u t u' = _; rw [Function.update_of_ne e]; ring⟩
  | bit β => exact ⟨if β then 1 else 0, 0, fun t => by show (if β then (1 : E) else 0) = _; ring⟩

theorem affIn_factor (s : Src) (u : ℕ) (β : Bool) :
    AffIn (fun q : ℕ → E => if β then s.eval q else 1 - s.eval q) u := fun q => by
  obtain ⟨a, b, h⟩ := affIn_eval (E := E) s u q
  cases β with
  | true => exact ⟨a, b, h⟩
  | false => exact ⟨1 - a, -b, fun t => by
      have h' : s.eval (Function.update q u t) = a + b * t := h t
      show 1 - s.eval (Function.update q u t) = _
      rw [h']
      ring⟩

theorem indep_factor {s : Src} {u : ℕ} (hs : u ∉ Src.vars [s]) (β : Bool) :
    Indep (fun q : ℕ → E => if β then s.eval q else 1 - s.eval q) u := fun q t => by
  have h : s.eval (Function.update q u t) = s.eval q := indep_eval (E := E) hs q t
  cases β with
  | true => exact h
  | false => show 1 - s.eval _ = 1 - s.eval _; rw [h]

theorem vars_cons (s : Src) (l : List Src) : Src.vars (s :: l) = Src.vars [s] ++ Src.vars l := by
  cases s <;> rfl

theorem vars_append : ∀ l l' : List Src, Src.vars (l ++ l') = Src.vars l ++ Src.vars l'
  | [], _ => rfl
  | s :: l, l' => by
      rw [List.cons_append, vars_cons, vars_append l l', vars_cons s l, List.append_assoc]

theorem indep_eqN {u : ℕ} :
    ∀ (l : List Src) (c : ℕ),
      u ∉ Src.vars l → Indep (fun q : ℕ → E => eqN l.length 0 (Src.pt l q) c) u
  | [], c, _ => fun _ _ => rfl
  | s :: l, c, h => by
      rw [vars_cons, List.mem_append, not_or] at h
      have := (indep_factor (E := E) h.1 ((c / 2 ^ l.length).testBit 0)).mul
        (indep_eqN l (c % 2 ^ l.length) h.2)
      intro q t
      show eqN (s :: l).length 0 (Src.pt (s :: l) (Function.update q u t)) c =
        eqN (s :: l).length 0 (Src.pt (s :: l) q) c
      rw [eqN_cons, eqN_cons]
      exact this q t

theorem affIn_eqN (u : ℕ) :
    ∀ (l : List Src) (c : ℕ),
      (Src.vars l).Nodup → AffIn (fun q : ℕ → E => eqN l.length 0 (Src.pt l q) c) u
  | [], c, _ => (indep_const _ u).affIn
  | s :: l, c, h => by
      rw [vars_cons, List.nodup_append] at h
      have key : AffIn
          (fun q : ℕ → E =>
            (if (c / 2 ^ l.length).testBit 0 then s.eval q else 1 - s.eval q) *
              eqN l.length 0 (Src.pt l q) (c % 2 ^ l.length)) u := by
        by_cases hu : u ∈ Src.vars [s]
        · exact (affIn_factor s u _).mul_indep (indep_eqN l _ fun hl => h.2.2 u hu u hl rfl)
        · exact AffIn.indep_mul (indep_factor hu _) (affIn_eqN u l _ h.2.1)
      intro q
      obtain ⟨α, β, hk⟩ := key q
      exact ⟨α, β, fun t => by
        show eqN (s :: l).length 0 (Src.pt (s :: l) (Function.update q u t)) c = _
        rw [eqN_cons]
        exact hk t⟩

/-! ## 4. At a vertex -/

theorem eval_vtx (s : Src) (v b : ℕ) :
    s.eval (vtx (E := E) v b) = if s.bitAt v b then 1 else 0 := by
  cases s with
  | var u => simp [Src.eval, Src.bitAt, vtx]
  | nvar u =>
    by_cases h : u < v ∧ b.testBit (v - 1 - u) = true
    · simp [Src.eval, Src.bitAt, vtx, h]
    · have h' : ¬ (u < v ∧ b.testBit (v - 1 - u) = true) := h
      simp only [Src.eval, Src.bitAt, vtx, if_neg h']
      rw [not_and] at h'
      by_cases hu : u < v
      · simp [hu, h' hu]
      · simp [hu]
  | bit β => rfl

/-- At a vertex, eq(the point of a list of sources, ·) picks the number of the list. -/
theorem sum_eqN_vtx (v b : ℕ) :
    ∀ (l : List Src) (G : ℕ → E),
      ∑ c ∈ range (2 ^ l.length), eqN l.length 0 (Src.pt l (vtx v b)) c * G c = G (Src.num l v b)
  | [], G => by simp [eqN, Src.num, numL]
  | s :: l, G => by
      have hpos : 0 < 2 ^ l.length := Nat.two_pow_pos _
      have step : ∀ a, ∑ c ∈ range (2 ^ l.length),
            eqN (s :: l).length 0 (Src.pt (s :: l) (vtx v b)) (a * 2 ^ l.length + c) *
              G (a * 2 ^ l.length + c) =
          (if a.testBit 0 then s.eval (vtx (E := E) v b) else 1 - s.eval (vtx (E := E) v b)) *
            G (a * 2 ^ l.length + Src.num l v b) := fun a => by
        rw [← sum_eqN_vtx v b l fun c => G (a * 2 ^ l.length + c), mul_sum]
        refine sum_congr rfl fun c hc => ?_
        have hc' := mem_range.mp hc
        have e1 : (a * 2 ^ l.length + c) / 2 ^ l.length = a := by
          rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hc', Nat.add_zero]
        have e2 : (a * 2 ^ l.length + c) % 2 ^ l.length = c := by
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hc']
        rw [eqN_cons, e1, e2, mul_assoc]
      rw [List.length_cons, pow_succ, Nat.mul_comm, Alg.sum_range_mul_add, sum_range_succ,
        sum_range_succ, sum_range_zero, zero_add]
      have s0 := step 0
      have s1 := step 1
      rw [List.length_cons] at s0 s1
      rw [s0, s1, eval_vtx]
      show _ = G ((if s.bitAt v b then 2 ^ (l.map fun s => s.bitAt v b).length else 0) +
            numL (l.map fun s => s.bitAt v b))
      rw [List.length_map]
      cases s.bitAt v b <;> simp [Src.num]

/-! ## 5. The two statements -/

theorem ofBits_vtx : Spec.ofBits_vtx := by
  intro F _ E _ _ Φ v cs rs T hk W b
  show ∑ y ∈ range Φ.h, ∑ c ∈ range (2 ^ (Φ.hi + Φ.lo)),
      (∑ r ∈ range (2 ^ rs.length), eqN rs.length 0 (Src.pt rs (vtx v b)) r * T r y) *
        eqN (Φ.hi + Φ.lo) 0 (Src.pt cs (vtx v b)) c * algebraMap F E (W y c) = _
  refine sum_congr rfl fun y _ => ?_
  rw [sum_eqN_vtx v b rs fun r => T r y, ← hk,
    ← sum_eqN_vtx v b cs fun c => T (Src.num rs v b) y * algebraMap F E (W y c)]
  exact sum_congr rfl fun c _ => by ring

theorem ofBits_ok : Spec.ofBits_ok := by
  intro F _ E _ _ Φ v cs rs T hk hOK W q
  obtain ⟨hnd, hlt⟩ := hOK
  rw [vars_append] at hnd hlt
  have hnd' := List.nodup_append.1 hnd
  have haff : ∀ u < v, AffIn (fun q => (ofBits cs rs T).at Φ W q) u := by
    intro u _
    show AffIn
      (fun q =>
        ∑ y ∈ range Φ.h, ∑ c ∈ range (2 ^ (Φ.hi + Φ.lo)),
          (∑ r ∈ range (2 ^ rs.length), eqN rs.length 0 (Src.pt rs q) r * T r y) *
            eqN (Φ.hi + Φ.lo) 0 (Src.pt cs q) c * algebraMap F E (W y c)) u
    refine AffIn.sum _ fun y _ => AffIn.sum _ fun c _ => AffIn.mul_indep ?_ (indep_const _ u)
    rw [← hk]
    by_cases hu : u ∈ Src.vars cs
    · exact AffIn.indep_mul
        (Indep.sum _ fun r _ =>
          (indep_eqN rs r fun hr => hnd'.2.2 u hu u hr rfl).mul (indep_const _ u))
        (affIn_eqN u cs c hnd'.1)
    · exact AffIn.mul_indep
        (AffIn.sum _ fun r _ => (affIn_eqN u rs r hnd'.2.1).mul_indep (indep_const _ u))
        (indep_eqN cs c hu)
  refine Eq.trans (sum_congr rfl fun X _ => ?_) (ext_glue v _ haff q)
  have e1 : Src.pt cs (glue v (vtx v X) q) = Src.pt cs (vtx v X) :=
    Src.pt_congr cs fun u hu => if_pos (hlt u (List.mem_append_left _ hu))
  have e2 : Src.pt rs (glue v (vtx v X) q) = Src.pt rs (vtx v X) :=
    Src.pt_congr rs fun u hu => if_pos (hlt u (List.mem_append_right _ hu))
  show _ * Φ.form
        (fun y => ∑ r ∈ range (2 ^ rs.length), eqN rs.length 0 (Src.pt rs (vtx v X)) r * T r y)
        (Src.pt cs (vtx v X)) W =
    _ * Φ.form (fun y =>
          ∑ r ∈ range (2 ^ rs.length), eqN rs.length 0 (Src.pt rs (glue v (vtx v X) q)) r * T r y)
        (Src.pt cs (glue v (vtx v X) q)) W
  rw [e1, e2]

end Cm
