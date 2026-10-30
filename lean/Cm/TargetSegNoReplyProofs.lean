-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegNoReplyProofs.lean: the statements of Cm/TargetSegNoReply.lean, proved.

`sameS S x x'`, defined there: all coefficient tables (`Term.coef`, Cb/Req/ReqSpec.lean) of the
segment S are the same at the instances x and x' (`sameT`, `sameA`, `sameF`: the same of terms, an
atom, a family). `segM s k` (Cm/TargetSegModel.lean): segment k of the model at the table s of
scales; 24 is the last.

Main names, for every s:
  `no_reply`: for k < 24 and requests x, x' with the same prompt, `sameS (segM s k) x x'`.
  `no_instance`: the same for 1 ≤ k < 24 and all requests x, x'.
  `reply_read`, a guard: the last segment does not have the property: two requests with the same
    prompt and the same range exist at which `sameS (segM s 24)` fails. (The guard at the requests
    with e = 0, y = 0 and y = 1.)

Section 1, the kit: on expressions (Cm/SegHeadExp.lean: `Mono`, `Ex`, `Ex1`), affine families
(Cm/SegAlg.lean: `affFam`) and families of degree two (Cm/SegFFCellKit.lean: `QSpec`).
Section 2, the first segments (even k < 24): the 34 families of keys (22 affine, 5 of degree two, 7
with a matrix product) and the identities have tables that do not read the instance at all; the
embedding's identity (group 0, that is k = 0) reads tok x.
Section 3, the second segments (odd k): 7 families of keys, 12 of identities: the same.

Limits: what the head of Cm/TargetSegNoReply.lean lists as not said is not said here either (among
other things the honest prover's cells, and protocols).
-/
import Cm.TargetSegNoReply

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All Finset
open Cm.Seg.Ex

/-! ## 1. The kit -/

section Kit
variable {X E α : Type} [Field E] {x x' : X}

/-- all monomials have the same coefficient table at x and x' -/
def SameC (p : Ex X E α) (x x' : X) : Prop := ∀ m ∈ p.lst, ∀ b, m.coef x b = m.coef x' b

theorem SameC.zero : SameC (Ex.zero : Ex X E α) x x' := fun _ h => absurd h List.not_mem_nil
theorem SameC.pub {c : X → ℕ → E} (h : ∀ b, c x b = c x' b) :
    SameC (Ex.pub c : Ex X E α) x x' := fun m hm b => by
  have hm' : m ∈ [(⟨c, []⟩ : Mono X E α)] := hm
  rw [List.mem_singleton] at hm'
  subst hm'
  exact h b
theorem SameC.con (k : E) : SameC (Ex.con k : Ex X E α) x x' := SameC.pub fun _ => rfl
theorem SameC.one (a : α) : SameC (Ex.one a : Ex X E α) x x' := fun m hm b => by
  have hm' : m ∈ [(⟨fun _ _ => 1, [a]⟩ : Mono X E α)] := hm
  rw [List.mem_singleton] at hm'
  subst hm'
  rfl
theorem SameC.add {p q : Ex X E α} (hp : SameC p x x') (hq : SameC q x x') :
    SameC (p + q) x x' := fun m hm => by
  rcases List.mem_append.1 (show m ∈ p.lst ++ q.lst from hm) with h | h
  · exact hp m h
  · exact hq m h
theorem SameC.sc {c : X → ℕ → E} (hc : ∀ b, c x b = c x' b) {p : Ex X E α} (hp : SameC p x x') :
    SameC (Ex.sc c p) x x' := fun m hm b => by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1
    (show m ∈ List.map (fun m => (⟨fun x b => c x b * m.coef x b, m.atoms⟩ : Mono X E α)) p.lst
      from hm)
  show c x b * n.coef x b = c x' b * n.coef x' b
  rw [hc b, hp n hn b]
theorem SameC.smul (k : E) {p : Ex X E α} (hp : SameC p x x') : SameC (k • p) x x' :=
  SameC.sc (x := x) (x' := x') (c := fun _ _ => k) (fun _ => rfl) hp
theorem SameC.sub {p q : Ex X E α} (hp : SameC p x x') (hq : SameC q x x') : SameC (p - q) x x' :=
  SameC.add hp (SameC.sc (x := x) (x' := x') (c := fun _ _ => (-1 : E)) (fun _ => rfl) hq)
theorem SameC.mul {p q : Ex X E α} (hp : SameC p x x') (hq : SameC q x x') :
    SameC (p * q) x x' := fun m hm b => by
  obtain ⟨m1, h1, hm⟩ := List.mem_flatMap.1
    (show m ∈ List.flatMap
        (fun m =>
          List.map
            (fun n => (⟨fun x b => m.coef x b * n.coef x b, m.atoms ++ n.atoms⟩ : Mono X E α))
            q.lst) p.lst from hm)
  obtain ⟨m2, h2, rfl⟩ := List.mem_map.1 hm
  show m1.coef x b * m2.coef x b = m1.coef x' b * m2.coef x' b
  rw [hp m1 h1 b, hq m2 h2 b]
theorem SameC.pSum {n : ℕ} {f : ℕ → Ex X E α} (h : ∀ k < n, SameC (f k) x x') :
    SameC (Ex.pSum n f) x x' := by
  induction n with
  | zero => exact SameC.zero
  | succ n ih =>
    exact SameC.add (ih fun k hk => h k (Nat.lt_succ_of_lt hk)) (h n (Nat.lt_succ_self n))

/-- Each compiled term has the coefficient table of one of the monomials. -/
theorem coef_termsFrom (o : ℕ) (p : List (Mono X E α)) :
    ∀ t ∈ Ex.termsFrom o p, ∃ m ∈ p, t.coef = m.coef := by
  induction p generalizing o with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons m p ih =>
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ⟨m, List.mem_cons_self .., rfl⟩
    · obtain ⟨n, hn, e⟩ := ih _ t ht
      exact ⟨n, List.mem_cons_of_mem _ hn, e⟩

theorem sameT_terms {p : Ex X E α} (h : SameC p x x') : sameT (Ex.terms p) x x' := fun t ht b => by
  obtain ⟨m, hm, e⟩ := coef_termsFrom 0 p t ht
  rw [e]
  exact h m hm b

end Kit

section Kit1
variable {X E : Type} [Field E] {x x' : X}

theorem sameA_sum {v w : ℕ} {p : Ex0 X E} (h : SameC p x x') :
    sameA (Atom.sum w (Ex0.poly v p) : Atom X E) x x' := sameT_terms h

/-- an expression of the upper level (`Ex1`): its own tables, and those under its sum atoms -/
def Same1 (p : Ex1 X E) (x x' : X) : Prop := SameC p x x' ∧ Ex.All (fun a => sameA a x x') p

theorem Same1.zero : Same1 (Ex.zero : Ex1 X E) x x' := ⟨SameC.zero, All.zero⟩
theorem Same1.con (k : E) : Same1 (Ex.con k : Ex1 X E) x x' := ⟨SameC.con k, All.con k⟩
theorem Same1.aff (f : ℕ → CForm E) : Same1 (aff f : Ex1 X E) x x' := ⟨SameC.one _, All.one trivial⟩
theorem Same1.sumA {v w : ℕ} {p : Ex0 X E} (h : SameC p x x') : Same1 (sumA v w p) x x' :=
  ⟨SameC.one _, All.one (sameA_sum h)⟩
theorem Same1.add {p q : Ex1 X E} (hp : Same1 p x x') (hq : Same1 q x x') : Same1 (p + q) x x' :=
  ⟨hp.1.add hq.1, All.add hp.2 hq.2⟩
theorem Same1.sub {p q : Ex1 X E} (hp : Same1 p x x') (hq : Same1 q x x') : Same1 (p - q) x x' :=
  ⟨hp.1.sub hq.1, All.sub hp.2 hq.2⟩
theorem Same1.mul {p q : Ex1 X E} (hp : Same1 p x x') (hq : Same1 q x x') : Same1 (p * q) x x' :=
  ⟨hp.1.mul hq.1, All.mul hp.2 hq.2⟩
theorem Same1.smul (k : E) {p : Ex1 X E} (hp : Same1 p x x') : Same1 (k • p) x x' :=
  ⟨hp.1.smul k, All.smul k hp.2⟩
theorem Same1.sc {c : X → ℕ → E} (hc : ∀ b, c x b = c x' b) {p : Ex1 X E} (hp : Same1 p x x') :
    Same1 (Ex.sc c p) x x' :=
  ⟨hp.1.sc hc, All.sc c hp.2⟩

/-- the compiled family -/
theorem sameF_fam1 {v : ℕ} {p : Ex1 X E} (h : Same1 p x x') : sameF (Ex1.fam v p) x x' :=
  ⟨sameT_terms h.1, Ex.atomAt_all _ h.2⟩

/-- an affine family, at any x and x' -/
theorem sameF_aff (v : ℕ) (f : ℕ → CForm E) : sameF (affFam v f : Fam X E) x x' := by
  refine ⟨fun t ht b => ?_, fun j _ => ?_⟩
  · rcases List.mem_singleton.1 ht with rfl
    rfl
  · show sameA (([Atom.base (.cell f)] : List (Atom X E)).getD j (.base (.cell fun _ => cK 0))) x x'
    rcases j with _ | j
    · trivial
    · trivial

/-- a family of degree two in cells, if its tables `S.κ` are the same at x and x' -/
theorem sameF_quad (S : QSpec X E) (h : ∀ n b, S.κ n x b = S.κ n x' b) : sameF S.fam x x' := by
  refine ⟨fun t ht b => ?_, fun j _ => ?_⟩
  · have ht' : t ∈
        (⟨fun _ _ => 1, [0]⟩ : Term X E) :: ⟨fun _ _ => 1, [1]⟩ ::
          (List.range S.nQ).map fun n => (⟨fun _ _ => 1, [2 * n + 2, 2 * n + 3]⟩ : Term X E) := ht
    rcases List.mem_cons.1 ht' with rfl | ht'
    · rfl
    rcases List.mem_cons.1 ht' with rfl | ht'
    · rfl
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 ht'
    rfl
  · show sameA
      (if j = 0 then .sum S.w S.inner
        else if j = 1 then .base (.cell S.a)
        else .base (.cell (if j % 2 = 0 then S.f ((j - 2) / 2) else S.g ((j - 2) / 2))))
      x x'
    by_cases h0 : j = 0
    · rw [if_pos h0]
      intro t ht b
      obtain ⟨n, _, rfl⟩ := List.mem_map.1
        (show t ∈ (List.range S.nS).map fun n => (⟨S.κ n, [2 * n, 2 * n + 1]⟩ : Term X E) from ht)
      exact h n b
    · rw [if_neg h0]
      by_cases h1 : j = 1
      · rw [if_pos h1]
        trivial
      · rw [if_neg h1]
        trivial

theorem SameC.cellsE (vx w : ℕ) :
    ∀ fs : List (ℕ → ℕ → ℕ → ℕ → CForm E), SameC (cellsE (X := X) vx w fs) x x'
  | [] => SameC.con 1
  | _ :: l => SameC.mul (SameC.one _) (SameC.cellsE vx w l)

theorem Same1.blk (vx w n : ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℕ → E)
    (fs : List (ℕ → ℕ → ℕ → ℕ → CForm E)) (ia : ℕ → IdxAtom E) :
    Same1 (blk (X := X) vx w n c fs ia) x x' :=
  Same1.sumA (SameC.pSum fun k _ =>
    SameC.sc (x := x) (x' := x') (c := fun _ B => at4 vx w (c k) B) (fun _ => rfl)
      (SameC.mul (SameC.cellsE vx w fs) (SameC.one _)))

theorem SameC.exProd {f : ℕ → Ex0 X E} : ∀ n, (∀ k < n, SameC (f k) x x') → SameC (exProd n f) x x'
  | 0, _ => SameC.con 1
  | n + 1, h =>
    SameC.mul (SameC.exProd n fun k hk => h k (Nat.lt_succ_of_lt hk)) (h n (Nat.lt_succ_self n))

end Kit1

/-! ## 2. The first segments -/

section FF
variable [scl : Scl] {X : Type} {x x' : X} (g : ℕ) (tb : Tables)

theorem same_wpart (s : FFSeg.Fam) : Same1 (wpart (X := X) g tb s) x x' := by
  cases s <;> first
    | exact Same1.zero
    | exact Same1.blk _ _ _ _ _ _
    | exact Same1.add (Same1.blk _ _ _ _ _ _) (Same1.blk _ _ _ _ _ _)

theorem same_kfAll (s : FFSeg.Fam) : sameF (kfAll (X := X) g tb s) x x' := by
  unfold kfAll
  split_ifs
  · exact sameF_aff _ _
  · exact sameF_quad _ fun _ _ => rfl
  · exact sameF_fam1 (Same1.add (Same1.aff _) (same_wpart g tb s))

theorem same_j11 (tok : X → ℕ → ℕ) (h : tok x = tok x') : sameF (j11Fam g tok) x x' := by
  refine ⟨fun t ht b => ?_, fun j _ => ?_⟩
  · have ht' : t ∈ [(⟨fun _ _ => 1, [0]⟩ : Term X Cb.Gl.E), ⟨fun _ _ => -1, [1]⟩] := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl <;> rfl
  · show sameA
      (([.base (.cell (a11 g)), .sum 18 (j11Inner tok)] : List (Atom X Cb.Gl.E)).getD
        j (.base (.cell fun _ => cK 0)))
      x x'
    rcases j with _ | _ | j
    · trivial
    · intro t ht b
      rcases List.mem_singleton.1 (show t ∈ [(⟨κ11 tok, [0]⟩ : Term X Cb.Gl.E)] from ht) with rfl
      show κ11 tok x b = κ11 tok x' b
      unfold κ11
      rw [h]
    · trivial

theorem same_idnFams (tok : X → ℕ → ℕ) (h : g = 0 → tok x = tok x') :
    ∀ f ∈ idnFams g tok, sameF f x x' := by
  intro f hf
  rcases (mem_idnFams g tok f).1 hf with ⟨k, _, rfl⟩ | rfl | ⟨hg, rfl⟩
  · exact sameF_quad _ fun _ _ => rfl
  · exact sameF_aff _ _
  · exact same_j11 g tok (h hg)

end FF

theorem same_ffSeg {X : Type} {x x' : X} (κ : ℕ → LayerScale) (nf : NormPar) (g : ℕ)
    (tok : X → ℕ → ℕ) (h : g = 0 → tok x = tok x') : sameS (ffSeg κ nf g tok) x x' :=
  ⟨same_idnFams (scl := SFK κ nf g) g tok h, fun k hk => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1
      (show k ∈ allFams.map fun s =>
          (kfAll (scl := SFK κ nf g) (X := X) g tbRef s,
            tabOf (FFSeg.lut tbRef (FFSeg.call s)) (tOf s)) from hk)
    exact same_kfAll (scl := SFK κ nf g) g tbRef s⟩

/-! ## 3. The second segments -/

section Att
variable [scl : Scl] {X E : Type} [Field E] [Algebra Cb.Gl.F E] {x x' : X} (g u0 : ℕ) (tb : Tables)

theorem same_attSpec : sameS (attSpec (X := X) (E := E) g u0 tb) x x' := by
  refine ⟨fun f hf => ?_, fun k hk => ?_⟩
  · rcases List.mem_append.1
      (show f ∈ (List.range DA.lT).map (famAt1 g) ++ [famAt2 g, famAt3 g] from hf) with h | h
    · obtain ⟨k, _, rfl⟩ := List.mem_map.1 h
      exact sameF_fam1 (Same1.mul (Same1.aff _) (Same1.sub (Same1.aff _) (Same1.con 1)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact sameF_fam1
          (Same1.sub (Same1.aff _)
            (Same1.sumA
              (SameC.mul (SameC.mul (SameC.one _) (SameC.one _))
                (SameC.exProd _ fun _ _ => SameC.one _))))
      · exact sameF_fam1 (Same1.sub (Same1.aff _) (Same1.sumA (SameC.one _)))
  · simp only [attSpec, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sameF_aff _ _
    · exact sameF_aff _ _
    · exact sameF_fam1
        (Same1.sub (Same1.aff _) (Same1.sumA (SameC.mul (SameC.one _) (SameC.one _))))
    · exact sameF_fam1
        (Same1.sub (Same1.aff _) (Same1.sumA (SameC.mul (SameC.one _) (SameC.one _))))
    · exact sameF_fam1
        (Same1.add
          (Same1.sc (x := x) (x' := x') (c := sg3) (fun _ => rfl)
            (Same1.sub
              (Same1.add (Same1.smul _ (Same1.sumA (SameC.mul (SameC.one _) (SameC.one _))))
                (Same1.aff _))
              (Same1.smul _ (Same1.mul (Same1.aff _) (Same1.aff _))))) (Same1.aff _))
    · exact sameF_aff _ _
    · exact sameF_aff _ _

end Att

/-! ## 4. The statements -/

theorem same_seg (s : Scales) {k : ℕ} (hk : k < 24)
    (x x' : Instance ppref) (h : k = 0 → x.prompt = x'.prompt) : sameS (segM s k) x x' := by
  rcases seg_cases
    (show k < nSeg from lt_trans hk (by show 24 < 25; norm_num)) with ⟨g,
      hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
  · show sameS (segOf s (attM s) (2 * g)) x x'
    rw [seg_ff s (attM s) hg]
    exact same_ffSeg s.kap s.nf g tokX fun hg0 => by
      show tokOf x.prompt = tokOf x'.prompt
      rw [h (by omega)]
  · show sameS (segOf s (attM s) (2 * g + 1)) x x'
    rw [seg_att s (attM s) hg]
    exact same_attSpec (scl := SFK s.kap s.nf g) g _ tbRef
  · exact absurd hk (lt_irrefl 24)

theorem no_reply : Spec.no_reply := fun s _ hk x x' h => same_seg s hk x x' fun _ => h

theorem no_instance : Spec.no_instance := fun s k h1 hk x x' =>
  same_seg s hk x x' fun h0 => absurd h0 (by omega)

theorem reply_read : Spec.reply_read := by
  intro s
  refine ⟨⟨fun _ => ⟨0, by decide⟩, ⟨0, by decide⟩, 0, 0⟩,
    ⟨fun _ => ⟨0, by decide⟩, ⟨1, by decide⟩, 0, 0⟩, rfl, rfl, rfl, fun h => ?_⟩
  have h1 := h
  unfold segM at h1
  rw [seg_head] at h1
  have h2 := (h1.1 idY (List.mem_cons_self ..)).1 _ (List.mem_singleton.2 rfl) 0
  have h3 : (if (0 : ℕ) < ppref.T then (((0 : ℕ) : ℕ) : Cb.Gl.E) else 0) =
    if (0 : ℕ) < ppref.T then (((1 : ℕ) : ℕ) : Cb.Gl.E) else 0 := h2
  rw [if_pos (by decide), if_pos (by decide), Nat.cast_zero, Nat.cast_one] at h3
  exact zero_ne_one h3

end Cm.Seg.TS
