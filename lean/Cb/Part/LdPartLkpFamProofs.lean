-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartLkpFamProofs.lean: the proofs of the statements of Cb/Part/LdPartLkpFam.lean (the key
families of a segment as the key functions of "shift ; assembled lookup"; the joint shifted key as
one family).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Named tools, on the polynomials of Cb/Part/LdPart.lean, for all index matrices over E. At all
points: `Fam.to_ext` (a well-formed family on more variables is the family at the point's last
coordinates), `Fam.reX_ext` (another type of instances). At vertices: `ldPartFam_vtx`;
`ldPartFam_mask`, `ldPartFam_pub`, `ldPartFam_add` (a public factor; a public table; side by side).
-/
import Cb.Part.LdPartLkpFam
import Cb.Part.LdPartLkpProofs
import Cb.Part.LdPartProofs
import Cb.Req.ReqGlueProofs
import Cb.Req.ReqFamTupleProofs
import Cb.Req.ReqNumsGlueProofs

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset Cb.LdLkp Cb.Lkp

/-! ## More variables; another type of instances: at all points -/

section Pts
variable {X X' F E : Type} [Field F] [Field E] [Algebra F E] (h k : ℕ)

omit [Field F] [Algebra F E] in
theorem Atom0.to_ext (a : Atom0 E) {N v : ℕ} (hv : v ≤ N) (WE : ℕ → ℕ → E)
    (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (a.to N v).ext h k N WE A q = a.ext h k v WE A (shiftPt (N - v) q) := by
  cases a with
  | cell f => exact ext_low E N v (fun b => (f b).val A) q hv
  | idx a => rfl

omit [Field F] [Algebra F E] in
theorem Term.low_ext (t : Term X E) {N v : ℕ} (hv : v ≤ N) (x : X) (q : ℕ → E)
    {Y Y' : ℕ → E} (hY : ∀ j ∈ t.atoms, Y j = Y' j) :
    (t.low v).ext N x q Y = t.ext v x (shiftPt (N - v) q) Y' := by
  show Blocks.ext N (fun b => t.coef x (b % 2 ^ v)) q * (t.atoms.map Y).prod =
    Blocks.ext v (t.coef x) (shiftPt (N - v) q) * (t.atoms.map Y').prod
  rw [ext_low E N v (t.coef x) q hv, List.map_congr_left hY]

omit [Field F] [Algebra F E] in
theorem Poly0.to_ext (P : Poly0 X E) {N : ℕ} (hv : P.v ≤ N) (x : X) (WE : ℕ → ℕ → E)
    (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (P.to N).ext h k x WE A q = P.ext h k x WE A (shiftPt (N - P.v) q) := by
  show ((P.terms.map (Term.low P.v)).map fun t =>
      t.ext N x q fun j => ((P.atom j).to N P.v).ext h k N WE A q).sum = _
  rw [List.map_map]
  unfold Poly0.ext
  exact congrArg List.sum
    (List.map_congr_left fun t _ =>
      Term.low_ext t hv x q fun j _ => Atom0.to_ext h k (P.atom j) hv WE A q)

theorem Atom.to_ext (a : Atom X E) (Φ : IdxFmt F) {N v : ℕ} (hw : a.WF Φ v) (hv : v ≤ N) (x : X)
    (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (a.to N v).ext h k N x WE A q = a.ext h k v x WE A (shiftPt (N - v) q) := by
  cases a with
  | base a => exact Atom0.to_ext h k a hv WE A q
  | sum w P =>
    have hP : P.v = v + w := hw.1
    show Blocks.ext N
        (fun b => ∑ j ∈ range (2 ^ w), (P.to (N + w)).ext h k x WE A (vtx (N + w) (b * 2 ^ w + j)))
        q =
      Blocks.ext v (fun b => ∑ j ∈ range (2 ^ w), P.ext h k x WE A (vtx (v + w) (b * 2 ^ w + j)))
        (shiftPt (N - v) q)
    rw [← ext_low E N v
        (fun b => ∑ j ∈ range (2 ^ w), P.ext h k x WE A (vtx (v + w) (b * 2 ^ w + j))) q hv]
    refine ext_congr (fun b _ => sum_congr rfl fun j hj => ?_) q
    rw [Poly0.to_ext h k P (by omega), hP, vtx_shift E (N + w) (v + w) _ (by omega),
      mod_pow_add b v w j (mem_range.1 hj)]

theorem Fam.to_ext (f : Fam X E) (Φ : IdxFmt F) {N : ℕ} (hw : f.WF Φ) (hv : f.v ≤ N) (x : X)
    (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (f.to N).ext h k x WE A q = f.ext h k x WE A (shiftPt (N - f.v) q) := by
  show ((f.terms.map (Term.low f.v)).map fun t =>
      t.ext N x q fun j => ((f.atom j).to N f.v).ext h k N x WE A q).sum = _
  rw [List.map_map]
  unfold Fam.ext
  exact congrArg List.sum
    (List.map_congr_left fun t ht =>
      Term.low_ext t hv x q fun j hj =>
        Atom.to_ext h k (f.atom j) Φ (hw.2 j (hw.1 t ht j hj)) hv x WE A q)

omit [Field F] [Algebra F E] in
theorem Poly0.reX_ext (π : X' → X) (P : Poly0 X E) (x' : X') (WE : ℕ → ℕ → E)
    (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (P.reX π).ext h k x' WE A q = P.ext h k (π x') WE A q := by
  show ((P.terms.map (Term.reX π)).map fun t =>
      t.ext P.v x' q fun j => (P.atom j).ext h k P.v WE A q).sum = _
  rw [List.map_map]
  rfl

omit [Field F] [Algebra F E] in
theorem Atom.reX_ext (π : X' → X) (a : Atom X E) (v : ℕ) (x' : X') (WE : ℕ → ℕ → E)
    (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (a.reX π).ext h k v x' WE A q = a.ext h k v (π x') WE A q := by
  cases a with
  | base a => rfl
  | sum w P =>
    show Blocks.ext v
        (fun b => ∑ j ∈ range (2 ^ w), (P.reX π).ext h k x' WE A (vtx (v + w) (b * 2 ^ w + j))) q =
      Blocks.ext v
        (fun b => ∑ j ∈ range (2 ^ w), P.ext h k (π x') WE A (vtx (v + w) (b * 2 ^ w + j))) q
    simp only [Poly0.reX_ext]

omit [Field F] [Algebra F E] in
theorem Fam.reX_ext (π : X' → X) (f : Fam X E) (x' : X') (WE : ℕ → ℕ → E)
    (A : ℕ → ℕ → ℕ → E) (q : ℕ → E) :
    (f.reX π).ext h k x' WE A q = f.ext h k (π x') WE A q := by
  show ((f.terms.map (Term.reX π)).map fun t =>
      t.ext f.v x' q fun j => ((f.atom j).reX π).ext h k f.v x' WE A q).sum = _
  rw [List.map_map]
  simp only [Atom.reX_ext]
  rfl

end Pts

/-! ## The steps, at vertices -/

section Vtx
variable {X E : Type} [Field E] (h k : ℕ) (x : X) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E)

/-- the polynomial at a vertex: the sum of terms at the atoms' values there -/
theorem ldPartFam_vtx (f : Fam X E) {b : ℕ} (hb : b < 2 ^ f.v) :
    f.ext h k x WE A (vtx f.v b) =
      (f.terms.map fun t => t.val x b fun j => (f.atom j).ext h k f.v x WE A (vtx f.v b)).sum := by
  unfold Fam.ext
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  unfold Term.ext Term.val
  rw [ext_vtx E f.v _ b hb]

theorem ldPartFam_mask (c : X → ℕ → E) (f : Fam X E) {b : ℕ} (hb : b < 2 ^ f.v) :
    (f.mask c).ext h k x WE A (vtx f.v b) = c x b * f.ext h k x WE A (vtx f.v b) := by
  refine (ldPartFam_vtx h k x WE A (f.mask c) (b := b) hb).trans ?_
  rw [ldPartFam_vtx h k x WE A f hb]
  show ((f.terms.map fun t => (⟨fun x b => c x b * t.coef x b, t.atoms⟩ : Term X E)).map
      fun t => t.val x b fun j => (f.atom j).ext h k f.v x WE A (vtx f.v b)).sum = _
  rw [List.map_map, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun t _ => mul_assoc _ _ _)

theorem ldPartFam_pub (v : ℕ) (c : X → ℕ → E) {b : ℕ} (hb : b < 2 ^ v) :
    (Fam.pub v c).ext h k x WE A (vtx v b) = c x b := by
  refine (ldPartFam_vtx h k x WE A (Fam.pub v c) (b := b) hb).trans ?_
  simp [Fam.pub, Term.val]

theorem ldPartFam_add {f g : Fam X E} (hf : ∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na) (hv : g.v = f.v)
    {b : ℕ} (hb : b < 2 ^ f.v) :
    (f.add g).ext h k x WE A (vtx f.v b) =
      f.ext h k x WE A (vtx f.v b) + g.ext h k x WE A (vtx f.v b) := by
  refine (ldPartFam_vtx h k x WE A (f.add g) (b := b) hb).trans ?_
  have hg := ldPartFam_vtx h k x WE A g (b := b) (by rw [hv]; exact hb)
  rw [hv] at hg
  rw [ldPartFam_vtx h k x WE A f hb, hg]
  show ((f.terms ++ g.terms.map fun t => (⟨t.coef, t.atoms.map (· + f.na)⟩ : Term X E)).map fun t =>
      t.val x b fun n =>
        (if n < f.na then f.atom n else g.atom (n - f.na)).ext h k f.v x WE A (vtx f.v b)).sum = _
  rw [List.map_append, List.sum_append, List.map_map]
  congr 1
  · exact congrArg List.sum
      (List.map_congr_left fun t ht =>
        Term.val_congr t x b fun j hj => by rw [if_pos (hf t ht j hj)])
  · refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    show t.coef x b *
        ((t.atoms.map (· + f.na)).map fun n =>
          (if n < f.na then f.atom n else g.atom (n - f.na)).ext h k f.v x WE A (vtx f.v b)).prod =
      t.coef x b * (t.atoms.map fun j => (g.atom j).ext h k f.v x WE A (vtx f.v b)).prod
    rw [List.map_map]
    refine congrArg (fun l => t.coef x b * List.prod l) (List.map_congr_left fun j _ => ?_)
    show (if j + f.na < f.na then f.atom (j + f.na) else g.atom (j + f.na - f.na)).ext
        h k f.v x WE A (vtx f.v b) = _
    rw [if_neg (by omega), Nat.add_sub_cancel]

end Vtx

/-! ## The joint family -/

section Key
variable {X F E : Type} [Field F] [Field E] [Algebra F E] (K : LdPartKeys X F E)

omit [Field F] [Algebra F E] in
theorem ldPartKeyUpTo_v (i : ℕ) : (K.keyUpTo i).v = K.g + K.v := by
  cases i <;> rfl

omit [Field F] [Field E] [Algebra F E] in
theorem ldPartKeys_le {f : ℕ} (hf : f < K.nk) : (K.fam f).v ≤ K.v := ldPartSz_kv K.sz hf

/-- the summand of `K.keyUpTo (i + 1)` for the family number i -/
theorem ldPartKeyPiece_wf (Φ : IdxFmt F) {i : ℕ} (hi : i < K.nk)
    (hw : (K.fam i).WF Φ) (c : X × E → ℕ → E) :
    (Fam.mask c (((K.fam i).reX Prod.fst).to (K.g + K.v))).WF Φ :=
  mask_wf Φ c
    (to_wf (X × E) F E _ Φ (K.g + K.v) (reX_wf X (X × E) F E Prod.fst (K.fam i) Φ hw)
      (le_trans (ldPartKeys_le K hi) (Nat.le_add_left _ _)))

theorem ldPartKeyUpTo_wf (Φ : IdxFmt F) : ∀ i ≤ K.nk, (∀ f < i, (K.fam f).WF Φ) → (K.keyUpTo i).WF Φ
  | 0, _, _ => pub_wf Φ _ _
  | i + 1, hi, hw =>
    add_wf Φ (ldPartKeyPiece_wf K Φ hi (hw i (Nat.lt_succ_self i)) _)
      (ldPartKeyUpTo_wf Φ i (Nat.le_of_succ_le hi) fun f hf => hw f (Nat.lt_succ_of_lt hf))
      (ldPartKeyUpTo_v K i)

theorem ldPartKeyUpTo_places (Φ : IdxFmt F) :
    ∀ i ≤ K.nk,
      (∀ f < i, (K.fam f).WF Φ) → ∀ p, p ∈ (K.keyUpTo i).places ↔ ∃ f < i, p ∈ (K.fam f).places
  | 0, _, _, p =>
    ⟨fun ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _),
      fun ⟨_, hf, _⟩ => absurd hf (Nat.not_lt_zero _)⟩
  | i + 1, hi, hw, p => by
    have h1 : p ∈ (K.keyUpTo (i + 1)).places ↔
        p ∈ (Fam.mask (fun _ b => if b / 2 ^ K.v = i then 1 else 0)
            (((K.fam i).reX Prod.fst).to (K.g + K.v))).places ∨
        p ∈ (K.keyUpTo i).places :=
      add_places (ldPartKeyUpTo_v K i) p
    have h2 : (Fam.mask (fun _ b => if b / 2 ^ K.v = i then (1 : E) else 0)
          (((K.fam i).reX (Prod.fst : X × E → X)).to (K.g + K.v))).places =
        (K.fam i).places :=
      (to_places (X × E) F E _ Φ (K.g + K.v)
          (reX_wf X (X × E) F E Prod.fst (K.fam i) Φ (hw i (Nat.lt_succ_self i)))
          (le_trans (ldPartKeys_le K hi) (Nat.le_add_left _ _))).trans
        (reX_places X (X × E) E Prod.fst (K.fam i))
    rw [h1, h2,
      ldPartKeyUpTo_places Φ i (Nat.le_of_succ_le hi) (fun f hf => hw f (Nat.lt_succ_of_lt hf)) p]
    constructor
    · rintro (hp | ⟨f, hf, hp⟩)
      · exact ⟨i, Nat.lt_succ_self i, hp⟩
      · exact ⟨f, Nat.lt_succ_of_lt hf, hp⟩
    · rintro ⟨f, hf, hp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf' | rfl
      · exact Or.inr ⟨f, hf', hp⟩
      · exact Or.inl hp

omit [Field F] [Algebra F E] in
theorem ldPartKeyUpTo_deg (d : ℕ) : ∀ i, (∀ f < i, (K.fam f).DegLe d) → (K.keyUpTo i).DegLe d
  | 0, _ => Req.degLe_pub (X × E) E _ _ d
  | i + 1, hw =>
    Req.degLe_add (X × E) E _ _ d
      (Req.degLe_mask (X × E) E _ _ d
        (Req.degLe_to (X × E) E _ _ d
          (degLe_reX X (X × E) E Prod.fst (K.fam i) d (hw i (Nat.lt_succ_self i)))))
      (ldPartKeyUpTo_deg d i fun f hf => hw f (Nat.lt_succ_of_lt hf))

/-- the induction: the public part, and the family whose number the leading bits write if that is
below i -/
theorem ldPartKeyUpTo_vtx (Φ : IdxFmt F) (h k : ℕ) (x : X) (θ : E) (WE : ℕ → ℕ → E)
    (A : ℕ → ℕ → ℕ → E) {b : ℕ} (hb : b < 2 ^ (K.g + K.v)) :
    ∀ i ≤ K.nk, (∀ f < i, (K.fam f).WF Φ) →
      (K.keyUpTo i).ext h k (x, θ) WE A (vtx (K.g + K.v) b) =
        (if b / 2 ^ K.v < i then
              (K.fam (b / 2 ^ K.v)).ext h k x WE A
                (vtx (K.fam (b / 2 ^ K.v)).v (b % 2 ^ (K.fam (b / 2 ^ K.v)).v))
            else 0) +
          ((b / 2 ^ K.v : ℕ) : E) * θ
  | 0, _, _ => by
    rw [if_neg (Nat.not_lt_zero _), zero_add]
    exact ldPartFam_pub h k (x, θ) WE A (K.g + K.v) _ hb
  | i + 1, hi, hw => by
    have hle : (K.fam i).v ≤ K.g + K.v := le_trans (ldPartKeys_le K hi) (Nat.le_add_left _ _)
    have hwi := reX_wf X (X × E) F E Prod.fst (K.fam i) Φ (hw i (Nat.lt_succ_self i))
    have e0 : (K.keyUpTo (i + 1)).ext h k (x, θ) WE A (vtx (K.g + K.v) b) =
        (Fam.mask (fun _ b => if b / 2 ^ K.v = i then 1 else 0)
              (((K.fam i).reX Prod.fst).to (K.g + K.v))).ext
            h k (x, θ) WE A (vtx (K.g + K.v) b) +
          (K.keyUpTo i).ext h k (x, θ) WE A (vtx (K.g + K.v) b) :=
      ldPartFam_add h k (x, θ) WE A
        (f := Fam.mask (fun _ b => if b / 2 ^ K.v = i then 1 else 0)
            (((K.fam i).reX Prod.fst).to (K.g + K.v)))
        (g := K.keyUpTo i) (ldPartKeyPiece_wf K Φ hi (hw i (Nat.lt_succ_self i)) _).1
        (ldPartKeyUpTo_v K i) (b := b) hb
    have e1 : (Fam.mask (fun _ b => if b / 2 ^ K.v = i then 1 else 0)
            (((K.fam i).reX Prod.fst).to (K.g + K.v))).ext
          h k (x, θ) WE A (vtx (K.g + K.v) b) =
        (if b / 2 ^ K.v = i then 1 else 0) *
          (((K.fam i).reX Prod.fst).to (K.g + K.v)).ext h k (x, θ) WE A (vtx (K.g + K.v) b) :=
      ldPartFam_mask h k (x, θ) WE A (fun _ b => if b / 2 ^ K.v = i then 1 else 0)
        (((K.fam i).reX Prod.fst).to (K.g + K.v)) (b := b) hb
    have e2 : (((K.fam i).reX Prod.fst).to (K.g + K.v)).ext h k (x, θ) WE A (vtx (K.g + K.v) b) =
        (K.fam i).ext h k x WE A (vtx (K.fam i).v (b % 2 ^ (K.fam i).v)) := by
      rw [Fam.to_ext h k _ Φ hwi hle, Fam.reX_ext]
      show (K.fam i).ext h k x WE A (shiftPt (K.g + K.v - (K.fam i).v) (vtx (K.g + K.v) b)) = _
      rw [vtx_shift E (K.g + K.v) (K.fam i).v b hle]
    have e3 := ldPartKeyUpTo_vtx Φ h k x θ WE A hb i (Nat.le_of_succ_le hi) fun f hf =>
      hw f (Nat.lt_succ_of_lt hf)
    refine e0.trans ?_
    rw [e1, e2, e3]
    by_cases hc : b / 2 ^ K.v = i
    · rw [if_pos hc, if_neg (by omega), if_pos (by omega), hc]
      ring
    · rw [if_neg hc]
      by_cases hc' : b / 2 ^ K.v < i
      · rw [if_pos hc', if_pos (by omega)]
        ring
      · rw [if_neg hc', if_neg (by omega)]
        ring

end Key

theorem ldPartKeyFam_v : Spec.ldPartKeyFam_v := fun _ _ _ _ _ _ _ _ K _ _ _ _ =>
  ⟨ldPartKeyUpTo_v K K.nk, rfl, rfl⟩

theorem ldPartKeyFam_wf : Spec.ldPartKeyFam_wf := fun _ _ _ _ _ _ K Φ hw =>
  ldPartKeyUpTo_wf K Φ K.nk (le_refl _) hw

theorem ldPartKeyFam_deg : Spec.ldPartKeyFam_deg := fun _ _ _ _ _ _ K d hw =>
  ldPartKeyUpTo_deg K d K.nk hw

theorem ldPartKeyFam_places : Spec.ldPartKeyFam_places := fun _ _ _ _ _ _ K Φ hw =>
  ldPartKeyUpTo_places K Φ K.nk (le_refl _) hw

theorem ldPartKeyFam_vtx : Spec.ldPartKeyFam_vtx := by
  intro X F E St J _ _ _ K Φ h k R xs st m θ hw b hb
  refine (ldPartKeyUpTo_vtx K Φ h k (xs st) θ (R.W m) (R.A m) hb K.nk (le_refl _) hw).trans ?_
  show _ = (if b / 2 ^ K.v < K.nk then
          (K.fam (b / 2 ^ K.v)).ext h k (xs st) (R.W m) (R.A m)
            (vtx (K.fam (b / 2 ^ K.v)).v (b % 2 ^ K.v % 2 ^ (K.fam (b / 2 ^ K.v)).v))
        else 0) +
      ((b / 2 ^ K.v : ℕ) : E) * θ
  by_cases hc : b / 2 ^ K.v < K.nk
  · rw [if_pos hc, if_pos hc, Nat.mod_mod_of_dvd b (pow_dvd_pow 2 (ldPartKeys_le K hc))]
  · rw [if_neg hc, if_neg hc]

theorem ldPartKeys_holds : Spec.ldPartKeys_holds := by
  intro X F E St J _ _ _ l Φ R xs st m W hw hW
  have hfam : ∀ f (hf : f < l.length), (LdPartKeys.ofList l).fam f = l[f].1 := fun f hf => by
    show (l.getD f _).1 = _
    rw [List.getD_eq_getElem _ _ hf]
  have htb : ∀ f (hf : f < l.length), (LdPartKeys.ofList l).tb f = l[f].2 := fun f hf => by
    show (l.getD f _).2 = _
    rw [List.getD_eq_getElem _ _ hf]
  rw [ldPartLk_inC E St J]
  have hkey : ∀ f (hf : f < l.length), ∀ b < 2 ^ l[f].1.v,
      l[f].1.ext Φ.h (Φ.hi + Φ.lo) (xs st) (R.W m) (R.A m) (vtx l[f].1.v b) =
        l[f].1.val Φ (xs st) W (R.A m) b := fun f hf b hb => by
    rw [hW]
    exact ldPart_vtxF Φ (xs st) W (R.A m) l[f].1 b (hw _ (List.getElem_mem hf)) hb
  constructor
  · intro H q hq b hb
    obtain ⟨f, hf, rfl⟩ := List.getElem_of_mem hq
    have H1 : InTable ((LdPartKeys.ofList l).fam f).v ((LdPartKeys.ofList l).tb f).T
        (fun b =>
          ((LdPartKeys.ofList l).fam f).ext
            Φ.h (Φ.hi + Φ.lo) (xs st) (R.W m) (R.A m) (vtx ((LdPartKeys.ofList l).fam f).v b))
        (fun u => algebraMap F E (((LdPartKeys.ofList l).tb f).t u)) := H f hf
    rw [hfam f hf, htb f hf] at H1
    obtain ⟨u, hu, he⟩ := H1 b hb
    exact ⟨_, ⟨u, hu, rfl⟩, (hkey f hf b hb).symm.trans he⟩
  · intro H f hf
    show InTable ((LdPartKeys.ofList l).fam f).v ((LdPartKeys.ofList l).tb f).T
      (fun b =>
        ((LdPartKeys.ofList l).fam f).ext
          Φ.h (Φ.hi + Φ.lo) (xs st) (R.W m) (R.A m) (vtx ((LdPartKeys.ofList l).fam f).v b))
      (fun u => algebraMap F E (((LdPartKeys.ofList l).tb f).t u))
    rw [hfam f hf, htb f hf]
    intro b hb
    obtain ⟨_, ⟨u, hu, rfl⟩, he⟩ := H _ (List.getElem_mem hf) b hb
    exact ⟨u, hu, (hkey f hf b hb).trans he⟩

end Cb
