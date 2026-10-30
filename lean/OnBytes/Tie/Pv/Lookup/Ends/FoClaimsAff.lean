-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoClaimsAff.lean.
The lookup's claims are affine in the entries: one list of forms for all values of the entries.

The flat list of a lookup's claims (Fo.claimsOf; Fo.claimsZ in the order of the smallness test)
reads the entries of the committed messages and of the mask row through a reading ν of the lookup's
places, through the columns' sums of the lookup's cells, and through the calls' key forms.

States:
  AffIn v: the function v of the entries' values is the value of one form (Fo.AffK): a list of
    (entry, coefficient) pairs and a constant. affIn_const, _coord, _add, _sub, _mulL, _mulR, _zext,
    _sum, _evalL, _val, _foldl: the rules.
  affIn_list: a list of such functions is, for all values of the entries, the list of the values of
    one list of forms.
  affIn_rowRes, affIn_colsK, affIn_pinColK, affIn_planesK, affIn_countK, affIn_leaves, affIn_bits,
    affIn_join: each kind of member, where ν reads place p as the entry placeOf mk pl p, or as 0
    where that is none, and call c's key vector enters as the value of a form KF c on the entries.
  claimsZ_forms: there is one list of forms on the entries whose values are Fo.claimsZ, for all
    values of the entries. The forms are found before the entries' values: they can hang on the
    shape, lm, the first slot, the rounds, the two maps of places and the key forms alone.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed which the coefficients are.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model Cb.Fo Cb.LdLkp Finset

section
variable {K J₀ : Type} [CommRing K]

/-- The function of the entries' values is the value of one form. -/
def AffIn (v : (J₀ → K) → K) : Prop := ∃ f : AffK J₀ K, ∀ μ, v μ = AffK.val f μ

theorem affIn_const (a : K) : AffIn (fun _ : J₀ → K => a) :=
  ⟨AffK.ofConst a, fun μ => (AffK.val_ofConst a μ).symm⟩

theorem affIn_coord (j : J₀) : AffIn (fun μ : J₀ → K => μ j) :=
  ⟨([(j, 1)], 0), fun μ => by simp [AffK.val]⟩

theorem affIn_add {u v : (J₀ → K) → K} (hu : AffIn u) (hv : AffIn v) :
    AffIn fun μ => u μ + v μ := by
  obtain ⟨f, hf⟩ := hu
  obtain ⟨g, hg⟩ := hv
  exact ⟨AffK.add f g, fun μ => by
    show u μ + v μ = _
    rw [AffK.val_add, hf, hg]⟩

theorem affIn_mulL (a : K) {v : (J₀ → K) → K} (hv : AffIn v) : AffIn fun μ => a * v μ := by
  obtain ⟨g, hg⟩ := hv
  exact ⟨AffK.smul a g, fun μ => by
    show a * v μ = _
    rw [AffK.val_smul, hg]⟩

theorem affIn_mulR (a : K) {v : (J₀ → K) → K} (hv : AffIn v) : AffIn fun μ => v μ * a := by
  have := affIn_mulL a hv
  simpa only [mul_comm] using this

theorem affIn_sub {u v : (J₀ → K) → K} (hu : AffIn u) (hv : AffIn v) :
    AffIn fun μ => u μ - v μ := by
  have := affIn_add hu (affIn_mulL (-1) hv)
  simpa only [neg_mul, one_mul, ← sub_eq_add_neg] using this

theorem affIn_zext (o : Option J₀) : AffIn (fun μ : J₀ → K => zext μ o) := by
  cases o with
  | none => exact affIn_const 0
  | some j => exact affIn_coord j

theorem affIn_sum {ι : Type} (s : Finset ι) (v : ι → (J₀ → K) → K) (h : ∀ i, AffIn (v i)) :
    AffIn fun μ => ∑ i ∈ s, v i μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using affIn_const (J₀ := J₀) (0 : K)
  | insert a s ha ih =>
    have := affIn_add (h a) ih
    simpa only [Finset.sum_insert ha] using this

theorem affIn_listSum {ι : Type} (v : ι → (J₀ → K) → K) (h : ∀ i, AffIn (v i)) :
    ∀ l : List ι, AffIn fun μ => (l.map fun i => v i μ).sum
  | [] => by simpa using affIn_const (J₀ := J₀) (0 : K)
  | a :: l => by
    have := affIn_add (h a) (affIn_listSum v h l)
    simpa only [List.map_cons, List.sum_cons] using this

theorem affIn_foldl {ι : Type} (v : ι → (J₀ → K) → K) (h : ∀ i, AffIn (v i)) :
    ∀ (l : List ι) (a : (J₀ → K) → K), AffIn a →
      AffIn fun μ => l.foldl (fun f i => f + v i μ) (a μ)
  | [], _, ha => ha
  | i :: l, a, ha => affIn_foldl v h l (fun μ => a μ + v i μ) (affIn_add ha (h i))

/-- A sparse form on any places, each read as an affine function of the entries. -/
theorem affIn_evalL {P : Type} (ν : (J₀ → K) → P → K) (h : ∀ p, AffIn fun μ => ν μ p)
    (l : List (P × K)) : AffIn fun μ => evalL (ν μ) l :=
  affIn_listSum (fun (pc : P × K) μ => pc.2 * ν μ pc.1) (fun pc => affIn_mulL pc.2 (h pc.1)) l

theorem affIn_val {P : Type} (ν : (J₀ → K) → P → K) (h : ∀ p, AffIn fun μ => ν μ p)
    (f : AffK P K) : AffIn fun μ => AffK.val f (ν μ) :=
  affIn_add (affIn_evalL ν h f.1) (affIn_const f.2)

/-- A list of such functions is the list of the values of one list of forms. -/
theorem affIn_list : ∀ l : List ((J₀ → K) → K), (∀ v ∈ l, AffIn v) →
    ∃ forms : List (AffK J₀ K), ∀ μ, (l.map fun v => v μ) = forms.map fun f => AffK.val f μ
  | [], _ => ⟨[], fun _ => rfl⟩
  | v :: l, h => by
    obtain ⟨f, hf⟩ := h v List.mem_cons_self
    obtain ⟨fs, hfs⟩ := affIn_list l fun u hu => h u (List.mem_cons_of_mem v hu)
    exact ⟨f :: fs, fun μ => by rw [List.map_cons, List.map_cons, hf, hfs]⟩

variable (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀)

/-- The reading of the lookup's places off the entries. -/
def nuAt (μ : J₀ → K) : Pl → K := fun p => zext μ (NumsEq.placeOf mk pl p)

theorem affIn_nu (p : Pl) : AffIn fun μ : J₀ → K => nuAt mk pl μ p := affIn_zext _

theorem affIn_rowRes (r : SRow Pl K) : AffIn fun μ : J₀ → K => rowRes (nuAt mk pl μ) r :=
  affIn_sub (affIn_evalL _ (affIn_nu mk pl) r.cf) (affIn_const r.tg)

theorem affIn_colsK (h : FoNums.Sh) (lm : ℕ) (z : List K) (col : ℕ) :
    AffIn fun μ : J₀ → K => colsK h lm z (nuAt mk pl μ) col :=
  affIn_sum _ _ fun _ => affIn_mulL _ (affIn_nu mk pl _)

theorem affIn_pinColK (lm col : ℕ) : AffIn fun μ : J₀ → K => Pin.pinColK lm (nuAt mk pl μ) col :=
  affIn_sum _ _ fun _ => affIn_mulL _ (affIn_nu mk pl _)

omit mk pl in
theorem affIn_planesK (h : FoNums.Sh) (lm : ℕ) (z : List K) (bit : (J₀ → K) → ℕ → K)
    (hb : ∀ col, AffIn fun μ => bit μ col) : AffIn fun μ => planesK h lm z (bit μ) :=
  affIn_foldl (fun col μ => bit μ col *
      ((eqTabK (exL z h.kT (h.kT + h.cK))).getD (col / 2 ^ (h.kT + 5 - lm)) 0 *
        (eqTabK (exL z 0 (h.kT + 5 - lm))).getD (col % 2 ^ (h.kT + 5 - lm)) 0))
    (fun col => affIn_mulR _ (hb col)) _ _ (affIn_const 0)

omit mk pl in
theorem affIn_countK (h : FoNums.Sh) (lm : ℕ) (pin : (J₀ → K) → ℕ → K)
    (hp : ∀ col, AffIn fun μ => pin μ col) : AffIn fun μ => Pin.countK h lm (pin μ) :=
  affIn_foldl (fun col μ => pin μ col) hp _ _ (affIn_const _)

theorem affIn_leaves (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (bit : (J₀ → K) → ℕ → K)
    (hb : ∀ col, AffIn fun μ => bit μ col) :
    AffIn fun μ => claimLeaves h lm jLK rs (nuAt mk pl μ) (bit μ) :=
  affIn_sub (affIn_add (affIn_add (affIn_evalL _ (affIn_nu mk pl) _)
    (affIn_mulL _ (affIn_evalL _ (affIn_nu mk pl) _)))
    (affIn_mulL _ (affIn_mulL _ (affIn_planesK h lm _ bit hb)))) (affIn_const _)

theorem affIn_bits (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (bit : (J₀ → K) → ℕ → K)
    (hb : ∀ col, AffIn fun μ => bit μ col) :
    AffIn fun μ => claimBits h lm jLK rs (nuAt mk pl μ) (bit μ) :=
  affIn_sub (affIn_sub (affIn_const _) (affIn_mulL _ (affIn_nu mk pl _)))
    (affIn_planesK h lm _ bit hb)

theorem affIn_join (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (kf : (J₀ → K) → ℕ → K)
    (hk : ∀ c, AffIn fun μ => kf μ c) :
    AffIn fun μ => claimJoin h lm jLK rs (nuAt mk pl μ) (kf μ) := by
  unfold claimJoin
  simp only [val_joinK, AffK.val_ofConst]
  exact affIn_sub (affIn_add (affIn_sum _ _ fun c => affIn_mulL _
    (affIn_sub (affIn_const _) (hk c))) (affIn_const _)) (affIn_val _ (affIn_nu mk pl) _)

/-- One list of forms on the entries for the lookup's claims. -/
theorem claimsZ_forms (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K)
    (KF : ℕ → AffK (Option J₀) K) :
    ∃ forms : List (AffK J₀ K), ∀ μ : J₀ → K,
      claimsZ h lm jLK rs (nuAt mk pl μ) (colsK h lm (endsOf h lm jLK rs).zb0 (nuAt mk pl μ))
        (colsK h lm (endsOf h lm jLK rs).zb1 (nuAt mk pl μ)) (Pin.pinColK lm (nuAt mk pl μ))
        (fun c => AffK.val (KF c) (zext μ)) = forms.map fun f => AffK.val f μ := by
  obtain ⟨forms, hf⟩ := affIn_list
    (((endsOf h lm jLK rs).rows.map fun r (μ : J₀ → K) => rowRes (nuAt mk pl μ) r) ++
      [fun μ => claimJoin h lm jLK rs (nuAt mk pl μ) (fun c => AffK.val (KF c) (zext μ)),
        fun μ => claimLeaves h lm jLK rs (nuAt mk pl μ)
          (colsK h lm (endsOf h lm jLK rs).zb0 (nuAt mk pl μ)),
        fun μ => claimBits h lm jLK rs (nuAt mk pl μ)
          (colsK h lm (endsOf h lm jLK rs).zb1 (nuAt mk pl μ)),
        fun μ => Pin.countK h lm (Pin.pinColK lm (nuAt mk pl μ))]) (by
      intro v hv
      rw [List.mem_append] at hv
      rcases hv with hv | hv
      · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hv
        exact affIn_rowRes mk pl r
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact affIn_join mk pl h lm jLK rs _ fun c => affIn_val _ affIn_zext (KF c)
        · exact affIn_leaves mk pl h lm jLK rs _ fun col => affIn_colsK mk pl h lm _ col
        · exact affIn_bits mk pl h lm jLK rs _ fun col => affIn_colsK mk pl h lm _ col
        · exact affIn_countK h lm _ fun col => affIn_pinColK mk pl lm col)
  refine ⟨forms, fun μ => ?_⟩
  rw [← hf μ]
  unfold claimsZ
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

end
end Fo
