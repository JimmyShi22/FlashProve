-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Valid.lean: book-keeping for the proof of the lemma on deferred programming of the
random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean): counts and potential by class; the
invariant of the public state (`Valid2`) with the four lemmas that each kind of action keeps it,
each under the hypotheses of its statement (`valid2_log`, `valid2_snoc`, `valid2_mark`,
`valid2_reveal`); the two bounds on a hit (`hitQ2`, `hitM2`).

Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A hit (`hitQ`, `hitM` in
Rom/DeferProof_tail.lean) is the lemma's bad event: a query or plain evaluation at the point of an
unreleased marked evaluation, or a marked evaluation at such a point or at a defined entry of the
table.

Why `Valid2.old`: `Valid` (Rom/DeferProof_tail.lean) at lengths 0 is a field of `Valid2` (it carries
the clause on the table and well-formedness), so that its four lemmas are used, not copied.
-/
import CompileK.SpecDefer2
import CompileK.Defer2Prob
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

open scoped ENNReal
open Prob
namespace Rom
namespace DeferTail2
open DeferTail

variable {S : OSpec} {sp : Split S} {K : Type} [DecidableEq K]

/-- the class of a marked evaluation, read at the empty list of values -/
def clsOf (cl : PtCls S K) (e : SEv S sp) : K := cl.of (e.key [])

def aCountK (cl : PtCls S K) (evs : List (SEv S sp)) (κ : K) : ℕ :=
  (evs.filter fun e => decide (clsOf cl e = κ)).length
def qCountK (cl : PtCls S K) (qs : List (Pt S)) (κ : K) : ℕ :=
  (qs.filter fun k => decide (cl.of k = κ)).length

/-- Σ over the classes of ks of a (b + a) / 2^ℓ -/
def potK (ℓ : K → ℕ) (ks : Finset K) (a b : K → ℕ) : ℝ≥0∞ :=
  ∑ κ ∈ ks, ((a κ * (b κ + a κ) : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ κ)

theorem potK_bump_b (ℓ : K → ℕ) (ks : Finset K) (a b : K → ℕ) {κ₀ : K} (h₀ : κ₀ ∈ ks) :
    (a κ₀ : ℝ≥0∞) * (1 / 2 ^ ℓ κ₀) + potK ℓ ks a b ≤
      potK ℓ ks a (Function.update b κ₀ (b κ₀ + 1)) := by
  refine sum_bump ks _ _ h₀ _ ?_ fun o _ hne => ?_
  · rw [Function.update_self, ← add_mul]
    gcongr
    exact_mod_cast (by nlinarith : a κ₀ + a κ₀ * (b κ₀ + a κ₀) ≤ a κ₀ * (b κ₀ + 1 + a κ₀))
  · rw [Function.update_of_ne hne]

theorem potK_bump_a (ℓ : K → ℕ) (ks : Finset K) (a b : K → ℕ) {κ₀ : K} (h₀ : κ₀ ∈ ks) :
    ((b κ₀ + a κ₀ : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ κ₀) + potK ℓ ks a b ≤
      potK ℓ ks (Function.update a κ₀ (a κ₀ + 1)) b := by
  refine sum_bump ks _ _ h₀ _ ?_ fun o _ hne => ?_
  · rw [Function.update_self, ← add_mul]
    gcongr
    exact_mod_cast (by
      nlinarith : b κ₀ + a κ₀ + a κ₀ * (b κ₀ + a κ₀) ≤ (a κ₀ + 1) * (b κ₀ + (a κ₀ + 1)))
  · rw [Function.update_of_ne hne]

theorem qCountK_cons (cl : PtCls S K) (k : Pt S) (qs : List (Pt S)) :
    qCountK cl (k :: qs) =
      Function.update (qCountK cl qs) (cl.of k) (qCountK cl qs (cl.of k) + 1) := by
  funext κ
  by_cases h : κ = cl.of k
  · subst h; simp [qCountK]
  · rw [Function.update_of_ne h]
    simp [qCountK, Ne.symm h]

theorem aCountK_snoc (cl : PtCls S K) (evs : List (SEv S sp)) (e : SEv S sp) :
    aCountK cl (evs ++ [e]) =
      Function.update (aCountK cl evs) (clsOf cl e) (aCountK cl evs (clsOf cl e) + 1) := by
  funext κ
  by_cases h : κ = clsOf cl e
  · subst h; simp [aCountK, List.filter_append]
  · rw [Function.update_of_ne h]
    simp [aCountK, List.filter_append, Ne.symm h]

omit [DecidableEq K] in
theorem clsOf_srel (cl : PtCls S K) (shown : List Tok) (x : SEv S sp) :
    clsOf cl (srel shown x) = clsOf cl x := by
  unfold clsOf
  rw [srel_key]

theorem aCountK_srel (cl : PtCls S K) (shown : List Tok) (evs : List (SEv S sp)) :
    aCountK cl (evs.map (srel shown)) = aCountK cl evs := by
  funext κ
  unfold aCountK
  rw [List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun x _ => ?_
  simp [clsOf_srel]

/-- the potential of a public state, by class -/
def potP (cl : PtCls S K) (ℓ : K → ℕ) (ks : Finset K) (p : PSt S sp) : ℝ≥0∞ :=
  potK ℓ ks (aCountK cl p.evs) (qCountK cl p.qs)

/-- one marked evaluation is in order, as the public sees it -/
structure EvOK (cl : PtCls S K) (J : K → Bool) (ℓ : K → ℕ) (ks : Finset K) (slots : List Slot)
    (shown : List Tok) (e : SEv S sp) : Prop where
  cst : ∀ w, cl.of (e.key w) = clsOf cl e
  mem : clsOf cl e ∈ ks
  one : J (clsOf cl e) = false → ∀ L, slots[e.charged]? = some (Slot.hid L) → ℓ (clsOf cl e) ≤ L
  two : J (clsOf cl e) = true →
    ∃ b, e.others = [b] ∧ (∀ v v' x x', e.pt v [x] = e.pt v' [x'] → v = v' ∧ x = x') ∧
    (e.released = false → b ∉ shown) ∧ ∀ L L', slots[e.charged]? = some (Slot.hid L) → slots[b]? = some (Slot.hid L') → ℓ (clsOf cl e) ≤ L + L'

/-- The invariant. -/
structure Valid2 (cl : PtCls S K) (J : K → Bool) (ℓ : K → ℕ) (ks : Finset K)
    (u : K → ℕ) (p : PSt S sp) : Prop where
  old : ∃ u₀, Valid (fun _ => 0) (ks.image cl.orc) u₀ p
  ev : ∀ e ∈ p.evs, EvOK cl J ℓ ks p.slots p.shown e
  count : ∀ κ, qCountK cl p.qs κ ≤ u κ + p.nPlain (cl.orc κ)

variable {cl : PtCls S K} {J : K → Bool} {ℓ : K → ℕ} {ks : Finset K}

theorem Valid2.wfP {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) : Wf p := by
  obtain ⟨u₀, h⟩ := hv.old
  exact h.toWf

omit [DecidableEq K] in
theorem clsOf_orc (cl : PtCls S K) (e : SEv S sp) : cl.orc (clsOf cl e) = e.o :=
  cl.orc_of (e.key [])

/-! ### a query or a plain evaluation -/

theorem valid2_log {u u' : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) (k : Pt S)
    (T : Table S) (nP : S.ι → ℕ)
    (hT : ∀ k' : Pt S, T k'.1 k'.2 ≠ none → p.table k'.1 k'.2 ≠ none ∨ k' = k)
    (h0 : ∀ u₀ : S.ι → ℕ, (∀ o, qCount p.qs o ≤ u₀ o + p.nPlain o) →
      ∃ u₁ : S.ι → ℕ, ∀ o, qCount (k :: p.qs) o ≤ u₁ o + nP o)
    (hc : ∀ κ, qCountK cl (k :: p.qs) κ ≤ u' κ + nP (cl.orc κ)) :
    Valid2 cl J ℓ ks u' (p.log k T nP) := by
  obtain ⟨u₀, h⟩ := hv.old
  obtain ⟨u₁, h1⟩ := h0 u₀ h.count
  exact ⟨⟨u₁, valid_log h k T nP hT h1⟩, hv.ev, hc⟩

theorem aCountK_eq_zero {u : K → ℕ} {p : PSt S sp}
    (hv : Valid2 cl J ℓ ks u p) {κ : K} (ho : κ ∉ ks) : aCountK cl p.evs κ = 0 := by
  rw [aCountK, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro x hx hxo
  exact ho ((of_decide_eq_true hxo) ▸ (hv.ev x hx).mem)

theorem potP_log_le {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) (k : Pt S)
    (T : Table S) (nP : S.ι → ℕ) :
    (aCountK cl p.evs (cl.of k) : ℝ≥0∞) * (1 / 2 ^ ℓ (cl.of k)) + potP cl ℓ ks p ≤
      potP cl ℓ ks (p.log k T nP) := by
  show _ + potK ℓ ks (aCountK cl p.evs) (qCountK cl p.qs) ≤
    potK ℓ ks (aCountK cl p.evs) (qCountK cl (k :: p.qs))
  rw [qCountK_cons]
  by_cases ho : cl.of k ∈ ks
  · exact potK_bump_b ℓ ks _ _ ho
  · rw [aCountK_eq_zero hv ho, Nat.cast_zero, zero_mul, zero_add]
    refine le_of_eq (Finset.sum_congr rfl fun o' ho' => ?_)
    rw [Function.update_of_ne fun h => ho (by rw [← h]; exact ho')]

/-! ### a new hidden token -/

omit [DecidableEq K] in
theorem evOK_snoc {p : PSt S sp} (hw : Wf p) {e : SEv S sp} (he : e ∈ p.evs)
    (h : EvOK cl J ℓ ks p.slots p.shown e) (s : Slot) :
    EvOK cl J ℓ ks (p.slots ++ [s]) p.shown e := by
  obtain ⟨t1, t2, _, _⟩ := hw.toks e he
  refine ⟨h.cst, h.mem, fun hJ L hL => h.one hJ L ?_, fun hJ => ?_⟩
  · rwa [List.getElem?_append_left t1] at hL
  · obtain ⟨b, hb, hi, hs, hl⟩ := h.two hJ
    refine ⟨b, hb, hi, hs, fun L L' h1 h2 => hl L L' ?_ ?_⟩
    · rwa [List.getElem?_append_left t1] at h1
    · rwa [List.getElem?_append_left (t2 b (by rw [hb]; exact List.mem_singleton.2 rfl))] at h2

theorem valid2_snoc {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) (L : ℕ) :
    Valid2 cl J ℓ ks u (p.snoc L) := by
  obtain ⟨u₀, h⟩ := hv.old
  exact ⟨⟨u₀, valid_snoc h L⟩, fun e he => evOK_snoc hv.wfP he (hv.ev e he) _, hv.count⟩

/-! ### a marked evaluation -/

theorem valid2_mark {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) (x : SEv S sp)
    (h1 : x.charged < p.slots.length) (h2 : ∀ y ∈ x.others, y < p.slots.length)
    (h3 : x.tail = p.slots.length) (h4 : x.charged ∉ x.others) (h5 : x.charged ∉ p.shown)
    (h6 : EvOK cl J ℓ ks p.slots p.shown x) :
    Valid2 cl J ℓ ks u (p.mark x) := by
  obtain ⟨u₀, h⟩ := hv.old
  refine ⟨⟨u₀,
      valid_mark h x h1 h2 h3 h4 h5
        (Finset.mem_image.2 ⟨_, h6.mem, clsOf_orc cl x⟩) fun _ _ => Nat.zero_le _⟩,
    fun e he => ?_, hv.count⟩
  rcases List.mem_append.1 he with he | he
  · exact evOK_snoc hv.wfP he (hv.ev e he) _
  · obtain rfl := List.mem_singleton.1 he
    refine ⟨h6.cst, h6.mem, fun hJ L hL => h6.one hJ L ?_, fun hJ => ?_⟩
    · rwa [show (p.mark e).slots = p.slots ++ [Slot.hid (sp.tl e.o)] from rfl,
        List.getElem?_append_left h1] at hL
    · obtain ⟨b, hb, hi, hs, hl⟩ := h6.two hJ
      refine ⟨b, hb, hi, hs, fun L L' a1 a2 => hl L L' ?_ ?_⟩
      · rwa [show (p.mark e).slots = p.slots ++ [Slot.hid (sp.tl e.o)] from rfl,
          List.getElem?_append_left h1] at a1
      · rwa [show (p.mark e).slots = p.slots ++ [Slot.hid (sp.tl e.o)] from rfl,
          List.getElem?_append_left (h2 b (by rw [hb]; exact List.mem_singleton.2 rfl))] at a2

/-! ### a reveal -/

theorem valid2_reveal {u : K → ℕ} {p : PSt S sp} {ts : List Tok} {ss' : List Slot}
    (hv : Valid2 cl J ℓ ks u p) (hf : Fixed ts p.slots ss') (hr : RevOK p ts)
    (hsh : ∀ x ∈ p.evs, J (clsOf cl x) = true →
      (srel (p.shown ++ ts) x).released = false → ∀ b ∈ x.others, b ∉ p.shown ++ ts) :
    Valid2 cl J ℓ ks u (p.reveal ts ss') := by
  obtain ⟨u₀, h⟩ := hv.old
  refine ⟨⟨u₀, valid_reveal h hf hr⟩, fun y hy => ?_, hv.count⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hx' := hv.ev x hx
  obtain ⟨_, hc, ho, _⟩ := srel_toks (p.shown ++ ts) x
  have hpt : ∀ v vs, HEq ((srel (p.shown ++ ts) x).pt v vs) (x.pt v vs) := by
    intro v vs
    rcases srel_cases (p.shown ++ ts) x with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he]
  refine ⟨fun w => by rw [srel_key, clsOf_srel]; exact hx'.cst w,
    by rw [clsOf_srel]; exact hx'.mem,
    fun hJ L hL => ?_, fun hJ => ?_⟩
  · rw [clsOf_srel] at hJ ⊢
    rw [hc] at hL
    exact hx'.one hJ L (hf.hid hL)
  · rw [clsOf_srel] at hJ ⊢
    obtain ⟨b, hb, hi, _, hl⟩ := hx'.two hJ
    refine ⟨b, by rw [ho]; exact hb, ?_,
      fun hrel => hsh x hx hJ hrel b (by rw [hb]; exact List.mem_singleton.2 rfl),
      fun L L' a1 a2 => ?_⟩
    · rcases srel_cases (p.shown ++ ts) x with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he] <;> exact hi
    · rw [hc] at a1
      exact hl L L' (hf.hid a1) (hf.hid a2)

/-! ### The two bounds on a hit -/

/-- Under `hv`: a query or a plain evaluation is a hit with probability at most (marked evaluations
of its class) / 2^ℓ. -/
theorem hitQ2 {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) (k : Pt S) :
    expect (law p.slots) (fun w => hitQ (p.inst w).evs k) ≤
      (aCountK cl p.evs (cl.of k) : ℝ≥0∞) * (1 / 2 ^ ℓ (cl.of k)) := by
  have hw := hv.wfP
  have h1 : ∀ w,
      hitQ (p.inst w).evs k ≤ (p.evs.map fun e => ind (e.released = false ∧ e.key w = k)).sum := by
    intro w
    refine le_trans (ind_mono ?_)
      (ind_exists_le_sum p.evs fun e => e.released = false ∧ e.key w = k)
    rintro ⟨e', he', hr, hk⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact ⟨e, he, hr, hk⟩
  refine (expect_mono _ h1).trans ?_
  rw [expect_list_sum]
  refine list_sum_le_count _ _ _ _ fun e he => ?_
  have hE := hv.ev e he
  by_cases ho : clsOf cl e = cl.of k
  · rw [if_pos (by simpa using ho)]
    by_cases hr : e.released = false
    · obtain ⟨L, hL⟩ := hw.hid (hw.toks e he).1 (hw.unrel e he hr)
      cases hJ : J (clsOf cl e) with
      | false =>
        have hp := point_prob e.charged e.others e.pt e.inj (hw.toks e he).2.2.2 hL
          (fun _ => k) (fun _ _ => rfl)
        exact le_trans (expect_mono _ fun w => ind_mono fun hh => hh.2)
          (hp.trans (ho ▸ inv_pow_le (hE.one hJ L hL)))
      | true =>
        obtain ⟨b, hb, hi, hs, hl⟩ := hE.two hJ
        have hbm : b ∈ e.others := by rw [hb]; exact List.mem_singleton.2 rfl
        obtain ⟨L', hL'⟩ := hw.hid ((hw.toks e he).2.1 b hbm) (hs hr)
        have hne : e.charged ≠ b := fun h => (hw.toks e he).2.2.2 (h ▸ hbm)
        have hp :=
          point_prob2 e.charged b e.pt hi hne hL hL' (fun _ => k) (fun _ _ => rfl) (fun _ _ => rfl)
        refine le_trans (expect_mono _ fun w => ind_mono fun hh => ?_)
          (hp.trans (ho ▸ inv_pow_le (hl L L' hL hL')))
        have := hh.2
        simp only [SEv.key, SEv.point, hb] at this
        exact this
    · rw [expect_ind_false _ _ fun w hh => hr hh.1]; exact zero_le _
  · rw [if_neg (by simpa using ho), expect_ind_false _ _ fun w hh => ho (by rw [← hE.cst w, hh.2])]

/-- Under the hypotheses below: a marked evaluation of class κ is a hit with probability at most
(logged points of κ + marked evaluations of κ) / 2^ℓ; T: the tokens that are drawn again. -/
theorem hitM2 {u : K → ℕ} {p : PSt S sp} (hv : Valid2 cl J ℓ ks u p) {o : S.ι} (t : Tok)
    (us : List Tok) (pt : Bits → List Bits → S.Dom o) (κ : K)
    (hκ : ∀ w, cl.of ⟨o, pt (gv w t) (us.map (gv w))⟩ = κ) (T : List Tok)
    (hP : ∀ tg : List Bits → Pt S, (∀ x ∈ T, ∀ w v, tg (w.set x v) = tg w) →
      expect (law p.slots) (fun w => ind ((⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) = tg w)) ≤
        1 / 2 ^ ℓ κ)
    (hind : ∀ e ∈ p.evs, e.o = o → ∀ x ∈ T, x ≠ e.charged ∧ x ∉ e.others) :
    expect (law p.slots)
        (fun w => hitM (p.inst w).table (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩) ≤
      ((qCountK cl p.qs κ + aCountK cl p.evs κ : ℕ) : ℝ≥0∞) * (1 / 2 ^ ℓ κ) := by
  obtain ⟨u₀, hold⟩ := hv.old
  have hoκ : cl.orc κ = o := by rw [← hκ []]; exact cl.orc_of _
  have h1 : ∀ w ∈ (law p.slots).support,
      hitM (p.inst w).table (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩ ≤
        (p.qs.map fun x => ind ((⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) = x)).sum +
          (p.evs.map fun e => ind ((⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) = e.key w)).sum := by
    intro w hw
    have hw' := (mem_support_law _ _).1 hw
    by_cases hh : (p.inst w).table o (pt (gv w t) (us.map (gv w))) ≠ none ∨
        Unrel (p.inst w).evs ⟨o, pt (gv w t) (us.map (gv w))⟩
    · have hor : (⟨o, pt (gv w t) (us.map (gv w))⟩ : Pt S) ∈ p.qs ∨
          ∃ e ∈ p.evs, e.key w = ⟨o, pt (gv w t) (us.map (gv w))⟩ := by
        rcases hh with hT | ⟨e', he', _, hk⟩
        · exact hold.table w hw' _ hT
        · obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
          exact Or.inr ⟨e, he, hk⟩
      rcases hor with hq | ⟨e, he, hk⟩
      · refine le_add_right (le_trans ?_ (ind_exists_le_sum p.qs _))
        rw [ind_pos ⟨_, hq, rfl⟩]; exact ind_le_one _
      · refine le_add_left (le_trans ?_ (ind_exists_le_sum p.evs _))
        rw [ind_pos ⟨e, he, hk.symm⟩]; exact ind_le_one _
    · rw [hitM, ind_neg hh]; exact zero_le _
  refine (expect_mono_support _ h1).trans ?_
  rw [expect_add, expect_list_sum, expect_list_sum, Nat.cast_add, add_mul]
  refine add_le_add (list_sum_le_count _ _ _ _ fun x _ => ?_)
    (list_sum_le_count _ _ _ _ fun e he => ?_)
  · by_cases ho : cl.of x = κ
    · rw [if_pos (by simpa using ho)]
      exact hP (fun _ => x) fun _ _ _ _ => rfl
    · rw [if_neg (by simpa using ho),
        expect_ind_false _ _ fun w hh => ho (by rw [← hh]; exact hκ w)]
  · by_cases ho : clsOf cl e = κ
    · rw [if_pos (by simpa using ho)]
      have heo : e.o = o := by rw [← clsOf_orc cl e, ho]; exact hoκ
      exact hP (fun w => e.key w) fun x hx w v =>
        e.key_set (hind e he heo x hx).1 (hind e he heo x hx).2 v
    · rw [if_neg (by simpa using ho),
        expect_ind_false _ _ fun w hh => ho (by rw [← (hv.ev e he).cst w, ← hh]; exact hκ w)]

end DeferTail2
end Rom
