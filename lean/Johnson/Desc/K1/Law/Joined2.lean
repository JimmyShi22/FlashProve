-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Joined2.lean: behind a yes at seeds that are not bad, at most one member of each
list meets the rows laid.

Main names: outs_spec, rowsOf_mem, cutSeeds_get; Msg.weight_congr, form_congr; ReadsAs;
unique_behind.

What is not claimed. That drawn seeds read as joint seeds of the field is a premise here (ReadsAs;
Sound.lean: reads_exists). "One member" is one vector of the sample map. Nothing on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.Joined

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Cb Cb.Ood Prob

variable {L : Type}

/-! ## The written messages, one by one -/

theorem outs_spec (codes : Codes) (seeds : List (List E × E)) (n : Nat) :
    ∀ (shapes : List OracleShape) (o : Nat) (ys : List E), fitB codes n shapes ys = true →
    ∀ (k : Nat) (hk : k < shapes.length), ∃ ys', shapes[k].answers ≤ ys'.length ∧
      (outs codes seeds o shapes ys)[k]? = some (wr codes seeds (o + k) shapes[k] ys')
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | s :: l, o, ys, h, k, hk => by
    have hrest : fitB codes n l (ys.drop s.answers) = true ∧ s.answers ≤ ys.length := by
      by_cases h0 : s.answers = 0
      · simp only [fitB, h0, if_true] at h
        simp [h0, h]
      · simp only [fitB, h0, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
        exact ⟨h.2, h.1.1.2⟩
    cases k with
    | zero => exact ⟨ys, hrest.2, by simp [outs]⟩
    | succ k =>
      obtain ⟨ys', h1, h2⟩ := outs_spec codes seeds n l (o + 1) (ys.drop s.answers) hrest.1 k
        (Nat.lt_of_succ_lt_succ hk)
      refine ⟨ys', by simpa using h1, ?_⟩
      simp only [outs, List.getElem?_cons_succ, List.getElem_cons_succ]
      rw [h2]
      congr 2
      omega

theorem rowsOf_mem (codes : Codes) (seeds : List (List E × E)) (o : Nat) (s : OracleShape)
    (ys : List E) (i : Nat) (hi : i < s.answers) (sd : List E × E) (y : E)
    (h1 : seeds[i]? = some sd) (h2 : ys[i]? = some y) :
    sampleRow (Msg.of codes s) o sd.1 sd.2 i y ∈ (rowsOf codes seeds o s ys).toList := by
  unfold rowsOf
  simp only [List.mem_map]
  refine ⟨((sd, y), i), ?_, rfl⟩
  rw [List.mem_zipIdx_iff_getElem?]
  rw [List.getElem?_zip_eq_some]
  exact ⟨by rw [List.getElem?_take_of_lt hi]; exact h1,
    by rw [List.getElem?_take_of_lt hi]; exact h2⟩

theorem cutSeeds_get (v : Nat) : ∀ (n : Nat) (l : List E) (i : Nat) (sd : List E × E),
    l.length = n * (v + 1) → (cutSeeds v n l)[i]? = some sd → sd.1.length = v
  | 0, _, i, sd, _, h => by simp [cutSeeds] at h
  | n + 1, l, i, sd, hl, h => by
    have hl' : l.length = n * (v + 1) + (v + 1) := by rw [hl, Nat.succ_mul]
    cases i with
    | zero =>
      simp only [cutSeeds, List.getElem?_cons_zero, Option.some.injEq] at h
      rw [← h]
      simp only [List.length_take]
      omega
    | succ i =>
      simp only [cutSeeds, List.getElem?_cons_succ] at h
      exact cutSeeds_get v n (l.drop (v + 1)) i sd (by rw [List.length_drop]; omega) h

/-! ## The left side reads the first coordinates alone -/

theorem Msg.weight_congr (m : Msg) (z z' : Nat → GE) (h : ∀ t, t < m.v → z t = z' t) (β : GE)
    (i : Nat) (part : Part) (j : Nat) : m.weight z β i part j = m.weight z' β i part j := by
  unfold Msg.weight
  rw [eqW_congr m.v z z' _ h]

theorem Msg.form_congr (m : Msg) (z z' : Nat → GE) (h : ∀ t, t < m.v → z t = z' t) (β : GE)
    (i : Nat) (u : Part → Nat → GE) : m.form z β i u = m.form z' β i u := by
  unfold Msg.form
  simp only [m.weight_congr z z' h]

/-! ## The seeds as read -/

/-- The seeds that a round's draw gives read, in the field, as the joint seeds ρ. -/
def ReadsAs (P : Par) (r₁ : Fmt.RoundView) (ρ : Seeds P) : Prop :=
  ∀ i : Fin P.seeds, ∃ sd, (seedsOf P r₁)[i.val]? = some sd ∧
    (∀ t : Fin P.coordinates, readL sd.1 t.val = (ρ i).1 t) ∧ readE sd.2 = ((ρ i).2 : GE)

/-- **Behind a yes at seeds that are not bad: of each sampled message's list at most one member, as
a vector, meets the rows laid on the message.** -/
theorem unique_behind (P : Par) (Lst : Nat → (Part → Nat → GE) → Prop) (owed : Option Nat)
    (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hB : planOkOwn P = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (hgood : ¬ Bad P Lst ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k)
    (w w' : Means.Words GE) (hw : Lst k.val (w (d.st.oracles.size + k.val)))
    (hw' : Lst k.val (w' (d.st.oracles.size + k.val))) :
    ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧ x.sampled = true ∧
      (Means.AllSay rdE d'.st x.sampleRows.toList w →
        Means.AllSay rdE d'.st x.sampleRows.toList w' →
        (msgAt P k).vec (w (d.st.oracles.size + k.val)) =
          (msgAt P k).vec (w' (d.st.oracles.size + k.val))) := by
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  have hcodes : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes := hc
  refine ⟨_, hx, by simp [wr, hk'], fun hs hs' => ?_⟩
  by_contra hne
  apply hgood
  refine ⟨k, hk, _, _, ⟨_, hw, rfl⟩, ⟨_, hw', rfl⟩, hne, ?_⟩
  simp only [planOkOwn, planOk, Bool.and_eq_true] at hB
  have hpadfit : (msgAt P k).padFits = true := by
    refine List.all_eq_true.1 hB.2 _ ?_
    simp only [Par.tuple, List.mem_filter]
    exact ⟨List.getElem_mem k.isLt, by simpa using hk'⟩
  have hne0 : ((msgAt P k).K != 0 || (msgAt P k).Kzk != 0) = true := by
    have hmem : (shapesOf P)[k.val] ∈ shapesOf P := List.getElem_mem k.isLt
    obtain ⟨nn, hn, hnn⟩ := List.mem_map.1 hmem
    have := Array.all_eq_true_iff_forall_mem.1 hB.1.1.1 nn (Array.mem_toList_iff.1 hn)
    rw [hnn] at this
    simp only [← Own.sentShapeFits_agrees, Blk.shapeOk, Bool.and_eq_true, decide_eq_true_eq] at this
    have h0 := this.1.1.1
    show ((shapesOf P)[k.val].mainRows != 0 || (shapesOf P)[k.val].maskRows != 0) = true
    by_cases hm : (shapesOf P)[k.val].mainRows = 0
    · have : (shapesOf P)[k.val].maskRows ≠ 0 := by omega
      simp [this]
    · simp [hm]
  have hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1) :=
    draw_len P r₁ r₂ hfit
  funext i
  have hi : i.val < P.seeds := Nat.lt_of_lt_of_le i.isLt (msgAt_answers_le P k)
  obtain ⟨sd, hsd, hz, hβ⟩ := hρ ⟨i.val, hi⟩
  have hlen : sd.1.length = P.coordinates := cutSeeds_get _ _ _ _ sd hdraw hsd
  have hv := msgAt_v_le P k hk
  obtain ⟨y, hyi⟩ : ∃ y, ys'[i.val]? = some y :=
    ⟨ys'[i.val]'(Nat.lt_of_lt_of_le i.isLt hy), List.getElem?_eq_getElem _⟩
  have hrow := rowsOf_mem P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
    ys' i.val i.isLt sd y hsd hyi
  have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
      ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
        (shapesOf P)[k.val] ys' := by simp [wr, hk']
  have hshape : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
      ys').shape = (shapesOf P)[k.val] := by
    unfold wr
    split <;> rfl
  rw [hrows] at hs hs'
  have key : ∀ ww : Means.Words GE,
      Means.Says rdE (behind P d (seedsOf P r₁) (answersIn r₂)).st
        (sampleRow (msgAt P k) (d.st.oracles.size + k.val) sd.1 sd.2 i.val y) ww →
      (msgAt P k).Z.val (ownSeeds (msgAt P k).answers (msgAt P k).v ρ)
        ((msgAt P k).vec (ww (d.st.oracles.size + k.val))) i = readE y := by
    intro ww hsay
    have h := says_iff _ _ _ hx sd.1 sd.2 i.val y ww
    rw [hcodes, hshape] at h
    have h2 := (h hne0 (by rw [hlen]; exact hv)).1 hsay
    rw [(msgAt P k).val_eq hne0 hpadfit, ← h2]
    have e2 : (((ownSeeds (msgAt P k).answers (msgAt P k).v ρ) i).2 : GE) = readE sd.2 := by
      unfold ownSeeds
      rw [dif_pos hi, hβ]
    rw [e2]
    refine (msgAt P k).form_congr _ _ (fun t ht => ?_) _ _ _
    have ht' : t < P.coordinates := Nat.lt_of_lt_of_le ht hv
    have e3 : ownSeeds (msgAt P k).answers (msgAt P k).v ρ i =
        (fun t => pointOf (ρ ⟨i.val, hi⟩).1 t.val, (ρ ⟨i.val, hi⟩).2) := by
      unfold ownSeeds
      rw [dif_pos hi]
    rw [e3, show readL sd.1 t = (ρ ⟨i.val, hi⟩).1 ⟨t, ht'⟩ from hz ⟨t, ht'⟩]
    simp only [pointOf, dif_pos ht, dif_pos ht']
  rw [key w (hs _ hrow), key w' (hs' _ hrow)]

end VerifiableInference.Desc.K1
