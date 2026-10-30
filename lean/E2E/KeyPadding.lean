-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPadding.lean: the padding of a key file's lookup, counted twice, its public factor, and with
them the relation after the lookup's first challenge in the library's own letters, general and at
the two lookups of the full size. The positions of padding of E2E/KeyPlanes.lean are as many as the
library's list of padding says (`Wf.paddingFrom`, `Wf.lookupOf`, OnBytes/Iop/Wf.lean;
`Lkp.paddingList`, OnBytes/Iop/Lkp.lean); so the public factor of the lookup's face (`Face.factor`
at `faceOfLkp`, Johnson/Desc/First/Look/K3LookupGeneral.lean, K3Key.lean), read in the field, is (alpha -
padding key)^(positions of padding). Definitions, statements and proofs.

What is shown.
  `gaps_from`: for runs that pass the verifier's test `Wf.runsOk`: the stretches that the library
    lays from a place on hold, together, 2^kCol keys for each place from there on that no run
    covers.
  `free_card`, **`padding_count`**: so, if every part's runs pass that test, `paddingCount k l` is
    the sum of the lengths in the padding of `Wf.lookupOf id ⟨k, rows⟩ l`.
  `rowAt_read`: the row of the table that the padding holds, read in the field, is the padding key,
    if that is a row of the table.
  **`factor_read`**: the public factor.
  `count_read`: the face's number of keys that are no padding is `liveCount`.
  `card_of_fits`: the premise "all positions are fewer than 2^W" of E2E/KeyPlanes.lean, at W the
    real planes, is what the verifier's own test `Wf.fitsMatrix` (OnBytes/Key/Ranges.lean) says.
  **`midPs`**: the relation after the first challenge at several parts, in the library's own
    letters, all read in the field, general in the item, the codes and the lookup's number: the
    product of the parts' roots over `keyVec` is `Face.factor` times the product over the planes j
    below W of (the product over the table's rows t of 1 + bit · (alpha - 1 - t))^(2^j), with the
    bits read by `bitVec` off the honest array (`planesVal`, E2E/KeyPlanesRead.lean).
  `keyAt_congr`, `keysIn_congr`: keys see a reader at the rows that the runs read and at the columns
    below 2^k alone.
  `runs_full`: the runs of the two lookups of the full size pass the test and read rows of the
    matrix alone: by an evaluation in Lean's kernel.
  `keysIn_words`: for a matrix M in range and machine words that spell its cells (whatever they hold
    beyond its rows and columns): every live key of both lookups is a row of its table.
  **`mid_full0`**, **`mid_full1`**: so `midPs` at the two lookups of the full size, with 40 and 39
    planes, for every M in range and such words, at every alpha and theta. Left as premises: the
    three of `bitVec_full` on the item and its code.

Limits.
- Mathematics on keys, bits and one public factor, read in the field by the library's `readE`: equal
  readings, not equal words. No round, no sumcheck, no mask, no coin.
- That the verifier's text of a lookup asks `midPs`'s relation is a reading of its head and of its
  steps on the tie and on the parts (Johnson/Desc/First/Look/K3LookupGeneral.lean); no theorem ties the
  two here, and the relation is held against no other Lean text of it. THE INNER FACTOR 1 + bit ·
  (alpha - 1 - t) IS WRITTEN OUT HERE: it is not the face's own `leaf`, and is not held against it.
- `keyVec` and `bitVec` are definitions of Johnson/Desc/Key/KeyK3W.lean,
  whose limits hold here too.
- The shift plays no part: a key file's lookup has none, and its one function has the number 0.
- `mid_full0` and `mid_full1` keep three premises on the item and its code. At the library's written
  sizes of the key they are met (E2E/KeyMidAtWritten.lean); that these are the sizes at any public
  files is not shown here.
- Nothing on hiding follows from this file.


-/
import E2E.KeyPlanesRead
import Johnson.Desc.First.Look.K3Key

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF GE toF readE)
open OnBytes.Params (WfRun WfPart WfLookup)
open Johnson.Pack (runIn hasPl)
open OnBytes.Wf (runsOk paddingFrom stretch lookupOf)
open Johnson.Pack (lk0Full lk1Full)
open VerifiableInference.Desc.Key (keyVec bitVec)
open Inst.Model.Layout (kRef)

/-! ## 1. The places that no run covers -/

/-- The places from a to below b that no run of the list covers. -/
def freeIn (rs : List WfRun) (a b : ℕ) : Finset ℕ := (Ico a b).filter fun u => (runIn rs u).isNone

/-- The lengths of a list of padding, added up. -/
def lens (ps : List OnBytes.Lkp.Padding) : ℕ := (ps.map (·.length)).sum

theorem lens_append (a b : List OnBytes.Lkp.Padding) : lens (a ++ b) = lens a + lens b := by
  unfold lens
  rw [List.map_append, List.sum_append]

theorem lens_stretch (kCol n row lo hi : ℕ) :
    lens (stretch kCol n row lo hi) = (hi - lo) * 2 ^ kCol := by
  unfold stretch lens
  by_cases h : lo < hi
  · rw [if_pos h]
    simp
  · rw [if_neg h, Nat.sub_eq_zero_of_le (Nat.not_lt.1 h)]
    simp

/-- Below all runs nothing is covered. -/
theorem runIn_below (lp : ℕ) (rs : List WfRun) (upto : ℕ) (h : runsOk lp upto rs = true) (u : ℕ)
    (hu : u < upto) : runIn rs u = none := by
  cases e : runIn rs u with
  | none => rfl
  | some r =>
    obtain ⟨hr, hp⟩ := Johnson.Pack.runIn_some rs u r e
    have := (Johnson.Pack.runsOk_ge lp rs upto h r hr).1
    have h1 := hp.1
    omega

/-- **The library's stretches of padding, counted.** -/
theorem gaps_from (kCol n row lp : ℕ) : ∀ (rs : List WfRun) (upto : ℕ)
    (acc : Array OnBytes.Lkp.Padding), runsOk lp upto rs = true → upto ≤ 2 ^ lp →
    lens (paddingFrom kCol n row lp upto rs acc).toList =
      lens acc.toList + (freeIn rs upto (2 ^ lp)).card * 2 ^ kCol
  | [], upto, acc, _, _ => by
    unfold paddingFrom
    rw [Array.toList_appendList, lens_append, lens_stretch]
    have e : freeIn [] upto (2 ^ lp) = Ico upto (2 ^ lp) :=
      Finset.filter_true_of_mem fun _ _ => rfl
    rw [e, Nat.card_Ico]
  | r :: rs, upto, acc, h, _ => by
    have h' := h
    unfold runsOk at h'
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h'
    unfold paddingFrom
    rw [gaps_from kCol n row lp rs (r.firstPlace + r.places) _ h5 (by omega),
      Array.toList_appendList, lens_append, lens_stretch, add_assoc, ← add_mul]
    refine congrArg (fun z => lens acc.toList + z * 2 ^ kCol) ?_
    -- the free places from upto on: those below the run, and those behind it
    have e : freeIn (r :: rs) upto (2 ^ lp) =
        Ico upto r.firstPlace ∪ freeIn rs (r.firstPlace + r.places) (2 ^ lp) := by
      ext u
      unfold freeIn
      simp only [mem_filter, mem_Ico, mem_union]
      by_cases hr : hasPl r u
      · have e1 : runIn (r :: rs) u = some r := by
          unfold runIn
          rw [List.find?_cons_of_pos (by simpa using hr)]
        have a1 := hr.1
        have a2 := hr.2
        rw [e1]
        simp only [Option.isNone_some, Bool.false_eq_true, and_false, false_iff, not_or, not_and]
        exact ⟨fun _ => by omega, fun hh => by omega⟩
      · have e1 : runIn (r :: rs) u = runIn rs u := by
          unfold runIn
          rw [List.find?_cons_of_neg (by simpa using hr)]
        rw [e1]
        unfold hasPl at hr
        constructor
        · rintro ⟨⟨b1, b2⟩, b3⟩
          by_cases hb : u < r.firstPlace
          · exact Or.inl ⟨b1, hb⟩
          · exact Or.inr ⟨⟨by omega, b2⟩, b3⟩
        · rintro (⟨b1, b2⟩ | ⟨⟨b1, b2⟩, b3⟩)
          · refine ⟨⟨b1, by omega⟩, ?_⟩
            rw [runIn_below lp rs _ h5 u (by omega)]
            rfl
          · exact ⟨⟨by omega, b2⟩, b3⟩
    have hd : Disjoint (Ico upto r.firstPlace) (freeIn rs (r.firstPlace + r.places) (2 ^ lp)) := by
      rw [Finset.disjoint_left]
      intro u hu hu'
      unfold freeIn at hu'
      have a1 := (mem_Ico.1 hu).2
      have a2 := (mem_Ico.1 (mem_filter.1 hu').1).1
      omega
    rw [e, card_union_of_disjoint hd, Nat.card_Ico]

/-- Every stretch that the library lays holds the row that it was told. -/
theorem rows_from (kCol n row lp : ℕ) : ∀ (rs : List WfRun) (upto : ℕ)
    (acc : Array OnBytes.Lkp.Padding), (∀ q ∈ acc.toList, q.row = row) →
    ∀ q ∈ (paddingFrom kCol n row lp upto rs acc).toList, q.row = row := by
  have hs : ∀ lo hi, ∀ q ∈ stretch kCol n row lo hi, q.row = row := fun lo hi q hq => by
    unfold stretch at hq
    by_cases h : lo < hi
    · rw [if_pos h, List.mem_singleton] at hq
      rw [hq]
    · rw [if_neg h] at hq
      exact absurd hq List.not_mem_nil
  intro rs
  induction rs with
  | nil =>
    intro upto acc ha q hq
    unfold paddingFrom at hq
    rw [Array.toList_appendList, List.mem_append] at hq
    exact hq.elim (ha q) (hs _ _ q)
  | cons r rs ih =>
    intro upto acc ha q hq
    unfold paddingFrom at hq
    refine ih _ _ (fun q' hq' => ?_) q hq
    rw [Array.toList_appendList, List.mem_append] at hq'
    exact hq'.elim (ha q') (hs _ _ q')

/-! ## 2. The positions of padding -/

theorem card_fin_filter (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (univ.filter fun u : Fin n => p u.val).card = ((range n).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  refine congrArg Finset.card ?_
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨u, hp, rfl⟩
    exact ⟨u.isLt, hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨⟨x, hx⟩, hp, rfl⟩

/-- The positions of padding, part by part. -/
theorem free_card (k : ℕ) (l : WfLookup) : paddingCount k l =
    (l.parts.map fun p => (freeIn p.runs 0 (2 ^ p.logPlaces)).card * 2 ^ k).sum := by
  classical
  rw [← sum_get (fun p : WfPart => (freeIn p.runs 0 (2 ^ p.logPlaces)).card * 2 ^ k)]
  unfold paddingCount
  have e : (univ.filter fun i : Pos l k => ¬ live k l i = true) =
      (univ : Finset (Fin l.parts.length)).sigma fun f =>
        (univ.filter fun u : Fin (2 ^ (l.parts.get f).logPlaces) =>
          (runIn (l.parts.get f).runs u.val).isNone = true) ×ˢ (univ : Finset (Fin (2 ^ k))) := by
    ext ⟨f, u, c⟩
    simp only [mem_filter, mem_univ, true_and, mem_sigma, mem_product, and_true]
    unfold live
    cases runIn (l.parts.get f).runs u.val <;> simp
  rw [e, Finset.card_sigma]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin,
    card_fin_filter _ fun u => (runIn (l.parts.get f).runs u).isNone = true]
  unfold freeIn
  rw [Nat.Ico_zero_eq_range]

/-- The library's padding of a list of parts, counted. -/
theorem lens_parts (kCol row : ℕ) : ∀ (ps : List WfPart) (n : ℕ),
    (∀ p ∈ ps, runsOk p.logPlaces 0 p.runs = true) →
    lens ((ps.zipIdx n).flatMap fun p =>
        (paddingFrom kCol p.2 row p.1.logPlaces 0 p.1.runs #[]).toList) =
      (ps.map fun p => (freeIn p.runs 0 (2 ^ p.logPlaces)).card * 2 ^ kCol).sum
  | [], _, _ => rfl
  | p :: ps, n, h => by
    rw [List.zipIdx_cons, List.flatMap_cons, lens_append, List.map_cons, List.sum_cons,
      lens_parts kCol row ps (n + 1) fun q hq => h q (List.mem_cons_of_mem _ hq),
      gaps_from kCol n row p.logPlaces p.runs 0 #[] (h p List.mem_cons_self) (Nat.zero_le _)]
    refine congrArg (fun z => z + _) ?_
    show 0 + _ = _
    rw [Nat.zero_add]

/-- **The positions of padding are as many as the library's list says.** -/
theorem padding_count (id : ℕ) (m : OnBytes.Wf.Matrix) (l : WfLookup)
    (h : ∀ p ∈ l.parts, runsOk p.logPlaces 0 p.runs = true) :
    paddingCount m.kCol l = lens (lookupOf id m l).padding := by
  rw [free_card]
  exact (lens_parts m.kCol l.paddingKey.toNat l.parts 0 h).symm

/-! ## 3. The public factor -/

/-- The row of the table that the padding holds, read in the field. -/
theorem rowAt_read (id : ℕ) (m : OnBytes.Wf.Matrix) (l : WfLookup)
    (hp : l.paddingKey.toNat < 2 ^ l.d) (theta : OnBytes.E) :
    readE (OnBytes.Lkp.rowAt (lookupOf id m l) theta l.paddingKey.toNat) =
      algebraMap GF GE (toF l.paddingKey) := by
  have e0 : l.paddingKey.toNat / 2 ^ l.d = 0 := Nat.div_eq_of_lt hp
  unfold OnBytes.Lkp.rowAt lookupOf
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false, List.find?_cons, e0, Nat.zero_div,
    beq_self_eq_true, List.isEmpty_nil, if_true]
  rw [OnBytes.Slice.readE_add, OnBytes.Slice.readE_mul, Nat.mod_eq_of_lt hp]
  unfold OnBytes.Lkp.natE
  rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_normF,
    OnBytes.Slice.toF_normF, UInt64.ofNat_toNat]
  show _ + algebraMap GF GE (toF 0) * _ = _
  rw [OnBytes.Slice.toF_zero, map_zero, zero_mul, add_zero]

/-- A product of powers of one value. -/
theorem foldl_pow_read (theta alpha : OnBytes.E) (κ : GE) :
    ∀ (ps : List (ℕ × (OnBytes.E → OnBytes.E))) (z : OnBytes.E),
      (∀ p ∈ ps, readE (p.2 theta) = κ) →
      readE (ps.foldl (fun a p =>
          OnBytes.mulE a (OnBytes.powE (OnBytes.subE alpha (p.2 theta)) p.1)) z) =
        readE z * (readE alpha - κ) ^ (ps.map (·.1)).sum
  | [], z, _ => by simp
  | p :: ps, z, h => by
    rw [List.foldl_cons, foldl_pow_read theta alpha κ ps _ fun q hq =>
        h q (List.mem_cons_of_mem _ hq),
      OnBytes.Slice.readE_mul, OnBytes.Slice.readE_pow, OnBytes.Slice.readE_sub,
      h p List.mem_cons_self, List.map_cons, List.sum_cons, pow_add, mul_assoc]

/-- **The public factor of the lookup's face, read in the field.** -/
theorem factor_read (id : ℕ) (m : OnBytes.Wf.Matrix) (l : WfLookup)
    (h : ∀ p ∈ l.parts, runsOk p.logPlaces 0 p.runs = true)
    (hp : l.paddingKey.toNat < 2 ^ l.d) (theta alpha : OnBytes.E) :
    readE ((VerifiableInference.Desc.K3.faceOfLkp (lookupOf id m l)).factor theta alpha) =
      (readE alpha - algebraMap GF GE (toF l.paddingKey)) ^ paddingCount m.kCol l := by
  have hl : OnBytes.Lkp.paddingList (lookupOf id m l) =
      (lookupOf id m l).padding.map fun q => (q.length, q.row) := by
    unfold OnBytes.Lkp.paddingList
    have e : ((lookupOf id m l).keys.filter (·.function.isNone)) = [] := rfl
    rw [e, List.map_nil, List.append_nil]
  have hr : ∀ q ∈ (lookupOf id m l).padding, q.row = l.paddingKey.toNat := fun q hq => by
    obtain ⟨p, -, hq'⟩ := List.mem_flatMap.1 hq
    exact rows_from m.kCol p.2 l.paddingKey.toNat p.1.logPlaces p.1.runs 0 #[]
      (fun _ h0 => absurd h0 List.not_mem_nil) q hq'
  unfold VerifiableInference.Desc.K3.Face.factor VerifiableInference.Desc.K3.faceOfLkp
  simp only [hl, List.map_map]
  rw [foldl_pow_read theta alpha (algebraMap GF GE (toF l.paddingKey)) _ _ fun p hp' => ?_,
    OnBytes.Slice.readE_one, one_mul, padding_count id m l h]
  · refine congrArg (fun z => _ ^ z) ?_
    unfold lens
    rw [List.map_map]
    rfl
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp'
    show readE (OnBytes.Lkp.rowAt (lookupOf id m l) theta q.row) = _
    rw [hr q hq]
    exact rowAt_read id m l hp theta

/-- **The face's number of keys that are no padding is the number of live positions.** -/
theorem count_read (id : ℕ) (m : OnBytes.Wf.Matrix) (l : WfLookup)
    (h : ∀ p ∈ l.parts, runsOk p.logPlaces 0 p.runs = true) :
    (VerifiableInference.Desc.K3.faceOfLkp (lookupOf id m l)).count = liveCount m.kCol l := by
  have hl : OnBytes.Lkp.paddingList (lookupOf id m l) =
      (lookupOf id m l).padding.map fun q => (q.length, q.row) := by
    unfold OnBytes.Lkp.paddingList
    have e : ((lookupOf id m l).keys.filter (·.function.isNone)) = [] := rfl
    rw [e, List.map_nil, List.append_nil]
  have e1 : (VerifiableInference.Desc.K3.faceOfLkp (lookupOf id m l)).allKeys =
      Fintype.card (Pos l m.kCol) := by
    rw [card_pos, sum_get fun p : WfPart => 2 ^ p.logPlaces * 2 ^ m.kCol]
    unfold VerifiableInference.Desc.K3.Face.allKeys VerifiableInference.Desc.K3.faceOfLkp lookupOf
    simp only [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    exact pow_add 2 _ _
  have e2 : (((VerifiableInference.Desc.K3.faceOfLkp (lookupOf id m l)).padding.map (·.1)).sum) =
      paddingCount m.kCol l := by
    rw [padding_count id m l h]
    unfold VerifiableInference.Desc.K3.faceOfLkp lens
    simp only [hl, List.map_map]
    rfl
  unfold VerifiableInference.Desc.K3.Face.count
  rw [e1, e2, ← live_add_padding, Nat.add_sub_cancel]

/-- The loop of the verifier's own test on a lookup and the matrix's size: K keys and those of the
parts that are left, padding counted, are fewer than 2^(real planes). -/
theorem parts_fit (m : OnBytes.Wf.Matrix) (l : WfLookup) : ∀ (ps : List WfPart) (K : ℕ),
    OnBytes.Wf.partsFit m l K ps = true → K < 2 ^ OnBytes.Wf.planesOf l →
    K + (ps.map fun p => 2 ^ p.logPlaces * 2 ^ m.kCol).sum < 2 ^ OnBytes.Wf.planesOf l
  | [], K, _, hK => by simpa using hK
  | p :: ps, K, h, _ => by
    unfold OnBytes.Wf.partsFit at h
    simp only [decide_eq_true_eq, Bool.and_eq_true] at h
    have h1 := parts_fit m l ps _ h.2 h.1.2
    rw [List.map_cons, List.sum_cons, ← pow_add, ← add_assoc]
    exact h1

/-- The verifier's own test on a lookup and the matrix's size (`Wf.fitsMatrix`) says that all
positions, padding counted, are fewer than 2^(real planes). Nothing in this library calls it; that
the two lookups of the full size have 40 and 39 real planes by `Wf.planesOf` is not typed. -/
theorem card_of_fits (m : OnBytes.Wf.Matrix) (l : WfLookup)
    (h : OnBytes.Wf.fitsMatrix m l = true) :
    Fintype.card (Pos l m.kCol) < 2 ^ OnBytes.Wf.planesOf l := by
  rw [card_pos, sum_get fun p : WfPart => 2 ^ p.logPlaces * 2 ^ m.kCol]
  have := parts_fit m l l.parts 0 h (Nat.two_pow_pos _)
  rwa [Nat.zero_add] at this

/-! ## 4. The relation after the first challenge in the library's own letters -/

/-- **General in the lookup**: the product of the parts' roots, over the library's `keyVec`, is the
face's public factor times the product over the planes j below W of (the product over the table's
rows t of 1 + bit · (alpha - 1 - t))^(2^j), the bits read by the library's `bitVec` off the honest
array. All read in the field. n: the lookup's number in the item. -/
theorem midPs (mat : ℕ → ℕ → OnBytes.F) (m : OnBytes.Wf.Matrix) (id : ℕ)
    (x : OnBytes.Params.WfPublic) (codes : OnBytes.Codes) (n : ℕ) (Bs : List OnBytes.Wf.Block)
    (hlay : OnBytes.Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell = Bs)
    (hg : Good x.lookups (OnBytes.ceilLog2 x.message.shape.mainRows)
      (codes.base.getD x.message.shape.code default).logEll Bs = true) (W : ℕ)
    (hone : ∀ j < W, j < 2 ^ (x.lookups.getD n default).mu ∧
      ((Bs.filter (·.lookup == n)).filter fun b =>
        decide (b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes)).length = 1)
    (hin : KeysIn (fun y c => toF (mat y c)) m.kCol (x.lookups.getD n default))
    (hp : (x.lookups.getD n default).paddingKey.toNat < 2 ^ (x.lookups.getD n default).d)
    (hinj : ∀ t t' : ℕ, t < 2 ^ (x.lookups.getD n default).d →
      t' < 2 ^ (x.lookups.getD n default).d → (t : GF) = (t' : GF) → t = t')
    (hW : Fintype.card (Pos (x.lookups.getD n default) m.kCol) < 2 ^ W)
    (hr : ∀ p ∈ (x.lookups.getD n default).parts, runsOk p.logPlaces 0 p.runs = true)
    (theta alpha : OnBytes.E) :
    ∏ f : Fin (x.lookups.getD n default).parts.length,
        ∏ i ∈ range (2 ^ ((x.lookups.getD n default).parts.get f).logPlaces * 2 ^ m.kCol),
          (readE alpha - readE (keyVec m (x.lookups.getD n default) mat f.val i)) =
      readE ((VerifiableInference.Desc.K3.faceOfLkp
          (lookupOf id m (x.lookups.getD n default))).factor theta alpha) *
        ∏ j ∈ range W, (∏ t : Fin (2 ^ (x.lookups.getD n default).d),
          (1 + readE (bitVec x codes n (planesVal (fun y c => toF (mat y c)) m.kCol x.lookups
              (codes.base.getD x.message.shape.code default).ell
              (OnBytes.ceilLog2 x.message.shape.mainRows))
              (j + 2 ^ (x.lookups.getD n default).mu * t.val)) *
            (readE alpha - 1 - ((t.val : ℕ) : GE)))) ^ 2 ^ j := by
  have hpad : ∃ t₀ : ℕ, t₀ < 2 ^ (x.lookups.getD n default).d ∧
      toF (x.lookups.getD n default).paddingKey = (t₀ : GF) := ⟨_, hp, rfl⟩
  rw [mid_parts m (x.lookups.getD n default) mat hin hpad hinj hW (readE alpha),
    factor_read id m (x.lookups.getD n default) hr hp theta alpha, OnBytes.Slice.readE_ofF]
  refine congrArg (fun z => _ * z) (Finset.prod_congr rfl fun j hj => ?_)
  refine congrArg (fun z => z ^ 2 ^ j) (Finset.prod_congr rfl fun t _ => ?_)
  obtain ⟨h1, h2⟩ := hone j (Finset.mem_range.1 hj)
  rw [bitVec_read (fun y c => toF (mat y c)) m.kCol x codes n Bs hlay hg j t.val h1 t.isLt, h2,
    Nat.cast_one, one_mul, map_natCast]

/-! ## 5. Keys see the matrix at the runs' rows alone -/

/-- Every row that a run of the lookup reads is below h. -/
def rowsBelow (l : WfLookup) (h : ℕ) : Bool :=
  l.parts.all fun p => p.runs.all fun r =>
    decide (r.firstRow + r.places + (l.digitWeight.length - 1) * r.stride ≤ h)

/-- Two readers that agree below h rows and 2^k columns give the same keys. -/
theorem keyAt_congr (e e' : ℕ → ℕ → GF) (k : ℕ) (l : WfLookup) (h : ℕ)
    (hb : rowsBelow l h = true) (he : ∀ y c, y < h → c < 2 ^ k → e y c = e' y c) (i : Pos l k) :
    keyAt e k l i = keyAt e' k l i := by
  unfold keyAt keyOfPlace
  cases hr : runIn (l.parts.get i.1).runs i.2.1.val with
  | none => rfl
  | some r =>
    obtain ⟨hm, hpl⟩ := Johnson.Pack.runIn_some _ _ r hr
    unfold rowsBelow at hb
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hb _ (List.get_mem l.parts i.1)) r hm
    simp only [decide_eq_true_eq] at h1
    refine congrArg (fun z => toF l.offset + z) (Finset.sum_congr rfl fun q hq => ?_)
    refine congrArg (fun z => toF (l.digitWeight.getD q 0) * z) (he _ _ ?_ i.2.2.isLt)
    have hq' := Finset.mem_range.1 hq
    have a1 := hpl.1
    have a2 := hpl.2
    have a3 : q * r.stride ≤ (l.digitWeight.length - 1) * r.stride :=
      Nat.mul_le_mul_right _ (by omega)
    unfold Johnson.Pack.rowOf
    omega

theorem keysIn_congr (e e' : ℕ → ℕ → GF) (k : ℕ) (l : WfLookup) (h : ℕ)
    (hb : rowsBelow l h = true) (he : ∀ y c, y < h → c < 2 ^ k → e y c = e' y c)
    (hin : KeysIn e k l) : KeysIn e' k l := fun i hi => by
  obtain ⟨t, ht, hk⟩ := hin i hi
  exact ⟨t, ht, by rw [← keyAt_congr e e' k l h hb he i]; exact hk⟩

/-! ## 6. At the full size -/

set_option maxRecDepth 1000000 in
/-- The runs of all parts of both lookups pass the verifier's test, and read rows of the matrix
alone. -/
theorem runs_full : (lk0Full.parts.all fun p => runsOk p.logPlaces 0 p.runs) = true ∧
    (lk1Full.parts.all fun p => runsOk p.logPlaces 0 p.runs) = true ∧
    rowsBelow lk0Full 3076096 = true ∧ rowsBelow lk1Full 3076096 = true := by decide +kernel

section
variable (M : Fin Inst.Model.Layout.hRef → Fin (2 ^ kRef) → GE)
  (hM : VerifiableInference.OnPublicFiles.Flat.InRange M) (mat : ℕ → ℕ → OnBytes.F)
  (hmat : ∀ (y c : ℕ) (hy : y < Inst.Model.Layout.hRef) (hc : c < 2 ^ kRef),
    toF (mat y c) = (M ⟨y, hy⟩ ⟨c, hc⟩).c0)
include hM hmat

/-- For a matrix in range, and machine words that spell its cells: every live key is a row of its
table. What the words hold beyond the matrix's rows and columns does not matter. -/
theorem keysIn_words : KeysIn (fun y c => toF (mat y c)) kRef lk0Full ∧
    KeysIn (fun y c => toF (mat y c)) kRef lk1Full := by
  have he : ∀ y c, y < 3076096 → c < 2 ^ kRef → entryOf M y c = toF (mat y c) :=
    fun y c hy hc => by
      unfold entryOf
      rw [dif_pos ⟨hy, hc⟩, hmat y c hy hc]
  exact ⟨keysIn_congr _ _ kRef lk0Full 3076096 runs_full.2.2.1 he (keysIn_full M hM).1,
    keysIn_congr _ _ kRef lk1Full 3076096 runs_full.2.2.2 he (keysIn_full M hM).2⟩

/-- **The first lookup of the full size, for a matrix in range**: the product of the twelve parts'
roots, over the library's `keyVec` at machine words that spell the matrix, is the face's public
factor times the product over the 40 real planes j of (the product over the table's rows t of 1 +
bit · (alpha - 1 - t))^(2^j), the bits read by the library's `bitVec` off the honest array: at every
alpha and theta. All read in the field. -/
theorem mid_full0 (rows id : ℕ) (x : OnBytes.Params.WfPublic) (codes : OnBytes.Codes)
    (hx : x.lookups = [lk0Full, lk1Full]) (hrows : x.message.shape.mainRows = 2)
    (hell : (codes.base.getD x.message.shape.code default).ell = 2 ^ 18)
    (theta alpha : OnBytes.E) :
    ∏ f : Fin lk0Full.parts.length,
        ∏ i ∈ range (2 ^ (lk0Full.parts.get f).logPlaces * 2 ^ kRef),
          (readE alpha - readE (keyVec ⟨kRef, rows⟩ lk0Full mat f.val i)) =
      readE ((VerifiableInference.Desc.K3.faceOfLkp
          (lookupOf id ⟨kRef, rows⟩ lk0Full)).factor theta alpha) *
        ∏ j ∈ range 40, (∏ t : Fin (2 ^ lk0Full.d),
          (1 + readE (bitVec x codes 0 (planesVal (fun y c => toF (mat y c)) kRef
              [lk0Full, lk1Full] (2 ^ 18) 1) (j + 2 ^ lk0Full.mu * t.val)) *
            (readE alpha - 1 - ((t.val : ℕ) : GE)))) ^ 2 ^ j := by
  have h0 : x.lookups.getD 0 default = lk0Full := by rw [hx]; rfl
  have hrb : OnBytes.ceilLog2 x.message.shape.mainRows = 1 := by rw [hrows]; decide
  have hle : (codes.base.getD x.message.shape.code default).logEll = 18 := by
    unfold OnBytes.Code.logEll
    rw [hell]
    decide
  have key := midPs mat ⟨kRef, rows⟩ id x codes 0 sixBlocks
    (by rw [hx, hell]; exact layout_full) (by rw [hx, hrb, hle]; exact good_full) 40
    (fun j hj => ⟨by rw [h0]; show j < 2 ^ 6; omega,
      by rw [(holders_full j (by omega)).1, if_pos hj]⟩)
    (by rw [h0]; exact (keysIn_words M hM mat hmat).1)
    (by rw [h0]; exact Nat.two_pow_pos _) (by rw [h0]; exact inj₀)
    (by rw [h0]; show Fintype.card (Pos lk0Full kRef) < 2 ^ 40
        rw [card_full.1]; norm_num)
    (by rw [h0]; exact fun p hp => List.all_eq_true.1 runs_full.1 p hp) theta alpha
  rw [h0, hell, hrb, hx] at key
  exact key

/-- **The second lookup**, with 39 real planes. -/
theorem mid_full1 (rows id : ℕ) (x : OnBytes.Params.WfPublic) (codes : OnBytes.Codes)
    (hx : x.lookups = [lk0Full, lk1Full]) (hrows : x.message.shape.mainRows = 2)
    (hell : (codes.base.getD x.message.shape.code default).ell = 2 ^ 18)
    (theta alpha : OnBytes.E) :
    ∏ f : Fin lk1Full.parts.length,
        ∏ i ∈ range (2 ^ (lk1Full.parts.get f).logPlaces * 2 ^ kRef),
          (readE alpha - readE (keyVec ⟨kRef, rows⟩ lk1Full mat f.val i)) =
      readE ((VerifiableInference.Desc.K3.faceOfLkp
          (lookupOf id ⟨kRef, rows⟩ lk1Full)).factor theta alpha) *
        ∏ j ∈ range 39, (∏ t : Fin (2 ^ lk1Full.d),
          (1 + readE (bitVec x codes 1 (planesVal (fun y c => toF (mat y c)) kRef
              [lk0Full, lk1Full] (2 ^ 18) 1) (j + 2 ^ lk1Full.mu * t.val)) *
            (readE alpha - 1 - ((t.val : ℕ) : GE)))) ^ 2 ^ j := by
  have h0 : x.lookups.getD 1 default = lk1Full := by rw [hx]; rfl
  have hrb : OnBytes.ceilLog2 x.message.shape.mainRows = 1 := by rw [hrows]; decide
  have hle : (codes.base.getD x.message.shape.code default).logEll = 18 := by
    unfold OnBytes.Code.logEll
    rw [hell]
    decide
  have key := midPs mat ⟨kRef, rows⟩ id x codes 1 sixBlocks
    (by rw [hx, hell]; exact layout_full) (by rw [hx, hrb, hle]; exact good_full) 39
    (fun j hj => ⟨by rw [h0]; show j < 2 ^ 6; omega,
      by rw [(holders_full j (by omega)).2, if_pos hj]⟩)
    (by rw [h0]; exact (keysIn_words M hM mat hmat).2)
    (by rw [h0]; exact Nat.two_pow_pos _) (by rw [h0]; exact inj₁)
    (by rw [h0]; show Fintype.card (Pos lk1Full kRef) < 2 ^ 39
        rw [card_full.2]; norm_num)
    (by rw [h0]; exact fun p hp => List.all_eq_true.1 runs_full.2.1 p hp) theta alpha
  rw [h0, hell, hrb, hx] at key
  exact key

end

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.gaps_from
#print axioms AtPublicFiles.Key.rows_from
#print axioms AtPublicFiles.Key.free_card
#print axioms AtPublicFiles.Key.padding_count
#print axioms AtPublicFiles.Key.rowAt_read
#print axioms AtPublicFiles.Key.factor_read
#print axioms AtPublicFiles.Key.count_read
#print axioms AtPublicFiles.Key.card_of_fits
#print axioms AtPublicFiles.Key.midPs
#print axioms AtPublicFiles.Key.keyAt_congr
#print axioms AtPublicFiles.Key.keysIn_congr
#print axioms AtPublicFiles.Key.runs_full
#print axioms AtPublicFiles.Key.keysIn_words
#print axioms AtPublicFiles.Key.mid_full0
#print axioms AtPublicFiles.Key.mid_full1
