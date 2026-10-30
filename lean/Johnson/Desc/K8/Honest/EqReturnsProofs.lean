-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqReturnsProofs.lean: THE SMALLNESS TEST: proofs of the five statements of
Johnson/Desc/K8/Honest/EqReturns.lean: `eqWeights`, `eqTie`, `eqRead`, `close` and `front` return
under premises on numbers, flags, marks and lengths; the read under one test on values beside.
Lemmas; none of the library's goals.

By the rules of Johnson/Desc/First/TailClaims/RetRules.lean (`Ret`) and the named parts of
Johnson/Desc/K8/Honest/EqParts.lean.
  `getD_set_self`, `getD_set_ne`   an array with one member laid anew
  `takenOf_size`, `takenOf_laidS`, `takenOf_self`, `all_of_getD`   the marks, and the marks behind
                                  one matrix's sums
  `Kept` (a structure: what the sums' step leaves), `foldAll_returns`   all matrices' sums are
                                  laid, each once
  `tieLeft_returns`, `tieRight_returns`, `zzCol_some`, `tabAt_some`, `readEnts_returns`
  `eqWeights_returns`, `eqTie_returns`, `eqRead_returns`, `close_returns`, `front_returns`
The limits are those of Johnson/Desc/K8/Honest/EqReturns.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqParts
import Johnson.Desc.First.TailClaims.RetRules

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret)

/-! ## Arrays -/

theorem getD_set_self {α : Type} (a : Array α) (i : Nat) (v d : α) (h : i < a.size) :
    (a.set! i v).getD i d = v := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem getD_set_ne {α : Type} (a : Array α) (i j : Nat) (v d : α) (h : i ≠ j) :
    (a.set! i v).getD j d = a.getD j d := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem all_of_getD (a : Array Bool) (h : ∀ i, i < a.size → a.getD i false = true) :
    a.all id = true := by
  refine Array.all_eq_true_iff_forall_mem.2 fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  have := h i hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at this
  exact this

/-! ## The weights and the sums -/

theorem takenOf_size (tl : HTailF2) : (takenOf tl).size = tl.NM := by
  unfold takenOf
  split
  · simp
  · rename_i h
    simpa using h

theorem takenOf_laidS (tl : HTailF2) (mu : Nat) :
    takenOf (laidS tl mu) = (takenOf tl).set! mu true := by
  have hs : ((takenOf tl).set! mu true).size = tl.NM := by
    simpa using takenOf_size tl
  show (if ((takenOf tl).set! mu true).size != tl.NM then Array.replicate tl.NM false
    else (takenOf tl).set! mu true) = _
  rw [if_neg (by simp [takenOf_size])]

theorem takenOf_self (tl : HTailF2) (h : tl.foldTakenF.size = tl.NM) :
    takenOf tl = tl.foldTakenF := by
  unfold takenOf
  rw [if_neg (by simp [h])]

/-- What the sums' step leaves. -/
structure Kept (tl tl' : HTailF2) : Prop where
  rest : unlaid tl' = unlaid tl
  vt : tl'.vt = tl.vt
  vp : tl'.vp = tl.vp
  rowX : tl'.rowX = tl.rowX
  loX : tl'.loX = tl.loX
  eqFirst : tl'.eqFirst = tl.eqFirst

/-- A number of the data that `unlaid` keeps. -/
theorem kept_num {α : Type} {tl tl' : HTailF2} (h : unlaid tl' = unlaid tl) (f : HTailF2 → α) :
    f (unlaid tl') = f (unlaid tl) := congrArg f h

/-- All matrices' sums are laid, each once. -/
theorem foldAll_returns : ∀ (l : List Nat) (tl : HTailF2), l.Nodup →
    (∀ mu ∈ l, mu < tl.NM ∧ (takenOf tl).getD mu true = false) →
    tl.gamX.size = tl.NM → tl.gamV.size = tl.NM →
    ∃ tl', l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) tl = some tl' ∧ Kept tl tl' ∧
      (∀ mu ∈ l, (tl'.gamX.getD mu #[]).size = (tl.mats.getD mu {}).k ∧
        (tl'.gamV.getD mu #[]).size = (tl.mats.getD mu {}).k) ∧
      (∀ mu, mu ∉ l → tl'.gamX.getD mu #[] = tl.gamX.getD mu #[] ∧
        tl'.gamV.getD mu #[] = tl.gamV.getD mu #[]) ∧
      ((tl.foldTakenF.size = tl.NM ∨ l ≠ []) → tl'.foldTakenF.size = tl.NM) ∧
      (∀ mu ∈ l, (takenOf tl').getD mu false = true) ∧
      ∀ mu, mu ∉ l → (takenOf tl').getD mu false = (takenOf tl).getD mu false
  | [], tl, _, _, _, _ =>
    ⟨tl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ h => absurd h (by simp), fun _ _ => ⟨rfl, rfl⟩,
      fun h => h.elim id fun h' => absurd rfl h', fun _ h => absurd h (by simp), fun _ _ => rfl⟩
  | mu :: l, tl, hn, hl, hX, hV => by
    obtain ⟨hmu, htk⟩ := hl mu (by simp)
    have hnd := List.nodup_cons.1 hn
    have e1 : tl.foldSums mu = some (laidS tl mu) := by
      rw [foldSums_eq, if_neg (by simp [htk, hmu])]
    have hsz : ((takenOf tl).set! mu true).size = tl.NM := by simpa using takenOf_size tl
    obtain ⟨tl', e2, hk, hin, hout, t1, t2, t3⟩ := foldAll_returns l (laidS tl mu) hnd.2
      (fun nu hnu => by
        obtain ⟨h1, h2⟩ := hl nu (by simp [hnu])
        refine ⟨h1, ?_⟩
        rw [takenOf_laidS, getD_set_ne _ _ _ _ _ (fun e : mu = nu => hnd.1 (by rw [e]; exact hnu))]
        exact h2)
      (by show (tl.gamX.set! mu _).size = tl.NM
          simpa using hX)
      (by show (tl.gamV.set! mu _).size = tl.NM
          simpa using hV)
    refine ⟨tl', by rw [List.foldlM_cons, e1]; exact e2,
      ⟨hk.rest, hk.vt, hk.vp, hk.rowX, hk.loX, hk.eqFirst⟩, fun nu hnu => ?_, fun nu hnu => ?_,
      fun _ => t1 (Or.inl hsz), fun nu hnu => ?_, fun nu hnu => ?_⟩
    · by_cases hq : nu ∈ l
      · exact hin nu hq
      · obtain rfl : nu = mu := by
          rcases List.mem_cons.1 hnu with h | h
          · exact h
          · exact absurd h hq
        obtain ⟨a1, a2⟩ := hout nu hq
        rw [a1, a2]
        refine ⟨?_, ?_⟩
        · show ((tl.gamX.set! nu _).getD nu #[]).size = _
          rw [getD_set_self _ _ _ _ (by rw [hX]; exact hmu), sumsAt_size]
        · show ((tl.gamV.set! nu _).getD nu #[]).size = _
          rw [getD_set_self _ _ _ _ (by rw [hV]; exact hmu)]
          split <;> rw [sumsAt_size]
    · have h1 : nu ∉ l := fun h => hnu (by simp [h])
      have h2 : mu ≠ nu := fun e => hnu (by simp [e])
      obtain ⟨a1, a2⟩ := hout nu h1
      rw [a1, a2]
      exact ⟨getD_set_ne _ _ _ _ _ h2, getD_set_ne _ _ _ _ _ h2⟩
    · by_cases hq : nu ∈ l
      · exact t2 nu hq
      · obtain rfl : nu = mu := by
          rcases List.mem_cons.1 hnu with h | h
          · exact h
          · exact absurd h hq
        rw [t3 nu hq, takenOf_laidS, getD_set_self _ _ _ _ (by rw [takenOf_size]; exact hmu)]
    · have h1 : nu ∉ l := fun h => hnu (by simp [h])
      have h2 : mu ≠ nu := fun e => hnu (by simp [e])
      rw [t3 nu h1, takenOf_laidS, getD_set_ne _ _ _ _ _ h2]

theorem getD_map_size {α : Type} (l : Array α) (f : α → Array E) (d : α) (i : Nat)
    (h : i < l.size) : ((l.map f).getD i #[]).size = (f (l.getD i d)).size := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem eqWeights_returns : Spec.eqWeights_returns := by
  intro tl front F cs hd hp ho htk
  have eP : tl.powersF F = some (laidP F.theta tl) := by
    rw [powersF_eq, if_neg (by simp [hd, hp, ho])]
  obtain ⟨tl', e2, hk, hin, _, t1, t2, _⟩ :=
    foldAll_returns (List.range tl.NM) (startS (laidP F.theta tl))
    List.nodup_range (fun mu hmu => ⟨List.mem_range.1 hmu, htk mu (List.mem_range.1 hmu)⟩)
    (by show (Array.replicate tl.NM (#[] : Array E)).size = tl.NM
        simp)
    (by show (Array.replicate tl.NM (#[] : Array E)).size = tl.NM
        simp)
  have R : Ret (eqWeights tl) front (F, cs) fun a s' => tl' = a ∧ s' = (F, cs) := by
    rw [eqWeights_eq]
    refine Ret.bind (P := fun a s₁ => a = laidP F.theta tl ∧ s₁ = (F, cs))
      (Ret.ask _ eP ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    exact Ret.get _ e2 ⟨rfl, rfl⟩
  obtain ⟨_, _, e, rfl, rfl⟩ := R
  refine ⟨_, e, ⟨hk.rest, ?_, ?_, fun mu hmu => ?_, fun mu hmu => ?_, fun mu hmu => ?_,
    fun mu hmu => ?_, hk.eqFirst, fun h0 => ?_⟩⟩
  · rw [hk.vt]
    exact powers_size _ _
  · rw [hk.vp]
    exact powers_size _ _
  · rw [hk.rowX]
    show ((tl.shp.map _).getD mu #[]).size = _
    rw [getD_map_size _ _ {} _ hmu, powers_size]
  · rw [hk.loX]
    show ((tl.shp.map _).getD mu #[]).size = _
    rw [getD_map_size _ _ {} _ hmu]
    rfl
  · exact (hin mu (List.mem_range.2 hmu)).1
  · exact (hin mu (List.mem_range.2 hmu)).2
  · have hN : tl'.NM = tl.NM := kept_num hk.rest (·.NM)
    have hs : tl'.foldTakenF.size = tl.NM :=
      t1 (Or.inr fun e => by
        have := congrArg List.length e
        simp at this
        omega)
    have ht := takenOf_self tl' (by rw [hs, hN])
    have hall : tl'.foldTakenF.all id = true := all_of_getD tl'.foldTakenF fun i hi => by
      rw [← ht]
      exact t2 i (List.mem_range.2 (by rw [← hs]; exact hi))
    unfold HTailF2.foldAllTakenF
    rw [hall, hs, hN]
    simp

/-! ## The tie -/

theorem tieLeft_returns (s : ShP) (r l : Array E) (hr : r.size = s.Rr) (hl : l.size = s.J) :
    ∃ w, tieLeft s r l = some w ∧ w.size = s.m := by
  unfold tieLeft
  rw [if_neg (by simp [hr, hl])]
  exact ⟨_, rfl, by simp⟩

theorem tieRight_returns (s : ShP) (l g : Array E) (hl : l.size = s.J) (hg : g.size = s.k) :
    ∃ w, tieRight s l g = some w ∧ w.size = s.J * s.k := by
  unfold tieRight
  rw [if_neg (by simp [hl, hg])]
  exact ⟨_, rfl, by simp⟩

theorem zzCol_some (tl : HTailF2) (mu p i : Nat) (hmu : mu < tl.NM) (hp : p ≤ 1)
    (hi : i < (tl.mats.getD mu {}).m) :
    tl.zzCol mu p i = some (p * tl.mz + tl.off.getD mu 0 + i) := by
  unfold HTailF2.zzCol
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hmu, hp⟩, hi⟩)]

theorem eqTie_returns : Spec.eqTie_returns := by
  intro tl mu front F cs h
  obtain ⟨wl, hwl, swl⟩ := tieLeft_returns _ _ _ h.rows h.lo
  obtain ⟨wr, hwr, swr⟩ := tieRight_returns _ _ _ h.lo h.gam
  have h0 := zzCol_some tl mu 0 0 h.mat (by omega) h.cells
  have h1 := zzCol_some tl mu 1 0 h.mat (by omega) h.cells
  have R : Ret (eqTie tl mu) front (F, cs) fun _ s' =>
      ∃ c, s' = (F, cs.push c) ∧ TieClaim tl mu c := by
    unfold eqTie
    dsimp only
    refine Ret.bind (P := fun w s₁ => w = wl ∧ s₁ = (F, cs)) (Ret.get _ hwl ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (P := fun w s₁ => w = wr ∧ s₁ = (F, cs)) (Ret.get _ hwr ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (P := fun c s₁ => c = 0 * tl.mz + tl.off.getD mu 0 + 0 ∧ s₁ = (F, cs))
      (Ret.get _ h0 ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (P := fun c s₁ => c = 1 * tl.mz + tl.off.getD mu 0 + 0 ∧ s₁ = (F, cs))
      (Ret.get _ h1 ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.emit _ ⟨_, rfl, ⟨rfl, lessBeta_ents _, lessBeta_slots _, ?_⟩⟩
    simp [runNums, swl, swr]
  obtain ⟨_, _, e, c, rfl, hc⟩ := R
  exact ⟨c, e, hc⟩

/-! ## The read -/

theorem tabAt_some (tl : HTailF2) (Fn : HFun) (c sg : Nat) (hm : Fn.mat < tl.NM) (hl : Fn.len ≠ 0)
    (hc : c < (tl.mats.getD Fn.mat {}).k) (hs : sg < segs tl Fn) :
    tl.tabAt Fn c sg = some (Fn.start + c * segs tl Fn + sg) := by
  unfold segs at hs ⊢
  unfold HTailF2.tabAt
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨hm, hl⟩)]
  dsimp only
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hc, hs⟩)]

/-- A read's entries are made, and its mark stays, where the sums from column c on are not 0. -/
theorem readEnts_returns (tl : HTailF2) (Fn : HFun) (sg tU cols : Nat) (m : E) (gc : Array E)
    (hm : Fn.mat < tl.NM) (hl : Fn.len ≠ 0) (hs : sg < segs tl Fn) : ∀ (count c : Nat)
    (e : Array Ent), c + count ≤ (tl.mats.getD Fn.mat {}).k →
    (∀ j, c ≤ j → j < c + count → isZeroE (gc.getD j zeroE) = false) →
    ∃ r, tl.readEnts Fn sg tU cols m gc count c e true = some (r, true) ∧
      r.toList.map (fun x => (x.tree, x.row, x.idx)) =
        e.toList.map (fun x => (x.tree, x.row, x.idx)) ++
          (List.range' c count).map fun col =>
            (tU, (Fn.start + col * segs tl Fn + sg) / cols,
              (Fn.start + col * segs tl Fn + sg) % cols)
  | 0, _, e, _, _ => by
    unfold HTailF2.readEnts
    exact ⟨e, rfl, by simp⟩
  | count + 1, c, e, hk, hz => by
    unfold HTailF2.readEnts
    rw [tabAt_some tl Fn c sg hm hl (by omega) hs]
    dsimp only
    rw [hz c (Nat.le_refl c) (by omega)]
    obtain ⟨r, e1, e2⟩ := readEnts_returns tl Fn sg tU cols m gc hm hl hs count (c + 1)
      (e.push { tree := tU, row := (Fn.start + c * segs tl Fn + sg) / cols,
                idx := (Fn.start + c * segs tl Fn + sg) % cols
                coef := mulE m (gc.getD c zeroE) })
      (by omega) fun j h1 h2 => hz j (by omega) (by omega)
    refine ⟨r, e1, ?_⟩
    rw [e2]
    simp [List.range'_succ]

theorem eqRead_returns : Spec.eqRead_returns := by
  intro tl Fn sg laid tU sums front F cs h hlive
  have hlen : 0 < Fn.len := Nat.pos_of_ne_zero h.len
  have hsl : sg * Fn.len < (tl.mats.getD Fn.mat {}).m := by
    have h1 : (sg + 1) * Fn.len ≤ segs tl Fn * Fn.len := Nat.mul_le_mul_right _ h.seg
    have h2 : segs tl Fn * Fn.len ≤ (tl.mats.getD Fn.mat {}).m := Nat.div_mul_le_self _ _
    rw [Nat.succ_mul] at h1
    omega
  have h0 := zzCol_some tl Fn.mat 0 (sg * Fn.len) h.mat (by omega) hsl
  have h1 := zzCol_some tl Fn.mat 1 (sg * Fn.len) h.mat (by omega) hsl
  obtain ⟨ents, he, hn⟩ := readEnts_returns tl Fn sg tU (colsOf F tU) (subE zeroE oneE)
    (tl.gamV.getD Fn.mat #[]) h.mat h.len h.seg (tl.mats.getD Fn.mat {}).k 0
    (Array.emptyWithCapacity (tl.mats.getD Fn.mat {}).k) (by omega)
    fun j _ hj => hlive j (show j < (tl.mats.getD Fn.mat {}).k by omega)
  have hrow : (colsOf F tU != 0 &&
      ((tl.tabAt Fn ((tl.mats.getD Fn.mat {}).k - 1) sg).all fun last =>
        decide (last / colsOf F tU < 2 ^ 32))) = true := by
    have hc : (colsOf F tU != 0) = true := by simpa using h.cols
    rw [hc, Bool.true_and]
    by_cases hk : 0 < (tl.mats.getD Fn.mat {}).k
    · rw [tabAt_some tl Fn _ sg h.mat h.len (by omega) h.seg]
      simpa using h.row hk
    · have hk0 : (tl.mats.getD Fn.mat {}).k = 0 := by omega
      have : tl.tabAt Fn ((tl.mats.getD Fn.mat {}).k - 1) sg = none := by
        unfold HTailF2.tabAt
        split
        · dsimp only
          rw [if_neg fun hq => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
            omega]
        · rfl
      rw [this]
      rfl
  have R : Ret (eqRead tl Fn sg laid sums) front (F, cs) fun _ s' =>
      ∃ c, s' = (F, cs.push c) ∧ ReadClaim tl F Fn sg laid tU c := by
    unfold eqRead
    dsimp only
    refine Ret.bind (P := fun u s₁ => tU = u ∧ s₁ = (F, cs)) (Ret.get _ h.unit ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (P := fun c s₁ => c = colsOf F tU ∧ s₁ = (F, cs))
      (Ret.ask _ rfl ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (P := fun _ s₁ => s₁ = (F, cs)) (Ret.mustAs _ hrow rfl) ?_
    rintro _ _ rfl
    refine Ret.bind (P := fun r s₁ => r = (ents, true) ∧ s₁ = (F, cs))
      (Ret.get _ he ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (P := fun _ s₁ => s₁ = (F, cs)) (Ret.testAs _ rfl rfl) ?_
    rintro _ _ rfl
    refine Ret.bind
      (P := fun c s₁ => c = 0 * tl.mz + tl.off.getD Fn.mat 0 + sg * Fn.len ∧ s₁ = (F, cs))
      (Ret.get _ h0 ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind
      (P := fun c s₁ => c = 1 * tl.mz + tl.off.getD Fn.mat 0 + sg * Fn.len ∧ s₁ = (F, cs))
      (Ret.get _ h1 ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.emit _ ⟨_, rfl, ⟨rfl, ?_, ?_, ?_⟩⟩
    · show ents.toList.map _ = _
      rw [hn, List.range_eq_range']
      simp
    · dsimp only
      rw [lessBeta_slots]
    · simp [runNums]
  obtain ⟨_, _, e, c, rfl, hc⟩ := R
  exact ⟨c, e, hc⟩

/-! ## The two steps of order -/

theorem close_returns : Spec.close_returns := by
  intro tl funs h
  unfold Order.close
  rw [h]
  rfl

theorem front_returns : Spec.front_returns := by
  intro tl L S h1 h2 h3
  unfold Order.front
  simp [h1, h2, h3]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqWeights_returns
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTie_returns
#print axioms VerifiableInference.Desc.First.K8.Honest.eqRead_returns
#print axioms VerifiableInference.Desc.First.K8.Honest.close_returns
#print axioms VerifiableInference.Desc.First.K8.Honest.front_returns
