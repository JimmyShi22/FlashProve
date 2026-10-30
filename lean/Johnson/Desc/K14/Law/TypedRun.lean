-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/TypedRun.lean: what the state that a run of the shared rounds hands to the two
proximity tests means, IN THE LIBRARY's TYPED LETTERS: the rows RecRow and FoldR, and the generator
matrix's values at the drawn locations (Cb/Ld/LdFoldEq.lean, LdLinWords.lean, LdLin.lean).

  run_facts       along a run: the small record's parts that the three families read are the same at
                  all places; the public shape's conditions, the clauses in front of (rec_gamma) and
                  those in front of (fold) hold.
  ptFn, ofFn_ptFn a list of elements of a known length, read as a point.
  seedsFn         the record's seeds, read as the typed seed.
  atOf            the place with a given number in a row's message.
  linW_py_inj     the rows of M are distinct vertices of the cube.
  typed_rows      **the law without chance**: along a run that reaches the two tests, if all
                  constraints on the two groups hold of words, then at the typed data made of the
                  public shape: RecRow holds of the record, gamma and the folded row; the generator
                  matrix applied to the folded row has, at every drawn location, the fold of the
                  column handed; FoldR holds of z_fd, psi_lo, the folded row's message and
                  omega_col.

What is not claimed. The typed data's letters err, eM, rank stay letters. Nothing on the typed rows
Ev and Dot, which read W. That the constraints hold of words is the proximity tests' law's to give.
No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.RunSound
import Johnson.Desc.K14.Law.Weights
import Johnson.Desc.K14.Law.TypedIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground

variable {K : Type} [Field K] (ρ : Reading K)

/-- A guard that lets a computation go on has held. -/
theorem guard_bind_some {α : Type} {c : Bool} {f : Unit → Option α} {a : α}
    (h : (guard (c = true) : Option Unit).bind f = some a) : c = true := by
  by_contra hne
  simp [guard, hne] at h

/-- "(rec_gamma)" says yes only where its three clauses hold. -/
theorem laysRec_clauses (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : laysRec p d rs = some d') : ok (laysRecL p d.loc) = true := by
  have e : laysRec p d rs = (guard (ok (laysRecL p d.loc) = true) : Option Unit).bind fun _ =>
      (joinP d d.loc.gU d.loc.oU.oracle false).bind fun d1 =>
        (recRows p d.loc).bind fun rows => addRowsP d1 d.loc.gU rows := rfl
  rw [e] at h
  exact guard_bind_some h

/-- (fold) can be made only where its two clauses hold. -/
theorem fold_clauses (S : LinShape) (l : Lin) (lay : VectorLay) (row : Row)
    (h : fold S l lay = some row) : ok (foldL S l) = true := by
  unfold fold at h
  simp only [Option.bind_eq_bind] at h
  exact guard_bind_some h

/-- **Along a run.** -/
theorem run_facts (p : Par) (d0 d2 d3 d7 d8 : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (h : SharedRun p d0 d2 d3 d7 d8 r4 cols) :
    d3.loc = d2.loc ∧ (∃ oo sp z, d7.loc = { d2.loc with oOmega := oo, oSp := sp, zFd := z }) ∧
      linOk d0.st.codes p.S = true ∧ ok (laysRecL p d2.loc) = true ∧
      ok (foldL p.S d7.loc) = true := by
  obtain ⟨hS, d1, a1, a2, d4, b1, b2, d5, d6, rs1, rs3, rs6, r7, r8, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6, h7, h8⟩ := h
  obtain ⟨o3, l3⟩ := onward_laysRec p d2 d3 rs3 h3
  obtain ⟨o4, l4⟩ := onward_loc p d3 d4 r4 cols h4
  obtain ⟨oO1, lO1⟩ := onward_recvP ftO d4 b1 (withOmega p.S) idsO rO
  obtain ⟨s5, oo, sp, hoo, l5⟩ := behindOmega_inv p b2 d5 idsO h5
  obtain ⟨o6, l6⟩ := onward_joins p d5 d6 rs6 h6
  have e7 := linZeta_inv d6 d7 r7 h7
  have l7 : d7.loc = { d2.loc with oOmega := oo, oSp := sp, zFd := drawn r7 } := by
    rw [e7]
    show ({ d6.loc with zFd := drawn r7 } : Lin) = _
    rw [l6, l5, cOl, lO1, l4, l3]
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, _⟩ := split_inv p d7 d8 r8 hS h8
  exact ⟨l3, ⟨oo, sp, _, l7⟩, linPoint_ok p d0 d1 rs1 h1, laysRec_clauses p d2 d3 rs3 h3,
    fold_clauses _ _ _ _ hf⟩

/-- A list of elements, read as a point with n coordinates. -/
def ptFn (n : Nat) (l : List E) : Fin n → K := fun i => ρ.val (l.getD i.val zeroE)

/-- Of a list of just n elements it is the list, read. -/
theorem ofFn_ptFn (n : Nat) (l : List E) (h : l.length = n) :
    List.ofFn (ptFn ρ n l) = l.map ρ.val := by
  refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_map, ptFn]
  rw [List.getD_eq_getElem _ _ (by simpa using h2)]

/-- The record's seeds, read as the typed seed. -/
def seedsFn (s : IndexShape) (key : TableKey) : Fin s.answers → (Fin s.cubeBits → K) × K :=
  fun a => (ptFn ρ s.cubeBits (key.seeds.getD a.val default).z,
    ρ.val (key.seeds.getD a.val default).beta)

/-- The place with the number n in a row's message. -/
def atOf (ell : Nat) (h : 0 < ell) (n : Nat) : Fin ell := ⟨n % ell, Nat.mod_lt _ h⟩

omit [Field K] in
/-- The rows of M are distinct vertices of the cube. -/
theorem linW_py_inj {ι κ J : Type} (S : LinShape) (X : Cb.LdIx K ι κ J) (at' : Nat → J) :
    Function.Injective (linW S X at').py := by
  intro y y' h
  have h' : bitsOf S.kRow y.val = bitsOf S.kRow y'.val := h
  have hR : S.matrixRows ≤ 2 ^ S.kRow := le_two_pow_ceilLog2 _
  have e := congrArg (numOf S.kRow) h'
  rw [numOf_bitsOf _ _ (lt_of_lt_of_le y.isLt hR), numOf_bitsOf _ _ (lt_of_lt_of_le y'.isLt hR)]
    at e
  exact Fin.ext e

/-- **The law without chance, in the library's typed letters.** -/
theorem typed_rows [Fintype K] (p : Par) (d0 d2 d3 d7 d8 eU eO : St) (r4 : Fmt.RoundView)
    (cols : List (Nat × List UInt64)) (h : SharedRun p d0 d2 d3 d7 d8 r4 cols)
    (kU : Reaches d8 eU d8.loc.gU) (kO : Reaches d8 eO d8.loc.gOmega) (m : Words K)
    (sU : Means.AllSay ρ eU.st (rowsOn eU d8.loc.gU) m)
    (sO : Means.AllSay ρ eO.st (rowsOn eO d8.loc.gOmega) m) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat)
    (hell : 0 < p.S.fold.index.code.ell) :
    (ixOf ρ p.S.fold err eM rank).RecRow
        (seedsFn ρ p.S.fold.index d2.loc.key,
          recOf p.S.fold.index fun k => ρ.val (d2.loc.key.record.getD k zeroE))
        (ptFn ρ p.S.fold.index.v (gamma p.S d2.loc))
        (fullOf p.S.fold fun k => m d2.loc.oU.oracle .main (d2.loc.oU.lay.index k)) ∧
    (∀ x ∈ locations p r4, ∀ hx : x < 2 ^ p.S.fold.index.code.logN, ∃ col,
      cols.lookup x = some col ∧
      (ixOf ρ p.S.fold err eM rank).G.mulVec
          (fullOf p.S.fold fun k => m d2.loc.oU.oracle .main (d2.loc.oU.lay.index k)) ⟨x, hx⟩ =
        ∑ r ∈ Finset.range (weights p.S d2.loc).size,
          ρ.val ((weights p.S d2.loc).getD r zeroE) * ρ.val (ofF (col.toArray.getD r 0))) ∧
    (linW p.S (ixOf ρ p.S.fold err eM rank) (atOf _ hell)).FoldR
        (ptFn ρ p.S.kRow d7.loc.zFd) (ptFn ρ p.S.kLo (d2.loc.psiSh.take p.S.kLo))
        ((ixOf ρ p.S.fold err eM rank).msg
          (fullOf p.S.fold fun k => m d2.loc.oU.oracle .main (d2.loc.oU.lay.index k)))
        (fun y => omegaOf d7.loc (linLayOmega d7.st.codes p.S) m y.val) := by
  obtain ⟨l3, ⟨oo, sp, z, l7⟩, hok, hrec, hfold⟩ := run_facts p d0 d2 d3 d7 d8 r4 cols h
  obtain ⟨hR, hL, hF⟩ := shared_means ρ p d0 d2 d3 d7 d8 eU eO r4 cols h kU kO m sU sO
  have hi := index_ok_of_linOk _ _ hok
  simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hrec
  obtain ⟨hfit0, _, hgl⟩ := hrec
  have hfit : d2.loc.key.fits p.S.fold.index = true := hfit0
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  obtain ⟨⟨_, hsl⟩, hzl⟩ := hfit
  simp only [ok, foldL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at hfold
  obtain ⟨hpl, hzfl⟩ := hfold
  have hpads : p.S.fold.index.plain + 3 * p.S.fold.index.answers = p.S.fold.index.code.ell := by
    simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hi
    have : p.S.fold.index.pads < p.S.fold.index.code.ell := by tauto
    unfold IndexShape.plain
    unfold IndexShape.pads at this ⊢
    omega
  have hroom : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.plain := by
    simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hS : p.S.ok = true := by tauto
    simp only [LinShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
    tauto
  refine ⟨?_, ?_, ?_⟩
  · rw [recRow_iff ρ p.S.fold err eM rank hpads]
    intro a
    have ha : a.val < d2.loc.key.seeds.length := by rw [hsl]; exact a.isLt
    have hmem : (d2.loc.key.seeds[a.val], a.val) ∈ d2.loc.key.seeds.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simp [ha]
    have h0 := hR _ hmem
    have hg : d2.loc.key.seeds.getD a.val default = d2.loc.key.seeds[a.val] :=
      List.getD_eq_getElem _ _ ha
    unfold RecEq at h0 ⊢
    simp only [seedsFn, hg]
    rw [ofFn_ptFn ρ _ _ (hzl _ (List.getElem_mem ha)), h0]
    refine Finset.sum_congr rfl fun r hr => ?_
    show ρ.val ((weights p.S d2.loc).getD r zeroE) * _ = _
    rw [ofFn_ptFn ρ _ _ hgl, weights_val ρ p.S d2.loc r (by
      rw [hgl]; exact Finset.mem_range.1 hr)]
  · intro x hx hlt
    obtain ⟨col, hc, hEq⟩ := hL x hx
    refine ⟨col, hc, ?_⟩
    rw [l3] at hEq
    exact (mulVec_iff ρ p.S.fold ⟨x, hlt⟩ _ _ _ _).1 hEq
  · rw [foldR_iff]
    have hps : (d2.loc.psiSh.take p.S.kLo).length = p.S.kLo := by
      have : d7.loc.psiSh = d2.loc.psiSh := by rw [l7]
      rw [this] at hpl
      rw [List.length_take, hpl]
      unfold LinShape.kCol
      omega
    rw [ofFn_ptFn ρ _ _ hps, ofFn_ptFn ρ _ _ hzfl]
    have e7 : d7.loc.psiSh = d2.loc.psiSh := by rw [l7]
    have eU7 : d7.loc.oU = d2.loc.oU := by rw [l7]
    unfold FoldEq at hF ⊢
    rw [e7] at hF
    rw [hF]
    refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun t ht => ?_
    have hlt : t + 2 ^ p.S.kLo * j < p.S.fold.index.code.ell := by
      have h1 := Finset.mem_range.1 hj
      have h2 := Finset.mem_range.1 ht
      have h3 : (j + 1) * 2 ^ p.S.kLo ≤ p.S.matrixRows * 2 ^ p.S.kLo :=
        Nat.mul_le_mul_right _ h1
      rw [Nat.succ_mul, Nat.mul_comm j] at h3
      omega
    congr 1
    show uOf d7.loc m _ = m d2.loc.oU.oracle .main
      (d2.loc.oU.lay.index ((t + 2 ^ p.S.kLo * j) % p.S.fold.index.code.ell))
    rw [Nat.mod_eq_of_lt hlt]
    unfold uOf
    rw [eU7]

end Desc.K14.Law
