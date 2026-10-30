-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/UnderIndex.lean: CONDITIONAL, among others on ties that are
not shown: at the member of a chain's thread at which the honest side of an attention segment's own
rounds (kind K5) is seated, in the world in which the items "the forms of a run are worth 0" are
said behind the member: UNDER THE SLOTS THAT THE CLAIMS ON THE MAXIMUM, ON ITS INDEX AND ON THE
INDEX's CELLS NAME LIE THE PROVER's VALUES AT THE VERIFIER's OWN NAMED POINTS (Under7, Under8,
Johnson/Desc/K5/Honest/Law/SayOf.lean). Statements with their proofs. under7 AND under8 ARE
CONDITIONAL and hang on the ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN. The
three lemmas sum_… have no premise; maxOf_some asks that the verifier's function returns.

  sum_iSF, sum_iSD, sum_iHB   what the row's jobs sum at three parts
  maxOf_some     the named points of the maximum, where the verifier's function returns
  under7         **Under7**
  under8         **Under8**

The premises are those of Honest/K5/Law/UnderDiv.lean: see its head.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.UnderDiv
import Johnson.Desc.K5.Honest.Law.ReadSF
import Johnson.Desc.K5.Honest.Law.ReadSD
import Johnson.Desc.K5.Honest.Law.ReadHB

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts hear pointsOf)
open H2K5.Honest (K5In Pub5 Chal shapes slotsTo ptsOf maxOf iSE iVM iVD iZero iM6 iSF iOm4 iSD iHB
  sSF sSD sHB m6 hbA Under7 Under8 counted_spec)

theorem sum_iSF (P : Pub5) (w : K5In) (c : Chal) : (jobs P).sum (iSF P.x) w c = sSF P w c := by
  simp [jobs, iSF, iVD, iVM, iSE]

theorem sum_iSD (P : Pub5) (w : K5In) (c : Chal) : (jobs P).sum (iSD P.x) w c = sSD P w c := by
  simp [jobs, iSD, iSF, iVD, iVM, iSE]

theorem sum_iHB (P : Pub5) (w : K5In) (c : Chal) : (jobs P).sum (iHB P.x) w c = sHB P w c := by
  simp [jobs, iHB, iSD, iSF, iVD, iVM, iSE]

/-- The named points of the maximum, where the verifier's function for the points returns. -/
theorem maxOf_some (P : Pub5) {c : Chal} {p₀ : Pts} (hp : ptsOf P c = some p₀) :
    maxOf P c = p₀.x := by
  unfold maxOf
  rw [hp]
  rfl

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  (hc : Z.P.counted = true)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
  (hz : OnBytes.Model.Road.Sized att.F) {G : Fork} {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
  (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
  {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {i : P.Runs.In}
  (hi : pointsOf Z.P.g g.zk hd5 Lf = some i.p)
include Hs Sc hc hT hd hM e hD hz hh hg hi

/-- **Under the slots that claim 7 names lie the prover's values at the verifier's points.**
CONDITIONAL: see the head. -/
theorem under7 : Under7 (worldOwn (behindPart s att G) [] D) Z.P.S i
    (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  obtain ⟨-, c2, c3, -, c5, -⟩ := counted_spec hc
  have L := laid_at Hs hd hM hz hh
  have Al := along_at Hs hd hM ⟨hz.vp, hz.mf, hz.got⟩ hh
  have PA := K5Law.points_are hi
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun l hl => ?_, fun t u ht hu => ?_⟩
  · have ht' : t < Z.P.x.pairs := by
      rw [c2]
      exact ht
    obtain ⟨n, hn⟩ : ∃ n, Z.P.x.pairs = n + 1 := ⟨Z.P.x.pairs - 1, by omega⟩
    obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iM6 Z.P.x))
    have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
    rw [PA.sM6, maxima_slots Hs Sc hT hd hM e hD L hn t (by omega), SumLaw.padTo_getD,
      if_pos (by omega)]
    unfold m6
    rw [maxOf_some Z.P hp₀]
    show Reading.gl.val (((List.range Z.P.g.NP).map fun b => H2K5.Honest.under (P.eqTab p₀.x.tg)
      fun hk => H2K5.Honest.under (P.eqTab p₀.x.ti) fun u =>
        (inOf Z.P.S Z.link (cells m.st.input.trace)).mx b hk u).getD t zeroE) = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show t < Z.P.g.NP from ht), K.tg (Nat.lt_succ_self _),
      K.ti (Nat.lt_succ_self _)]
    rfl
  · have hq := H2K5.Honest.shape_iSF Z.P.x
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hq (L.atIndex _ hq) Al.atIndex (by
      rw [sum_iSF]
      show 2 * Z.P.g.NP = 2 * Z.P.x.pairs
      rw [c2])
    have ht' : 2 * t < 2 * Z.P.x.pairs := by
      rw [c2]
      exact Nat.mul_lt_mul_of_pos_left ht (by omega)
    rw [PA.scF]
    show (worldOwn (behindPart s att G) [] D).slot (hd5.atIndex.sEnd + 2 * t) = _
    rw [hE _ ht', sum_iSF, H2K5.Honest.sSF_endAt Z.P _ _ _ (by rw [← c2]; exact ht'), hr]
    rfl
  · have hq := H2K5.Honest.shape_iSD Z.P.x
    obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSD Z.P.x))
    have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hq (L.key _ hq) Al.key (by
      rw [sum_iSD]
      show Z.P.g.Lam + Z.P.g.NP * Z.P.g.lt = Z.P.x.Lam + Z.P.x.pairs * Z.P.x.lt
      rw [c2, c3, c5])
    have hl' : l < Z.P.x.Lam + Z.P.x.pairs * Z.P.x.lt := by
      rw [c5]
      exact Nat.lt_of_lt_of_le hl (Nat.le_add_right _ _)
    rw [PA.scd]
    show (worldOwn (behindPart s att G) [] D).slot (hd5.key.sEnd + l) = _
    rw [hE _ hl', sum_iSD, H2K5.Honest.sSD_eq,
      H2K5.Honest.sd_endAt_kc _ _ _ _ _ (show l < Z.P.g.Lam from hl), hr]
    unfold H2K5.Honest.rhoOf
    rw [maxOf_some Z.P hp₀, K.scF (show iSF Z.P.x < iSD Z.P.x by
      unfold iSF iSD
      omega)]
    rfl
  · have hq := H2K5.Honest.shape_iSD Z.P.x
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hq (L.key _ hq) Al.key (by
      rw [sum_iSD]
      show Z.P.g.Lam + Z.P.g.NP * Z.P.g.lt = Z.P.x.Lam + Z.P.x.pairs * Z.P.x.lt
      rw [c2, c3, c5])
    have hj' : Z.P.S.Lam + t * Z.P.S.cf.lt + u < Z.P.x.Lam + Z.P.x.pairs * Z.P.x.lt := by
      rw [c2, c3, c5]
      show Z.P.S.Lam + t * Z.P.S.cf.lt + u < Z.P.S.Lam + Z.P.S.NP * Z.P.S.cf.lt
      have h1 : (t + 1) * Z.P.S.cf.lt ≤ Z.P.S.NP * Z.P.S.cf.lt := Nat.mul_le_mul_right _ ht
      rw [Nat.succ_mul] at h1
      omega
    rw [PA.scd]
    show (worldOwn (behindPart s att G) [] D).slot
      (hd5.key.sEnd + (Z.P.S.Lam + t * Z.P.S.cf.lt + u)) = _
    rw [hE _ hj', sum_iSD, H2K5.Honest.sSD_eq]
    show Reading.gl.val ((H2K5.Honest.sdOf Z.P.g _ _ _).endAt _
      (Z.P.g.Lam + t * Z.P.g.lt + u)) = _
    rw [H2K5.Honest.sd_endAt_ib _ _ _ _ _ t (show u < Z.P.g.lt from hu), hr]
    rfl

/-- **Under the slots that claim 8 names lie the prover's values at the verifier's points.**
CONDITIONAL: see the head. -/
theorem under8 : Under8 (worldOwn (behindPart s att G) [] D) Z.P.S i
    (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  obtain ⟨-, c2, -⟩ := counted_spec hc
  have L := laid_at Hs hd hM hz hh
  have Al := along_at Hs hd hM ⟨hz.vp, hz.mf, hz.got⟩ hh
  have PA := K5Law.points_are hi
  intro j hj
  have hq := H2K5.Honest.shape_iHB Z.P.x
  obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hq (L.cells _ hq) Al.cells (by
    rw [sum_iHB]
    show 2 * Z.P.g.NP = 2 * Z.P.x.pairs
    rw [c2])
  have hj' : j < 2 * Z.P.x.pairs := by
    rw [c2]
    exact hj
  rw [PA.scH]
  show (worldOwn (behindPart s att G) [] D).slot (hd5.cells.sEnd + j) = _
  rw [hE j hj', sum_iHB]
  by_cases h2 : j % 2 = 0
  · rw [if_pos h2]
    have ej : j = 2 * (j / 2) := by omega
    rw [ej, H2K5.Honest.sHB_even, hr, ← ej]
    rfl
  · rw [if_neg h2]
    have ej : j = 2 * (j / 2) + 1 := by omega
    have e2 : (2 * (j / 2) + 1) / 2 = j / 2 := by omega
    rw [ej, H2K5.Honest.sHB_odd, hr, e2]
    rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sum_iSF
#print axioms ProofFile.Honest.K5.sum_iSD
#print axioms ProofFile.Honest.K5.sum_iHB
#print axioms ProofFile.Honest.K5.maxOf_some
#print axioms ProofFile.Honest.K5.under7
#print axioms ProofFile.Honest.K5.under8
