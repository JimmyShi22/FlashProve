-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/UnderDiv.lean: CONDITIONAL, among others on ties that are
not shown: at the member of a chain's thread at which the honest side of an attention segment's own
rounds (kind K5) is seated, in the world in which the items "the forms of a run are worth 0" are
said behind the member: UNDER THE SLOTS THAT THE CLAIMS ON THE DIVISION AND ON THE VALUE PRODUCT
NAME LIE THE PROVER's VALUES AT THE VERIFIER's OWN NAMED POINTS (Under5, UnderV,
Johnson/Desc/K5/Honest/Law/SayOf.lean). Statements with their proofs. under5 AND underV ARE
CONDITIONAL and hang on the ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN. The
six tools take no tie; sum_iSE, sum_iVM and sum_iVD have no premise.

  products_end   an end value of a sum of products of two maps, by its number
  sum_iSE, sum_iVM, sum_iVD   what the row's jobs sum at three parts
  lead_list      the scalars in front of the division's sumcheck, as a list
  five_is        the first of these scalars' slots
  under5         **Under5**
  underV         **UnderV**, at the two sums' totals, the accumulated output and the denominator

The premises, beside those of sum_slots (Honest/K5/Law/Slots.lean): the public test on the planner's
numbers (Pub5.counted, Johnson/Desc/K5/Honest/Law/Lengths.lean); the ledger's arrays have their
length; the kind's hearing returns at the rounds as played; i.p are the named points that the
verifier's function makes of what was heard, at the key points that the lookup on the calls left.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtPoints
import Johnson.Desc.K5.Honest.Law.SayOf
import Johnson.Desc.K5.Honest.Law.Lengths

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts hear pointsOf)
open H2K5.Honest (K5In Pub5 Chal Summand ofProducts shapes slotsTo ptsOf iSE iGam iVM iVD sSE sVM
  sVD accAt zcAt rhAt rhpAt ibAt rh2At rhp2At atRow Under5 UnderV counted_spec)

/-- An end value of a sum of products of two maps, by its number. -/
theorem products_end {S : Summand} {vars np : Nat} {Wf : Array E → Array E}
    {A B : Array E → Nat → E} (hS : S = ofProducts vars np Wf A B) (xs : List E) (j : Nat) :
    S.endAt xs j = if j % 2 = 0 then A xs.toArray (j / 2) else B xs.toArray (j / 2) := by
  subst hS
  show (if (j % 2 == 0) = true then A xs.toArray (j / 2) else B xs.toArray (j / 2)) = _
  by_cases h : j % 2 = 0
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · rw [if_neg h, if_neg (by simpa using h)]

theorem sum_iSE (P : Pub5) (w : K5In) (c : Chal) : (jobs P).sum (iSE P.x) w c = sSE P w c := by
  simp [jobs, iSE]

theorem sum_iVM (P : Pub5) (w : K5In) (c : Chal) : (jobs P).sum (iVM P.x) w c = sVM P w c := by
  simp [jobs, iVM, iSE]

theorem sum_iVD (P : Pub5) (w : K5In) (c : Chal) : (jobs P).sum (iVD P.x) w c = sVD P w c := by
  simp [jobs, iVD, iVM, iSE]

/-- The scalars in front of the division's sumcheck, as a list. CONDITIONAL: the verifier's function
for the points returns p₀ at the challenges c. -/
theorem lead_list (P : Pub5) (w : K5In) {c : Chal} {p₀ : Pts} (hp : ptsOf P c = some p₀) :
    (jobs P).alone (iSE P.x) w c =
      [accAt P.g w p₀.d, (sSE P w c).total, zcAt P.g w p₀.d, rhAt P.g w p₀.d, rhpAt P.g w p₀.d] ++
        ibAt P.g w p₀.d ++ [rh2At P.g w p₀.d, rhp2At P.g w p₀.d] := by
  rw [alone_iSE]
  unfold H2K5.Honest.leadSE
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

include Hs hc hd hM hz hh in
/-- The first slot of the scalars in front of the division's sumcheck. -/
theorem five_is : hd5.five = att.F.next + slotsTo Z.P.x (iSE Z.P.x) := by
  have L := laid_at Hs hd hM hz hh
  have hq := H2K5.Honest.shape_iSE Z.P.x
  rw [H2K5.Honest.leadBehind_zero Z.P.x (counted_spec hc).1] at hq
  have h1 := L.five
  have h2 : hd5.division.first =
      att.F.next + slotsTo Z.P.x (iSE Z.P.x) + (0 + 5 + Z.P.x.lt + 2) := (L.division _ hq).first
  omega

variable {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {i : P.Runs.In}
  (hi : pointsOf Z.P.g g.zk hd5 Lf = some i.p)
include Hs Sc hc hT hd hM e hD hz hh hg hi

/-- **Under the slots that claim 5 names lie the prover's values at the verifier's points.**
CONDITIONAL: see the head. -/
theorem under5 : Under5 (worldOwn (behindPart s att G) [] D) Z.P.S i
    (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  obtain ⟨c1, c2, c3, -⟩ := counted_spec hc
  have L := laid_at Hs hd hM hz hh
  have Al := along_at Hs hd hM ⟨hz.vp, hz.mf, hz.got⟩ hh
  have PA := K5Law.points_are hi
  have hq := H2K5.Honest.shape_iSE Z.P.x
  rw [H2K5.Honest.leadBehind_zero Z.P.x c1] at hq
  have SP := L.division _ hq
  have hl := lead_slots Hs Sc hT hd hM e hD hq SP
  have h5 := five_is Hs hc hd hM hz hh
  obtain ⟨p₀, Dv, hp₀, hDv, ed, eec⟩ :=
    div_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))
  have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
  have hk := K.key.d
  have hlist := lead_list Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) hp₀
  have hib : (ibAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) p₀.d).length = Z.P.x.lt := by
    unfold ibAt
    rw [List.length_map, List.length_range, c3]
  have hkk := hk
  simp only [H2K5.Honest.divKey, Prod.mk.injEq] at hkk
  obtain ⟨e1, e2, -, -, -, -, -, e8, e9, e10, -⟩ := hkk
  refine ⟨?_, ?_, ?_, fun t ht => ?_, ?_, ?_, ?_⟩
  · rw [PA.s5, h5, hl 2 (by omega), hlist]
    show Reading.gl.val (zcAt Z.P.g _ p₀.d) = _
    rw [H2K5.Honest.zcAt_same _ _ hk]
    rfl
  · rw [PA.s5, h5, hl 3 (by omega), hlist]
    show Reading.gl.val (rhAt Z.P.g _ p₀.d) = _
    rw [H2K5.Honest.rhAt_same _ _ hk]
    rfl
  · rw [PA.s5, h5, hl 4 (by omega), hlist]
    show Reading.gl.val (rhpAt Z.P.g _ p₀.d) = _
    rw [H2K5.Honest.rhpAt_same _ _ hk]
    rfl
  · have ht' : t < Z.P.x.lt := by
      rw [c3]
      exact ht
    rw [PA.sIB, L.bits, h5,
      show att.F.next + slotsTo Z.P.x (iSE Z.P.x) + 5 + t =
        att.F.next + slotsTo Z.P.x (iSE Z.P.x) + (5 + t) by omega,
      hl (5 + t) (by omega), hlist,
      List.getD_append _ _ _ _ (by
        rw [List.length_append, hib]
        show 5 + t < 5 + Z.P.x.lt
        omega),
      List.getD_append_right _ _ _ _ (by
        show 5 ≤ 5 + t
        omega)]
    show Reading.gl.val ((ibAt Z.P.g _ p₀.d).getD (5 + t - 5) zeroE) = _
    rw [Nat.add_sub_cancel_left]
    unfold ibAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by rw [← c3]; exact ht'), e2, e9, e10]
    rfl
  · rw [PA.s5h, L.two, h5,
      show att.F.next + slotsTo Z.P.x (iSE Z.P.x) + 5 + Z.P.x.lt =
        att.F.next + slotsTo Z.P.x (iSE Z.P.x) + (5 + Z.P.x.lt) by omega,
      hl (5 + Z.P.x.lt) (by omega), hlist,
      List.getD_append_right _ _ _ _ (by
        rw [List.length_append, hib]
        exact Nat.le_refl _),
      List.length_append, hib]
    show Reading.gl.val (([rh2At Z.P.g _ p₀.d, rhp2At Z.P.g _ p₀.d] : List OnBytes.E).getD
      (5 + Z.P.x.lt - (5 + Z.P.x.lt)) zeroE) = _
    rw [Nat.sub_self]
    show Reading.gl.val (rh2At Z.P.g _ p₀.d) = _
    rw [H2K5.Honest.rh2At_same _ _ hk]
    rfl
  · rw [PA.s5h, L.two, h5,
      show att.F.next + slotsTo Z.P.x (iSE Z.P.x) + 5 + Z.P.x.lt + 1 =
        att.F.next + slotsTo Z.P.x (iSE Z.P.x) + (5 + (Z.P.x.lt + 1)) by omega,
      hl (5 + (Z.P.x.lt + 1)) (by omega), hlist,
      List.getD_append_right _ _ _ _ (by
        rw [List.length_append, hib]
        show 5 + Z.P.x.lt ≤ 5 + (Z.P.x.lt + 1)
        omega),
      List.length_append, hib]
    show Reading.gl.val (([rh2At Z.P.g _ p₀.d, rhp2At Z.P.g _ p₀.d] : List OnBytes.E).getD
      (5 + (Z.P.x.lt + 1) - (5 + Z.P.x.lt)) zeroE) = _
    rw [show 5 + (Z.P.x.lt + 1) - (5 + Z.P.x.lt) = 1 by omega]
    show Reading.gl.val (rhp2At Z.P.g _ p₀.d) = _
    rw [H2K5.Honest.rhp2At_same _ _ hk]
    rfl
  · intro j hj
    have hS := H2K5.Honest.sSE_eq Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) _ hDv
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hq SP Al.division (by
      rw [sum_iSE, hS]
      show 2 * Z.P.g.NP = 2 * Z.P.x.pairs
      rw [c2])
    have hj' : j < 2 * Z.P.x.pairs := by
      rw [c2]
      exact hj
    rw [PA.scE]
    show (worldOwn (behindPart s att G) [] D).slot (hd5.division.sEnd + j) = _
    rw [hE j hj', sum_iSE, products_end hS, hr, ed, eec, e1, e8]
    rfl

/-- **Under the slots that claim 6 names lie the prover's values**: the two sums' totals, each at
the challenges in front of its own part; the accumulated output and the denominator, and the end
values, at the verifier's points. CONDITIONAL: see the head. -/
theorem underV : UnderV (worldOwn (behindPart s att G) [] D) Z.P.S i
    (inOf Z.P.S Z.link (cells m.st.input.trace))
    (sVM Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
      (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x))))).total
    (sVD Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
      (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))))).total
    (accAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d)
    (zcAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) := by
  obtain ⟨c1, c2, -⟩ := counted_spec hc
  have L := laid_at Hs hd hM hz hh
  have Al := along_at Hs hd hM ⟨hz.vp, hz.mf, hz.got⟩ hh
  have PA := K5Law.points_are hi
  have hq := H2K5.Honest.shape_iSE Z.P.x
  rw [H2K5.Honest.leadBehind_zero Z.P.x c1] at hq
  have hl := lead_slots Hs Sc hT hd hM e hD hq (L.division _ hq)
  have h5 := five_is Hs hc hd hM hz hh
  obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))
  have K0 := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
  have hlist := lead_list Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) hp₀
  refine ⟨?_, ?_, ?_, (under5 Hs Sc hc hT hd hM e hD hz hh hg hi).zc, fun j hj => ?_,
    fun j hj => ?_⟩
  · rw [PA.sCl, ← Aff.value_slot (ρ := Reading.gl)]
    exact start_below Hs Sc hT hd hM e hD L
  · rw [PA.sCl, ← Aff.value_slot (ρ := Reading.gl)]
    exact start_on Hs Sc hT hd hM e hD L
  · rw [PA.s5, h5, ← Nat.add_zero (att.F.next + slotsTo Z.P.x (iSE Z.P.x)), hl 0 (by omega), hlist]
    show Reading.gl.val (accAt Z.P.g _ p₀.d) = _
    rw [H2K5.Honest.accAt_same _ _ K0.key.d]
  · obtain ⟨p₁, Dv, hp₁, hDv, ed, eec⟩ :=
      div_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x))
    have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₁
    have hk := K.key.d
    have hkk := hk
    simp only [H2K5.Honest.divKey, Prod.mk.injEq] at hkk
    have e8 := hkk.2.2.2.2.2.2.2.1
    have hS := H2K5.Honest.sVM_eq Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) _ hDv
    have hqM := H2K5.Honest.shape_iVM Z.P.x
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hqM (L.below _ hqM) Al.below (by
      rw [sum_iVM, hS]
      show 2 * Z.P.g.NP = 2 * Z.P.x.pairs
      rw [c2])
    have hj' : j < 2 * Z.P.x.pairs := by
      rw [c2]
      exact hj
    rw [PA.vpm]
    show (worldOwn (behindPart s att G) [] D).slot (hd5.below.sEnd + j) = _
    rw [hE j hj', sum_iVM, products_end hS, hr, ed, eec, e8]
    simp only [H2K5.Honest.vmA_same Z.P.g _ hk,
      H2K5.Honest.vmB_same Z.P.g _ hk (K.gam (Nat.lt_succ_self _))]
    rfl
  · obtain ⟨p₁, Dv, hp₁, hDv, ed, eec⟩ :=
      div_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))
    have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₁
    have hk := K.key.d
    have hkk := hk
    simp only [H2K5.Honest.divKey, Prod.mk.injEq] at hkk
    have e8 := hkk.2.2.2.2.2.2.2.1
    have hS := H2K5.Honest.sVD_eq Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) _ hDv
    have hqD := H2K5.Honest.shape_iVD Z.P.x
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hqD (L.on _ hqD) Al.on (by
      rw [sum_iVD, hS]
      show 2 * Z.P.g.NP = 2 * Z.P.x.pairs
      rw [c2])
    have hj' : j < 2 * Z.P.x.pairs := by
      rw [c2]
      exact hj
    rw [PA.vpd]
    show (worldOwn (behindPart s att G) [] D).slot (hd5.on.sEnd + j) = _
    rw [hE j hj', sum_iVD, products_end hS, hr, ed, eec, e8]
    simp only [H2K5.Honest.vdA_same Z.P.g _ hk,
      H2K5.Honest.vdB_same Z.P.g _ hk (K.gam (show iGam Z.P.x < iVD Z.P.x by
        unfold iGam iVD
        omega))]
    rfl

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.products_end
#print axioms ProofFile.Honest.K5.sum_iSE
#print axioms ProofFile.Honest.K5.sum_iVM
#print axioms ProofFile.Honest.K5.sum_iVD
#print axioms ProofFile.Honest.K5.lead_list
#print axioms ProofFile.Honest.K5.five_is
#print axioms ProofFile.Honest.K5.under5
#print axioms ProofFile.Honest.K5.underV
