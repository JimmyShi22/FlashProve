-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/FrontsAt2.lean: CONDITIONAL: A SECOND FORM of one
declaration of Johnson/Desc/ProofFile/Honest/K5/Law/FrontsAt.lean: `frontsOk_at`.
Those take as a premise that the cells meet all three of the library's families of
identities on an attention segment (`AtIdn`, Johnson/Desc/K5/Honest/Law/Idn.lean). These take the
first two families alone (`Idn12`, Johnson/Desc/K5/Honest/Law/Idn12/Idn2.lean).

Why. CONDITIONALLY, `Idn12` follows from two items that the row of the segment's own rounds asks in
front (Johnson/Desc/K5/Honest/Law/IdnOfAsked.lean): among others under the library's head on the
public input as a hypothesis, hH and hc; none of these, nor the items, is shown. The third family on
the whole cube follows from no such item.

How. THE TEXT IS THE ELDER FILE's: each declaration named above with its docstring and its proof,
the premise's name exchanged, and each name of a declaration that has a second form exchanged for
that form's (a subscript 2 at its end). Every other lemma is called from the elder files, which are
imported and stay as they are.

Limits. Those of that file, whose head says what each premise is.
Every theorem is conditional.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FrontsAt
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.RowsBehind2

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard hear pointsOf)
open H2K5.Honest (PublicAll Idn12 tOf iSE iVM iVD iZero iM6 iSF iOm4 iSD iOm5 iHB heardAt pubOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **What is still owed for the rows, paid at the member** (`FrontsOk₂`,
Honest/K5/Law/Idn12/RowsBehind2.lean) but for two clauses. CONDITIONAL on: the three ties between
the witness and the honest side (Sc), WHICH ARE NOT SHOWN; the half's seat; the thread in front;
the challenges fit; the prover's side of the step; an attention segment is open; the kind's hearing
returns on the rounds played; what the lookup on the calls heard is there (hg); the public premises
at the seat's numbers and the plan's lookup shape (Pu); there is a pair, which is handed through;
AND THE WITNESS's CELLS MEET THE FIRST TWO OF THE LIBRARY's FAMILIES OF IDENTITIES (Id), which is
handed through. -/
theorem frontsOk_at₂ (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {F : Fork} {hd5 : Heard}
    {st : P.St} (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, st))
    {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) (Pu : PublicAll Z.P A.fs)
    (hpairs : Z.P.x.pairs ≠ 0)
    (Id : Idn12 Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace)))) :
    FrontsOk₂ Z (inOf Z.P.S Z.link (cells m.st.input.trace)) m.st.heard ds g.zk hd5 := by
  obtain ⟨g0, hg0, K3, -⟩ := Sc.keyTie k s m E hT att e
  obtain rfl : g0 = g := Option.some.inj (hg0.symm.trans hg)
  obtain ⟨g1, hg1, hk, -⟩ := key_at Sc hT e hd
  obtain rfl : g1 = g0 := Option.some.inj (hg1.symm.trans hg)
  have H := Pu.sized
  have Kp := H2K5.Honest.keyPts_of_keysFit Pu.keys K3
  have SF : ∀ q, H2K5.Honest.SameTo Z.P.x q hd5
      (heardAt Z.P (frontQ Z m.st.heard ds q) fun _ => none) := fun q =>
    same_front Hs hT.2.1 hM hh (Nat.le_refl _)
  refine { sized := H, planned := Pu.planned, token := Pu.lt16, someUnit := Pu.score,
           somePair := hpairs, key := hk, div := ?_, unit := ?_,
           omF := (SF _).om (by unfold iM6 iSF; omega),
           ptF := (SF _).point (by unfold iZero iSF; omega),
           omH := (SF _).om'' (by unfold iOm5 iHB; omega),
           ptH := (SF _).point (by unfold iZero iHB; omega), rho := ?_,
           om4 := ((SF _).om' (by unfold iOm4 iSD; omega)).symm, index := ?_, idn := Id }
  · intro q _
    obtain ⟨p₀, Dv, hp₀, hDv, ed, -⟩ := div_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x q)
    obtain ⟨uW, Cu⟩ := H2K5.Honest.pts_cut (show pointsOf Z.P.g _ _ _ = some p₀ from hp₀)
    exact ⟨Dv, _, _, hDv, H2K5.Honest.divPts_pubOf Reading.gl H hDv (by rw [hk]; exact Kp) Pu.wl,
      by rw [ed, Cu.pwW]; exact Pu.pairsWl uW Cu.single _⟩
  · intro i u ug hu hug
    obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x i)
    obtain ⟨kk, hkk, Ld⟩ := RowsAt.forall₂_at
      (H2K5.Honest.units_laid (show pointsOf Z.P.g _ _ _ = some p₀ from hp₀)) i ug hug
    have hk' : (H2K5.Honest.ptsOf Z.P (frontQ Z m.st.heard ds i)).bind (·.scores[i]?) =
        some kk := by
      show (H2K5.Honest.ptsOf Z.P (chalOf Z _)).bind _ = _
      rw [hp₀]
      show p₀.scores[i]? = some kk
      rw [← Array.getElem?_toList]
      exact hkk
    have pr : H2K5.Honest.PairsAre Z.P.g kk.pw := by
      rw [Ld.pw]
      exact Pu.pairsScores ug (List.mem_of_getElem? hug) _
    have Kq : P.KeyPtsAre Reading.gl (OnBytes.Road.L5.callsOf A.fs)
        (pubOf Reading.gl Z.P (frontQ Z m.st.heard ds i)
          (OnBytes.Slice.readV (g1.zx ++ g1.zy))).z (frontQ Z m.st.heard ds i).zk := by
      rw [hk]
      exact Kp
    refine ⟨kk, hk', (Pu.pieces ug (List.mem_of_getElem? hug)).trans
      (Pu.geo.score u (List.mem_of_getElem? hu)).symm, ?_⟩
    obtain ⟨_, _, u1, u2, _, _, _, U, Um, Ud, -, -⟩ := Pu.units
    have hsc : Z.P.g.scores = [u1, u2] := U.sco
    match i, hu, hug, hk', Kq with
    | 0, hu, hug, hk', Kq =>
      obtain rfl : u1 = ug := by
        rw [hsc] at hug
        exact Option.some.inj hug
      exact H2K5.Honest.sKM_tame_x Reading.gl H _ hu hug hk' U.below Pu.vKM Kq Um pr
    | 1, hu, hug, hk', Kq =>
      obtain rfl : u2 = ug := by
        rw [hsc] at hug
        exact Option.some.inj hug
      exact H2K5.Honest.sKD_tame_x Reading.gl H _ hu hug hk' U.on Pu.vKD Kq Ud Pu.lookFits.lM pr
    | n + 2, _, hug, _, _ =>
      rw [hsc] at hug
      cases hug
  · obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSD Z.P.x))
    obtain ⟨uW, Cu⟩ := H2K5.Honest.pts_cut (show pointsOf Z.P.g _ _ _ = some p₀ from hp₀)
    show (H2K5.Honest.maxOf Z.P (chalOf Z _)).scF.r = _
    unfold H2K5.Honest.maxOf
    rw [hp₀]
    show p₀.x.scF.r = _
    rw [Cu.scF]
    exact ((SF _).atIndex (by unfold iSF iSD; omega)).symm
  · refine ⟨pubOf Reading.gl Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => 0,
      H2K5.Honest.indexPts_pubOf Reading.gl Z.P _ _, fun j _ => ?_, fun j _ => ?_⟩
    · show OnBytes.Road.pt Reading.gl
        (heardAt Z.P (frontQ Z m.st.heard ds (iM6 Z.P.x)) fun _ => none).point j =
        OnBytes.Road.pt Reading.gl
          (heardAt Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => none).point j
      rw [← (SF (iM6 Z.P.x)).point (by unfold iZero iM6; omega),
        ← (SF (iSF Z.P.x)).point (by unfold iZero iSF; omega)]
    · show OnBytes.Road.pt Reading.gl
        (heardAt Z.P (frontQ Z m.st.heard ds (iM6 Z.P.x)) fun _ => none).point (Z.P.D.lg + j) =
        OnBytes.Road.pt Reading.gl
          (heardAt Z.P (frontQ Z m.st.heard ds (iSF Z.P.x)) fun _ => none).point (Z.P.D.lg + j)
      rw [← (SF (iM6 Z.P.x)).point (by unfold iZero iM6; omega),
        ← (SF (iSF Z.P.x)).point (by unfold iZero iSF; omega)]

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.frontsOk_at₂
