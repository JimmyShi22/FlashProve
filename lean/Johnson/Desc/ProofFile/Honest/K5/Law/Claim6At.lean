-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Claim6At.lean: CONDITIONAL: at the member of a chain's thread
at which the honest side of an attention segment's own rounds (kind K5) is seated: THE EQUATION OF
THE VALUE PRODUCT, ON THE FOUR VALUES AS THEY LIE UNDER THE SLOTS: the two sums' totals, each at the
challenges in front of its own part; the accumulated output and the denominator at the verifier's
own named points; the batching element as the verifier's points hold it. It is the premise he of
say6_holds (Honest/K5/Law/SayParts.lean). One statement with its proof.

  claim6_at      CONDITIONAL: the equation, out of claim6_fronts
                 (Johnson/Desc/K5/Honest/Law/Starts.lean), which has both totals at one list of
                 challenges, the two lone values at another, and the library's own letter for the
                 batching element

The premises. Those of pts_to (Honest/K5/Law/AtPoints.lean), the ties (K5Script,
Honest/K5/Law/Script.lean, WHICH ARE NOT SHOWN) among them. Public: the two premises on the
shape's and the planner's numbers (Sized, Planned); the unit of the list of the remainders' low
bits is the library's family (UW); piece number b is pair number b (pr). On the lookup's points: the
key points that the lookup on the calls left, read, are the library's at an end point z (Kp). ON THE
CELLS: THE IDENTITIES OF AN HONEST ATTENTION SEGMENT (AtIdn, Johnson/Desc/K5/Honest/Law/Idn.lean).
Of these the proof spends the third family alone, through its batch at the point z (Rider, same
file); Honest/K5/Law/Idn12/Claim6At2.lean has the statement under that weaker premise.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AtPoints
import Johnson.Desc.K5.Honest.Law.Starts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left hear pointsOf KeyPtsAre UnitIs)
open H2K5.Honest (iSE iGam iVM iVD sVM sVD accAt zcAt Planned PairsAre AtIdn tOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **The equation of the value product, on the four values as they lie under the slots.**
CONDITIONAL: see the head. -/
theorem claim6_at (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {F : Fork} {hd5 : Heard}
    {st : P.St} (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, st))
    {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {i : P.Runs.In}
    (hi : pointsOf Z.P.g g.zk hd5 Lf = some i.p)
    (H : H2K5.Honest.Sized Z.P) (Pl : Planned Z.P) {C : Inst.Model.AttSeg.Calls} {z : Nat → GE}
    (Kp : KeyPtsAre Reading.gl C z g.zk)
    (UW : ∀ wl, Z.P.g.single .wl = some wl → ∃ q, UnitIs Z.P.D C .w3 q wl)
    (pr : PairsAre Z.P.g i.p.d.pwW)
    (Id : AtIdn Z.P.D (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace)))) :
    Reading.gl.val (sVM Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVM Z.P.x))))).total +
      Reading.gl.val (sVD Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))))).total -
      Reading.gl.val (accAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) -
      Reading.gl.val i.p.d.gam *
        Reading.gl.val (zcAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) i.p.d) = 0 := by
  obtain ⟨g', hg', hk, -⟩ := key_at Sc hT e hd
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  obtain ⟨p₁, Dv, hp₁, hDv, ed, -⟩ :=
    div_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x))
  obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))
  have K1 := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₁
  have K0 := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
  have w1 : p₁.d.pwW = i.p.d.pwW := by
    have h1 := K1.key.d
    simp only [H2K5.Honest.divKey, Prod.mk.injEq] at h1
    exact h1.1
  have w0 : p₀.d.pwW = i.p.d.pwW := by
    have h1 := K0.key.d
    simp only [H2K5.Honest.divKey, Prod.mk.injEq] at h1
    exact h1.1
  have R := H2K5.Honest.divPts_pubOf Reading.gl H hDv (C := C) (z := z)
    (by rw [hk]; exact Kp) UW
  have L0 := H2K5.Honest.lonePts_of Reading.gl H hp₀ (C := C)
    (p := H2K5.Honest.pubOf Reading.gl Z.P
      (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iVD Z.P.x)))) z)
    (by rw [hk]; exact Kp) UW (by rw [w0]; exact pr)
  have h6 := H2K5.Honest.claim6_fronts Reading.gl H
    (inOf Z.P.S Z.link (cells m.st.input.trace)) Pl hDv hp₀ R (by rw [ed, w1]; exact pr) L0 Id
  rw [← R.gam, ed, K1.gam (show iGam Z.P.x < iVD Z.P.x by
      unfold iGam iVD
      omega)] at h6
  unfold H2K5.Honest.accV H2K5.Honest.zcV at h6
  rw [H2K5.Honest.ofDiv_some hp₀, H2K5.Honest.ofDiv_some hp₀,
    H2K5.Honest.accAt_same _ _ K0.key.d, H2K5.Honest.zcAt_same _ _ K0.key.d,
    ← H2K5.Honest.stable_sVM Z.P _ (q := iVM Z.P.x) (fronts_key Sc hT hd e _ _)
      (fronts_agree Hs hT.2.1 ds (H2K5.Honest.HeardIs.firstOf_mono Z.P.x
        (show iVM Z.P.x ≤ iVD Z.P.x from Nat.le_succ _))) (Nat.lt_succ_self _)] at h6
  exact h6

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.claim6_at
