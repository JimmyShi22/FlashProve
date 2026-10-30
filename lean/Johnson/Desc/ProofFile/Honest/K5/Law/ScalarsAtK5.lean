-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ScalarsAtK5.lean: CONDITIONAL, among others on ties that are
not shown: at the member of a chain's thread at which the honest side of an attention segment's own
rounds (kind K5) is seated, in the world in which the items "the forms of a run are worth 0" are
said behind the member: UNDER THE SLOT OF EACH NAMED SCALAR THAT THE KEY FORMS READ LIES THE
PROVER's VALUE OF THAT NAME (ScalarsAt, Johnson/Desc/K5/Honest/Law/KeysSlots.lean, at scalarOf,
Johnson/Desc/K5/Honest/Law/RuleAll.lean). Statements with their proofs. EVERY STATEMENT IS
CONDITIONAL, and the last hangs on the ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT
SHOWN.

  rem_plane      a remainder-table unit's plane claim: its first slot and its number of values
  scalars_at     **ScalarsAt**, at the first two remainder-table units, the first two softmax-table
                 units and the division, all at the verifier's own named points; the three scalars
                 that are sums over cubes are the summands' totals, each at the challenges in front
                 of its own part

The premises are those of Honest/K5/Law/UnderDiv.lean (see its head), the public premise on the
shape's numbers (Sized, Johnson/Desc/K5/Honest/Law/Cells.lean), and eight look-ups in what was heard
and in the verifier's points.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.UnderUnits
import Johnson.Desc.K5.Honest.Law.KeysSlots

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
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts RemP ScoreP Geo hear pointsOf geoOf)
open H2K5.Honest (iSE sK sSE ibAt ScalarsAt scalarOf counted_spec)

/-- A remainder-table unit's plane claim. CONDITIONAL: the verifier's function for the points
returns; the two look-ups. -/
theorem rem_plane {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) {n a : Nat} {u : RemP} (ha : h.remainders[n]? = some a)
    (hu : p.planes[n]? = some u) : u.s0 = a ∧ u.np = 3 := by
  have Pl := K5Law.planes_are hp
  have hn : n < h.remainders.size := by
    rcases Nat.lt_or_ge n h.remainders.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at ha
      cases ha
  have hr : (g.units .kr [.rm, .rd])[n]? =
      some ((g.units .kr [.rm, .rd])[n]'(by rw [Pl.nR]; exact hn)) := List.getElem?_eq_getElem _
  obtain rfl := Option.some.inj ((Pl.rem n _ a hr ha).symm.trans hu)
  exact ⟨rfl, rfl⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **Under the slot of each named scalar that the key forms read lies the prover's value of that
name.** CONDITIONAL: see the head. -/
theorem scalars_at (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
    (hc : Z.P.counted = true) {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List OpenedColumn} (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m E ds y cols) {att : VerifiableInference.Desc.First.AttOwn}
    (e : s.here = .att att) {dc : List Fmt.Drawn} {D : Bound GQ}
    (hD : MaskIs T own rdOf k s att m dc D) (hz : OnBytes.Model.Road.Sized att.F) {G : Fork}
    {hd5 : Heard} {rest : List Fmt.RoundView} {lead : Nat}
    (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
    {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {Lf : Left} {i : P.Runs.In}
    (hi : pointsOf Z.P.g g.zk hd5 Lf = some i.p) (H : H2K5.Honest.Sized Z.P) {a1 a2 : Nat}
    {k1 k2 : ScoreP} {pM pD cM cD : RemP} (ha1 : hd5.remainders[0]? = some a1)
    (ha2 : hd5.remainders[1]? = some a2) (hk1 : i.p.scores[0]? = some k1)
    (hk2 : i.p.scores[1]? = some k2) (hpM : i.p.planes[0]? = some pM)
    (hpD : i.p.planes[1]? = some pD) (hcM : i.p.planes[k1.claim]? = some cM)
    (hcD : i.p.planes[k2.claim]? = some cD) :
    ScalarsAt (worldOwn (behindPart s att G) [] D) (OnBytes.Road.L5.dimOf Z.P.S) a1 a2 k1 k2 i.p.d
      (scalarOf Reading.gl (geoOf Z.P.S) (inOf Z.P.S Z.link (cells m.st.input.trace)) pM pD cM cD
        k1 k2 i.p.d
        (sK Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x 0))) 0).total
        (sK Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x 1))) 1).total
        (sSE Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))))).total) := by
  have L := laid_at Hs hd hM hz hh
  have PA := K5Law.points_are hi
  have UP := under_planes Hs Sc hc hT hd hM e hD hz hh hg hi
  have U5 := under5 Hs Sc hc hT hd hM e hD hz hh hg hi
  have UV := underV Hs Sc hc hT hd hM e hD hz hh hg hi
  have F1 := unit_facts Hs Sc hc hT hd hM e hD hz hh hg hi hk1
  have F2 := unit_facts Hs Sc hc hT hd hM e hD hz hh hg hi hk2
  have mem : ∀ {n : Nat} {u : RemP}, i.p.planes[n]? = some u → u ∈ i.p.planes.toList :=
    fun h => Array.mem_toList_iff.2 (Array.mem_of_getElem? h)
  -- a unit's seventh scalar
  have hss : ∀ (n : Nat) (kv : ScoreP), i.p.scores[n]? = some kv →
      (worldOwn (behindPart s att G) [] D).slot (kv.s0 + 6) =
        Reading.gl.val (sK Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x n))) n).total := by
    intro n kv hkv
    have hn : n < hd5.scores.size := by
      rw [← (K5Law.points_counts hi).2.2]
      rcases Nat.lt_or_ge n i.p.scores.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at hkv
        cases hkv
    have ho : hd5.scores[n]? = some hd5.scores[n] := Array.getElem?_eq_getElem hn
    have hu : Z.P.x.score[n]? = some (Z.P.x.score[n]'(by rw [← L.size]; exact hn)) :=
      List.getElem?_eq_getElem _
    have hs0 : kv.s0 = hd5.scores[n].1 := by
      have h1 := congrArg (fun l => l[n]?) (K5Law.s0_are PA)
      simp only [List.getElem?_map, Array.getElem?_toList, hkv, ho, Option.map_some] at h1
      exact Option.some.inj h1
    rw [hs0, ← Aff.value_slot (ρ := Reading.gl)]
    exact start_unit_at Hs Sc hT hd e hM hD L hu ho
  intro kk hkk
  match kk, hkk with
  | .cell .m1 jj, hj =>
    obtain ⟨e1, e2⟩ := rem_plane hi ha1 hpM
    show (worldOwn (behindPart s att G) [] D).slot (a1 + jj) = _
    rw [← e1]
    exact UP pM (mem hpM) jj (by rw [e2]; exact hj)
  | .cell .d1 jj, hj =>
    obtain ⟨e1, e2⟩ := rem_plane hi ha2 hpD
    show (worldOwn (behindPart s att G) [] D).slot (a2 + jj) = _
    rw [← e1]
    exact UP pD (mem hpD) jj (by rw [e2]; exact hj)
  | .cell .m2 jj, hj =>
    obtain ⟨uv, huv, -, hs0, hsl⟩ := F1.plane
    obtain rfl := Option.some.inj (huv.symm.trans hcM)
    show (worldOwn (behindPart s att G) [] D).slot (k1.s0 + jj) = _
    rw [← hs0]
    exact hsl jj hj
  | .cell .d2 jj, hj =>
    obtain ⟨uv, huv, -, hs0, hsl⟩ := F2.plane
    obtain rfl := Option.some.inj (huv.symm.trans hcD)
    show (worldOwn (behindPart s att G) [] D).slot (k2.s0 + jj) = _
    rw [← hs0]
    exact hsl jj hj
  | .ms .M, _ => exact F1.under.maximum
  | .ms .D, _ => exact F2.under.maximum
  | .ss .M, _ => exact hss 0 k1 hk1
  | .ss .D, _ => exact hss 1 k2 hk2
  | .acc, _ => exact UV.acc
  | .zo, _ =>
    show (worldOwn (behindPart s att G) [] D).slot (i.p.d.s5 + 1) = _
    rw [PA.s5, ← Aff.value_slot (ρ := Reading.gl)]
    exact start_division Hs Sc hT hd hM e hD L (counted_spec hc).1
  | .zc, _ => exact U5.zc
  | .rh, _ => exact U5.rh
  | .rh', _ => exact U5.rhp
  | .ib t, ht =>
    have ht' : t < Z.P.S.cf.lt := by
      have h1 : t < Z.P.D.lT := ht
      rw [← H.lt] at h1
      exact h1
    show (worldOwn (behindPart s att G) [] D).slot (i.p.d.sIB + t) =
      Reading.gl.val ((ibAt (geoOf Z.P.S) _ i.p.d).getD t zeroE)
    rw [U5.ib t ht']
    unfold ibAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show t < (geoOf Z.P.S).lt from ht')]
    rfl
  | .rg, _ => exact U5.r2
  | .rg', _ => exact U5.r2p

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rem_plane
#print axioms ProofFile.Honest.K5.scalars_at
