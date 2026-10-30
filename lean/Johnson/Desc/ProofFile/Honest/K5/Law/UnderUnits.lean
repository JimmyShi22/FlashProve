-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/UnderUnits.lean: CONDITIONAL, among others on ties that are
not shown: at the member of a chain's thread at which the honest side of an attention segment's own
rounds (kind K5) is seated, in the world in which the items "the forms of a run are worth 0" are
said behind the member: UNDER THE SLOTS THAT THE PLANE CLAIMS AND THE CLAIMS ON THE SOFTMAX-TABLE
UNITS NAME LIE THE PROVER's VALUES AT THE VERIFIER's OWN NAMED POINTS (UnderPlanes, UnderUnit,
Johnson/Desc/K5/Honest/Law/SayOf.lean). Statements with their proofs. EVERY STATEMENT ON A SLOT IS
CONDITIONAL, and all these hang on the ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT
SHOWN.

  flat3, alone_at, kr_at, aloneK_list, sum_unit, pieces_size   lists, and what the row's jobs send
                 and sum at a unit's part
  UnitFacts, unit_facts   all that is said of the unit number n: its plane claim's five slots, and
                 UnderUnit
  under_unit     **UnderUnit**, at every unit of i.p
  under_planes   **UnderPlanes**

The premises are those of Honest/K5/Law/UnderDiv.lean: see its head.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.UnderDiv
import Johnson.Desc.ProofFile.Honest.K5.Law.StartUnit
import Johnson.Desc.First.Att.Claims.PlanesAre
import Johnson.Desc.First.Att.Claims.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts RemP ScoreP UnitG hear pointsOf geoOf)
open H2K5.Honest (K5In Pub5 Chal shapes slotsTo ptsOf aloneOk aloneKR aloneK leadK krAt kAt planeOf
  maxAt sK unitA unitB remKey unitKey UnderPlanes UnderUnit counted_spec)

/-! ## 1 Lists -/

/-- Three by three. -/
theorem flat3 {α : Type} (f : α → Nat → E) : ∀ (l : List α) (t y : Nat) (v : α), y < 3 →
    l[t]? = some v → (l.flatMap fun u => (List.range 3).map (f u)).getD (3 * t + y) zeroE = f v y
  | [], _, _, _, _, h => by cases h
  | a :: l, 0, y, v, hy, h => by
    cases h
    rw [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
      List.getD_append _ _ _ _ (by rw [List.length_map, List.length_range]; exact hy),
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hy]
    rfl
  | a :: l, t + 1, y, v, hy, h => by
    rw [List.flatMap_cons,
      List.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; omega),
      List.length_map, List.length_range, show 3 * (t + 1) + y - 3 = 3 * t + y by omega]
    exact flat3 f l t y v hy h

/-- The first six of a unit's seven scalars, in what the row's jobs send at its part. CONDITIONAL:
the test on the public data says yes at the challenges c. -/
theorem alone_at (P : Pub5) (w : K5In) {c : Chal} (ha : aloneOk P c = true) {n : Nat}
    (hn : n < P.x.score.length) {y : Nat} (hy : y < 6) :
    ((jobs P).alone n w c).getD ((if n = 0 then P.x.planeMessages * 3 else 0) + y) zeroE =
      (aloneK P w c n).getD y zeroE := by
  have h6 := H2K5.Honest.Lengths.aloneK_length ha w hn
  have hl : ∀ sv : E, (leadK P w c n sv).getD y zeroE = (aloneK P w c n).getD y zeroE :=
    fun sv => by
      unfold leadK
      rw [List.getD_append _ _ _ _ (by rw [h6]; exact hy)]
  rw [alone_unit P w c hn]
  by_cases h0 : n = 0
  · subst h0
    have h3 := H2K5.Honest.Lengths.aloneKR_length ha w
    rw [if_pos rfl, if_pos (show ((0 : Nat) == 0) = true from rfl),
      List.getD_append_right _ _ _ _ (by rw [h3]; omega), h3, Nat.add_sub_cancel_left]
    exact hl _
  · rw [if_neg h0, if_neg (by simpa using h0), List.nil_append, Nat.zero_add]
    exact hl _

/-- The remainder-table units' scalars, in what the row's jobs send at the first part. CONDITIONAL:
as `alone_at`; there is a softmax-table unit. -/
theorem kr_at (P : Pub5) (w : K5In) {c : Chal} (ha : aloneOk P c = true)
    (hn : 0 < P.x.score.length) {j : Nat} (hj : j < P.x.planeMessages * 3) :
    ((jobs P).alone 0 w c).getD j zeroE = (aloneKR P w c).getD j zeroE := by
  rw [alone_unit P w c hn, if_pos (show ((0 : Nat) == 0) = true from rfl),
    List.getD_append _ _ _ _ (by rw [H2K5.Honest.Lengths.aloneKR_length ha w]; exact hj)]

/-- A unit's five planes' values and its maximum, as a list. CONDITIONAL: the three look-ups. -/
theorem aloneK_list (P : Pub5) (w : K5In) {c : Chal} {p₀ : Pts} (hp : ptsOf P c = some p₀)
    {n : Nat} {k₀ : ScoreP} (hk : p₀.scores[n]? = some k₀) {u₀ : RemP}
    (hu : p₀.planes[k₀.claim]? = some u₀) :
    aloneK P w c n = (List.range 5).map (planeOf P.g w u₀) ++ [maxAt P.g w k₀] := by
  unfold aloneK
  rw [hp]
  show (kAt P.g w p₀ n).getD [] = _
  unfold kAt
  rw [hk]
  show ((p₀.planes[k₀.claim]?).bind _).getD [] = _
  rw [hu]
  rfl

theorem sum_unit (P : Pub5) (w : K5In) (c : Chal) {n : Nat} (hn : n < P.x.score.length) :
    (jobs P).sum n w c = sK P w c n := if_pos hn

/-- A unit has a weight for each of its pieces. -/
theorem pieces_size (u : UnitG) (zk : Array E) : (P.piecesOf u zk).size = u.pcs.length := by
  unfold P.piecesOf
  rw [List.size_toArray, List.length_mergeSort, List.length_map]

/-! ## 2 A softmax-table unit -/

/-- All that is said of the unit k, number n. It is a definition. -/
structure UnitFacts (W : World GE) (S : OnBytes.Attention.Shape) (w : K5In) (i : P.Runs.In)
    (nR n : Nat) (k : ScoreP) : Prop where
  claim : k.claim = nR + n
  plane : ∃ uv, i.p.planes[k.claim]? = some uv ∧ uv.np = 5 ∧ uv.s0 = k.s0 ∧
    ∀ y, y < 5 → W.slot (uv.s0 + y) = Reading.gl.val (planeOf (geoOf S) w uv y)
  under : UnderUnit W S w k

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

/-- **The unit number n.** CONDITIONAL: see the head; kv is unit number n of i.p. -/
theorem unit_facts {n : Nat} {kv : ScoreP} (hkv : i.p.scores[n]? = some kv) :
    UnitFacts (worldOwn (behindPart s att G) [] D) Z.P.S
      (inOf Z.P.S Z.link (cells m.st.input.trace)) i hd5.remainders.size n kv := by
  obtain ⟨-, -, -, -, -, -, -, c8⟩ := counted_spec hc
  have L := laid_at Hs hd hM hz hh
  have Al := along_at Hs hd hM ⟨hz.vp, hz.mf, hz.got⟩ hh
  have PA := K5Law.points_are hi
  have Pl := K5Law.planes_are hi
  have hcnt := (K5Law.points_counts hi).2.2
  have hn : n < i.p.scores.size := by
    rcases Nat.lt_or_ge n i.p.scores.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hkv
      cases hkv
  have hnS : n < hd5.scores.size := by
    rw [← hcnt]
    exact hn
  have hnx : n < Z.P.x.score.length := by
    rw [← L.size]
    exact hnS
  have hu' : Z.P.x.score[n]? = some Z.P.x.score[n] := List.getElem?_eq_getElem hnx
  have hug : Z.P.g.scores[n]? = some (Z.P.g.scores[n]'(by rw [PA.nH]; exact hnS)) :=
    List.getElem?_eq_getElem _
  have ho : hd5.scores[n]? = some hd5.scores[n] := Array.getElem?_eq_getElem hnS
  generalize Z.P.x.score[n] = u' at hu'
  generalize Z.P.g.scores[n]'(by rw [PA.nH]; exact hnS) = ug at hug
  generalize hd5.scores[n] = o at ho
  obtain ⟨k', hk', hcl, hpl, hs0, -, hpw, -⟩ := Pl.unit n ug o hug ho
  obtain rfl : k' = kv := Option.some.inj (hk'.symm.trans hkv)
  have hq := H2K5.Honest.shape_unit Z.P.x n u' hu'
  obtain ⟨SP, h7⟩ := L.unit n o _ ho hq
  have hl := lead_slots Hs Sc hT hd hM e hD hq SP
  have ho1 : o.1 = att.F.next + slotsTo Z.P.x n +
      (if n = 0 then Z.P.x.planeMessages * 3 else 0) := by
    have h2 : o.2.first = att.F.next + slotsTo Z.P.x n +
        ((if n = 0 then Z.P.x.planeMessages * 3 else 0) + 7) := SP.first
    omega
  obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x n)
  have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
  have ha := ok_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x n)
  obtain ⟨k₀, hk₀, ek⟩ : ∃ k₀, p₀.scores[n]? = some k₀ ∧ unitKey k₀ = unitKey k' := by
    have h1 := H2K5.Honest.key_unit K.key n
    rw [hk'] at h1
    cases h2 : p₀.scores[n]? with
    | none =>
      rw [h2] at h1
      cases h1
    | some k₀ =>
      rw [h2] at h1
      exact ⟨k₀, rfl, Option.some.inj h1⟩
  have ecl : k₀.claim = k'.claim := by
    have e' := ek
    simp only [unitKey, Prod.mk.injEq] at e'
    exact e'.2.1
  obtain ⟨u₀, hu₀, eu⟩ : ∃ u₀, p₀.planes[k₀.claim]? = some u₀ ∧
      remKey u₀ = remKey (K5Law.remOfUnit g.zk ug o.1) := by
    have h1 := H2K5.Honest.key_plane K.key k'.claim
    rw [hpl, ← ecl] at h1
    cases h2 : p₀.planes[k₀.claim]? with
    | none =>
      rw [h2] at h1
      cases h1
    | some u₀ =>
      rw [h2] at h1
      exact ⟨u₀, rfl, Option.some.inj h1⟩
  have hlist := aloneK_list Z.P (inOf Z.P.S Z.link (cells m.st.input.trace)) hp₀ hk₀ hu₀
  have hslot : ∀ t, t < 6 → (worldOwn (behindPart s att G) [] D).slot (o.1 + t) =
      Reading.gl.val (((List.range 5).map (planeOf Z.P.g
        (inOf Z.P.S Z.link (cells m.st.input.trace)) u₀) ++
          [maxAt Z.P.g (inOf Z.P.S Z.link (cells m.st.input.trace)) k₀]).getD t zeroE) := by
    intro t ht
    rw [ho1, Nat.add_assoc, hl _ (by omega), alone_at Z.P _ ha hnx ht, hlist]
  refine ⟨hcl, ⟨_, hpl, rfl, hs0.symm, fun t ht => ?_⟩, ?_, fun j hj => ?_⟩
  · show (worldOwn (behindPart s att G) [] D).slot (o.1 + t) = _
    rw [hslot t (by omega), List.getD_append _ _ _ _ (by
      rw [List.length_map, List.length_range]
      exact ht), List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht,
      H2K5.Honest.planeOf_same _ _ eu]
    rfl
  · rw [hs0, hslot 5 (by omega)]
    show Reading.gl.val (maxAt Z.P.g _ k₀) = _
    rw [H2K5.Honest.maxAt_same _ _ ek]
    rfl
  · have hS := H2K5.Honest.sK_eq Z.P (inOf Z.P.S Z.link (cells m.st.input.trace))
      (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x n))) hug
      (k := k₀) (by rw [hp₀]; exact hk₀)
    have hnp : ug.pcs.length = u'.2 := by
      have h1 := c8 n u' hu'
      rw [hug] at h1
      exact h1
    obtain ⟨hr, hE⟩ := end_at Hs Sc hT hd hM e hD hq SP (Al.score n u' o hu' ho) (by
      rw [sum_unit Z.P _ _ hnx, hS]
      show 2 * ug.pcs.length = 2 * u'.2
      rw [hnp])
    have hj' : j < 2 * u'.2 := by
      rw [← hnp, ← pieces_size ug (g.zk.getD ug.call #[]), ← hpw]
      exact hj
    have hends : k'.sc.ends = o.2.sEnd := by
      have h1 := congrArg (fun l => l[n]?) (K5Law.ends_are PA)
      simp only [List.getElem?_map, Array.getElem?_toList, hk', ho, Option.map_some] at h1
      exact Option.some.inj h1
    have hchal : k'.sc.r = P.chal o.2 := by
      have h1 := congrArg (fun l => l[n]?) (K5Law.chal_are PA)
      simp only [List.getElem?_map, Array.getElem?_toList, hk', ho, Option.map_some] at h1
      exact Option.some.inj h1
    rw [hends, hE j hj', sum_unit Z.P _ _ hnx, products_end hS, hr, hchal]
    simp only [H2K5.Honest.unitA_same Z.P.g _ ek, H2K5.Honest.unitB_same Z.P.g _ ek]
    rfl

/-- **Under the slots that claim 4 names at a unit lie the prover's values at the verifier's
points.** CONDITIONAL: see the head. -/
theorem under_unit : ∀ x ∈ i.p.scores.toList, UnderUnit (worldOwn (behindPart s att G) [] D) Z.P.S
    (inOf Z.P.S Z.link (cells m.st.input.trace)) x := by
  intro x hx
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hx
  rw [Array.getElem?_toList] at hn
  exact (unit_facts Hs Sc hc hT hd hM e hD hz hh hg hi hn).under

/-- **Under the plane claims' slots lie the prover's values at the verifier's points.**
CONDITIONAL: see the head. -/
theorem under_planes : UnderPlanes (worldOwn (behindPart s att G) [] D) Z.P.S i
    (inOf Z.P.S Z.link (cells m.st.input.trace)) := by
  obtain ⟨c1, -⟩ := counted_spec hc
  have L := laid_at Hs hd hM hz hh
  have PA := K5Law.points_are hi
  have Pl := K5Law.planes_are hi
  obtain ⟨-, hcp, hcs⟩ := K5Law.points_counts hi
  have hnR : hd5.remainders.size = Z.P.x.planeMessages := by
    have h1 := (same_front Hs hT.2.1 hM hh (n := 0) (q := 0) (Nat.le_refl _)).nR
    rw [h1]
    exact Array.size_replicate
  have hpos : 0 < Z.P.x.score.length := by
    cases hsc : Z.P.x.score with
    | nil =>
      rw [hsc] at c1
      cases c1
    | cons _ _ => exact Nat.succ_pos _
  intro u hu t ht
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hu
  rw [Array.getElem?_toList] at hn
  have hlt : n < hd5.remainders.size + hd5.scores.size := by
    rcases Nat.lt_or_ge n i.p.planes.size with h | h
    · rw [← hcp]
      exact h
    · rw [Array.getElem?_eq_none h] at hn
      cases hn
  rcases Nat.lt_or_ge n hd5.remainders.size with h1 | h1
  · have hr : (Z.P.g.units .kr [.rm, .rd])[n]? =
        some ((Z.P.g.units .kr [.rm, .rd])[n]'(by rw [Pl.nR]; exact h1)) :=
      List.getElem?_eq_getElem _
    have hs0 : hd5.remainders[n]? = some hd5.remainders[n] := Array.getElem?_eq_getElem h1
    generalize (Z.P.g.units .kr [.rm, .rd])[n]'(by rw [Pl.nR]; exact h1) = r at hr
    generalize hd5.remainders[n] = s0 at hs0
    have e2 := Pl.rem n r s0 hr hs0
    obtain rfl : K5Law.remAt Z.P.g g.zk r s0 = u := Option.some.inj (e2.symm.trans hn)
    have ht3 : t < 3 := ht
    have hu0 : Z.P.x.score[0]? = some Z.P.x.score[0] := List.getElem?_eq_getElem hpos
    generalize Z.P.x.score[0] = u0 at hu0
    have hq := H2K5.Honest.shape_unit Z.P.x 0 u0 hu0
    have ho : hd5.scores[0]? = some (hd5.scores[0]'(by rw [L.size]; exact hpos)) :=
      Array.getElem?_eq_getElem _
    generalize hd5.scores[0]'(by rw [L.size]; exact hpos) = o at ho
    obtain ⟨SP, -⟩ := L.unit 0 o _ ho hq
    have hl := lead_slots Hs Sc hT hd hM e hD hq SP
    obtain ⟨p₀, hp₀⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x 0)
    have K := pts_to Hs Sc hT hd hM e hh hg hi (Nat.le_refl _) hp₀
    have ha := ok_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x 0)
    obtain ⟨v, hv, ev⟩ : ∃ v, p₀.planes[n]? = some v ∧
        remKey v = remKey (K5Law.remAt Z.P.g g.zk r s0) := by
      have h2 := H2K5.Honest.key_plane K.key n
      rw [hn] at h2
      cases h3 : p₀.planes[n]? with
      | none =>
        rw [h3] at h2
        cases h2
      | some v =>
        rw [h3] at h2
        exact ⟨v, rfl, Option.some.inj h2⟩
    have hj : 3 * n + t < Z.P.x.planeMessages * 3 := by
      rw [← hnR]
      omega
    show (worldOwn (behindPart s att G) [] D).slot (s0 + t) = _
    rw [L.rem n s0 hs0, Nat.add_assoc,
      show att.F.next = att.F.next + slotsTo Z.P.x 0 from rfl,
      hl (3 * n + t) (by
        show 3 * n + t < (if (0 : Nat) = 0 then Z.P.x.planeMessages * 3 else 0) + 7
        rw [if_pos rfl]
        omega),
      kr_at Z.P _ ha hpos hj]
    unfold aloneKR
    rw [hp₀]
    show Reading.gl.val ((krAt Z.P.g _ p₀ Z.P.x.planeMessages).getD (3 * n + t) zeroE) = _
    unfold krAt
    rw [flat3 _ _ n t v ht3 (by
      rw [List.getElem?_take_of_lt (by rw [← hnR]; exact h1), Array.getElem?_toList]
      exact hv), H2K5.Honest.planeOf_same _ _ ev]
    rfl
  · have h2 : n - hd5.remainders.size < i.p.scores.size := by
      rw [hcs]
      omega
    have hk : i.p.scores[n - hd5.remainders.size]? = some i.p.scores[n - hd5.remainders.size] :=
      Array.getElem?_eq_getElem h2
    have F := unit_facts Hs Sc hc hT hd hM e hD hz hh hg hi hk
    obtain ⟨uv, huv, hnp, -, hsl⟩ := F.plane
    rw [F.claim, show hd5.remainders.size + (n - hd5.remainders.size) = n by omega, hn] at huv
    obtain rfl := Option.some.inj huv
    exact hsl t (by rw [← hnp]; exact ht)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.flat3
#print axioms ProofFile.Honest.K5.alone_at
#print axioms ProofFile.Honest.K5.kr_at
#print axioms ProofFile.Honest.K5.aloneK_list
#print axioms ProofFile.Honest.K5.sum_unit
#print axioms ProofFile.Honest.K5.pieces_size
#print axioms ProofFile.Honest.K5.unit_facts
#print axioms ProofFile.Honest.K5.under_unit
#print axioms ProofFile.Honest.K5.under_planes
