-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TermsEnds.lean: CONDITIONAL.

Not shown here. THAT THE CLAIMS WHICH THE HONEST SIDE HOLDS (Sides.ends) ARE THE VERIFIER's AT A
RUN, and that the job's point is the verifier's end point of the second token sumcheck. That the
families of the verifier's list are of the sorts that TokAsk names (TokAsks); that there are 2 ^ lt
tokens; that the lookup's low coordinates are ls in number: hypotheses on public data. All that
ValAff.lean leaves open. No example is known. No property is claimed.

THE END VALUES OF THE SECOND TOKEN SUMCHECK ARE WHAT THE CLAIMS THAT THE HONEST SIDE HOLDS
(Sides.ends) ASK. That these are termsForms' claims is sides_ends (TermsField.lean). The honest
side of the sub-protocol K4 makes, token by token, minus the value of each claim «a slot less a
form» with 0 under every slot, and sends the extension of that table at the sumcheck's point
(Johnson/Desc/K4/Honest/Terms.lean, jobTermsOn). Here: read in the field, end value number e is
minus the value of claim number e on the honest reads AT THE POINT; and so, in a world with the
true entries and 0 under every slot, minus that claim's worth (a form is worth x in a world:
Aff.value gives x).

  fit_tok, has_tok, affFits_tok   the honest side's tests at two token points of one length.
  readsAt_some   where readsAt returns at one list of points it returns at every list.
  tokenRows_at, endsOn_at, jobTermsOn_open   the maker's text, opened.
  terms_end      end value number e is minus claim number e's value on the honest reads at the
                 point.
  terms_true     it is minus that claim's worth at the true entries, with 0 under every slot.
-/
import Johnson.Road.K4.C.TokReads
import Johnson.Road.K4.C.ValAff
import Johnson.Road.K4.C.RowMaps
import Johnson.Desc.K4.Honest.Terms
import Johnson.Desc.K4.Honest.Law.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Env TableAsk TableAt layTables tableAsks funsOf matIx nEndT)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads Sides Job matsOf laidOf famsAt readsAt wtsFit
  valAff valAff? affFits endsOn tokenRows jobTermsOn mle)
open OnBytes.Road.K4 (entryOf)

local notation "cornerAt" => OnBytes.Desc.First.K4.Honest.bitsOf

/-- **The test on a family has one answer at two token points of one length.** -/
theorem fit_tok {y : Lay} {fo : Forest.Heard} {zlow x x' : Array E} {a : TableAsk} (hk : TokAsk a)
    (hok : AskOk a) (hx : x.size = x'.size) :
    wtsFit y fo (tokPts zlow x) a = wtsFit y fo (tokPts zlow x') a := by
  by_cases hn : Named a
  · rcases hk.resolve_left (not_not.mpr hn) with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨h1, h2⟩
    · have he : a.point.isEmpty = false := by rw [hp]; rfl
      rw [fit_found he (p := ("rt", x)) (by rw [hp]; exact find_rt zlow x),
        fit_found he (p := ("rt", x')) (by rw [hp]; exact find_rt zlow x')]
      show (if a.lng = true then x.size == _ && _ && _ else x.size == _ && _) =
        (if a.lng = true then x'.size == _ && _ && _ else x'.size == _ && _)
      rw [hx]
    · have he : a.point.isEmpty = false := by rw [hp]; rfl
      have hs : (longPoint zlow x).size = (longPoint zlow x').size := by
        unfold longPoint
        rw [Array.size_append, Array.size_append, hx]
      rw [fit_found he (p := ("Y", longPoint zlow x)) (by rw [hp]; exact find_Y zlow x),
        fit_found he (p := ("Y", longPoint zlow x')) (by rw [hp]; exact find_Y zlow x')]
      show (if a.lng = true then (longPoint zlow x).size == _ && _ && _
          else (longPoint zlow x).size == _ && _) =
        (if a.lng = true then (longPoint zlow x').size == _ && _ && _
          else (longPoint zlow x').size == _ && _)
      rw [hs]
    · unfold wtsFit
      rw [phiOf_lacks hn (find_none zlow x h1 h2), phiOf_lacks hn (find_none zlow x' h1 h2),
        find_none zlow x h1 h2, find_none zlow x' h1 h2]
  · have he : a.point.isEmpty = true := hok.resolve_right hn
    unfold wtsFit
    rw [if_pos he, if_pos he, phiOf_planes (tokPts zlow x) (tokPts zlow x') hn]

variable {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {zlow : Array E}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- The test on a place likewise. -/
theorem has_tok (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hk : TokAsks Q) {x x' : Array E} (hx : x.size = x'.size) {R R' : Reads}
    (hR : readsAt Q w fo (tokPts zlow x) = some R) (hR' : readsAt Q w fo (tokPts zlow x') = some R')
    {pos : ℕ} (hh : R.has pos = true) : R'.has pos = true := by
  obtain ⟨-, L2⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨q, hq, m, hmq, c, sg, hc, hsg, rfl⟩ := place_of_has hR hl hh
  have hask : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  have hj := place_lt (matsOf Q) q.1.L m.1 hc hsg
  rw [(fam_at hR' hl hq hmq hj).2.1, ← fit_tok (hk _ hask) (ask_ok hask) hx,
    ← (fam_at hR hl hq hmq hj).2.1]
  exact hh

/-- The test on a form likewise. -/
theorem affFits_tok (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hk : TokAsks Q) {x x' : Array E} (hx : x.size = x'.size) {R R' : Reads}
    (hR : readsAt Q w fo (tokPts zlow x) = some R) (hR' : readsAt Q w fo (tokPts zlow x') = some R')
    {v : Env} {a : Aff} (h : affFits v R a = true) : affFits v R' a = true := by
  unfold affFits at h ⊢
  rw [← Array.all_toList, List.all_eq_true] at h ⊢
  intro e he
  have h1 := h e he
  rw [Bool.and_eq_true] at h1 ⊢
  exact ⟨h1.1, has_tok hl hk hx hR hR' h1.2⟩

/-- Where readsAt returns at one list of points it returns at every list. -/
theorem readsAt_some {pt : List (String × Array E)} {R : Reads} (h : readsAt Q w fo pt = some R)
    (pt' : List (String × Array E)) : ∃ R', readsAt Q w fo pt' = some R' := by
  unfold readsAt famsAt at h ⊢
  cases hq : laidOf Q with
  | none =>
    rw [hq] at h
    cases h
  | some laid => exact ⟨_, rfl⟩

/-- The maker's rows at token t. -/
theorem tokenRows_at {S : Sides} {rows : Array (Array E × Array (E × E × E))}
    (h : tokenRows S = some rows) {t : ℕ} (ht : t < S.v.y.T) :
    ∃ R sh tr, S.readsTok (cornerAt S.v.y.h.lt t) = some R ∧ endsOn S R = some sh ∧
      rows[t]? = some (sh, tr) := by
  unfold tokenRows at h
  obtain ⟨y', hy, hb⟩ := amapM_get h (i := t) (x := t) (by simp [ht])
  obtain ⟨R, hR, h1⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨sh, hs, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨tr, -, h3⟩ := Option.bind_eq_some_iff.mp h2
  obtain rfl := Option.some.inj h3
  exact ⟨R, sh, tr, hR, hs, hb⟩

/-- The values at given reads: member e. -/
theorem endsOn_at {S : Sides} {R : Reads} {sh : Array E} (h : endsOn S R = some sh) {e : ℕ}
    {a : Aff} (ha : S.ends[e]? = some a) :
    affFits S.v R a = true ∧ sh[e]? = some (negE (valAff S.v R (fun _ => zeroE) a)) := by
  unfold endsOn at h
  obtain ⟨y', hy, hb⟩ := amapM_get h (i := e) (x := a) (by rw [List.getElem?_toArray]; exact ha)
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
  unfold valAff? at hx
  by_cases c : affFits S.v R a = true
  · rw [if_pos c] at hx
    obtain rfl := Option.some.inj hx
    exact ⟨c, hb⟩
  · rw [if_neg c] at hx
    cases hx

/-- The job, opened: its rows, its number of variables, its end values. -/
theorem jobTermsOn_open {S : Sides} {J : Job} (h : jobTermsOn S = some J) :
    ∃ rows, tokenRows S = some rows ∧ J.cube.n = S.v.y.h.lt ∧ ∀ rs, J.ends rs =
      (((Array.range (nEndT S.v.y)).map fun i => rows.map fun x => x.1.getD i zeroE).map
        fun t => mle t (J.cube.pointOf rs)).toList := by
  unfold jobTermsOn at h
  obtain ⟨rows, hr, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact ⟨rows, hr, rfl, fun _ => rfl⟩

/-- **End value number e of the second token sumcheck is minus the value of claim number e on the
honest reads at the job's point.** Rz: these reads. -/
theorem terms_end {S : Sides} {J : Job} (hJ : jobTermsOn S = some J)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r) (hk : TokAsks S.Q)
    (hy : S.v.y = S.Q.P.y) (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hlow : S.zlow.size = S.v.y.ls)
    (rs : List E) {Rz : Reads} (hRz : S.readsTok (J.cube.pointOf rs) = some Rz) {e : ℕ}
    (he : e < nEndT S.v.y) {a : Aff} (ha : S.ends[e]? = some a) :
    affFits S.v Rz a = true ∧ Reading.gl.val ((J.ends rs).getD e zeroE) =
      -Reading.gl.val (valAff S.v Rz (fun _ => zeroE) a) := by
  obtain ⟨rows, hrows, hn, hends⟩ := jobTermsOn_open hJ
  have hz : (J.cube.pointOf rs).size = S.Q.P.y.h.lt := by
    rw [OnBytes.Desc.First.K4.Honest.CubeLaw.pointOf_size, hn, hy]
  -- the reads at the corners
  have hex : ∀ t, t < 2 ^ S.Q.P.y.h.lt → ∃ R sh tr,
      S.readsTok (cornerAt S.Q.P.y.h.lt t) = some R ∧ endsOn S R = some sh ∧
        rows[t]? = some (sh, tr) := by
    intro t ht
    have := tokenRows_at hrows (t := t) (by rw [hT, hy]; exact ht)
    rw [hy] at this
    exact this
  haveI : Nonempty Reads := ⟨Rz⟩
  choose! Rt sh tr h1 h2 h3 using hex
  have hRt : ∀ t, t < 2 ^ S.Q.P.y.h.lt →
      readsAt S.Q S.w S.fo (tokPts S.zlow (cornerAt S.Q.P.y.h.lt t)) = some (Rt t) := h1
  have hRz' : readsAt S.Q S.w S.fo (tokPts S.zlow (J.cube.pointOf rs)) = some Rz := hRz
  have hpos : 0 < 2 ^ S.Q.P.y.h.lt := Nat.two_pow_pos _
  have hfit : affFits S.v Rz a = true :=
    affFits_tok hl hk (by rw [cornerAt_size, hz]) (hRt 0 hpos) hRz' (endsOn_at (h2 0 hpos) ha).1
  refine ⟨hfit, ?_⟩
  obtain ⟨-, lin⟩ := valAff_tok (slot := fun _ => zeroE) hl hk (by rw [hlow, hy]) hz hRz' hRt hfit
  rw [lin, hends]
  have eE : ((((Array.range (nEndT S.v.y)).map fun i => rows.map fun x => x.1.getD i zeroE).map
      fun t => mle t (J.cube.pointOf rs)).toList).getD e zeroE =
      mle (rows.map fun x => x.1.getD e zeroE) (J.cube.pointOf rs) := by
    rw [toList_getD, getD_map_lt _ _ (by rw [Array.size_map, Array.size_range]; exact he) zeroE #[],
      getD_map_lt _ _ (by rw [Array.size_range]; exact he) #[] 0]
    have e0 : (Array.range (nEndT S.v.y)).getD e 0 = e := by simp [Array.getD, he]
    rw [e0]
  rw [eE, OnBytes.Desc.First.K4.Honest.CubeLaw.mle_read, hz, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  have hrow : (rows.map fun x => x.1.getD e zeroE).getD t zeroE =
      negE (valAff S.v (Rt t) (fun _ => zeroE) a) := by
    have g1 := h3 t ht'
    have g2 := (endsOn_at (h2 t ht') ha).2
    have hlt : t < rows.size := (Array.getElem?_eq_some_iff.mp g1).1
    have gr : rows.getD t (#[], #[]) = (sh t, tr t) := by
      rw [Array.getD_eq_getD_getElem?, g1]
      rfl
    rw [getD_map_lt rows _ hlt zeroE (#[], #[]), gr]
    show (sh t).getD e zeroE = _
    rw [Array.getD_eq_getD_getElem?, g2]
    rfl
  have hneg : Reading.gl.val (negE (valAff S.v (Rt t) (fun _ => zeroE) a)) =
      -Reading.gl.val (valAff S.v (Rt t) (fun _ => zeroE) a) := Slice.readE_neg _
  rw [hrow, hneg]
  ring

/-- **It is minus that claim's worth at the true entries, with 0 under every slot.** W: such a
world. -/
theorem terms_true {S : Sides} {J : Job} (hJ : jobTermsOn S = some J)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r) (hk : TokAsks S.Q)
    (hy : S.v.y = S.Q.P.y) (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hlow : S.zlow.size = S.v.y.ls)
    (rs : List E) {e : ℕ} (he : e < nEndT S.v.y) {a : Aff} (ha : S.ends[e]? = some a)
    {fo' : Forest.Heard} {pts : List (String × Array E)} {tl : HTailF2} {Mm : Mats Cb.Gl.E}
    {G : ℕ → Prop} {funs : Array HFun} (hf : funsOf S.Q.P.y fo' pts r.2.1 = some funs)
    (hp : PtsPart (tokPts S.zlow (J.cube.pointOf rs)) pts)
    (hfo : (∀ i, G i → i ≠ (matIx S.Q.P.y).iB) ∨ fo' = S.fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf S.Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf S.Q) S.w.cell Mm) {W : World Cb.Gl.E}
    (hW : W.entry = entryOf Reading.gl tl funs S.v.iU3 S.v.K3 Mm) (hS : ∀ j, W.slot j = 0)
    (hG : ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * S.v.K3 + x.idx) → G z.1.mat) :
    Reading.gl.val ((J.ends rs).getD e zeroE) = -a.value Reading.gl W := by
  obtain ⟨rows, hrows, -, -⟩ := jobTermsOn_open hJ
  obtain ⟨R0, -, -, h0, -, -⟩ := tokenRows_at hrows (t := 0) (by rw [hT]; exact Nat.two_pow_pos _)
  obtain ⟨Rz, hRz⟩ := readsAt_some (Q := S.Q) (w := S.w) (fo := S.fo) h0
    (tokPts S.zlow (J.cube.pointOf rs))
  obtain ⟨hfit, e1⟩ := terms_end hJ hl hk hy hT hlow rs hRz he ha
  rw [e1, valAff_true hRz hl hf hp hfo hm hNM hC hfit hW
    (fun x _ => by rw [hS, Reading.gl.zero]) hG]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.fit_tok
#print axioms OnBytes.Road.K4.C.has_tok
#print axioms OnBytes.Road.K4.C.affFits_tok
#print axioms OnBytes.Road.K4.C.readsAt_some
#print axioms OnBytes.Road.K4.C.tokenRows_at
#print axioms OnBytes.Road.K4.C.endsOn_at
#print axioms OnBytes.Road.K4.C.jobTermsOn_open
#print axioms OnBytes.Road.K4.C.terms_end
#print axioms OnBytes.Road.K4.C.terms_true
