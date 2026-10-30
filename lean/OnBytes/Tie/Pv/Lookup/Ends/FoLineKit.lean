-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLineKit.lean.
The head's key forms, one segment at a time: what the segments' files share.

Fo.LineLaw (OnBytes/Tie/Pv/Lookup/Ends/FoAlgH2.lean) is what the head's key forms come down to, one
segment at a time. It is proved at one of the nine segments, ROW, under line_ROW's premises
(OnBytes/Tie/Pv/Lookup/Ends/FoRowH.lean).

Defines:
  FoundH R q g: the byte-level verifier finds call q and segment g under g's name.
  SlLaw R lay q g OFF nl J: the law of Head.Sl, on which eight of the nine segments hang: the form
    that Head.Sl returns for a tensor of the matrix hf (nl limbs of J features from feature OFF on)
    under segment g's weights has, under the law of the reads, the value: the sum over the segment's
    entries x of the weight of x's column times the extension over the positions of the tensor's
    number at x (OnBytes.Ends.H.limbs). A proposition, said at the reading in the library's
    extension field, of runs that leave state and context. No statement of this library concludes
    it.
States:
  loop_val: the value of a form that a loop builds up, term by term.
  extL_smul: the extension at a list takes a factor out.
  ewOf_ok: the weights of a segment's entries, as Head.ewOf returns them.
  ew_get: the weight of entry x is the equality weight of x's column.
Not claimed: anything on soundness, completeness or hiding.
Nor is SlLaw claimed here.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoReadH
import OnBytes.Tie.Pv.Lookup.Ends.FoAlgH2

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Ends OnBytes.Ends.H

/-- The byte-level verifier finds call q and segment g under g's name. -/
structure FoundH (R : Head.Run) (q : ℕ) (g : Seg) : Prop where
  call : Head.callNo R.L g.name = some q
  seg : (R.L.calls.getD q default).seg? g.name = some g

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The value of a form that a loop builds up, term by term. -/
theorem loop_val (W : World K) (F : Fork) (c : Ctx) (body : ℕ → Aff → SubM (ForInStep Aff))
    (term : ℕ → K)
    (hb : ∀ i s out, body i s F c = .ok out → ∃ s', out = ((ForInStep.yield s', F), c) ∧
      s'.value ρ W = s.value ρ W + term i) :
    ∀ (l : List ℕ) (s : Aff) (out), (forIn l s body) F c = .ok out →
      out.1.2 = F ∧ out.2 = c ∧ out.1.1.value ρ W = s.value ρ W + (l.map term).sum
  | [], s, out, h => by
    rw [List.forIn_nil] at h
    rw [(pure_ok s F c out).1 h]
    exact ⟨rfl, rfl, by simp⟩
  | i :: l, s, out, h => by
    rw [List.forIn_cons, bind_ok] at h
    obtain ⟨st, G, c1, h1, h2⟩ := h
    obtain ⟨s', e, hv⟩ := hb i s _ h1
    have e1 : st = ForInStep.yield s' :=
      congrArg (fun x : (ForInStep Aff × Fork) × Ctx => x.1.1) e
    have e2 : G = F := congrArg (fun x : (ForInStep Aff × Fork) × Ctx => x.1.2) e
    have e3 : c1 = c := congrArg (fun x : (ForInStep Aff × Fork) × Ctx => x.2) e
    rw [e1, e2, e3] at h2
    obtain ⟨a1, a2, a3⟩ := loop_val W F c body term hb l s' out h2
    refine ⟨a1, a2, ?_⟩
    rw [a3, hv, List.map_cons, List.sum_cons, add_assoc]

theorem extL_smul (k : K) (f : ℕ → K) (z : List K) :
    extL (fun i => k * f i) z = k * extL f z := by
  unfold extL
  rw [lsum, lsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end

/-- The weights of a segment's entries. -/
theorem ewOf_ok (R : Head.Run) (q : ℕ) (g : Seg) (hN : FoundH R q g) (F G : Fork) (c d : Ctx)
    (ew : Array E) (h : Head.ewOf R g.name F c = .ok ((ew, G), d)) :
    ew = g.pos.map (fun p => (eqTab (Head.zjOf R.L R.x.g1 q)).getD p zeroE) ∧ G = F ∧ d = c := by
  unfold Head.ewOf Head.segOf at h
  dsimp only at h
  rw [bind_ok] at h
  obtain ⟨⟨q', C, g'⟩, F1, c1, h1, h⟩ := h
  obtain ⟨q'', e1, h1⟩ := bindGetAs_ok _ _ _ F c _ h1
  obtain ⟨g'', e2, h1⟩ := bindGetAs_ok _ _ _ F c _ h1
  have e3 := (pure_ok _ _ _ _).1 h1
  have hq : q'' = q := Option.some.inj (e1.symm.trans hN.call)
  rw [hq] at e2 e3
  have hg : g'' = g := Option.some.inj (e2.symm.trans hN.seg)
  rw [hg] at e3
  have t0 : q' = q := congrArg (fun y : ((ℕ × CallD × Seg) × Fork) × Ctx => y.1.1.1) e3
  have t1 : g' = g := congrArg (fun y : ((ℕ × CallD × Seg) × Fork) × Ctx => y.1.1.2.2) e3
  have t2 : F1 = F := congrArg (fun y : ((ℕ × CallD × Seg) × Fork) × Ctx => y.1.2) e3
  have t3 : c1 = c := congrArg (fun y : ((ℕ × CallD × Seg) × Fork) × Ctx => y.2) e3
  rw [t0, t1, t2, t3] at h
  have e4 := (pure_ok _ _ _ _).1 h
  exact ⟨congrArg (fun y : (Array E × Fork) × Ctx => y.1.1) e4,
    congrArg (fun y : (Array E × Fork) × Ctx => y.1.2) e4,
    congrArg (fun y : (Array E × Fork) × Ctx => y.2) e4⟩

/-- The weight of entry x is the equality weight of x's column. -/
theorem ew_get (e : Array E) (pos : Array ℕ) (x : ℕ) (hx : x < pos.size) :
    (pos.map fun p => e.getD p zeroE).getD x zeroE = e.getD (pos.getD x 0) zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hx,
    Array.getD_eq_getD_getElem? (xs := pos), Array.getElem?_eq_getElem hx]
  rfl

/-- **The law of Head.Sl.** -/
def SlLaw (R : Head.Run) (lay : WsLay) (q : ℕ) (g : Seg) (OFF nl J : ℕ) : Prop :=
  ∀ (F : Fork) (c : Ctx) (a : Aff), Head.Sl R g.name OFF nl J F c = .ok ((a, F), c) →
    ∀ (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E),
      ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
        (fun m r c => cell (.cell m r c)) →
      a.value Reading.gl W = ((List.range g.n).map fun x =>
        Reading.gl.val ((eqTab (Head.zjOf R.L R.x.g1 q)).getD (g.pos.getD x 0) zeroE) *
          extL (limbs (pubH R lay) cell nl OFF J x)
            (rdA Reading.gl (Head.ztOf R.h R.L R.x.g1 q))).sum

end Fo
