-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EndFields.lean: the fields of a panel of the verifier's batched sumcheck that the
end of that sumcheck reads beside the two sides' forms, kind of panel by kind.

What one panel adds to the two elements of the field As and Bs (dEnd,
Johnson/Road/FormsKeysEnd.lean) hangs on whether the panel has the selector, on the number of its
never-sent vector, on whether it has weight claims, on its rows, and on its public weights. The
record SidesAre (Johnson/Road/K4/PanelSides.lean) does not keep these. Here they are read off the
verifier's steps once more, for each of the fifteen kinds.

Main names:
  `virtOf`: the number of a panel's never-sent vector: 0 for D, 1 + l for Dr l, none for the others.
  `EndFields`: the record: selector, never-sent vector, weight claims, rows, claim; for Dr l the
    call's weight, the one row weight and the selector's shown values; for D the rows' weights.
  `endFields_of`: EndFields of a panel b that IsPanelOf a panel pn of the library, under SigFits.
  `placed_fields`: so on the verifier's own placed list, member by member against pans D.
Limits. SigFits is a premise. Fields and public weights alone: nothing on what the never-sent
vectors or the weight claims' vectors hold, on the panels' places, on a run, on soundness or on
hiding.


-/
import Johnson.Road.K4.PanelSidesAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff eqTab WsShape WsClaim)
open OnBytes.Model.Layer (Env Lay SBlk Panels PanelEnv ClaimEnv panelA panelT panelsA panelsT kT
  placePanels)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Pan pans wc call)

variable {K : Type} [Field K]

/-- The number of a panel's never-sent vector. -/
def virtOf : Pan → Option ℕ
  | .D => some 0
  | .Dr l => some (1 + l)
  | _ => none

/-- What the end of the batched sumcheck reads of a panel, beside the two sides' forms. y, sh: the
verifier's layout and the values that the second token sumcheck has shown; z: the lookup's point. -/
structure EndFields [scl : Scl] (ρ : Reading K) (y : Lay) (sh : Array E) (D : Dim) (z : ℕ → K)
    (b : SBlk) (pn : Pan) : Prop where
  tri : b.tri = pn.three
  virt : b.virt = virtOf pn
  v0w : pn.weight = true → ∃ v0, b.v0 = some v0
  v0n : pn.weight = false → b.v0 = none
  ni : pn.three = false → b.ni = pn.nr D
  claim : b.claim = if pn.late then 1 else 0
  dr : ∀ l, pn = .Dr l → ρ.val b.ec = wc D z (call .D) ∧ wtK ρ b 0 = (Pan.Dr l).wt D z 0 ∧
    ∀ e, e < y.h.NE → ρ.val (b.sl.getD e zeroE) =
      ρ.val (sh.getD (y.NN * y.Lam + y.LamM + l * y.h.NE + e) zeroE)
  dB : pn = .D → ∀ i, i < D.nl → ρ.val b.ec * wtK ρ b i = wc D z (call .D) * Pan.D.wt D z i

section Kinds

variable [scl : Scl] {ρ : Reading K} {y : Lay} {sh : Array E} {D : Dim} {z : ℕ → K} {b : SBlk}
  {pn : Pan}

/-- A panel that is neither D nor Dr l. -/
theorem endFields_other (hk0 : virtOf pn = none) (ht : b.tri = pn.three) (hk : b.virt = none)
    (hw : pn.weight = true → ∃ v0, b.v0 = some v0) (hn : pn.weight = false → b.v0 = none)
    (hni : pn.three = false → b.ni = pn.nr D) (hc : b.claim = if pn.late then 1 else 0) :
    EndFields ρ y sh D z b pn where
  tri := ht
  virt := hk.trans hk0.symm
  v0w := hw
  v0n := hn
  ni := hni
  claim := hc
  dr := fun l e => by
    subst e
    have h' : (some (1 + l) : Option ℕ) = none := hk0
    cases h'
  dB := fun e => by
    subst e
    have h' : (some 0 : Option ℕ) = none := hk0
    cases h'

end Kinds

section Whole

variable [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv} {c : ClaimEnv}
  {h : Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim} {lk L0 : ℕ}
  {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- **One panel, of any of the fifteen kinds.** -/
theorem endFields_of (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) {TS : List ℕ}
    (hTS : TS = [0, 1, 2, 5]) {cl : List WsClaim} {b : SBlk} {pn : Pan}
    (hI : IsPanelOf p c TS cl b pn) : EndFields ρ p.v.y p.shownT D z b pn := by
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  have hAC := callsAC_of_lines S.lines
  have hLam : p.v.y.Lam = D.nl := S.port.fits.Lam
  have hLamM : p.v.y.LamM = D.ne := S.port.fits.LamM
  cases pn with
  | G =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht (f3 rfl) (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun _ => hni.trans hLam) f1
  | U =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht (f3 rfl) (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun _ => hni.trans hLam) f1
  | O =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht (f3 rfl) (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun _ => hni.trans hLam) f1
  | V =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht (f3 rfl) (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun _ => hni.trans hLam) f1
  | LR =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    rw [hn] at hbl f3
    have hni : b.ni = p.v.y.LamM := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht (f3 rfl) (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun _ => hni.trans hLamM) f1
  | QK =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, H⟩ := hI
    obtain ⟨st, st', l, hn, hst, hs, hbl, -, -, -⟩ := id H
    rw [hn] at hs
    obtain ⟨f1, f2, f3⟩ := facts_QK hs hbl
    rw [panelT_QK_plain] at hs
    have e0 := (Option.some.inj hs).symm
    subst e0
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht f3 (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun _ => hni.trans hLam) f1
  | N1 =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_N1 hs hbl
    rw [panelT_N1_eq] at hs
    obtain ⟨_, _, e⟩ := of_bind_some hs
    rw [e, plain_push] at hbl
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht f2
      (fun k => Bool.noConfusion (show false = true from k)) (fun _ => h0)
      (fun _ => hni.trans hLam) f1
  | N2 =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_N2 hs hbl
    rw [panelT_N2_eq] at hs
    obtain ⟨_, _, e⟩ := of_bind_some hs
    rw [e, plain_push] at hbl
    have hni : b.ni = p.v.y.Lam := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht f2
      (fun k => Bool.noConfusion (show false = true from k)) (fun _ => h0)
      (fun _ => hni.trans hLam) f1
  | XR =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_XR h3 hs hbl
    rw [panelT_XR_eq, h3] at hs
    obtain ⟨_, _, e⟩ := of_bind_some (o := p.v.ewOf "XR") hs
    rw [e, plain_push] at hbl
    have hni : b.ni = p.v.y.LamM := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht f2
      (fun k => Bool.noConfusion (show false = true from k)) (fun _ => h0)
      (fun _ => hni.trans hLamM) f1
  | DD =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_DD h3 hs hbl
    rw [panelT_DD_eq, h3] at hs
    obtain ⟨_, _, e⟩ := of_bind_some (o := p.v.ewOf "DD") hs
    rw [e, plain_push] at hbl
    have hni : b.ni = p.v.y.LamM := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht f2
      (fun k => Bool.noConfusion (show false = true from k)) (fun _ => h0)
      (fun _ => hni.trans hLamM) f1
  | MR =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_MR h3 hs hbl
    rw [panelT_MR_eq, h3] at hs
    obtain ⟨_, _, e⟩ := of_bind_some (o := p.v.ewOf "MR") hs
    rw [e, plain_push] at hbl
    have hni : b.ni = p.v.y.LamM := congrArg SBlk.ni (push_inj hbl).symm
    exact endFields_other rfl ht f2
      (fun k => Bool.noConfusion (show false = true from k)) (fun _ => h0)
      (fun _ => hni.trans hLamM) f1
  | Gr lm =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', _, -, -, hlm, -, hstep, hbl, -, -, -⟩ := H
    rw [hn] at hstep
    obtain ⟨f1, -⟩ := facts_tri hstep hbl
    obtain ⟨xx, hxx, e⟩ := of_bind_some
      (o := (Array.range p.v.y.h.d).mapM fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) hstep
    rw [e, tri_push] at hbl
    have hk : b.virt = none := congrArg SBlk.virt (push_inj hbl).symm
    exact endFields_other rfl ht hk (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun k => Bool.noConfusion (show true = false from k)) f1
  | Ur lm =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', _, -, -, hlm, -, hstep, hbl, -, -, -⟩ := H
    rw [hn] at hstep
    obtain ⟨f1, -⟩ := facts_tri hstep hbl
    obtain ⟨xx, hxx, e⟩ := of_bind_some
      (o := (Array.range p.v.y.h.d).mapM fun k2 => p.v.shIn (p.v.tensorAt "xr" "rt") lm k2) hstep
    rw [e, tri_push] at hbl
    have hk : b.virt = none := congrArg SBlk.virt (push_inj hbl).symm
    exact endFields_other rfl ht hk (fun _ => ⟨v0, h0⟩)
      (fun k => Bool.noConfusion (show true = false from k))
      (fun k => Bool.noConfusion (show true = false from k)) f1
  | D =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.D).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, -, -⟩ := facts_acc hacc hbl
    rw [hn, panelA_D_eq, plain_push] at hbl
    have eb := push_inj hbl
    subst eb
    have hel : ElTie ρ p.v D z q (call Fam.D) := by
      rw [hq']
      exact S.el _ (by decide)
    have hec : ρ.val (p.e.getD q zeroE) = wc D z (call Fam.D) := by
      rw [hq']
      exact S.wc _ (by decide)
    exact
      { tri := rfl
        virt := rfl
        v0w := fun _ => ⟨_, rfl⟩
        v0n := fun k => Bool.noConfusion (show true = false from k)
        ni := fun _ => hLam
        claim := rfl
        dr := fun l e => by cases e
        dB := fun _ i hi => by
          have hL : i < p.v.y.Lam := by
            rw [hLam]
            exact hi
          show ρ.val (p.e.getD q zeroE) * ρ.val (((Array.range p.v.y.Lam).map fun i =>
              mulE ((eqTab (p.v.zl q)).getD i zeroE) (Model.Layer.pw
                (Model.Layer.tOf (p.v.sc.kl (p.v.lay i) Model.Layer.Lkd)))).getD i zeroE) =
            wc D z (call Fam.D) *
              Inst.Model.Site.scl (D.Pl i).kd (Inst.Model.FFSeg.el D z (call Fam.D) i)
          rw [hec, range_map_getD _ _ hL, S.port.fits.kd i hi, scl_weight S.port.fits.num,
            hel i hi] }
  | Dr lm =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', _, -, -, hlm, -, hstep, hbl, -, -, -⟩ := H
    rw [hTS] at hq
    have hq' : q = (call Fam.D).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hstep
    have e : Model.Layer.tri p.v.y (p.e.getD q zeroE) 1 p.v.y.h.fe
        ((Array.range p.v.y.h.NE).map fun e => p.shownT.getD
          (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE)
        #[] (some (1 + lm))
        (mulE ((eqTab (p.v.zl q)).getD (2 * lm + 1) zeroE)
          (kT p.v.sc (p.v.lay (2 * lm + 1)) Model.Layer.Lkd)) st = st' := Option.some.inj hstep
    rw [← e, tri_push] at hbl
    have eb := push_inj hbl
    subst eb
    have hl : 2 * lm + 1 < D.nl := odd_lt D (by rw [← hLamM]; exact hlm)
    have hel : ElTie ρ p.v D z q (call Fam.D) := by
      rw [hq']
      exact S.el _ (by decide)
    have hec : ρ.val (p.e.getD q zeroE) = wc D z (call Fam.D) := by
      rw [hq']
      exact S.wc _ (by decide)
    exact
      { tri := rfl
        virt := rfl
        v0w := fun _ => ⟨_, rfl⟩
        v0n := fun k => Bool.noConfusion (show true = false from k)
        ni := fun k => Bool.noConfusion (show true = false from k)
        claim := rfl
        dr := fun l el => by
          obtain rfl : lm = l := Pan.Dr.inj el
          refine ⟨hec, ?_, fun e he => ?_⟩
          · show ρ.val (mulE ((eqTab (p.v.zl q)).getD (2 * lm + 1) zeroE) (Model.Layer.pw
                (Model.Layer.tOf (p.v.sc.kl (p.v.lay (2 * lm + 1)) Model.Layer.Lkd)))) =
              Inst.Model.Site.scl (D.Pl (2 * lm + 1)).kd
                (Inst.Model.FFSeg.el D z (call Fam.D) (2 * lm + 1))
            rw [S.port.fits.kd (2 * lm + 1) hl, scl_weight S.port.fits.num, hel _ hl]
          · show ρ.val (((Array.range p.v.y.h.NE).map fun e => p.shownT.getD
                (p.v.y.NN * p.v.y.Lam + p.v.y.LamM + lm * p.v.y.h.NE + e) zeroE).getD e zeroE) = _
            rw [range_map_getD _ _ he]
        dB := fun k => by cases k }

/-- **The placed list.** The place of a panel is no field of the record. -/
theorem placed_fields (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) {TS : List ℕ}
    (hTS : TS = [0, 1, 2, 5]) {pans' : Panels} {cl : List WsClaim}
    (hp : panelsT p TS (panelsA p {}) = some pans') (hc : c.weightClaims TS = some cl) :
    List.Forall₂ (fun b pn => EndFields ρ p.v.y p.shownT D z b pn)
      (placePanels pans'.bl).1.toList (pans D) := by
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  have hne : p.v.y.LamM = D.ne := by
    rw [S.env]
    exact S.aim.claim.LamM
  refine (placed_are_pans p c S.env hp hc h3 hne S.lines hTS).imp fun b' pn k => ?_
  obtain ⟨b, ⟨o, rfl⟩, hI⟩ := k
  have e := endFields_of S hTS hI
  exact ⟨e.tri, e.virt, e.v0w, e.v0n, e.ni, e.claim, e.dr, e.dB⟩

end Whole

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.endFields_other
#print axioms OnBytes.Road.K4.endFields_of
#print axioms OnBytes.Road.K4.placed_fields
