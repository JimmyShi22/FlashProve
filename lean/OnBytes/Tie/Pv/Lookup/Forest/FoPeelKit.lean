-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean.
Written rounds read as typed rounds, by the kind of round, and a stretch of such rounds.

A file's chain has written rounds (OnBytes/Slice/Draws.lean: `wRound d`): the verifier's message is
hash blocks with a round's test bits, the prover's message words. A typed protocol has field
elements. Soundness is carried from typed to written rounds along maps of messages, round by round
(`CarryS`, OnBytes/Flat/CarrySkip.lean). This file has these maps for every typed round that is
read as plain data (the scalars sent, the elements drawn), and for every list of such rounds.

Main names.
 * `flW d m c`: a written round's two messages as plain data. `Meets d s`: the written round d
   sends and draws what the spec s says (Tw.RSp: scalars sent, elements drawn, none of them 0) and
   nothing else. `flW_fit`: then its plain data fit s.
 * `Rd r' s`: a reader of the typed round r': a prover's message from the scalars, a verifier's
   message from the elements, and the reading back, which undoes both on all that fits s.
 * The kinds of round: `Rd.draw` (nothing sent; one element or a point drawn), `Rd.zero` (one
   scalar, one element), `Rd.var` (the coefficients of a variable of a short sumcheck, one
   challenge; with the variable whose challenge is never 0), `Rd.vals` (values sent, nothing
   drawn).
 * `Rds s' sp`: a reader for each round of a typed shape; `Rds.app`. `car ds s' sp R h`: the maps
   from the written rounds ds (Run/PlanQS.lean: `PQ.uL (ckP .two) ds`) to the typed shape.
 * `car_tr`: a written transcript has an image if and only if every round's test of work passes,
   and then the image is `img` of its plain data. `car_read`: the image, read back, is the written
   transcript's plain data, and these fit the spec. `car_fits`: the written rounds' error counts
   bear the typed rounds' if each is at least the typed count times the sampler's own bound on how
   many strings of blocks give one value. `outs_app`: the reading back of two shapes in a row.

Does not say: which rounds a given description has (that ds meets sp is a premise); that a typed
protocol's own reading is `outs`; anything on a verifier.
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Flat.CarrySkip
import OnBytes.Slice.RoundsMaps
import Cb.Pv.Lookup.Out.TwUn

set_option autoImplicit false

namespace Fo.Peel
open Iop Prob Run OnBytes.Slice OnBytes.Flat TwV

/-! ### one written round as plain data -/

/-- A written round's two messages as plain data: the elements sent, the elements drawn. -/
def flW (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) : List GE × List GE :=
  (ansOf d m, elemsV _ (OnBytes.Slice.valsOf d c))

/-- The written round d sends and draws what the spec says, and nothing else. -/
structure Meets (d : PQ.RD) (s : Tw.RSp) : Prop where
  sd : SendsDraws d s.sent s.drawn 0 0
  nz : s.nz = true → ∀ i, i < s.drawn → IsNZ (Fmt.dsOf d.entry d.kind) i

theorem elems_fit {d : PQ.RD} {s : Tw.RSp} (h : Meets d s)
    (v : Vals .two (Fmt.dsOf d.entry d.kind)) (a : List GE) (ha : a.length = s.sent) :
    Tw.RFit s (a, elemsV _ v) := by
  have hl : (elemsV _ v).length = s.drawn := (elemsV_length _ v).trans h.sd.els
  refine ⟨ha, hl, fun hz x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have h0 := elemsV_nz _ i (h.nz hz i (hl ▸ hi)) v
  rwa [List.getD_eq_getElem _ _ hi] at h0

theorem flW_fit {d : PQ.RD} {s : Tw.RSp} (h : Meets d s) (m : (wRound d).Msg)
    (c : (wRound d).Chal) : Tw.RFit s (flW d m c) :=
  elems_fit h _ _ (by
    rw [← rvOf_sent d m c, List.length_map]
    exact h.sd.sent_length m c)

/-! ### a reader of one typed round -/

/-- A reader of the typed round r' at the spec s. -/
structure Rd (r' : Round) (s : Tw.RSp) where
  /-- the typed prover's message, from the scalars sent -/
  fm : List GE → r'.Msg
  /-- the typed verifier's message, from the elements drawn -/
  g : List GE → r'.Chal
  /-- the reading back -/
  out : r'.Msg → r'.Chal → List GE × List GE
  inv : ∀ r, Tw.RFit s r → out (fm r.1) (g r.2) = r

theorem Rd.g_inj {r' : Round} {s : Tw.RSp} (R : Rd r' s) {a l l' : List GE}
    (h : Tw.RFit s (a, l)) (h' : Tw.RFit s (a, l')) (e : R.g l = R.g l') : l = l' := by
  have x := R.inv _ h
  have y := R.inv _ h'
  simp only at x y
  rw [e] at x
  exact congrArg Prod.snd (x.symm.trans y)

theorem Rd.vals_inj {r' : Round} {s : Tw.RSp} (R : Rd r' s) {d : PQ.RD} (h : Meets d s) :
    Function.Injective fun v : Vals .two (Fmt.dsOf d.entry d.kind) => R.g (elemsV _ v) :=
  fun v w e => OnBytes.Slice.vals_inj _ h.sd.plain v w
    (R.g_inj (elems_fit h v (List.replicate s.sent 0) (by simp))
      (elems_fit h w (List.replicate s.sent 0) (by simp)) e)
    ((possV_nil _ h.sd.poss v).trans (possV_nil _ h.sd.poss w).symm)

/-! ### the kinds of round -/

noncomputable section Kinds
open Cb Cb.LdLkp Johnson.L5.Layers

/-- Nothing is sent; k elements are drawn, which make a value of D. -/
def Rd.draw {D : Type} [Fintype D] [Nonempty D] (dl : D → List GE) (k : ℕ) (mk : List GE → D)
    (h : ∀ l, l.length = k → dl (mk l) = l) : Rd (IOR.drawRound D) ⟨0, k, false⟩ where
  fm := fun _ => ((), ())
  g := mk
  out := fun _ c => ([], dl c)
  inv := fun r hr => by
    show (([] : List GE), dl (mk r.2)) = r
    rw [h _ hr.2.1]
    exact Prod.ext (Tw.nil_of_len _ hr.1).symm rfl

/-- One scalar is sent, one element is drawn: the first round of a sumcheck. -/
def Rd.zero : Rd (pRound0 GE) ⟨1, 1, false⟩ where
  fm := fun l => ((), l.headD 0)
  g := fun l => l.headD 0
  out := fun m c => ([m.2], [c])
  inv := fun r hr => by
    show (([r.1.headD 0], [r.2.headD 0]) : List GE × List GE) = r
    rw [Tw.one_of_len _ hr.1, Tw.one_of_len _ hr.2.1]

/-- A variable of a short sumcheck: its coefficients are sent, its challenge is drawn. hv: every
element that the spec lets through is the value of a challenge. -/
def Rd.var (f : PFmt GE) (s : Tw.RSp)
    (hv : s.sent = f.n ∧ s.drawn = 1 ∧ ∀ x : GE, (s.nz = true → x ≠ 0) → ∃ c : f.Ch, f.val c = x) :
    Rd (sRound f) s where
  fm := fun l => ((), fun i : Fin f.n => l.getD i.1 0)
  g := fun l => Function.invFun f.val (l.headD 0)
  out := fun m c => (List.ofFn m.2, [f.val c])
  inv := fun r hr => Tw.round_inv f s r hv hr

/-- Values are sent, in the order of the list sh; nothing is drawn. -/
def Rd.vals {A : Type} (sh : List A) (hn : sh.Nodup) : Rd (pRoundV GE A) ⟨sh.length, 0, false⟩ where
  fm := fun l => ((), Tw.valsOf sh l)
  g := fun _ => ()
  out := fun m _ => (sh.map m.2, [])
  inv := fun r hr => by
    show ((sh.map (Tw.valsOf sh r.1), []) : List GE × List GE) = r
    rw [Tw.map_valsOf sh hn r.1 hr.1]
    exact Prod.ext rfl (Tw.nil_of_len _ hr.2.1).symm

end Kinds

/-! ### a stretch of rounds -/

/-- A reader for each round of a typed shape. -/
def Rds : Shape → List Tw.RSp → Type
  | [], [] => Unit
  | r' :: s', s :: sp => Rd r' s × Rds s' sp
  | [], _ :: _ => Empty
  | _ :: _, [] => Empty

/-- Two shapes in a row. -/
def Rds.app : (a : Shape) → (sa : List Tw.RSp) → {b : Shape} → {sb : List Tw.RSp} → Rds a sa →
    Rds b sb → Rds (a ++ b) (sa ++ sb)
  | [], [], _, _, _, S => S
  | _ :: a, _ :: sa, _, _, R, S => (R.1, Rds.app a sa R.2 S)
  | [], _ :: _, _, _, R, _ => nomatch R
  | _ :: _, [], _, _, R, _ => nomatch R

/-- The reading back of a typed transcript. -/
def outs : (s' : Shape) → (sp : List Tw.RSp) → Rds s' sp → Tr s' → Rounds GE
  | [], [], _, _ => []
  | _ :: s', _ :: sp, R, τ => R.1.out τ.1 τ.2.1 :: outs s' sp R.2 τ.2.2
  | [], _ :: _, R, _ => nomatch R
  | _ :: _, [], R, _ => nomatch R

/-- The typed transcript of plain data. -/
def img : (s' : Shape) → (sp : List Tw.RSp) → Rds s' sp → Rounds GE → Tr s'
  | [], [], _, _ => ()
  | _ :: s', _ :: sp, R, rs =>
    (R.1.fm (rs.headD ([], [])).1, R.1.g (rs.headD ([], [])).2, img s' sp R.2 rs.tail)
  | [], _ :: _, R, _ => nomatch R
  | _ :: _, [], R, _ => nomatch R

theorem outs_img : ∀ (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp) (rs : Rounds GE),
    List.Forall₂ Tw.RFit sp rs → outs s' sp R (img s' sp R rs) = rs
  | [], [], _, _, .nil => rfl
  | _ :: s', _ :: sp, R, _, .cons (b := r) (l₂ := rs) h1 h2 => by
    show R.1.out (R.1.fm r.1) (R.1.g r.2) :: outs s' sp R.2 (img s' sp R.2 rs) = r :: rs
    rw [R.1.inv r h1, outs_img s' sp R.2 rs h2]
  | [], _ :: _, R, _, _ => nomatch R
  | _ :: _, [], R, _, _ => nomatch R

theorem outs_app : ∀ (a : Shape) (sa : List Tw.RSp) {b : Shape} {sb : List Tw.RSp} (R : Rds a sa)
    (S : Rds b sb) (τ : Tr (a ++ b)),
    outs (a ++ b) (sa ++ sb) (Rds.app a sa R S) τ =
      outs a sa R (Tr.fst τ) ++ outs b sb S (Tr.snd (s := a) τ)
  | [], [], _, _, _, _, _ => rfl
  | _ :: a, _ :: sa, _, _, R, S, τ =>
    congrArg (R.1.out τ.1 τ.2.1 :: ·) (outs_app a sa R.2 S τ.2.2)
  | [], _ :: _, _, _, R, _, _ => nomatch R
  | _ :: _, [], _, _, R, _, _ => nomatch R

section Written

/-- A written transcript as plain data. -/
def flWs : (ds : List PQ.RD) → Tr (PQ.uL (ckP .two) ds) → Rounds GE
  | [], _ => []
  | d :: ds, (m, c, τ) => flW d m c :: flWs ds τ

/-- The maps from the written rounds ds to the typed shape. -/
def car : (ds : List PQ.RD) → (s' : Shape) → (sp : List Tw.RSp) → Rds s' sp →
    ds.length = sp.length → CarryS (PQ.uL (ckP .two) ds) s'
  | [], [], [], _, _ => .nil
  | d :: ds, _ :: s', _ :: sp, R, h =>
    .step (r := wRound d) (fun m => R.1.fm (ansOf d m))
      (fun _ => chalTo d fun v => R.1.g (elemsV _ v))
      fun _ _ => car ds s' sp R.2 (Nat.succ.inj h)
  | [], _ :: _, _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], [], _, h => absurd h (by simp)
  | _, [], _ :: _, R, _ => nomatch R
  | _, _ :: _, [], R, _ => nomatch R

/-- A written transcript has an image if and only if every round's test of work passes; the image
is made of its plain data. -/
theorem car_tr : ∀ (ds : List PQ.RD) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (τ : Tr (PQ.uL (ckP .two) ds)), (car ds s' sp R h).tr τ =
      if PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true then
        some (img s' sp R (flWs ds τ)) else none
  | [], [], [], _, _, _ => rfl
  | d :: ds, _ :: s', _ :: sp, R, h, (m, c, τ) => by
    show (chalTo d (fun v => R.1.g (elemsV _ v)) c).bind (fun c' =>
      ((car ds s' sp R.2 (Nat.succ.inj h)).tr τ).map fun τ' => (R.1.fm (ansOf d m), c', τ')) = _
    rw [car_tr ds s' sp R.2 (Nat.succ.inj h) τ]
    show _ = if (GChal.pass (b := d.entry.work) c &&
        PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ)) = true then
      some (R.1.fm (ansOf d m), R.1.g (elemsV _ (OnBytes.Slice.valsOf d c)),
        img s' sp R.2 (flWs ds τ)) else none
    unfold chalTo
    cases GChal.pass (b := d.entry.work) c <;>
      cases PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) <;> rfl
  | [], _ :: _, _ :: _, _, h, _ => absurd h (by simp)
  | _ :: _, [], [], _, h, _ => absurd h (by simp)
  | _, [], _ :: _, R, _, _ => nomatch R
  | _, _ :: _, [], R, _, _ => nomatch R

theorem flWs_fit : ∀ (ds : List PQ.RD) (sp : List Tw.RSp), List.Forall₂ Meets ds sp →
    ∀ τ : Tr (PQ.uL (ckP .two) ds), List.Forall₂ Tw.RFit sp (flWs ds τ)
  | [], [], .nil, _ => .nil
  | _ :: ds, _ :: sp, .cons h1 h2, (m, c, τ) => .cons (flW_fit h1 m c) (flWs_fit ds sp h2 τ)

/-- The image, read back, is the written transcript's plain data; these fit the spec; every test of
work has passed. -/
theorem car_read (ds : List PQ.RD) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ Meets ds sp) (τ : Tr (PQ.uL (ckP .two) ds)) (τ' : Tr s')
    (h : (car ds s' sp R hM.length_eq).tr τ = some τ') :
    outs s' sp R τ' = flWs ds τ ∧ List.Forall₂ Tw.RFit sp (flWs ds τ) ∧
      PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true := by
  rw [car_tr] at h
  split at h
  · next hp =>
    obtain rfl := Option.some.inj h
    exact ⟨outs_img s' sp R _ (flWs_fit ds sp hM τ), flWs_fit ds sp hM τ, hp⟩
  · cases h

/-- A written transcript without an image has failed a test of work. -/
theorem car_none (ds : List PQ.RD) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (h : ds.length = sp.length) (τ : Tr (PQ.uL (ckP .two) ds))
    (h0 : (car ds s' sp R h).tr τ = none) :
    PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = false := by
  rw [car_tr] at h0
  split at h0
  · cases h0
  · next hp => exact Bool.eq_false_iff.2 hp

/-- Each written count is at least the typed count times the sampler's bound of its round. -/
def Bears : (ds : List PQ.RD) → (s' : Shape) → Err s' → Err (PQ.uL (ckP .two) ds) → Prop
  | [], [], _, _ => True
  | d :: ds, _ :: s', ε, ε' =>
    ε.1 * (bsRound .two d.entry d.kind).w ≤ ε'.1 ∧ Bears ds s' ε.2 ε'.2
  | [], _ :: _, _, _ => True
  | _ :: _, [], _, _ => True

theorem car_fits : ∀ (ds : List PQ.RD) (s' : Shape) (sp : List Tw.RSp) (R : Rds s' sp)
    (hM : List.Forall₂ Meets ds sp) (ε : Err s') (ε' : Err (PQ.uL (ckP .two) ds)),
    Bears ds s' ε ε' → (car ds s' sp R hM.length_eq).Fits ε ε'
  | [], [], [], _, _, _, _, _ => trivial
  | d :: ds, _ :: s', _ :: sp, R, .cons h1 h2, ε, ε', hB =>
    ⟨⟨_, fun _ c' => chalTo_fib d _ (R.1.vals_inj h1) h1.sd.logN c', hB.1⟩,
      fun _ _ => car_fits ds s' sp R.2 h2 ε.2 ε'.2 hB.2⟩
  | _, [], _ :: _, R, _, _, _, _ => nomatch R
  | _, _ :: _, [], R, _, _, _, _ => nomatch R

end Written
end Fo.Peel
