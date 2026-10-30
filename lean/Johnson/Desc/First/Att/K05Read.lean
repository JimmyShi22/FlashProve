-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Read.lean: readers along any chain of the library's attention rounds
(Cb/Pv/Att/Own.lean: Ch), so
that written rounds can be read as the chain's typed rounds with the library's own kit
(OnBytes/Tie/Pv/Lookup/Forest/FoPeelKit.lean, FoPeelKitT.lean: Rd, Rds, img, carT). No new carry is
made: chCarry is carT at
the specs and readers that this file lays along a chain.

Main names:
  `rdRide`, `rdSend`: two readers more: a round that sends riders and one scalar and draws one
    element; a round that
    sends n scalars and draws what the stage draws.
  `DrRd`, `RideRd`, `ChRd`: what a reader must be told at a draw, at a sumcheck's stage, along a
    chain.
  `chSp`, `chRds`: the specs and the readers along a chain.
  `chCarry`, `chCarry_fits`, `chCarry_tr`: the carry; its counts bear the chain's errors, where the
    written rounds meet
    the specs (MeetsT) and the written counts bear the typed ones (BearsT); where every test of work
      passes, its image
    of a written transcript is img of the view's rounds, read in the field.
  `img_app`, `ChIs`, `img_join`: plain data that are, stage by stage, the stages' transcripts have
    the chain's joined
    transcript as their image. `ChRd.comap`, `ChIs.comap`.

Sources: the kit's four files; Cb/Pv/Att/ChainRun.lean; OnBytes/Tie/Pv/Att/OwnTie.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKitT
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelForB
import Cb.Pv.Att.ChainRun
import OnBytes.Tie.Pv.Att.OwnTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Pv.Att Cb.Pv.Lay Johnson.L5.Layers OnBytes OnBytes.Model OnBytes.Slice OnBytes.Flat
open OnBytes.Maker Run Fo.Peel TwV

noncomputable section

/-- A sumcheck's first round with n riders: n + 1 scalars are sent, one element is drawn. -/
def rdRide (n : ℕ) : Rd (rRoundN GE n) ⟨n + 1, 1, false⟩ where
  fm := fun l => ((), (fun i : Fin n => l.getD i.1 0, l.getD n 0))
  g := fun l => l.headD 0
  out := fun m c => (List.ofFn m.2.1 ++ [m.2.2], [c])
  inv := fun r hr => by
    show ((List.ofFn (fun i : Fin n => r.1.getD i.1 0) ++ [r.1.getD n 0], [r.2.headD 0]) : List GE × List GE) = r
    rw [Tw.one_of_len _ hr.2.1]
    refine Prod.ext ?_ rfl
    have h1 : r.1.length = n + 1 := hr.1
    show List.ofFn (fun i : Fin n => r.1.getD i.1 0) ++ [r.1.getD n 0] = r.1
    have h2 := Tw.ofFn_getD r.1 (n + 1) h1
    rw [List.ofFn_succ_last] at h2
    exact h2

/-- How a draw's value is made of k elements, and read back. -/
structure DrRd (D : Type) where
  k : ℕ
  dl : D → List GE
  mkD : List GE → D
  inv : ∀ l, l.length = k → dl (mkD l) = l

/-- n scalars are sent; k elements are drawn, which make a value of D. -/
def rdSend (n : ℕ) {D : Type} [Fintype D] [Nonempty D] (q : DrRd D) : Rd (sendRound GE (Fin n) D) ⟨n, q.k, false⟩ where
  fm := fun l => ((), fun i : Fin n => l.getD i.1 0)
  g := q.mkD
  out := fun m c => (List.ofFn m.2, q.dl c)
  inv := fun r hr => by
    show ((List.ofFn (fun i : Fin n => r.1.getD i.1 0), q.dl (q.mkD r.2)) : List GE × List GE) = r
    rw [Tw.ofFn_getD r.1 n hr.1, q.inv _ hr.2.1]

/-- A sumcheck's stage: the variables' specs; the end values' names. -/
structure RideRd (Y : PscPar GE) where
  sp : List Tw.RSp
  fit : Tw.VFit Y.fmt sp
  sh : List Y.A
  nd : sh.Nodup

variable {M : Type}

/-- A reader's data for each stage. -/
def ChRd : {X : Type} → Ch GE M X → Type
  | _, .done _ => Unit
  | _, .ride Y _ _ _ _ _ _ next => RideRd Y × ChRd next
  | _, .draw D _ _ next => DrRd D.D × ChRd next
  | _, .send _ D _ _ _ next => DrRd D.D × ChRd next

/-- The rounds' specs. -/
def chSp : {X : Type} → (c : Ch GE M X) → ChRd c → List Tw.RSp
  | _, .done _, _ => []
  | _, .ride _ n _ _ _ _ _ next, r =>
    (⟨n + 1, 1, false⟩ :: (r.1.sp ++ [⟨r.1.sh.length, 0, false⟩])) ++ chSp next r.2
  | _, .draw _ _ _ next, r => [⟨0, r.1.k, false⟩] ++ chSp next r.2
  | _, .send n _ _ _ _ next, r => [⟨n, r.1.k, false⟩] ++ chSp next r.2

/-- The readers of a sumcheck's stage. -/
def rideRds (Y : PscPar GE) (n : ℕ) (q : RideRd Y) :
    Rds (shapeRN Y n) (⟨n + 1, 1, false⟩ :: (q.sp ++ [⟨q.sh.length, 0, false⟩])) :=
  (rdRide n, Rds.app (sRounds Y.fmt) q.sp (rdsS Y.fmt q.sp q.fit)
    (show Rds [pRoundV GE Y.A] [⟨q.sh.length, 0, false⟩] from (Rd.vals q.sh q.nd, ())))

/-- The readers along the chain. -/
def chRds (Ex : ExtSpec) : {X : Type} → (c : Ch GE M X) → (r : ChRd c) → Rds (c.R Ex).shape (chSp c r)
  | _, .done _, _ => ()
  | _, .ride Y n _ _ _ _ _ next, r => Rds.app (shapeRN Y n) _ (rideRds Y n r.1) (chRds Ex next r.2)
  | _, .draw D _ _ next, r =>
    Rds.app [drawRound D.D] [⟨0, r.1.k, false⟩]
      (show Rds [drawRound D.D] [⟨0, r.1.k, false⟩] from (Rd.draw r.1.dl r.1.k r.1.mkD r.1.inv, ()))
      (chRds Ex next r.2)
  | _, .send n D _ _ _ next, r =>
    Rds.app [sendRound GE (Fin n) D.D] [⟨n, r.1.k, false⟩]
      (show Rds [sendRound GE (Fin n) D.D] [⟨n, r.1.k, false⟩] from (rdSend n r.1, ())) (chRds Ex next r.2)

/-- **The reading.** -/
def chCarry (Ex : ExtSpec) {X : Type} (c : Ch GE M X) (r : ChRd c) (ds : List RDT)
    (hl : ds.length = (chSp c r).length) : CarryS (uLT (ckP .two) ds) (c.R Ex).shape :=
  carT ds _ (chSp c r) (chRds Ex c r) hl

/-- **(b)**: the written counts bear the typed ones. -/
theorem chCarry_fits (Ex : ExtSpec) {X : Type} (c : Ch GE M X) (r : ChRd c) (ds : List RDT)
    (hM : List.Forall₂ MeetsT ds (chSp c r)) (ε' : Err (uLT (ckP .two) ds))
    (hB : BearsT ds (c.R Ex).shape (c.eps Ex) ε') : (chCarry Ex c r ds hM.length_eq).Fits (c.eps Ex) ε' :=
  carT_fits ds _ _ _ hM _ _ hB

/-- Where every test of work passes, the image is img of the view's rounds, read in the field. -/
theorem chCarry_tr (Ex : ExtSpec) {X : Type} (c : Ch GE M X) (r : ChRd c) (ds : List RDT)
    (hl : ds.length = (chSp c r).length) (hA : ∀ d ∈ ds, NoAns d.items) (τ : Tr (uLT (ckP .two) ds))
    (hp : passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true) :
    (chCarry Ex c r ds hl).tr τ =
      some (img _ _ (chRds Ex c r) ((rvT (ckP .two) ds τ).map (Fo.rdRV Reading.gl))) := by
  unfold chCarry
  rw [carT_tr, if_pos hp, flWsT_view ds τ hA]

/-! ## The image, stage by stage -/

theorem img_app : ∀ (a : Shape) (sa : List Tw.RSp) {b : Shape} {sb : List Tw.RSp} (R : Rds a sa) (S : Rds b sb)
    (ra rb : Rounds GE), ra.length = sa.length →
    img (a ++ b) (sa ++ sb) (Rds.app a sa R S) (ra ++ rb) = Tr.app (img a sa R ra) (img b sb S rb)
  | [], [], _, _, _, _, [], _, _ => rfl
  | _ :: a, _ :: sa, _, _, R, S, x :: ra, rb, h => by
    show (R.1.fm x.1, R.1.g x.2, img (a ++ _) (sa ++ _) (Rds.app a sa R.2 S) (ra ++ rb)) = _
    rw [img_app a sa R.2 S ra rb (by simpa using h)]
    rfl
  | [], [], _, _, _, _, _ :: _, _, h => by simp at h
  | _ :: _, _ :: _, _, _, _, _, [], _, h => by simp at h
  | [], _ :: _, _, _, R, _, _, _, _ => nomatch R
  | _ :: _, [], _, _, R, _, _, _, _ => nomatch R

/-- The plain data are the stages' transcripts', stage by stage. -/
def ChIs : {X : Type} → (c : Ch GE M X) → ChRd c → c.Trs → Rounds GE → Prop
  | _, .done _, _, _, p => p = []
  | _, .ride Y n _ _ _ _ _ next, r, ts, p =>
    ∃ pa pb, p = pa ++ pb ∧ pa.length = (r.1.sp ++ [(⟨r.1.sh.length, 0, false⟩ : Tw.RSp)]).length + 1 ∧
      img (shapeRN Y n) _ (rideRds Y n r.1) pa = ts.1 ∧ ChIs next r.2 ts.2 pb
  | _, .draw _ _ _ next, r, ts, p => ∃ x pb, p = x :: pb ∧ r.1.mkD x.2 = ts.1 ∧ ChIs next r.2 ts.2 pb
  | _, .send n _ _ _ _ next, r, ts, p =>
    ∃ x pb, p = x :: pb ∧ (fun i : Fin n => x.1.getD i.1 0) = ts.1.1 ∧ r.1.mkD x.2 = ts.1.2 ∧ ChIs next r.2 ts.2 pb

/-- **Then the image of the plain data is the chain's joined transcript.** -/
theorem img_join (Ex : ExtSpec) : ∀ {X : Type} (c : Ch GE M X) (r : ChRd c) (ts : c.Trs) (p : Rounds GE),
    ChIs c r ts p → img _ _ (chRds Ex c r) p = c.join Ex ts
  | _, .done _, _, _, _, _ => rfl
  | _, .ride Y n _ _ _ _ _ next, r, ts, _, h => by
    obtain ⟨pa, pb, rfl, hl, h1, h2⟩ := h
    show img (shapeRN Y n ++ (next.R Ex).shape) (_ ++ _) (Rds.app (shapeRN Y n) _ (rideRds Y n r.1)
      (chRds Ex next r.2)) (pa ++ pb) = Tr.app (s := shapeRN Y n) ts.1 (next.join Ex ts.2)
    rw [img_app _ _ _ _ pa pb (by rw [hl]; rfl), h1, img_join Ex next r.2 ts.2 pb h2]
  | _, .draw D _ _ next, r, ts, _, h => by
    obtain ⟨x, pb, rfl, h1, h2⟩ := h
    have ih := img_join Ex next r.2 ts.2 pb h2
    show ((((), ()), r.1.mkD x.2, img (next.R Ex).shape _ (chRds Ex next r.2) pb) :
      Tr (drawRound D.D :: (next.R Ex).shape)) = (((), ()), ts.1, next.join Ex ts.2)
    rw [h1, ih]
  | _, .send n D _ _ _ next, r, ts, _, h => by
    obtain ⟨x, pb, rfl, h0, h1, h2⟩ := h
    have ih := img_join Ex next r.2 ts.2 pb h2
    show ((((), fun i : Fin n => x.1.getD i.1 0), r.1.mkD x.2, img (next.R Ex).shape _ (chRds Ex next r.2) pb) :
      Tr (sendRound GE (Fin n) D.D :: (next.R Ex).shape)) = (((), ts.1.1), ts.1.2, next.join Ex ts.2)
    rw [h0, h1, ih]

/-- The reader's data of a chain read at other statements. -/
def ChRd.comap : {X : Type} → (c : Ch GE M X) → ChRd c → {X' : Type} → (f : X' → X) → ChRd (c.comap f)
  | _, .done _, _, _, _ => ()
  | _, .ride _ _ _ _ _ _ _ next, r, _, _ => (r.1, ChRd.comap next r.2 _)
  | _, .draw _ _ _ next, r, _, _ => (r.1, ChRd.comap next r.2 _)
  | _, .send _ _ _ _ _ next, r, _, _ => (r.1, ChRd.comap next r.2 _)

theorem ChIs.comap : ∀ {X : Type} (c : Ch GE M X) (r : ChRd c) (ts : c.Trs) (p : Rounds GE) {X' : Type}
    (f : X' → X), ChIs c r ts p → ChIs (c.comap f) (ChRd.comap c r f) (c.trsComap f ts) p
  | _, .done _, _, _, _, _, _, h => h
  | _, .ride _ _ _ _ _ _ _ next, r, ts, _, _, _, h => by
    obtain ⟨pa, pb, e, hl, h1, h2⟩ := h
    exact ⟨pa, pb, e, hl, h1, ChIs.comap next r.2 ts.2 pb _ h2⟩
  | _, .draw _ _ _ next, r, ts, _, _, _, h => by
    obtain ⟨x, pb, e, h1, h2⟩ := h
    exact ⟨x, pb, e, h1, ChIs.comap next r.2 ts.2 pb _ h2⟩
  | _, .send _ _ _ _ _ next, r, ts, _, _, _, h => by
    obtain ⟨x, pb, e, h0, h1, h2⟩ := h
    exact ⟨x, pb, e, h0, h1, ChIs.comap next r.2 ts.2 pb _ h2⟩

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.img_join
#print axioms VerifiableInference.Desc.First.Att.P.ChIs.comap
#print axioms VerifiableInference.Desc.First.Att.P.chCarry_fits
#print axioms VerifiableInference.Desc.First.Att.P.chCarry_tr
