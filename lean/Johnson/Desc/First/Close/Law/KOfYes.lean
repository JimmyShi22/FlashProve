-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/KOfYes.lean: THE TWO EQUATIONS OF NUMBERS AT THE HEAD OF K10's PROMISE
ARE READ OFF THE BLOCK's OWN YES. Definitions, statements and proofs.

Why. `K10OnS` (AtBlockSelf.lean, beside this file) begins with two equations: the frame's record of
the group at the frame's link has the typed stage's k and h. They read `frame.groups[frame.link]`:
the link steps on at K10's own block: as a public item of a table ("K10.on") that sentence would be
made by the closing of the segment before and kept by every block of the segment. The closing's own
text tests both numbers. A clause that every yes implies can be struck from the promise of a law in
the form `Leads`: where it fails the block never says yes, and what never happens costs nothing
(`Doomed.of_forall`).
  `fold_stretch`, `closing_stretch`, `entries_length`, `closeFrame_k`: the test "K10.stretch": a yes
    at the entries of a place Pr: the frame's record of the group has k = Pr.k.
  `bat_layout`, `closing_kh`, `closeFrame_kh`: the test "K10.kh": at a yes the frame's record's k
    and h ARE those of the layout that the statement gives the frame's group; and the begun
    statement gives the same layout (`begun_layout`).
  `K10OnT`, `k10_any_k`: the law without the equation on k, with hPr : Pr.k = R.s.h + R.s.g: a
    premise on LETTERS (the place's number against the typed stage's).
  `K10OnU`, `k10_any_u`: the law without either equation: in their place one clause: the layout that
    the statement gives the frame's group has the stage's h.
Limits. (1) THE PROMISE STILL READS THE FRAME, ITS MOVING PART WITH IT. `K10OnU`'s new clause names
the group by `frame.group`. `K10On`'s own clauses (front, tied, masks, rows, code, place), which
stand as they were, are said at `frame.group`, `frame.mask` and the plan `planOf ..`, whose codes
are the frame's shape's and whose k and h are again those of `frame.groups[frame.link]`. What has
fallen is the two EQUATIONS between that record's k and h and the typed stage's: what the named item
"K10.on" said. Whether the clauses that remain need a sentence on `frame.group` or `frame.mask` that
some block must make and others keep is not looked at here. (2) The new clause is a promise on the
record: on the statement's layout, a function of the group's members' shapes: who draws it from a
table's promise is not said here. (3) hPr is shown of no place and no typed group here. (4) Of
`K10On`, rows and half of masks follow from "the statement is in order" (OnOfOrder.lean). (5)
`closeFrame_kh` also gives lay.k and lay.h at the begun statement's layout, which EndSays.lean asks
as premises: not laid in there. All other bounds of the law stand. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.AtAny
import Johnson.Desc.First.Close.Law.Inv
import Johnson.Desc.Sound.PieceOut
import Johnson.Desc.Own.LayoutAgree
import Johnson.Desc.First.Close.Law.LayBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice

/-- **A yes of the fold has as many entries "FOLD round" as the shape's layout has row variables.**
    -/
theorem fold_stretch {S S' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : fold S F row m es rs = .ok (out, S')) : es.length = 1 + F.layout.k := by
  unfold fold at h
  cases hD : foldD 0 (onSt S) F row (some m) es rs with
  | error e => rw [hD] at h; exact absurd h (by simp [Except.map])
  | ok y =>
    unfold foldD at hD
    split at hD
    · rename_i eE eR rE rR
      obtain ⟨_, k1, -⟩ := ok_bind hD
      have k1 := need_ok k1
      simp only [Bool.and_eq_true, beq_iff_eq] at k1
      rw [List.length_cons, k1.1, Nat.add_comm]
    · exact absurd hD (by simp)

/-- **A yes of the closing: the plan has two entries and one for each of its k row variables.** -/
theorem closing_stretch {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    P.entries.length = 2 + P.k := by
  unfold closing at h
  split at h
  · rename_i eB es rB rs' he
    obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, -, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    have e := fold_stretch h
    have e2 : es.length = 1 + P.k := e
    rw [he, List.length_cons, e2]
    omega
  · exact absurd h (by simp)

theorem entries_length (Pr : Par) : (entries Pr).length = 2 + Pr.k := by
  simp only [entries, List.length_cons, List.length_replicate]
  omega

/-- **A yes of the frame's closing at a place's entries: the frame's record of the group at its link
has the place's k.** -/
theorem closeFrame_k {owed : Option Nat} {f : ReqFrame} {S : Statement} {Pr : Par}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S (entries Pr) rs = .ok x) :
    ∃ G, f.groups[f.link]? = some G ∧ G.k = Pr.k := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨L, -, h⟩ := ok_bind h
  obtain ⟨G, kG, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨y, kc, -⟩ := ok_bind h
  have e := closing_stretch (out := y.1) (S' := y.2) kc
  have e' : (entries Pr).length = 2 + G.k := e
  rw [entries_length] at e'
  exact ⟨G, got_ok kG, by omega⟩

/-- **The layout that a yes of the batching returns is the statement's own, for the group.** -/
theorem bat_layout {S S1 : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow}
    {lay : GroupLayout} (h : bat S g e r = .ok (row, lay, S1)) :
    ∃ G, S.groups[g]? = some G ∧ S.layout g = some lay := by
  unfold bat at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨p, k1, h⟩ := ok_bind h
  have k1 := got_ok k1
  obtain ⟨x, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨row', -, h⟩ := ok_bind h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -⟩ := h
  unfold Ground.beginRunP at k1
  split at k1
  · cases hG : (onSt S).st.groups[g]? with
    | none => simp [hG] at k1
    | some G =>
      simp [hG] at k1
      refine ⟨G, hG, ?_⟩
      rw [← k1]
      exact Own.layout_of_group hG
  · exact absurd k1 (by simp)

/-- **A yes of the closing: the statement's layout of the group has the plan's k and h** (its test
"K10.kh"). -/
theorem closing_kh {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ G lay, S.groups[g]? = some G ∧ S.layout g = some lay ∧ lay.k = P.k ∧ lay.h = P.h := by
  unfold closing at h
  split at h
  · obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, k2, -⟩ := ok_bind h
    obtain ⟨G, hG, hL⟩ := bat_layout (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    have k2 := need_ok k2
    simp only [Bool.and_eq_true, beq_iff_eq] at k2
    exact ⟨G, p.2.1, hG, hL, k2.1, k2.2⟩
  · exact absurd h (by simp)

/-- **A yes of the frame's closing: the frame's record of the group at its link has the k and the h
of the statement's layout of the frame's group**, in front of and behind the beginning of the test.
-/
theorem closeFrame_kh {owed : Option Nat} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) :
    ∃ Gf G lay, f.groups[f.link]? = some Gf ∧ S.groups[f.group]? = some G ∧
      S.layout f.group = some lay ∧ (begun S f.group G).layout f.group = some lay ∧
      lay.k = Gf.k ∧ lay.h = Gf.h := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨L, -, h⟩ := ok_bind h
  obtain ⟨Gf, kG, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨y, kc, -⟩ := ok_bind h
  obtain ⟨G, lay, hG, hL, e1, e2⟩ := closing_kh (out := y.1) (S' := y.2) kc
  exact ⟨Gf, G, lay, got_ok kG, hG, hL, by rw [OnBytes.LayLaw.begun_layout S _ G hG]; exact hL,
    e1, e2⟩

section
open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR Prob Run KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (pull : (R.Sh.Cin.J → GE) → R.G.C.J → GE) (n : ℕ)
  (num : R.G.Row B ≃ Fin n)
  (fx : Fin ((R.Sh.fold (SbV R B) (slV R pull) (ZV R n num)).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp).Msg × Wp))
  (bC bZ : ℕ) (w₀ : S.Wit × Wp)
  (w₁ : LdBrW R.G (R.sizeB keep (SbV R B) (slV R pull) (ZV R n num)).kp Wp)

/-- **K10's condition in front, WITHOUT THE EQUATION ON k**: `K10OnS` (AtBlockSelf.lean) but for its
first clause. -/
def K10OnT (L : List (BatFoldCaller GE))
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (Pr : Par) {F : Frame}
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a : VerifiableInference.Desc.First.S × F.E.Str) : Prop :=
  (planOf (entries Pr) (rdK a.1)).h = R.s.h ∧
    K10On R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS (planOf (entries Pr) (rdK a.1)) (rdK
      a.1).2.1.group (rdK a.1).2.1.mask (entries Pr) rdK fa a

/-- **K10's LAW WITH THE EQUATION ON k READ OFF THE BLOCK's OWN YES**: `k10_any_self` at the promise
`K10OnT`, with hPr : the place's k is the typed stage's number of row variables: A PREMISE ON
    LETTERS,
not on the record. By cases on the record: where the frame's record of the group has that k, the
law; where it has another, the block never says yes (`closeFrame_k`), and what never happens costs
nothing. -/
theorem k10_any_k
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
      dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
      dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx (rd2
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
      bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits)
    (hg : R.Good)
    (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d)
    (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (hPr : Pr.k = R.s.h + R.s.g)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (x : Johnson.Bridge.FoldedPlace)
    (hx : x.Paid)
    (hxs : x.s = R.s)
    (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC)
    (hxZ : bZ ≤ x.bZ)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace)
    (hy : y.Paid)
    (hys : y.s = R.s)
    (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1)
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows)) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10OnT R N keep pull n num fx A₀ bC bZ w₀
      w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE dR (Yc
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp
      a.2 τ ∧ sTests (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
      (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx
      A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK
      a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK
      a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment =
      reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
        a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
        G).layout (rdK a.1).2.1.group = some lay → ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows
        (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G)
        lay (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j = readE
        (runRows (rdK a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
          (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds)) := fun a ha => by
  by_cases hk : (planOf (entries Pr) (rdK a.1)).k = R.s.h + R.s.g
  · exact
      k10_any_self R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv
        hP pS Pr b H base ext err fa x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB a ⟨hk, ha.1,
        ha.2⟩
  · refine Doomed.of_forall _ _ fun τ a' hb => absurd ?_ hk
    obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := Piece.out_decide _ a a' τ hb
    obtain ⟨x', hx', -⟩ := H _ _ _ _ (below_yes _ _ _ _ _ hd)
    obtain ⟨G, hG, e⟩ := closeFrame_k hx'
    show ((rdK a.1).2.1.groups[(rdK a.1).2.1.link]?.getD default).k = _
    rw [hG]
    exact e.trans hPr

/-- **K10's condition in front, without the two equations on the frame's record of the group**: in
their place ONE CLAUSE: the layout that the statement gives the frame's group has the typed stage's
number of mask row variables. -/
def K10OnU (L : List (BatFoldCaller GE))
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    (Pr : Par) {F : Frame}
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (a : VerifiableInference.Desc.First.S × F.E.Str) : Prop :=
  (∀ lay, (rdK a.1).2.2.layout (rdK a.1).2.1.group = some lay → lay.h = R.s.h) ∧
    K10On R N keep pull n num fx A₀ bC bZ w₀ w₁ L pS (planOf (entries Pr) (rdK a.1)) (rdK
      a.1).2.1.group (rdK a.1).2.1.mask (entries Pr) rdK fa a

/-- **K10's LAW WITH BOTH EQUATIONS READ OFF THE BLOCK's OWN YES**: `k10_any_k` at the promise
`K10OnU`. By cases on the record: where the frame's record of the group has the stage's h, that law;
where it has another, the block never says yes: its test "K10.kh" holds that h against the
statement's layout's (`closeFrame_kh`), which has the stage's by the promise. -/
theorem k10_any_u
    (L : List (BatFoldCaller GE))
    (dB dE dR : RDT)
    (ρ : Rd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) (wT dB) (wT
      dE) (wT dR))
    (hρ : ρ = realRd (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁) dB dE
      dR (oneOf id) (oneOf id))
    (hst : StepOK (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).n fx (rd2
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC
      bZ w₀ w₁)).n).mon fx.1 = 1)
    (hFi : R.G.Fits)
    (hg : R.Good)
    (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d)
    (hv : ∀ a, (R.view a).Fix R.G.e)
    (hP : Pulls R pull)
    (pS : ∀ as : (Σ a : R.G.A, (S.om a.1).Z.S), (S.om as.1.1).Z.D → R.Sh.Cin.J → GE)
    {Cl W : Type}
    {F : Frame}
    (Pr : Par)
    (b : Block VerifiableInference.Desc.First.S Cl)
    (H : ∀ s rs gs s', b.decide s rs gs = .ok s' → ∃ x, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2
      (entries Pr) rs = .ok x ∧ s' = wrK s x.1 x.2)
    (hPr : Pr.k = R.s.h + R.s.g)
    (base : ℕ)
    (ext : VerifiableInference.Desc.First.S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE ::
      List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀
      w₁)).k dR)) → W → W)
    (err : Err (uLT (ckP .two) (dB :: dE :: List.replicate (Yc (R.foldCaller keep (SbV R B) (slV R
      pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k dR)))
    (fa : VerifiableInference.Desc.First.S × F.E.Str → ((kBatFoldRide L).src (R.foldCaller keep (SbV
      R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).X × ((kBatFoldRide L).src (R.foldCaller
      keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).E.Str)
    (x : Johnson.Bridge.FoldedPlace)
    (hx : x.Paid)
    (hxs : x.s = R.s)
    (hxe : x.e = R.e)
    (hxC : bC ≤ x.bC)
    (hxZ : bZ ≤ x.bZ)
    {na nb : String}
    (iE : IsRd (toRD dE) (Fmt.M1.rEps na))
    (iR : IsRd (toRD dR) (Fmt.M1.rTwo nb))
    (y : Johnson.Bridge.BatPlace)
    (hy : y.Paid)
    (hys : y.s = R.s)
    (hye : y.e = R.e)
    (hyz : (ZV R n num).err ≤ y.rows - 1)
    (iB : IsRd (toRD dB) (Fmt.M2.rBatN y.rows)) :
    (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n
      num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.red.Leads (K10OnU R N keep pull n num fx A₀ bC bZ w₀
      w₁ L pS Pr fa) (fun a a' => (∃ τ, a'.2 = (pieceOn (W := W) (F := F) b base dB dE dR (Yc
      (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ior.imp
      a.2 τ ∧ sTests (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
      (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ = true ∧
      closeFrame (rdK a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 (entries Pr) ((sView (ckP .two) (pieceOn (W
      := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep (SbV R B) (slV R pull) (ZV R n num) fx
      A₀ bC bZ w₀ w₁)).k ext err).stage a.2 τ).rounds.map noDigest) = .ok (rdBK a'.1)) ∧ a'.1 = wrK
      a.1 (rdBK a'.1).1 (rdBK a'.1).2 ∧ ((rdK a.1).1 = none ∧ ∃ lk, (rdK a.1).2.1.shape.link[(rdK
      a.1).2.1.link]? = some lk ∧ (rdK a.1).2.1.next = .laterOrClose ∧ (rdK a.1).2.1.moment =
      reqMoments lk) ∧ (rdBK a'.1).1 = {
          (rdK a.1).2.1 with
          rows := (rdBK a'.1).1.rows, mask := none, link := (rdK a.1).2.1.link + 1, next := .first }
      ∧ (CarriedAt R N keep (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁ L (fa a) (rdBK
        a'.1).1.rows → (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧ ∀ m :
        S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) → ∀ G lay, (rdK
        a.1).2.2.groups[(rdK a.1).2.1.group]? = some G → (begun (rdK a.1).2.2 (rdK a.1).2.1.group
        G).layout (rdK a.1).2.1.group = some lay → ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows
        (rdK a.1).2.2 G).toList.length), ∑ j, rowVec N (begun (rdK a.1).2.2 (rdK a.1).2.1.group G)
        lay (runRows (rdK a.1).2.2 G).toList[i] j * (R.Sh.rho.up (R.G.msg m, r)).1 j = readE
        (runRows (rdK a.1).2.2 G).toList[i].target))
      (Err.cap 128 (uLT (ckP .two) (pieceOn (W := W) (F := F) b base dB dE dR (Yc (R.foldCaller keep
          (SbV R B) (slV R pull) (ZV R n num) fx A₀ bC bZ w₀ w₁)).k ext err).ds)) := fun a ha => by
  by_cases hh : (planOf (entries Pr) (rdK a.1)).h = R.s.h
  · exact
      k10_any_k R N keep pull n num fx A₀ bC bZ w₀ w₁ L dB dE dR ρ hρ hst hfx hFi hg hj hc he hv hP
        pS Pr b H hPr base ext err fa x hx hxs hxe hxC hxZ iE iR y hy hys hye hyz iB a ⟨hh, ha.2⟩
  · refine Doomed.of_forall _ _ fun τ a' hb => absurd ?_ hh
    obtain ⟨-, -, ⟨gs, hd⟩, -⟩ := Piece.out_decide _ a a' τ hb
    obtain ⟨x', hx', -⟩ := H _ _ _ _ (below_yes _ _ _ _ _ hd)
    obtain ⟨Gf, G, lay, hGf, -, hL, -, -, e⟩ := closeFrame_kh hx'
    show ((rdK a.1).2.1.groups[(rdK a.1).2.1.link]?.getD default).h = _
    rw [hGf]
    exact e.symm.trans (ha.1 lay hL)

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.k10_any_u
#print axioms VerifiableInference.Desc.First.Close.closeFrame_k
#print axioms VerifiableInference.Desc.First.Close.closeFrame_kh
#print axioms VerifiableInference.Desc.First.Close.k10_any_k
