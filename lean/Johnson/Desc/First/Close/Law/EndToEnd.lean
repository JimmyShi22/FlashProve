-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/EndToEnd.lean: THE LAW OF K10, END TO END, AS ONE STATEMENT: from the
frame's closing over its written rounds to the program's rows at the decoded messages. A statement
and its proof.

  `frameRed_yes`: where `frameRed` puts out, at a record that stands at the place, `closing` has
    said yes and returned the claim in the frame behind and the statement behind.
  `k10_rows`: `(frameRed ρ es rec).Leads on' Q ε'` (Johnson/Desc/Plain/Leads.lean): on the
    statements with `on` that stand at the place (`AtPlace`) the prover has lost, at the start,
    towards: whatever `closeFrame` puts out, (1) the statement in front rides along; (2) the frame
    behind is the frame in front with the claim laid into `rows`, no mask, the next link, "first";
    (3) IF what is carried holds of that claim (`CarriedAt`, Leads.lean) THEN every member's word
    decodes with its sample, and at whatever family m is the decodings EVERY ROW OF `runRows` of the
    group, by its number, holds: `rowVec` of it (BatTie.lean), on the arranged messages of m with
    any randomness, gives the reading of its target.
  `closeFrame_asks`, `frameRed_asks`: what `closeFrame` asks of the record in front of `closing`:
    nothing is owed; the link is there; the frame stands at "later or close", at the link's last
    moment.
  `k10_rows_asks`: `k10_rows` with these four in its end, and with the premise on the readings'
    being defined (hD) paid by `defAt_of_yes` (DefAt.lean) from two facts on the readings alone:
    each is defined at every list of one element.
It joins `k10_leads_good`, `k10_front`, `frame_leads` and `front_program`, each beside this file, by
the frame rule `Leads.conseq`. The errors are those of `k10_leads_good`. "Every row": `OrderedV`
lists ALL names of typed rows, the claim's and every member's sample rows, against the whole list
`runRows`.
Premises: those of `k10_leads_good` (Leads.lean), at the statement that `rec` reads. Limits: those
of the four files. Called at no value. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.FrameLaw
import Johnson.Desc.First.Close.Law.AllRows
import Johnson.Desc.First.Close.Law.DefAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

/-- Where the frame's closing puts out, at the place, `closing` has said yes. -/
theorem frameRed_yes {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR) (P : Plan)
    (g : Nat) (mask : Option Nat) (es : List Fmt.Entry) {A : Type}
    (rec : A → Option Nat × ReqFrame × Statement) (a : A)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (b : A × ReqFrame × Statement)
    (hb : (frameRed ρ es rec).out a τ = some b) (hp : AtPlace P g mask es (rec a)) :
    closing P (rec a).2.2 g mask (ρ.V τ) = .ok (b.2.1.rows, b.2.2) := by
  have hb' : (match closeFrame (rec a).1 (rec a).2.1 (rec a).2.2 es (ρ.V τ) with
    | .ok x => some (a, x.1, x.2)
    | .error _ => none) = some b := hb
  split at hb'
  · next x hx =>
    obtain rfl := Option.some.inj hb'
    obtain ⟨G, rows, hG, hc, hf⟩ := closeFrame_lays (f' := x.1) (S' := x.2) hx
    obtain ⟨h1, h2, h3⟩ := hp
    rw [h3 G hG, h1, h2] at hc
    have hr : x.1.rows = rows := by rw [hf]
    rw [hc, hr]
  · cases hb'

/-- What the frame's closing asks of the record in front of `closing`. -/
theorem closeFrame_asks {owed : Option Nat} {f f' : ReqFrame} {S S' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f S es rs = .ok (f', S')) :
    owed = none ∧ ∃ L, f.shape.link[f.link]? = some L ∧ f.next = .laterOrClose ∧
      f.moment = reqMoments L := by
  unfold closeFrame at h
  obtain ⟨_, k0, h⟩ := ok_bind h
  obtain ⟨L, k1, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨_, k3, -⟩ := ok_bind h
  have k3 := need_ok k3
  simp only [Bool.and_eq_true, beq_iff_eq] at k3
  exact ⟨Option.isNone_iff_eq_none.1 (need_ok k0), L, got_ok k1, k3.1, k3.2⟩

/-- The same where `frameRed` puts out. -/
theorem frameRed_asks {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR)
    (es : List Fmt.Entry) {A : Type} (rec : A → Option Nat × ReqFrame × Statement) (a : A)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (b : A × ReqFrame × Statement)
    (hb : (frameRed ρ es rec).out a τ = some b) :
    (rec a).1 = none ∧ ∃ L, (rec a).2.1.shape.link[(rec a).2.1.link]? = some L ∧
      (rec a).2.1.next = .laterOrClose ∧ (rec a).2.1.moment = reqMoments L := by
  have hb' : (match closeFrame (rec a).1 (rec a).2.1 (rec a).2.2 es (ρ.V τ) with
    | .ok x => some (a, x.1, x.2)
    | .error _ => none) = some b := hb
  split at hb'
  · next x hx => exact closeFrame_asks (f' := x.1) (S' := x.2) hx
  · cases hb'

section Caller
variable {S : Sig GE} (R : RowsK S) (N : SlotNames R) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **THE LAW OF K10, END TO END.** -/
theorem k10_rows (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hZo : Z.OK) (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt R.Sh j → fr ν s j = 0)
    (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry) {A : Type}
    (rec : A → Option Nat × ReqFrame × Statement)
    (fa : A → ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (on : A → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).on (fa a))
    (ε' : Err (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (hFit : ρ.carS.Fits (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx
      (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) fun _ => bZ) ε')
    (hD : ∀ a, on a → ∀ τ x, closing P (rec a).2.2 g mask (ρ.V τ) = .ok x → ρ.DefAt (ρ.V τ))
    (hO : ∀ a, on a → ∀ (τ : Tr (rB :: rE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR)) x,
      closing P (rec a).2.2 g mask (ρ.V τ) = .ok x → ∀ G e z lay,
      (rec a).2.2.groups[g]? = some G →
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun (rec a).2.2 g G).layout g = some lay →
      OrderedV R Sb sl Z N fr (fa a).1.1.1 (fa a).1.2 z e (begun (rec a).2.2 g G) lay
        (runRows (rec a).2.2 G).toList)
    (hM : ∀ a, on a → ∀ G lay, (rec a).2.2.groups[g]? = some G →
      (begun (rec a).2.2 g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (rec a).2.2 G).toList, MaskFits (begun (rec a).2.2 g G) lay w)
    (hR : ∀ a, on a → ∀ G, (rec a).2.2.groups[g]? = some G →
      ∀ w ∈ (runRows (rec a).2.2 G).toList, RowFits (begun (rec a).2.2 g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((rec a).2.2.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    (frameRed ρ es rec).Leads (fun a => on a ∧ AtPlace P g mask es (rec a))
      (fun a b => b.1 = a ∧
        b.2.1 = { (rec a).2.1 with
          rows := b.2.1.rows, mask := none, link := (rec a).2.1.link + 1, next := .first } ∧
        (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rec a).2.2.groups[g]? = some G →
              (begun (rec a).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rec a).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rec a).2.2 g G) lay (runRows (rec a).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rec a).2.2 G).toList[i].target)) ε' := by
  have h1 := k10_leads_good R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR ρ hS hst hfx hZo hFi hg hj
    hc he hv fr hfr P g mask (fun a => (rec a).2.2) fa on hon ε' hFit hD hO hM hR hk hh hZ
  have h2 := k10_front R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR ρ P g mask
    (fun a => (rec a).2.2) fa on ε' h1
  have h3 := frame_leads ρ P g mask es rec on _ ε' h2
  refine h3.conseq (fun _ k => k) fun a τ b ha hb hq => ?_
  obtain ⟨q1, q2, -, q3⟩ := hq
  refine ⟨q1, q2, fun hcar => ?_⟩
  have hF := q3 hcar
  refine ⟨hF.1, fun m hm G lay hG hl r i hi => ?_⟩
  have hy := frameRed_yes ρ P g mask es rec a τ b hb ha.2
  obtain ⟨G', x, _, _, _, vB, _, _, _, _, _, _, e0, -, -, p3, -⟩ := closing_inv2 hy
  have eV : ρ.V τ = ρ.viewB τ.1 τ.2.1 :: ρ.viewE τ.2.2.1 τ.2.2.2.1 ::
      ρ.vK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k τ.2.2.2.2 := rfl
  rw [eV] at e0
  obtain ⟨e1, -⟩ := List.cons.inj e0
  obtain ⟨z, gz⟩ := Option.isSome_iff_exists.1 ((hD a ha.1 τ _ hy).1 (ρ.viewB τ.1 τ.2.1) (by
    rw [eV]
    show _ ∈ [ρ.viewB τ.1 τ.2.1]
    exact List.mem_singleton.2 rfl))
  have hOV := hO a ha.1 τ _ hy G x z lay hG (by rw [e1]; exact p3) gz hl
  exact front_program R keep Sb sl Z A₀ R.Sh.par.Cw.nat
    (ldGroup_shape_laws GE S R.G R.Sh (R.sh_ok hg)).1 (fa a) hF m hm hOV r i hi

/-- **THE LAW OF K10, END TO END**, with the readings' being defined paid from two facts on the
readings alone, and with what the frame's closing asks of the record said in the end. -/
theorem k10_rows_asks (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hZo : Z.OK) (hFi : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e) (hc : CountsAt R.s R.e bC bZ)
    (he : R.G.e < R.s.d) (hv : ∀ a, (R.view a).Fix R.G.e)
    (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt R.Sh j → fr ν s j = 0)
    (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry) {A : Type}
    (rec : A → Option Nat × ReqFrame × Statement)
    (fa : A → ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (on : A → Prop)
    (hon : ∀ a, on a →
      ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).on (fa a))
    (ε' : Err (rB :: rE ::
      List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR))
    (hFit : ρ.carS.Fits (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx
      (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) fun _ => bZ) ε')
    (hZ1 : ∀ e, (ρ.rdZ [e]).isSome) (hC1 : ∀ e, (ρ.rdCh [e]).isSome)
    (hO : ∀ a, on a → ∀ (τ : Tr (rB :: rE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR)) x,
      closing P (rec a).2.2 g mask (ρ.V τ) = .ok x → ∀ G e z lay,
      (rec a).2.2.groups[g]? = some G →
      (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun (rec a).2.2 g G).layout g = some lay →
      OrderedV R Sb sl Z N fr (fa a).1.1.1 (fa a).1.2 z e (begun (rec a).2.2 g G) lay
        (runRows (rec a).2.2 G).toList)
    (hM : ∀ a, on a → ∀ G lay, (rec a).2.2.groups[g]? = some G →
      (begun (rec a).2.2 g G).layout g = some lay → R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows (rec a).2.2 G).toList, MaskFits (begun (rec a).2.2 g G) lay w)
    (hR : ∀ a, on a → ∀ G, (rec a).2.2.groups[g]? = some G →
      ∀ w ∈ (runRows (rec a).2.2 G).toList, RowFits (begun (rec a).2.2 g G) w)
    (hk : P.k = R.s.h + R.s.g) (hh : P.h = R.s.h)
    (hZ : ∀ a, on a → ((rec a).2.2.codes.mask.getD P.maskCode default).ell = R.s.Z.l) :
    (frameRed ρ es rec).Leads (fun a => on a ∧ AtPlace P g mask es (rec a))
      (fun a b => b.1 = a ∧
        ((rec a).1 = none ∧ ∃ L, (rec a).2.1.shape.link[(rec a).2.1.link]? = some L ∧
          (rec a).2.1.next = .laterOrClose ∧ (rec a).2.1.moment = reqMoments L) ∧
        b.2.1 = { (rec a).2.1 with
          rows := b.2.1.rows, mask := none, link := (rec a).2.1.link + 1, next := .first } ∧
        (CarriedAt R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L (fa a) b.2.1.rows →
          (∃ m : S.Msg, ∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) ∧
          ∀ m : S.Msg, (∀ i, S.decs (fa a).1.2 (fa a).2.1.2 i = some (m i)) →
            ∀ G lay, (rec a).2.2.groups[g]? = some G →
              (begun (rec a).2.2 g G).layout g = some lay →
              ∀ (r : R.G.C.Q → GE) (i : ℕ) (hi : i < (runRows (rec a).2.2 G).toList.length),
                ∑ j, rowVec N (begun (rec a).2.2 g G) lay (runRows (rec a).2.2 G).toList[i] j *
                    (R.Sh.rho.up (R.G.msg m, r)).1 j =
                  readE (runRows (rec a).2.2 G).toList[i].target)) ε' :=
  (k10_rows R N keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR ρ hS hst hfx hZo hFi hg hj hc he hv fr hfr
    P g mask es rec fa on hon ε' hFit (fun _ _ _ _ h => defAt_of_yes ρ h hZ1 hC1) hO hM hR hk hh
    hZ).conseq (fun _ k => k) fun a τ b _ hb hq =>
      ⟨hq.1, frameRed_asks ρ es rec a τ b hb, hq.2⟩

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.frameRed_yes
#print axioms VerifiableInference.Desc.First.Close.k10_rows
#print axioms VerifiableInference.Desc.First.Close.closeFrame_asks
#print axioms VerifiableInference.Desc.First.Close.k10_rows_asks
