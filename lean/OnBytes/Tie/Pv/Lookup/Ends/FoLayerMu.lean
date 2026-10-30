-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLayerMu.lean.
The numbers of variables of a layer sub-proof's three product layers, in the record of the tables of
reads: they are what the layout's routine computes; said of what that routine returns, of the
layers' public numbers, and of the public record of a call.

What it is for. takes_hearOwn (OnBytes/Tie/Pv/Tail/TakesLayerProved.lean [not in this library]),
the law on which entries of the plan the own rounds of a layer sub-proof's check use up, has three
premises on the record P.rd: muV, muH and muH2 are the sums that OnBytes/Model/LayerLayout.lean's
readsOf computes. Here they are shown wherever the record comes from that routine;
OnBytes/Tie/Pv/Lookup/Ends/FoDoorsTook.lean [not in this library] uses them.

Main names.
 * `readsOf_mu`: Layer.readsOf y = .ok rd gives rd.muV = rd.lNI + y.lPd + y.h.lt, rd.muH = y.h.ll +
   y.lPf + y.h.lt and rd.muH2 = y.h.ll - 1 + y.lfe + y.h.lt.
 * `pubOf_mu`: the same of P.rd and P.y, at a P that Layer.Pub.of (OnBytes/Model/LayerPlan.lean) has
   returned.
 * `publicOf_layers`: where Verify.publicOf (OnBytes/Model/VerifyPublic.lean) returns X, X.layers is
   what Layer.Pub.of has returned, at some arguments. They stand under a bare ∃: the proof walks
   publicOf's text as publicOf_scan of OnBytes/Model/VerifyDerives.lean does and keeps that one
   equation; which arguments they are is not said (publicOf_cut of
   OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean has the layout).
 * `public_mu`: the three equations at { X.layers with tokv := tk }, for every tk.

The statements of readsOf_mu and pubOf_mu are proved also as takes_hearOwn_reads and
takes_hearOwn_pub in OnBytes/Tie/Pv/Tail/TakesLayerPremises.lean [not in this library]; that
file stops at a record that Layer.Pub.of returns: publicOf_layers and public_mu have no like there.

Limits. Nothing on the record's other fields. Nothing on what the three numbers are at any
configuration.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.VerifyDerives

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model
open OnBytes.Params (exc_bind)

/-- **The numbers of variables of the three product layers, in the tables of reads that the layout's
routine returns.** -/
theorem readsOf_mu {y : Layer.Lay} {rd : Layer.Reads} (h : Layer.readsOf y = .ok rd) :
    rd.muV = rd.lNI + y.lPd + y.h.lt ∧ rd.muH = y.h.ll + y.lPf + y.h.lt ∧
      rd.muH2 = y.h.ll - 1 + y.lfe + y.h.lt := by
  unfold Layer.readsOf at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- **The same of the public numbers of the layers that Pub.of returns.** -/
theorem pubOf_mu {y : Layer.Lay} {sc : Layer.Scales} {rope : Array Nat} {wsLay : WsLay} {V : Nat}
    {tokv : Array Nat} {set : Settings} {P : Layer.Pub}
    (h : Layer.Pub.of y sc rope wsLay V tokv set = .ok P) :
    P.rd.muV = P.rd.lNI + P.y.lPd + P.y.h.lt ∧ P.rd.muH = P.y.h.ll + P.y.lPf + P.y.h.lt ∧
      P.rd.muH2 = P.y.h.ll - 1 + P.y.lfe + P.y.h.lt := by
  unfold Layer.Pub.of at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i rd hr
      cases h
      exact readsOf_mu hr

/-- **The layers' public numbers in the public record are what Pub.of has returned.** -/
theorem publicOf_layers {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    ∃ y sc rope wsLay V tokv set, Layer.Pub.of y sc rope wsLay V tokv set = .ok X.layers := by
  unfold Verify.publicOf at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals first
    | (cases h; exact ⟨_, _, _, _, _, _, _, by assumption⟩)
    | cases h

/-- **The three numbers in the public record's layers, whatever the tokens laid in.** -/
theorem public_mu {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (tk : Array Nat) :
    ({ X.layers with tokv := tk } : Layer.Pub).rd.muV =
        ({ X.layers with tokv := tk } : Layer.Pub).rd.lNI +
          ({ X.layers with tokv := tk } : Layer.Pub).y.lPd +
          ({ X.layers with tokv := tk } : Layer.Pub).y.h.lt ∧
      ({ X.layers with tokv := tk } : Layer.Pub).rd.muH =
        ({ X.layers with tokv := tk } : Layer.Pub).y.h.ll +
          ({ X.layers with tokv := tk } : Layer.Pub).y.lPf +
          ({ X.layers with tokv := tk } : Layer.Pub).y.h.lt ∧
      ({ X.layers with tokv := tk } : Layer.Pub).rd.muH2 =
        ({ X.layers with tokv := tk } : Layer.Pub).y.h.ll - 1 +
          ({ X.layers with tokv := tk } : Layer.Pub).y.lfe +
          ({ X.layers with tokv := tk } : Layer.Pub).y.h.lt := by
  obtain ⟨y, sc, rope, wsLay, V, tokv, set, hP⟩ := publicOf_layers h
  have m := pubOf_mu hP
  exact m

end Fo
