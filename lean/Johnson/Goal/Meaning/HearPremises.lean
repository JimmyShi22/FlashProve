-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HearPremises.lean: what a builder of the record Pub34
(Johnson/Road/Rows/LayerEnds34.lean:182 ff.) from a run of a layer sub-proof's check asks of the
public files, as one record, and that record at all public files in the goals' scope.

A builder takes a run's letters and, beside them, premises on public data: at the layers' public
record P with the request's tokens, the plan hp of the group g, a shape, the call lines, the
library's sizes, the weights' shape, the number of column bits and the tables.
  pubAt X tokv: the layers' public record that publicOf returns, with a request's tokens laid in:
    what the verifier hands to a layer sub-proof's check (OnBytes/Model/VerifyLinks.lean:27).
  HearPublic: twenty premises, under the names of the record's fields. Three are worded for a
    caller:
    hs0 says, beside "Forest.shape returns s0", that s0 has the number of calls and the calls of the
    layout's field fo, so that a premise on s0 can be paid in the layout's letters; R is said of
    every environment with P's layout and scales and the group g, and of all challenges; hmats is no
    field of the record: it is the list of matrices at which the tables of the reads are laid.
  hearPublic_in_scope: HearPublic at pubAt X tokv, for all tokens, every group below 12 and its plan
    in X.G, at layerShape X.P, X.P.polCalls, DF, weightShape X.P X.y, kRef, tbRef: from
    VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z = .ok pp, publicOf Z.pol Z.KL lay = .ok X and
    Numerals of the reading.
Not claimed: that a run returns; any letter of a run; what the lookup has heard.
-/
import Johnson.Goal.Meaning.Pub34All

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.P34

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Shape layout scalesHeld readsOf)
open OnBytes.Model.Verify (publicOf Public weightShape layerShape)
open Inst.Model (Tables tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim used lut)

/-- The layers' public record with a request's tokens. -/
def pubAt (X : Public) (tokv : Array ℕ) : Layer.Pub := { X.layers with tokv := tokv }

/-- The premises on public data, under the names of Pub34's fields. -/
structure HearPublic {K : Type} [Field K] (ρ : Reading K) (P : Layer.Pub) (hp : Layer.HPlan2)
    (g : ℕ) (hS : Shape) (pc : List (List String)) (D : Dim) (s : WsShape) (lk : ℕ)
    (tb : Tables) : Prop where
  hy : layout hS pc = .ok P.y
  S : Switches hS
  hs : scalesHeld hS P.sc = .ok ()
  hg : g < P.y.NGr
  hrd : readsOf P.y = .ok P.rd
  hmats : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g
  hρ : Numerals ρ
  Z : Sized hS D
  hc : D.cap = hS.lidb
  hN : LinesAre P.y
  hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used D k)
  hs0 : ∃ s0, Forest.shape P.y.cl P.y.h.lidb = .ok s0 ∧ s0.NC = P.y.fo.NC ∧
    s0.calls = P.y.fo.calls
  Zw : SizedW s D.P
  hsL : s.L = hS.L
  hlw : wsLayOf s true lk = .ok P.wsLay
  h4 : hS.p4 = true
  R : ∀ v : Env, v.y = P.y → v.sc = P.sc → v.g = g → ∀ (rs rt : Array E) (lam : ℕ),
    lam < P.y.Lam →
      RopeFits ρ { v := v, wsLay := P.wsLay, rope := P.rope, rs := rs, rt := rt } D tb
        (g * P.y.Lam) lam
  htm : (hp.tl.mats.map fun M => (M.m, M.k)) = matsR P.y g
  hNM : hp.tl.NM = hp.tl.mats.size
  hpad : ∀ k : Fin 8,
    ρ.val (ofF ((P.y.cl.getD k.val {}).tauAt (P.y.cl.getD k.val {}).t0)) =
      (((lut tb k).pad : ℤ) : K)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- THE PREMISES ON PUBLIC DATA, at all public files in the goals' scope. -/
theorem hearPublic_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ)
    (tokv : Array ℕ) {g : ℕ} (hg : g < 12) {hp : Layer.HPlan2} (hG : X.G[g]? = some hp) :
    HearPublic ρ (pubAt X tokv) hp g (layerShape X.P) X.P.polCalls DF (weightShape X.P X.y) kRef
      tbRef := by
  obtain ⟨⟨hy, S, hs, hrd, Zd, hc, hN, hfl, Zw, hsL, hlw, h4⟩, hN12, ⟨s0, pub, hs0, efo⟩, hT, hM,
    hpad, R⟩ := pub34_all hZ hR h hρ
  exact {
    hy := hy
    S := S
    hs := hs
    hg := by
      show g < X.y.NGr
      rw [hN12]
      exact hg
    hrd := hrd
    hmats := hM g
    hρ := hρ
    Z := Zd
    hc := hc
    hN := hN
    hfl := hfl
    hs0 := ⟨s0, hs0, by
      show s0.NC = X.y.fo.NC
      rw [efo], by
      show s0.calls = X.y.fo.calls
      rw [efo]⟩
    Zw := Zw
    hsL := hsL
    hlw := hlw
    h4 := h4
    R := fun v hvy hvs hvg rs rt lam hl => by
      have y := R { v := v, wsLay := X.layers.wsLay, rope := X.layers.rope, rs := rs, rt := rt }
        hvy hvs rfl (by show v.g < 12; rw [hvg]; exact hg) lam
        (by show lam < v.y.Lam; rw [hvy]; exact hl)
      have e : v.g * v.y.Lam = g * X.y.Lam := by rw [hvg, hvy]; rfl
      have y' : RopeFits ρ
          { v := v, wsLay := X.layers.wsLay, rope := X.layers.rope, rs := rs, rt := rt } DF tbRef
          (v.g * v.y.Lam) lam := y
      rw [e] at y'
      exact y'
    htm := (hT g hp hG).1
    hNM := (hT g hp hG).2
    hpad := hpad }

#print axioms hearPublic_in_scope

end Meaning.P34
