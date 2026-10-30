-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Flat/CarrySForms.lean: how one written round is read as one typed round (`RMap`,
OnBytes/Flat/CarrySMaps.lean), by what the round draws.

The written rounds of a file draw in a few forms: nothing; one element; n elements; a seed (c
elements and a factor other than 0); t positions; two lists of positions; elements and positions.
OnBytes/Slice/CorePeel.lean, RoundsOf.lean and RoundsMaps.lean read the typed values of each form as
a value of a plain type (`gOne`, `gVec`, `gSeed`, `gPos`, `gLoc`, `gMix`) and show that the reading
is one-to-one. A typed block's verifier message has a type of the block's caller. Here each form
gives an `RMap` from the caller's map ι of that plain type into the typed round's verifier messages,
and `RMap.OK` from "ι is one-to-one".

Main names:
  `RMap.via fm g₀ ι`, `via_ok`: the general form.
  `RMap.none`, `one`, `vec`, `seed`, `pos`, `loc`, `mix`, each with `…_ok`: what is asked of the
    written round is `SendsDraws (toRD d) ns ne np a` (OnBytes/Slice/RoundsOf.lean) at the form's
    numbers; for a seed the four facts of `gSeed_inj`.

Limits: no protocol occurs here. Nothing on how the prover's message is read: fm is the caller's.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Flat.CarrySMaps
import OnBytes.Slice.RoundsMaps

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Prob Run OnBytes.Maker OnBytes.Slice

namespace RMap
variable {d : RDT} {r' : Round} (fm : (wT d).Msg → r'.Msg)

/-- The typed values are read by g₀ as a value of V, and that by ι as a typed verifier message. -/
def via {V : Type} (g₀ : Vals .two (Fmt.dsOf d.entry d.kind) → V) (ι : V → r'.Chal) : RMap d r' :=
  ⟨fm, fun v => ι (g₀ v)⟩

theorem via_ok {V : Type} {g₀ : Vals .two (Fmt.dsOf d.entry d.kind) → V} {ι : V → r'.Chal}
    (h₀ : Function.Injective g₀) (hι : Function.Injective ι) (hl : d.entry.logN ≤ 64) :
    (via fm g₀ ι).OK :=
  ⟨hι.comp h₀, hl⟩

/-- A round that draws nothing. -/
def none (c : r'.Chal) : RMap d r' := via fm (fun _ => ()) fun _ => c

theorem none_ok {ns a : ℕ} (h : SendsDraws (toRD d) ns 0 0 a) (c : r'.Chal) : (none fm c).OK :=
  via_ok fm (gUnit_inj _ h.plain h.els h.poss) (fun _ _ _ => rfl) h.logN

/-- A round that draws one element. -/
def one (ι : GE → r'.Chal) : RMap d r' := via fm (gOne _) ι

theorem one_ok {ns a : ℕ} (h : SendsDraws (toRD d) ns 1 0 a) {ι : GE → r'.Chal}
    (hι : Function.Injective ι) : (one fm ι).OK :=
  via_ok fm h.gOne_inj hι h.logN

/-- A round that draws n elements. -/
def vec (n : ℕ) (ι : (Fin n → GE) → r'.Chal) : RMap d r' := via fm (gVec n _) ι

theorem vec_ok {ns n a : ℕ} (h : SendsDraws (toRD d) ns n 0 a) {ι : (Fin n → GE) → r'.Chal}
    (hι : Function.Injective ι) : (vec fm n ι).OK :=
  via_ok fm h.gVec_inj hι h.logN

/-- A round that draws a seed: c elements and a factor other than 0. -/
noncomputable def seed (c : ℕ) (ι : (Fin c → GE) × GEˣ → r'.Chal) : RMap d r' :=
  via fm (gSeed c _) ι

theorem seed_ok {c : ℕ} (hp : PlainDraws (Fmt.dsOf d.entry d.kind))
    (hE : nE (Fmt.dsOf d.entry d.kind) = c + 1) (hP : nP (Fmt.dsOf d.entry d.kind) = 0)
    (hz : IsNZ (Fmt.dsOf d.entry d.kind) c) (hl : d.entry.logN ≤ 64)
    {ι : (Fin c → GE) × GEˣ → r'.Chal} (hι : Function.Injective ι) : (seed fm c ι).OK :=
  via_ok fm (gSeed_inj c _ hp hE hP hz) hι hl

/-- A round that draws t positions below 2^a. -/
def pos (a t : ℕ) (ι : (Fin t → Fin (2 ^ a)) → r'.Chal) : RMap d r' := via fm (gPos a t _) ι

theorem pos_ok {ns t a : ℕ} (h : SendsDraws (toRD d) ns 0 t a) {ι : (Fin t → Fin (2 ^ a)) → r'.Chal}
    (hι : Function.Injective ι) : (pos fm a t ι).OK :=
  via_ok fm h.gPos_inj hι h.logN

/-- A round that draws two lists of positions below 2^a. -/
def loc (a t0 t1 : ℕ) (ι : (Fin t0 → Fin (2 ^ a)) × (Fin t1 → Fin (2 ^ a)) → r'.Chal) :
    RMap d r' :=
  via fm (gLoc a t0 t1 _) ι

theorem loc_ok {ns t0 t1 a : ℕ} (h : SendsDraws (toRD d) ns 0 (t0 + t1) a)
    {ι : (Fin t0 → Fin (2 ^ a)) × (Fin t1 → Fin (2 ^ a)) → r'.Chal}
    (hι : Function.Injective ι) : (loc fm a t0 t1 ι).OK :=
  via_ok fm h.gLoc_inj hι h.logN

/-- A round that draws n elements and t positions below 2^a. -/
def mix (n a t : ℕ) (ι : (Fin n → GE) × (Fin t → Fin (2 ^ a)) → r'.Chal) : RMap d r' :=
  via fm (gMix n a t _) ι

theorem mix_ok {ns n t a : ℕ} (h : SendsDraws (toRD d) ns n t a)
    {ι : (Fin n → GE) × (Fin t → Fin (2 ^ a)) → r'.Chal} (hι : Function.Injective ι) :
    (mix fm n a t ι).OK :=
  via_ok fm h.gMix_inj hι h.logN

end RMap

end OnBytes.Flat

#print axioms OnBytes.Flat.RMap.via_ok
#print axioms OnBytes.Flat.RMap.none_ok
#print axioms OnBytes.Flat.RMap.one_ok
#print axioms OnBytes.Flat.RMap.vec_ok
#print axioms OnBytes.Flat.RMap.seed_ok
#print axioms OnBytes.Flat.RMap.pos_ok
#print axioms OnBytes.Flat.RMap.loc_ok
#print axioms OnBytes.Flat.RMap.mix_ok
