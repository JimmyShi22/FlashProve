-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowWideParts.lean: every witness map on transcripts of strings is given by parts; a composed
map whose second extractor decodes the middle statement does not read the tail.
Both are facts on what a witness map of the type that `SndBKT` (Ior/KnowWide.lean) takes reads.

A definition, statements and proofs.
A witness map reads a slot's witness off a transcript of a batch IOP. A slot is one of the N places
of a batch, each with one instance or empty, with its own local transcript.
A wide witness map (Ior/KnowWide.lean) is typed on transcripts; an extractor of a compiled argument
can feed symbols of oracles, plain parts and verifier messages (`witOf w`). Where all oracles are
strings that are given by their symbols (`Shape.IsPoint`) the two are the same.

Main names:
  `Tr.ofParts h ρ pl o` (Iop/ViewKit.lean), for h : all oracles are strings: the transcript with
    these verifier messages, plain parts and symbols; `Spec.ofParts_eq`: a transcript of strings is
    put together again from its three parts.
  `WitP.ofT h wit`, `Spec.witOf_ofT`: the title's first half; see their docstrings.
What a composed map reads: "an IOR in every slot, then a batch IOP" (Ior/KnowWideOnline.lean:
`witSeqT F e₁ e₂ d`). If the second map reads the middle statement only (the decoder of the
statement: Ior/KnowWide.lean: `sndBKT_of_det` at the batch IOP with the slots' own oracles in the
instance), then:
  `Spec.witSeqT_fst`: the composed map reads the first part of the local transcript only: nothing
    that is sent or drawn in the batch IOP.
  `Spec.fst_ofParts`: the first part of a transcript put together reads the verifier messages of the
    first part only.
  `Spec.blindFrom_of_fst`: so, by parts, on transcripts of strings, a map that reads the first part
    only does not read the verifier messages from round |first part| on (Ior/KnowWidePass.lean:
    `WitP.BlindFrom`).
So: with a sending and its sample in F, and the decoder "the member of the list that agrees with the
sample" for what stands behind, the witness map of a session reads the instance, the encoded index,
and F's rounds: oracles, answers, seeds [no theorem here].

Limits: beyond the sentence above that is marked "[no theorem here]", this file says nothing on any
protocol, list or sample. It says nothing on how an extractor of a compiled argument learns the
verifier messages that are read.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowWideOnline
import Ior.KnowWidePass
import Iop.ViewKit

set_option autoImplicit false

namespace Iop
open Prob

/-- a map on transcripts, by parts -/
def WitP.ofT {X W : Type} {E : ExtSpec} {s : Shape} (h : s.IsPoint) (wit : X → E.Str → Tr s → W) :
    WitP X E s W :=
  fun x y o pl ρ => wit x y (Tr.ofParts h ρ pl o)

namespace Spec

def ofParts_eq : Prop :=
  ∀ (s : Shape) (h : s.IsPoint) (τ : Tr s), Tr.ofParts h τ.rho τ.plains τ.read = τ

/-- States: every map on transcripts of strings is given by parts. -/
def witOf_ofT : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (h : s.IsPoint) (wit : X → E.Str → Tr s → W),
    witOf (WitP.ofT h wit) = wit

/-- States: if the second map reads the middle statement only, the composed map reads the first part
of the local transcript only. -/
def witSeqT_fst : Prop :=
  ∀ (X Xl WA WB : Type) (E0 Ej : ExtSpec) (F : IOR X E0 Xl (E0.prod Ej)) (t : Shape)
      (e₁ : X × E0.Str → Tr F.shape → WB → WA) (dm : Xl × Ej.Str → E0.Str → WB) (d : WA) (x : X)
      (y : E0.Str) (τ τ' : Tr (F.shape ++ t)),
    Tr.fst τ = Tr.fst τ' →
    witSeqT F e₁ (fun a y0 (_ : Tr t) => dm a y0) d x y τ =
      witSeqT F e₁ (fun a y0 (_ : Tr t) => dm a y0) d x y τ'

def fst_ofParts : Prop :=
  ∀ (s t : Shape) (h : (s ++ t).IsPoint) (o : Orcs (s ++ t))
      (pl : Plains (s ++ t)) (ρ ρ' : Rho (s ++ t)),
    Rho.AgreeTo s.length ρ ρ' →
    Tr.fst (Tr.ofParts h ρ pl o) = Tr.fst (s := s) (Tr.ofParts h ρ' pl o)

/-- States: by parts, on transcripts of strings: if the map reads the first part of the transcript
only, no verifier message from the end of the first part on is read. -/
def blindFrom_of_fst : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s t : Shape)
      (h : (s ++ t).IsPoint) (wit : X → E.Str → Tr (s ++ t) → W),
    (∀ x y τ τ', Tr.fst (s := s) τ = Tr.fst τ' → wit x y τ = wit x y τ') →
    (WitP.ofT h wit).BlindFrom s.length

end Spec

theorem ofParts_eq : Spec.ofParts_eq
  | [], _, () => rfl
  | r :: s, (h, hs), ((o, pl), c, τ) => by
      show ((h.ofSyms fun p => r.rd o p, pl), c, Tr.ofParts hs τ.rho τ.plains τ.read) =
        ((o, pl), c, τ)
      rw [ofParts_eq s hs τ, h.ofSyms_rd o]

theorem witOf_ofT : Spec.witOf_ofT := by
  intro X W E s h wit
  funext x y τ
  show wit x y (Tr.ofParts h τ.rho τ.plains τ.read) = wit x y τ
  rw [ofParts_eq s h τ]

theorem witSeqT_fst : Spec.witSeqT_fst := by
  intro X Xl WA WB E0 Ej F t e₁ dm d x y τ τ' h
  simp only [witSeqT, h]

theorem fst_ofParts : Spec.fst_ofParts
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, t, (h, hs), o, (pl, pls), (c, ρ), (c', ρ'), hρ => by
      show ((h.ofSyms fun p => o (.inl p), pl),
          c,
          Tr.fst (Tr.ofParts hs ρ pls fun p => o (.inr p))) =
        ((h.ofSyms fun p => o (.inl p), pl),
          c',
          Tr.fst (s := s) (Tr.ofParts hs ρ' pls fun p => o (.inr p)))
      rw [hρ.1, fst_ofParts s t hs (fun p => o (.inr p)) pls ρ ρ' hρ.2]

theorem blindFrom_of_fst : Spec.blindFrom_of_fst := fun _ _ _ s t h _ hw x y o pl ρ ρ' hρ =>
  hw x y _ _ (fst_ofParts s t h o pl ρ ρ' hρ)

end Iop
