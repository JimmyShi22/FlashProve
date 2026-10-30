-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K1PenR/AtK1Seat.lean: Johnson/Desc/First/K8/LawCondK1.lean's three statements, and
joined_kind, at the names that Johnson/IMR/K1Seat.lean gives the reads' place's block of the lot of
K1 (k1Reads, k1Quiet). No new argument: each is the library file's statement at these
letters. That X is the link number l as built is what IM.k1_mem hands out beside k1Reads.
Compiled with the whole library.
Limits: those of LawCondK1.lean. Nothing on soundness.

-/
import Johnson.IMR.K1Seat
import Johnson.Desc.First.K8.LawCondK1

set_option autoImplicit false

namespace K1Pen

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready

variable (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
  (reads : Option (List Nat)) {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

theorem k1Reads_kind (hX : G.built[l]? = some X)
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    X.kind = 0 ∨ X.kind = 1 ∨ X.kind = 2 :=
  VerifiableInference.Desc.First.K8.Ready.joined_kind _ _ G l X _ _ _ _ hX h

theorem k1Reads_makes_layers (hX : G.built[l]? = some X) (h0 : X.kind = 0)
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    ∃ hp, G.W.G[X.g]? = some hp ∧ lay7B hp.tl s' = true ∧ onThirdB s' = funsThirdB s :=
  VerifiableInference.Desc.First.K8.Ready.k1Reads_makes_layers _ _ _ _ _ _ _ G l X _ _ _ _ hX h0 h

theorem k1Reads_makes_head (hX : G.built[l]? = some X) (h2 : X.kind = 2)
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    lay7B G.W.H.tl s' = true ∧ onThirdB s' = true :=
  VerifiableInference.Desc.First.K8.Ready.k1Reads_makes_head _ _ _ _ _ _ _ G l X _ _ _ _ hX h2 h

theorem k1Reads_makes_att (h1 : X.kind = 1)
    (h : (IM.k1Reads Z G l X pr reads).decide s rs gs = .ok s') :
    onThirdB s' = true ∧ ∀ tlP, lay7B tlP s' = lay7B tlP s :=
  VerifiableInference.Desc.First.K8.Ready.k1Reads_makes_att _ _ _ _ _ _ _ G l X _ _ _ _ h1 h

end K1Pen

#print axioms K1Pen.k1Reads_kind
#print axioms K1Pen.k1Reads_makes_layers
#print axioms K1Pen.k1Reads_makes_head
#print axioms K1Pen.k1Reads_makes_att
