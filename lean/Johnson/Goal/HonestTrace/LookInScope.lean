-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/LookInScope.lean

ClaimsZero (Johnson/HonestTrace/LookAtClaims.lean) at the trace theTrace X i x, for public files in
scope, at a request that is served, and under the side premises on ν, θ and C below: at each of the
25 lookups of the calls, every member of the list Fo.claimsOf is 0 at the rounds rsF. This file
states no goal.

"In scope" means: VerifierAndGoals.InScope Z = true, VerifierAndGoals.readFiles Z returns, and publicOf returns X on Z's
parameter and scale files, with any layout file or none. "A served request" means: ServesAt X i x.
"The side premises" are the conditions on ν, θ and C in the next sentence.

Main theorems: "claimsZero_layers_in_scope", "claimsZero_att_in_scope", "claimsZero_head_in_scope":
in scope, at a served request: for every ν that reads, at every place .cell r c inside the planes'
rows and columns, the cell (r, c) of the sub-proof's planes' matrix in theTrace X i x, and 0 at
.zero; for every θ that is 0 where the lookup's shape has one call; for every al, every jLK and all
challenges C with C.Fits at the shape's v and d: ClaimsZero holds at group g < 12, at the attention
sub-proof of group g < 12, and at the head.

Limits. It joins claimsZero_layers, claimsZero_att and claimsZero_head with lookPub_in_scope,
planesLaid_in_scope and meetsAll_theTrace (Johnson/Goal/HonestTrace/FullPlanesInScope.lean) and adds
nothing to them. The limits of these files hold here. Above all: that the premises can be met
together is known thinly. "premises_met_of_public" (Johnson/Goal/HonestTrace/FullInScope.lean) meets
them at the stored full-size example's files, at some index and a request with r = 1,023 and e =
1,024, which has no counted position (in its proof all weights and tokens are 0); which further
served requests theorems of this library exhibit is said in the head of
Johnson/HonestTrace/Full.lean, "Limits": those named there are all at synthetic weights. And that
publicOf returns at these files is a premise of that theorem, which this library checks by an
evaluation (a #guard in Johnson/Goal/Meaning/ScopeRun.lean, whose head says that it is no theorem).
The premise on θ asks nothing where a lookup has several calls. At the two example sets' shapes the
lookups of the layers, of attention and of the head have 8, 4 and 6 calls, by the lines call, callA
and callH of their parameter files; for attention in the goals' scope the 4 is a theorem
("sameCalls_in_scope", Johnson/Goal/Meaning/AttForInScope.lean).

Not claimed: that a verifier accepts these rounds; that a prover's program sends them; completeness
of the protocol; anything on what the rounds show of the keys.

-/
import Johnson.HonestTrace.LookAtClaims
import Johnson.Goal.HonestTrace.FullPlanesInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.Look

open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open OnBytes.Ends (NameA)
open OnBytes.Model.Verify (publicOf)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref}

/-- In scope, at a served request, for g < 12: under the side premises on ν, θ and C, ClaimsZero at
the lookup of the calls of group g, read from theTrace X i x. -/
theorem claimsZero_layers_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (T : ServesAt X i x) {g : ℕ} (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.y.h.lmb, ∀ c < X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb),
      ν (.cell r c) = cellMW (theTrace X i x (2 * g)) i.mat (.cell (Ends.G.iB X.y) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    ClaimsZero X.y.fo X.y.h.lmb jLK
      (Ends.G.kvG X.layers g (cellMW (theTrace X i x (2 * g)) i.mat)) θ al ν C :=
  claimsZero_layers (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h T)
    (planesLaid_in_scope hZ hR h i x) hg jLK ν hν h0 θ al h1 C hC

/-- In scope, at a served request, for g < 12: under the side premises on ν, θ and C, ClaimsZero at
the lookup of the calls of the attention sub-proof of group g, read from theTrace X i x. -/
theorem claimsZero_att_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (T : ServesAt X i x) {g : ℕ} (hg : g < 12) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ (Hd.shapeA X g).cf.lmb,
      ∀ c < (fsAt X g).NC * 2 ^ ((fsAt X g).kT + 5 - (Hd.shapeA X g).cf.lmb),
      ν (.cell r c) = (cellZ (theTrace X i x (2 * g + 1)) : NameA → Cb.Gl.E)
        ⟨(Hd.shapeA X g).cf.NAs + 2, r, c⟩)
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several (fsAt X g) = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits (fsAt X g).v (fsAt X g).d 5) :
    ClaimsZero (fsAt X g) (Hd.shapeA X g).cf.lmb jLK
      (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (cellZ (theTrace X i x (2 * g + 1)))) θ al ν C :=
  claimsZero_att (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h T)
    (planesLaid_in_scope hZ hR h i x) hg jLK ν hν h0 θ al h1 C hC

/-- In scope, at a served request: under the side premises on ν, θ and C, ClaimsZero at the lookup
of the calls of the output head, read from theTrace X i x. -/
theorem claimsZero_head_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (T : ServesAt X i x) (jLK : ℕ) (ν : _root_.Fo.Pl → Cb.Gl.E)
    (hν : ∀ r < 2 ^ X.hS.lmbH, ∀ c < X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH),
      ν (.cell r c) = readH (theTrace X i x 24) i.mat (.cell (X.hS.NHf + 2) r c))
    (h0 : ν .zero = 0) (θ al : Cb.Gl.E) (h1 : FoNums.several X.HLy.fs = false → θ = 0)
    (C : Chal Cb.Gl.E) (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (Ends.H.kvH (pubHAt X x) (readH (theTrace X i x 24) i.mat)) θ al ν C :=
  claimsZero_head (lookPub_in_scope hZ hR h) (meetsAll_theTrace hZ hR h T)
    (planesLaid_in_scope hZ hR h i x) jLK ν hν h0 θ al h1 C hC

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.claimsZero_layers_in_scope
#print axioms OnBytes.HonestTrace.Look.claimsZero_att_in_scope
#print axioms OnBytes.HonestTrace.Look.claimsZero_head_in_scope
