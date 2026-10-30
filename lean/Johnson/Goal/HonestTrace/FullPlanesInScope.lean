-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/FullPlanesInScope.lean

At public files in the goals' scope and a request that is served: the full-size trace with its
planes (theTrace, Johnson/HonestTrace/FullPlanes.lean) meets the bundle MeetsAll, its planes are the
planes of its own keys, and in each of the 25 sub-proofs the relation after the challenge
(Cb.Lkp.MidP) holds of the lookup on the sub-proof's own calls, at the trace's own keys and bits.
This file states no goal.

"The three premises on the public files" are: Z is in the goals' scope (VerifierAndGoals.InScope Z = true);
the goals' reader returns pp (VerifierAndGoals.readFiles Z = .ok pp); publicOf returns X at Z's files.

Main theorems, each under the three premises:
* "planesIn_in_scope", "lookPub_in_scope": PlanesIn X and LookPub X, the public premises of
  FullPlanes.lean.
* "planesLaid_in_scope": PlanesLaid X i x (theTrace X i x), for every index i and every request x.
* "meetsAll_theTrace": at a request that is served (ServesAt X i x): MeetsAll X i x (theTrace X i
  x).
* "midP_in_scope": at a request that is served, for all elements θ and al of Cb.Gl.E: Cb.Lkp.MidP at
  each of the 12 groups of layers, the 12 groups' attention and the head, of the sub-proof's joint
  key vector, joint table, public padding and planes' bits, with the keys and the bits read from
  theTrace X i x.

Limits. The full size and the goals' scope alone. MidP has three clauses: the bits are 0 or 1;
weighted by 2^j they add up to 2^v less the number of padding keys; the two products agree (in full:
lawA's docstring, Johnson/HonestTrace/CountsAttention.lean). Of a sub-proof's two lookups this file
speaks of the one on the sub-proof's own calls. The layers' laws stand under Road.Switches, a
premise on the shape's switches that is no test of the Lean verifier under OnBytes/Model/ (by a
reading of Layer.layout's tests, OnBytes/Model/LayerLayout.lean: they let other values of these
switches pass); in the goals' scope it holds, and "lookPub_in_scope" proves it. That the premises
can
be met together is "premises_met_of_public" (Johnson/Goal/HonestTrace/FullInScope.lean): at the
stored full-size example's files some index serves some request with r = 1,023 and e = 1,024, which
has no counted position; and that only if publicOf returns at these files, which that theorem keeps
as a premise and which this library checks by an evaluation (a #guard in
Johnson/Goal/Meaning/ScopeRun.lean, whose head says that it is no theorem). Which further served
requests theorems of this library exhibit is said in the head of Johnson/HonestTrace/Full.lean,
"Limits": those named there are all at synthetic weights.

Not claimed: that the key vectors, tables and bits of OnBytes/Tie/Pv/Lookup/Ends/G.lean, A.lean and
H.lean are what the verifier computes or tests; that a prover commits to these matrices; that a
proof made from this trace is accepted (completeness of the protocol); anything on a claim, a round,
a mask or a message.

-/
import Johnson.HonestTrace.FullPlanes
import Johnson.Goal.HonestTrace.FullInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open OnBytes.Ends (NameA)
open OnBytes.Model.Verify (publicOf)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; publicOf returns X): PlanesIn X. -/
theorem planesIn_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : PlanesIn X :=
  planesIn_of_layersHead h (Hd.public_of_core h (Hd.core_of_scope hZ hR h))

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; publicOf returns X): LookPub X. -/
theorem lookPub_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : LookPub X :=
  lookPub_of_public h (Hd.public_of_core h (Hd.core_of_scope hZ hR h))
    (Meaning.P34.pub34_public hZ hR h).2.2.1

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; publicOf returns X), at a request that is served: MeetsAll X i x (theTrace X i x). -/
theorem meetsAll_theTrace (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx} {x : Instance ppref}
    (T : ServesAt X i x) : MeetsAll X i x (theTrace X i x) :=
  meetsAll_in_scope hZ hR h (fun k r c => planesOf_01 X x i.mat _ k r c) T

/-- Under the three premises on the public files (Z is in the goals' scope; the goals' reader
returns pp; publicOf returns X), for every index i and every request x: PlanesLaid X i x (theTrace X
i x). -/
theorem planesLaid_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (i : Cm.Idx) (x : Instance ppref) :
    PlanesLaid X i x (theTrace X i x) :=
  planesLaid_theTrace (planesIn_in_scope hZ hR h) (lookPub_in_scope hZ hR h) i x

/-- **The relation after the challenge (MidP) at the trace, in all 25 sub-proofs.** Under the three
premises on the public files (Z is in the goals' scope; the goals' reader returns pp; publicOf
returns X), at a request that is served, for all θ and al of Cb.Gl.E: Cb.Lkp.MidP holds at each
group g below 12 of layers, at the attention of each group g below 12 and at the head, of the
sub-proof's joint key vector, joint table, public padding and planes' bits, with the keys and the
bits read from the lists 2 g, 2 g + 1 and 24 of theTrace X i x. -/
theorem midP_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {i : Cm.Idx} {x : Instance ppref}
    (T : ServesAt X i x) (θ al : Cb.Gl.E) :
    (∀ g < 12, Cb.Lkp.MidP X.y.fo.v X.y.fo.d 5 32
      (Ends.G.keyG X.layers g (cellMW (theTrace X i x (2 * g)) i.mat) θ)
      (Ends.G.tabG X.layers θ) (FoNums.pads X.y.fo)
      (fun u j => Ends.G.bitsG X.y (cellMW (theTrace X i x (2 * g)) i.mat) (u * 32 + j)) al) ∧
    (∀ g < 12, Cb.Lkp.MidP (fsAt X g).v (fsAt X g).d 5 32
      (Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (cellZ (theTrace X i x (2 * g + 1))) θ)
      (Ends.A.tabA (fsAt X g) θ) (FoNums.pads (fsAt X g))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (cellZ (theTrace X i x (2 * g + 1)))
        (u * 32 + j)) al) ∧
    Cb.Lkp.MidP X.HLy.fs.v X.HLy.fs.d 5 32
      (Ends.H.keyH (pubHAt X x) (readH (theTrace X i x 24) i.mat) θ)
      (Ends.H.tabH (pubHAt X x) θ) (FoNums.pads X.HLy.fs)
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs (readH (theTrace X i x 24) i.mat) (u * 32 + j)) al :=
  have Q := lookPub_in_scope hZ hR h
  have M := meetsAll_theTrace hZ hR h T
  have L := planesLaid_in_scope hZ hR h i x
  ⟨fun _ hg => midP_layers Q M L hg θ al, fun _ hg => midP_att Q M L hg θ al,
    midP_head Q M L θ al⟩

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.planesIn_in_scope
#print axioms OnBytes.HonestTrace.lookPub_in_scope
#print axioms OnBytes.HonestTrace.meetsAll_theTrace
#print axioms OnBytes.HonestTrace.planesLaid_in_scope
#print axioms OnBytes.HonestTrace.midP_in_scope
