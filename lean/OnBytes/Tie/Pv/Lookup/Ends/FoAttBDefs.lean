-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttBDefs.lean: the two tests on the attention sub-proof's public
numbers: the definitions.

Two tests on the sub-proof's shape and on the lookup's record of public numbers. They are premises
of statements on the attention sub-proof's key forms; at a shape at which one of them is false these
statements say nothing:
  pubA_of_test (OnBytes/Tie/Pv/Lookup/Ends/FoAttPub.lean): pubAB at a record's own shape, lookup's
    record and call qWH, with the hypothesis Fo.HeardA, gives Fo.PubA;
  heardA_of_hear, pubA_of_hear (OnBytes/Tie/Pv/Lookup/Ends/FoHeardRun.lean): of every record that a
    run of Attention.hear P returns, heardB at P.S and P.fs gives Fo.HeardA, and pubAB and heardB at
    P.S, P.fs and one number qWH give Fo.PubA;
  att_run_keys (the same file): under both tests at P.NC, a run of Attention.run P that returns is
    a named chain of runs, and in every world that meets LinA and ProdA at that chain's record each
    call's key form has the value of the extension of the call's key vector at its point;
  passed_att_keys (OnBytes/Tie/Pv/Lookup/Ends/FoPassedAtt.lean): the like from a passing result of
    the whole call, under both tests at every attention plan of the public record.
That the tests are true at any shape is stated nowhere, and no file of this library runs them. This
file holds the tests' definitions and imports no file of proofs, so that they can be run wherever a
parameter file lies.

 - callEqB: two calls agree in every field.
 - pcsB: the pieces of a call are aligned and pairwise apart.
 - pubCallB, pubAB S fs NC qWH b': the first test. At each call below NC: pcsB; at the call qWH: the
   padding row's value is 0 and all pieces are of the segment wh; at another call of kind R16: it
   holds the segments wl and ix and no other, the padding row's value is 0, dh T G = 2^b', each
   piece of wl has 1 + b' bits; of kind KFD: the lookup's record has this call at q; of kind KR: the
   padding row's value is 0; at a call of kind WH other than qWH the test is false.
 - cutA, cutB: where Attention.scoreUnit cuts a segment's inner point.
 - heardNumB, heardCallB, callsB, heardB S fs NC qWH b': the second test. B = 2^lB, nT = 2^lnT,
   T = 2^lt, b' = lgk + lt + ldh; the cuts of the inner points of fm and fd add up to the segments'
   numbers of bits; the last call that holds wh is qWH; fs has the shape's calls; each piece has its
   segment's number of bits and its call holds its segment; a call of kind KR has pieces of rm, rd
   alone; one of kind KFD of fm, fd alone, and the bits of the segments that it holds fit the
   call's; a call of kind R16 is the last that holds wl and the last that holds ix, and their bits
   fit.

No statement. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.AttentionHeard
import OnBytes.Tie.Pv.Lookup.Ends.Joint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Ends

/-- Two calls agree in every field. -/
def callEqB (a b : Call) : Bool :=
  decide (a.name = b.name) && decide (a.n = b.n) && decide (a.iota = b.iota) &&
    decide (a.k = b.k) && decide (a.kappa = b.kappa) && decide (a.fn = b.fn) &&
    decide (a.t0 = b.t0) && decide (a.tau = b.tau) && decide (a.pub = b.pub) &&
    decide (a.heavy = b.heavy)

/-- PcsOK as a test. -/
def pcsB (n : ℕ) (ps : List Attention.Piece) : Bool :=
  decide (∀ p ∈ ps, p.b ≤ n ∧ 2 ^ p.b ∣ p.off ∧ p.off + 2 ^ p.b ≤ 2 ^ n) &&
    decide (ps.Pairwise fun p q => p.off + 2 ^ p.b ≤ q.off ∨ q.off + 2 ^ q.b ≤ p.off)

/-- The test at a call. -/
def pubCallB (S : Attention.Shape) (fs : Forest.Shape) (qWH b' q : ℕ) (c : ACall) : Bool :=
  pcsB c.call.n c.pcs.toList &&
    if qWH = q then
      decide (tauN fs q (t0N fs q) = 0) && decide (∀ p ∈ c.pcs.toList, p.seg ∈ [Attention.Seg.wh])
    else match c.kind with
      | .r16 => c.holds .wl && c.holds .ix && decide (tauN fs q (t0N fs q) = 0) &&
          decide (∀ p ∈ c.pcs.toList, p.seg ∈ [Attention.Seg.wl, Attention.Seg.ix]) &&
          decide (S.dh * S.T * S.G = 2 ^ b') &&
          decide (∀ p ∈ c.pcs.toList.filter (fun x : Attention.Piece => x.seg == Attention.Seg.wl),
            p.b = 1 + b')
      | .kfd => (fs.calls[q]?).any fun k => callEqB k c.call
      | .kr => decide (tauN fs q (t0N fs q) = 0)
      | .wh => false

/-- The test at a shape. -/
def pubAB (S : Attention.Shape) (fs : Forest.Shape) (NC qWH b' : ℕ) : Bool :=
  (List.range NC).all fun q => (S.calls[q]?).any fun c => pubCallB S fs qWH b' q c

/-- Where scoreUnit cuts the inner point: behind g and the slot row. -/
def cutA (S : Attention.Shape) : ℕ := S.cf.lgk + (S.lnT - 1)

/-- Where the coordinates of the row within a tile begin. -/
def cutB (S : Attention.Shape) (s : Attention.Seg) : ℕ :=
  if s == Attention.Seg.fm then cutA S + S.lnT else S.cf.lgk + S.lnT

/-- On the shape's numbers. -/
def heardNumB (S : Attention.Shape) (b' : ℕ) : Bool :=
  decide (S.B = 2 ^ S.cf.lB) && decide (S.nT = 2 ^ S.lnT) && decide (S.T = 2 ^ S.cf.lt) &&
    decide (b' = S.cf.lgk + S.cf.lt + S.cf.ldh) &&
    decide (S.segB .fm = cutA S + S.lnT + 2 * S.cf.lB) &&
    decide (S.segB .fd = S.cf.lgk + S.lnT + 2 * S.cf.lB)

/-- At a call. -/
def heardCallB (S : Attention.Shape) (qWH q : ℕ) (a : ACall) : Bool :=
  decide (∀ p ∈ a.pcs.toList, p.b = S.segB p.seg ∧ a.holds p.seg = true) &&
    if qWH = q then true else match a.kind with
      | .kr => decide (∀ p ∈ a.pcs.toList, p.seg ∈ [Attention.Seg.rm, Attention.Seg.rd])
      | .kfd => decide (∀ p ∈ a.pcs.toList, p.seg ∈ [Attention.Seg.fm, Attention.Seg.fd]) &&
          decide (∀ s ∈ [Attention.Seg.fm, Attention.Seg.fd], a.holds s = true →
            S.segB s ≤ a.call.n)
      | .r16 => decide (lastHolding S .wl = some q) && decide (lastHolding S .ix = some q) &&
          decide (S.segB .wl ≤ a.call.n) && decide (S.segB .ix ≤ a.call.n)
      | .wh => true

/-- The lookup's record has the shape's calls. -/
def callsB (fs : Forest.Shape) (S : Attention.Shape) : Bool :=
  decide (fs.calls.size = S.calls.size) && (List.range S.calls.size).all fun i =>
    callEqB (fs.calls.getD i default) (S.calls.getD i default).call

/-- **The second test.** -/
def heardB (S : Attention.Shape) (fs : Forest.Shape) (NC qWH b' : ℕ) : Bool :=
  heardNumB S b' && decide (lastHolding S .wh = some qWH) && callsB fs S &&
    (List.range NC).all fun q => (S.calls[q]?).any fun a => heardCallB S qWH q a

end Fo
