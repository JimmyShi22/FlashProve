-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeysH.lean.
The key forms of the lookup of the output head's sub-proof: what is owed for them, as one named
proposition.

In the head's sub-proof the form that stands for a call's key vector (Head.keyForm) does not list
the keys. It names entries of the sub-proof's vector of reads, public terms, and two slots: the
claimed sums of two sumchecks that the sub-proof runs later. The key vector itself is a function of
the committed cells (OnBytes.Ends.H.kvH): affine in them but for two products. So "the form's value
is the key vector's extension at the call's point" is a condition on the world, in two parts, and an
algebraic identity beside them.

Defines:
  pubH R lay: what is public at the head, off the byte-level verifier's record of a run.
  MadeH R: the record is made as the head's check makes it: the layout by Head.layout, the covered
    positions by Head.coveredOf, the list of matrices by Head.matsH, the lookup's record by a run of
    Forest.pad that returned, the merged point, the two calls' numbers and the checked tokens by
    their routines (the reply's token an entry of the vocabulary, as Head.replyToken tests), the
    tables by a run of Head.tablesOf that returned.
  gamAt: the share of one segment's products in a call's key vector.
  ProdH ρ R lay W cell: (the products) the two slots hold the extensions of the products' shares:
    the stream times the reciprocal, at the call with the segment NF; the difference of two logits,
    at the call with HD0. Of the second slot it is 2^lPd / 2^(sh + 15) times what stands under the
    slot that is the extension.
  AlgH: A CLOSED PROPOSITION, NOT PROVED HERE: at the reading in the library's extension field
    (Reading.gl): for every record made so, every call and every run of Head.keyForm that returns a
    form v: in every world and for all cells that meet
    the law of the reads (Fo.ReadsAll, at all tables but those of the planes' matrix: funsH) and
    ProdH, the value of v is the extension of the call's key vector at the call's point.
States:
  keysAt_head: under AlgH, from the runs of Head.keyForm to Fo.KeysAt.
ReadsAll and ProdH are conditions on the world: what the smallness test's claims on the reads, and
the two later sumchecks, are to enforce. AlgH is algebra alone. It was held by value, on made-up
cells, at two small shapes, by a test file that is [not in this library].
Not claimed: anything on soundness, completeness or hiding. Nor is AlgH itself claimed. MadeH is a
premise in this file. Where it is concluded: of a record put together from runs of Head.hear, on a
view, and of Head.tablesOf, under four equations on public numbers: Fo.made_of_run
(OnBytes/Tie/Pv/Lookup/Ends/FoMadeH.lean); these four equations, from what Verify.publicOf and
Head.coveredOf return: Fo.Pub.madeH_public (OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeys
import OnBytes.Tie.Pv.Lookup.Ends.H

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.H

/-- What is public at the head. lay: the layout of the committed weights. -/
def pubH (R : Head.Run) (lay : WsLay) : PubH :=
  { h := R.h, L := R.L, b := R.b, cov := R.cov, win := R.x.win, lay := lay }

/-- The record of a run is made as the head's check makes it. -/
structure MadeH (R : Head.Run) : Prop where
  lay : ∃ tau, Head.layout R.h tau = .ok R.L
  cov : ∃ so, Head.coveredOf so R.h.T R.h.V = .ok R.cov
  mats : ∃ gid sid, R.hp.tl.mats = Head.matsH R.h R.L R.b gid sid
  nm : R.hp.tl.NM = R.hp.tl.mats.size
  pad : ∃ F0 c0 F1 c1, Forest.pad R.L.cl R.L.fs.pub R.h.LIDB F0 c0 = .ok ((R.x.g1, F1), c1)
  zl : lastOf R.x.g1.zx R.h.la = .ok R.x.Zl
  qN : Head.callNo R.L "NF" = some R.x.qN
  qH : Head.callNo R.L "HD0" = some R.x.qH
  win : ∃ y, y < R.h.V ∧ R.x.win = Head.winOf R.cov R.h.T y
  tabs : ∃ F2 c2 F3 c3, Head.tablesOf R.h R.L R.hp R.cov R.x F2 c2 = .ok ((R.t, F3), c3)

section
variable {K : Type} [Field K]

/-- The share of segment sn's products in call q's key number i. -/
def gamAt (P : PubH) (cell : NameH → K) (sn : String) (q i : ℕ) : K :=
  match colH P.L q (i / P.h.T) with
  | some (s, x) => if s == sn then gamH P cell sn x (i % P.h.T) else 0
  | none => 0

variable (ρ : Reading K)

/-- Call q's point, read. -/
def zkH (R : Head.Run) (q : ℕ) : List K := rdA ρ (R.x.g1.zk.getD q #[])

/-- The two slots hold the extensions of the products' shares. -/
structure ProdH (R : Head.Run) (lay : WsLay) (W : World K) (cell : NameH → K) : Prop where
  stream : W.slot R.x.tN.sCl = extL (gamAt (pubH R lay) cell "NF" R.x.qN) (zkH ρ R R.x.qN)
  logits : iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl =
    extL (gamAt (pubH R lay) cell "HD0" R.x.qH) (zkH ρ R R.x.qH)

end

/-- The head's tables of reads, without those of the planes' matrix, which no key form reads. -/
def funsH (R : Head.Run) : Array HFun := R.t.funs.filter fun f => f.mat != R.h.NHf + 2

/-- **The head's key forms read the calls' key vectors: the algebra, as one closed proposition.**
It is said at the reading in the library's extension field. -/
def AlgH : Prop :=
  ∀ (R : Head.Run) (lay : WsLay), MadeH R →
    ∀ (q : ℕ) (laid laid' : Array ℕ) (F G : Fork) (c c' : Ctx) (v : Aff),
      q < R.x.g1.shape.NC → Head.keyForm R q laid F c = .ok (((v, laid'), G), c') →
      ∀ (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E),
        ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
          (fun m r c => cell (.cell m r c)) →
        ProdH Reading.gl R lay W cell →
        v.value Reading.gl W = extL (kvH (pubH R lay) cell q) (zkH Reading.gl R q)

/-- Under AlgH: from the runs of Head.keyForm to KeysAt. -/
theorem keysAt_head (hA : AlgH) (R : Head.Run) (lay : WsLay) (hR : MadeH R) (KF : Array Aff)
    (F : Fork)
    (hKF : ∀ q < R.x.g1.shape.NC, ∃ laid laid' G c c',
      Head.keyForm R q laid F c = .ok (((KF.getD q (Aff.ofConst zeroE), laid'), G), c'))
    (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E)
    (hU : ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
      (fun m r c => cell (.cell m r c)))
    (hP : ProdH Reading.gl R lay W cell) :
    KeysAt Reading.gl W R.x.g1.shape.NC KF (kvH (pubH R lay) cell) (zkH Reading.gl R) := by
  intro q hq
  obtain ⟨laid, laid', G, c, c', h⟩ := hKF q hq
  exact hA R lay hR q laid laid' F G c c' _ hq h W cell hU hP

end Fo
