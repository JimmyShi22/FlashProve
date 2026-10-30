-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyBlkWrittenRec.lean: a yes of the written link, at a decision whose yes gives the
yes of the program's link at two keys WITH A RECORD, gives the yes in the field, for a chain of
three stages or more.

OnBytes/Slice/ManyBlk.lean concludes a chain's yes in the field from the program's yes on a view,
given the joint after the link's steps and the batching, and given that the view shows the written
trees' columns. It reads no key and no record. At the view that the written link hands its decision,
OnBytes/Slice/ManyHeadRec.lean has the first and OnBytes/Slice/ManyView.lean the second. This file
joins the three.

Main theorem.
 `yes_in_field_manyR`   whenever the written link accepts a transcript, the chain's yes in the field
                        holds, at the claim that the batching makes of the link's rows, the rows of
                        the two records among them, in the order of `RowNo.port`, and at the first
                        tree's standard words: for a decision whose yes on a view gives the yes of
                        the program's link there (`hdec`; the decision of the program's link is
                        one), and for a pair of records r that the two keys hold. The conclusion has
                        the form of the hypothesis `hsem` of `link_chain_joh`
                        (OnBytes/Slice/LinkChainJoh.lean) at the rows `rowsXR`, the sample map
                        `recZ` and the numbers `RowNo.port`.

Not claimed. The converse. That any transcript is accepted at keys with a record. The public facts
on sizes, codes, shapes, rounds and trees, `hdec`, `HeadKeepsR`, that the keys name the items 0 and
1 (`hi0`, `hi1`) and that the keys hold the records of r (`KeyHasR`), which are hypotheses: they are
shown of no setting here. At a key that fits and passes the program's test but has a factor which
reads as 0 in the field (a word not below the prime) no r meets `hK0` or `hK1`: nothing is said of
such a key. Where a key's record and seeds come from. Nothing on a link of fewer than three stages,
or whose masks do not ride in the switches' messages. Nothing on the dry run. Nothing on soundness.

-/
import OnBytes.Slice.ManyBlk
import OnBytes.Slice.ManyHeadRec

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (LinkShape IoppStage)

/-- Whenever the written link, whose rounds after the fifth are the batching's round dA and the
rounds of the chain c, accepts a transcript, the chain's yes in the field holds. dec: a decision
whose yes on a view gives the yes of the program's link there (`hdec`). r: a pair of records with n
answers each, which the two keys hold if their sizes fit the tables' shape and no seed's factor is
the program's 0 (three words 0: `isZeroE`; that it reads as no 0 in the field asks besides that its
words are below the prime: OnBytes/Slice/ManyBlkKeysRec.lean) (`hK0`, `hK1`: the program tests both
conditions). The link has at least three stages, its masks ride, and its group has two members of
equal shape sh and no mask rows. fr: the fresh mask's shape; f1: the first row of the second
member's block. All other hypotheses are public facts on sizes, codes, shapes, rounds and trees, but
for `hkeep` and that the keys name the items 0 and 1 (`hi0`, `hi1`). The word g1 is not read. -/
theorem yes_in_field_manyR (S : Sz) (t₀ lg n : ℕ) (Λ : LinkShape) (first further : TableKey)
    (st1 : IoppStage) (rest : List IoppStage) (htest : Λ.test = st1 :: rest)
    (h2 : 2 ≤ rest.length) (hride : Λ.choice.masksRide = true) (s0 : Start) (K : Codes)
    (d1 d2 d3 d4 d5 dA : PQ.RD) (c : Chain (S.sg t₀)) (xs : List PQ.XO) (dec : PQ.View → Bool)
    (hdec : ∀ V, dec V = true → (linkVerify Λ first further).decides s0 V = true)
    (hs0 : (S.sg t₀).h = 0) (hP : c.Pub K st1 rest) (hh : HeadTrees d1 d2 d3 d4 d5 dA)
    (hc : c.Trees) (hl : 1 + c.len ≤ 2 ^ 16) (sh fr : OracleShape)
    (hW : PQ.colW d2.tree = Fmt.M2.widthOf S.P.mems 1)
    (mem : Fmt.M2.Mem) (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true)
    (hm0 : mem.masks = 0) (f1 : ℕ) (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1])
    (hf1 : mem.rows ≤ f1) (hk : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem])
    (hR : sh.mainRows = mem.rows) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hs : s0.samples = 1) (hi0 : first.item = 0) (hi1 : further.item = 1)
    (hpads : 3 * n ≤ S.P.T.l) (r : (S.lkR (recZ S.P.T.l lg n)).X0)
    (hK0 : first.fits Λ.table = true → (first.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side false 1).index first r.1)
    (hK1 : further.fits Λ.table = true → (further.seeds.all fun x => !isZeroE x.beta) = true →
      KeyHasR S.P.v lg n (Λ.side true 1).index further r.2)
    (hS : LinkSizes S Λ s0.st.codes) (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1))
    (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hkeep : ∀ V, HeadKeepsR Λ first further (startCtx s0 V) V K S.P.Z.l
      (GroupTie (S.sg t₀) 0 [sh, sh, fr] #[some 0, some f1] #[none, none]))
    (g1 : (wRound d2).Orc → (S.sg t₀).cIn.Word)
    (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : c.Bl)
    (hacc : (written S d1 d2 d3 d4 d5 (dA :: c.rds) xs dec).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, c.trL b) = true) :
    c.Acc (sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
        (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
          (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (drawnE dA cA))
      (wordIn (S.sg t₀) (col1 S d2 m2.1)) (wordFr (S.sg t₀) (col1 S d2 m2.1)) (g1 m2.1) b := by
  have hv : dec (PQ.viewX (ckP .two) _ S.P.T.a xs y
      (manyTr d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b)) = true :=
    accept_view _ _ xs dec y _ m0 c0 hacc
  obtain ⟨w0, w1⟩ := shows_many d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hh hc hl
    S.P.T.a xs y
  exact acc_of_link _ Λ first further st1 rest htest h2 hride s0 K S c hs0 hP _ _ b sh fr d2 m2 w0
    w1 hW mem hmems hE hm0 f1 hst hf1 hk hR h3 hz hfm hfz
    (headRuns_manyR S t₀ lg n Λ first further st1 s0 K _ d1 d2 d3 d4 d5 dA c m1 c1 m2 c2 m3 c3 m4 c4
      m5 c5 mA cA b xs r y hs hi0 hi1 hpads hK0 hK1 hS hF hd hn0 hn1 (hkeep _)) (hdec _ hv)

end OnBytes.Slice
