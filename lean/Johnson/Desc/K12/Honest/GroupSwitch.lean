-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/GroupSwitch.lean: the values' half of the first code switch of a proximity
test: the claim after the switch is true at the new message. The first switch is the one out of the
stage whose tables hold a group of messages that were sent earlier. The statement is at a group of
any layout, at the dealt columns with the keys that the description's `keyed`
(Johnson/Desc/K12/Join.lean) puts on them. It is `claim_behind`
(Johnson/Prover/Link/SwitchHolds.lean) with that theorem's hypothesis `hy`, on what was read, proved
by `hy_group` (Johnson/Desc/K12/Honest/GroupReads.lean). It does at the first stage what `switch_V`
(Johnson/Prover/Link/SwitchV.lean) does at a stage that a switch has made. General in the two
stages, the group, the group's public data and the layout. One theorem with its proof; `first_V`
(Johnson/Desc/K12/Honest/FirstValues.lean) calls it. Nothing of the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written) is used:
that file is not among this file's imports, direct or indirect.

In the list: s and s' are the stages (`Sg`, OnBytes/Slice/Stage.lean) before and after the switch.
A group G (`Gp s`, OnBytes/Slice/KeyGroup.lean) is a finite family of members; a member is the
format of a sent message (`G.mb j`) with a seat (`G.seat j`): the rows of the stage's tables that
the message's rows take. P (`GpData G`, OnBytes/Slice/BlkProxGp.lean) is what is public of the
group. p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of a proximity test in
a description. m and r are the members' messages and tails; `layJ G m` and `layQ G r`
(Johnson/Desc/K12/Honest/Group.lean) are these on the stage's tables. The fresh table is the first
fold's fresh mask rows; φ and ψ are its message and tails. fr gives the values in the free room of
the new mask table. m, r, φ, ψ and fr are free parameters. The old rows (`old`) are the three folded
rows that the switch reads. γ is `readP (s.h + s.g) gamma`: the fold's point `gamma`, read in the
field. `foldMsg` and `foldTl` (Johnson/Prover/Link/FoldEnc.lean) are the three folded messages and
tails. `gMsg` and `gAns` (Johnson/Prover/Link/SwitchMsg.lean) are the new message and the answer to
its sample. A claim is a target with a vector of coefficients. It is true at a message if the
products of the coefficients with the message's entries add up to the target (`Slf.Holds` at
`Slf.idf`, Cb/Ld/LdRel.lean). cu (`IoppStage`) and L (`GroupLayout`) are the program's stage and the
group's layout; id is the number of the fresh table's oracle message. `cut`, gs, `dAt` and c, and
the fields of P, are explained in the head of GroupReads.lean.

  `switch_V_group`: under the hypotheses listed below: the row after the switch and the batching,
    read in the field (`stmGk s' lay.k lay.h row`, OnBytes/Slice/BlkRead.lean), is true at the new
    message `gMsg hf (foldMsg s (layJ G m) φ γ) (foldTl s (layQ G r) ψ γ) fr`

By what. `claim_behind` at `foldMsg s (layJ G m) φ γ` and `foldTl s (layQ G r) ψ γ`. Its hypothesis
`hlaws` comes from `hs` by `laws_of_sized` (Johnson/Prover/Link/SwitchHolds.lean), its hypothesis
`hy` from `hy_group`. The hypothesis `hlog` of `hy_group` (the old rows' code has the stage's depth)
is proved here from the fields `code` of `Pg` and of `h`.

Hypotheses of `switch_V_group`.
- `hf`: what a switch asks of the two stages' sizes (`CsFit`, OnBytes/Slice/CsData.lean).
- `hs`: four inequalities on the sizes of s (`Sg.Sized`, OnBytes/Slice/Numbers.lean).
- `h`: what the switch and the batching after it have done (`Did`,
  Johnson/Desc/K12/Law/SwDid.lean): at the chain's first tree's number `p.nums.firstTree`, on the
  columns `keyed p cut gs`, to a target with the new codes' numbers nc and nz, the numbers of row
  variables of s' and one answer.
- The public hypotheses of `claim_behind`, with the same statements as there. `Pg`: the program's
  data at the switch are those of s and s' (`CsProg`, OnBytes/Slice/BlkCsJoint.lean). `hkeptO`: the
  old rows have no form on a kept member. `hG`: the group before the switch (`D.G`) has the new
  codes' numbers nc and nz, no member and no row, and its test has not begun. `hd0`, `hd1`: the old
  rows' two forms on mask rows have `s.Z.l` entries each. `hc`: each tensor of their form on the
  main row has `ceilLog2 s.C.l` variables.
- Four more hypotheses of `claim_behind`, also with the same statements as there. They are on what
  was sampled in the switch's two rounds, not on the plan or the program's data. `ht`, `hx`: `s.t`
  positions were sampled, each below `2 ^ s.C.a`. `hβ`: the unit β is the seed's factor `D.beta`,
  read in the field. The factor is a sampled element (the field `seed` of `Did`); since β is a unit,
  `hβ` cannot be met where the factor reads as 0 (`Did` has a field of its own, `factor`:
  `isZeroE D.beta = false`). `hQ`: `Qs i` is sampled position number i.
- `hk`, `hh`, `hP`, `hL`, `hparts`, `hkeys`: the public hypotheses of the library's reading theorem
  at a group (`firstReads_keyed`, Johnson/Desc/K12/Law/FirstRead.lean), at the statement S and the
  book Bk before the switch.
- The hypotheses of `hy_group` on the trees' columns, word for word. `hdM`, `hdF`: `P.d j` is
  `dAt (P.tp j)`, and `P.dF` is `dAt P.ft`. `hlenM`, `hlenF`: each tree's columns have the tree's
  width. `hpos`: group by group, the dealt positions are the tree's own list under the sampled
  positions. `hcols`: each dealt column is the column function's at its own position, which lies in
  the tree, and has the tree's width. `hZa`: the mask code is not longer than the fresh table's
  tree. `hMain`, `hMask`: at each position of a member's tree the column function's column holds, at
  the member's cut (`P.lay j`), the symbols of the code words of the member's rows at m and r.
  `hF`: the same for the fresh table's rows at φ and ψ, from word `P.oF` of a column on.
- `hold`, `hkept`, `hγ`, also word for word those of `hy_group`: the old rows are the first fold's
  output; the row that was folded has no form on a kept member; the fold's point has `s.h + s.g`
  coordinates.
- `hHolds`: the claim before the switch (`stmS s old`) is true at the three folded messages.
- `hans`: the answer that the switch has taken (`D.alpha`) reads as `gAns`, at the seed's point
  `D.z` and β.

Limits. It is the same as `switch_V` in its conclusion only, with `layJ G m` and `layQ G r` as the
stage's message and tails: the chain's first tree's number and the dealt columns are the place's
(`p.nums.firstTree`) and those of `keyed` here, free parameters there; that a stage which a switch
has made is a group of one member is not shown. No hypothesis of `switch_V_group` is proved here;
that they hold together, at any value, is not shown in this file. Four of them (`ht`, `hx`, `hβ`,
`hQ`) are on sampled positions and a sampled element, and `hβ` leaves out every seed whose factor
reads as 0. That the switch accepts is inside `Did`: it is a hypothesis and is not shown. Nothing on
how a tail, a mask or the free room's values are chosen. Nothing on completeness, on soundness or on
what is hidden.
-/
import Johnson.Desc.K12.Honest.GroupReads
import Johnson.Prover.Link.SwitchHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open Johnson.Prover.Link (symG ext0 foldMsg foldTl gAns gMsg claim_behind laws_of_sized)

/-- **The values' half of the first switch, at a group**: the row after the switch and the batching
is true at the new message. The hypotheses are listed in the head of this file. -/
theorem switch_V_group {s s' : Sg} (hf : CsFit s s') (hs : s.Sized) (fr : ℕ → GE)
    (p : P12) (cut : List Fmt.DeclaredRound) (gs : List (List (ℕ × List UInt64)))
    (G : Gp s) (P : GpData G) (cu : IoppStage) (L : GroupLayout) (id : ℕ)
    {old : SingleRows} {nc nz gp : ℕ} {others : Array OracleNotice} {S S' : Statement}
    {Bk Bk' : TreeBook} {roots : ℕ} {out : Switched} {row : GroupRow} {lay : GroupLayout}
    {theta : E} {D : Taken}
    (h : Did p.nums.firstTree (keyed p cut gs) old (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) gp
      others S Bk roots S' Bk' out row lay theta D)
    (Pg : CsProg s s' S.codes old nc nz) (hkeptO : old.kept = #[])
    (hG : D.G = { code := nc, maskCode := nz })
    (hd0 : (old.d.getD 0 #[]).size = s.Z.l) (hd1 : (old.d.getD 1 #[]).size = s.Z.l)
    (hc : ∀ v ∈ old.c.tensors, v.vars = ceilLog2 s.C.l)
    (ht : D.rC.drawn.poss.length = s.t) (hx : ∀ x ∈ D.rC.drawn.poss, x < 2 ^ s.C.a)
    (β : GEˣ) (hβ : β.val = readE D.beta) (Qs : Fin s.t → s.Ps)
    (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (hP : P.Pub p.nums.firstTree) (hL : P.LayG L)
    (hparts : PartsP P S Bk id)
    (hkeys : (cut.flatMap fun r => r.opens.map fun o => o.1.tree - p.nums.firstTree) =
      P.ts.map P.key)
    (dAt : ℕ → PQ.RD) (hdM : ∀ j, P.d j = dAt (P.tp j)) (hdF : P.dF = dAt P.ft)
    (c : ℕ → ℕ → List UInt64)
    (hlenM : ∀ j x, x < 2 ^ (G.mb j).a → (c (P.tp j) x).length = PQ.colW (P.d j).tree)
    (hlenF : ∀ x, x < 2 ^ P.aF → (c P.ft x).length = PQ.colW P.dF.tree)
    (hpos : List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => grp.map (·.1) =
      (ownAt (P.log t) (Positions.ofDraws s.C.a D.rC.drawn.poss)).toList) P.ts gs)
    (hcols : List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ x ∈ grp,
      x.1 < PQ.posN (dAt t).tree ∧ (c t x.1).length = PQ.colW (dAt t).tree ∧ x.2 = c t x.1) P.ts gs)
    (hZa : s.Z.a ≤ P.aF)
    (m : G.Msgs) (r : Tails G) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hMain : ∀ j x, x < 2 ^ (G.mb j).a → ∀ i : Fin (G.mb j).nM,
      (if (P.lay j).base then read1 (c (P.tp j) x) ((P.lay j).oM + i.val)
        else read3 (c (P.tp j) x) ((P.lay j).oM + 3 * i.val)) =
        symG (G.mb j).C x (ext0 fun a => m j (.inl (i, a))) (ext0 fun q => r j (.inl (i, q))))
    (hMask : ∀ j x, x < 2 ^ (G.mb j).a → ∀ i : Fin (G.mb j).nZ,
      read3 (c (P.tp j) x) ((P.lay j).oZ + 3 * i.val) =
        symG (G.mb j).Z (x % 2 ^ (G.mb j).Z.a) (ext0 fun a => m j (.inr (i, a)))
          (ext0 fun q => r j (.inr (i, q))))
    (hF : ∀ x, x < 2 ^ P.aF → ∀ b : Fin s.h → Bool, read3 (c P.ft x) (P.oF + 3 * Sz.rowNo b) =
        symG s.Z (x % 2 ^ s.Z.a) (ext0 fun a => φ (b, a)) (ext0 fun q => ψ (b, q)))
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = s.h + s.g)
    (hHolds : (Slf.idf (E := GE) (J := s.cMid.J)).Holds (stmS s old)
      (foldMsg s (layJ G m) φ (readP (s.h + s.g) gamma)))
    (hans : readE D.alpha = gAns hf (foldMsg s (layJ G m) φ (readP (s.h + s.g) gamma))
      (foldTl s (layQ G r) ψ (readP (s.h + s.g) gamma)) fr
      (readP _ (D.z (switchTargetStage nc nz (s'.h + s'.g) s'.h 1) S), β)) :
    (Slf.idf (E := GE) (J := s'.cIn.J)).Holds (stmGk s' lay.k lay.h row)
      (gMsg hf (foldMsg s (layJ G m) φ (readP (s.h + s.g) gamma))
        (foldTl s (layQ G r) ψ (readP (s.h + s.g) gamma)) fr) := by
  have hC : codeOf D.code = s.C := by
    have k := Pg.code
    rw [h.code] at k
    exact Option.some.inj k
  have hlog : D.code.logN = s.C.a := congrArg (·.a) hC
  exact claim_behind hf _ _ fr (laws_of_sized hs) h Pg hkeptO hG hd0 hd1 hc ht hx β hβ Qs hQ
    (hy_group p cut gs s hs G P cu L id h hk hh hP hL hparts hkeys dAt hdM hdF c hlenM hlenF hpos
      hcols hZa m r φ ψ hMain hMask hF S₀ row₀ eps claim gamma hold hkept hγ hlog Qs hQ ht)
    hHolds hans

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.switch_V_group
