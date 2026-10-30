-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkReads.lean: THE RECORDS' ROAD: THE TIE IN FRONT OF THE LINK's FIRST CODE
SWITCH.
  linkReads   ReadTie (Johnson/Desc/K12/Law/JointK.lean: whatever the plain Tw.L9.readOld
  returns at the drawn positions are the long symbols of the folded words) AT THE LINK's
  GROUP: two
              members of one shape and the first fold's mask, the three parts of ONE tree (K12's
              SeatP), every dealt column being the written oracle's at its own position: at the
              words that the
              library reads off the first tree: wordIn s (col1 S d orc) · wordFr s (col1 S d orc):
              frW | frF | srW | srF are these.
HOW. The twin, for three parts, of K12's seatReads (Johnson/Desc/K12/Law/SwRead.lean: one member and
the mask): its readPartsP CALLED AS IT LIES; then the library's link_symS
(OnBytes/Slice/BlkCsReadG.lean:123:
pure: no context, no run) CALLED AS IT LIES, where seatReads walks the three tables by hand. It is
the port of the library's group_symS (:179), which speaks of a run.
No run of `verify-on-bytes`. Nothing on soundness by itself.
-/
import Johnson.Desc.K12.Law.SwRead
import OnBytes.Slice.BlkCsReadG
import OnBytes.Slice.BlkCuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

theorem linkReads (firstTree : Nat) (S : Sz) (s : Sg) (hs0 : s.h = 0) (cu : IoppStage)
    (L : GroupLayout)
    (st : Statement) (book : TreeBook) (o0 o1 id n : Nat) (d : PQ.RD) (orc : (wRound d).Orc)
    (cols : List Tw.L9.Col) (poss : List Nat) (sh fr : OracleShape) (mem : Fmt.M2.Mem)
    (hmems : S.P.mems = [mem, mem]) (hE : mem.overE = true) (hm0 : mem.masks = 0) (f1 : ℕ)
    (hst : (Fmt.M2.starts [mem, mem]).1 = [some 0, some f1]) (hf1 : mem.rows ≤ f1)
    (hk1 : f1 + mem.rows ≤ 2 ^ Fmt.M2.kOf [mem, mem]) (hR : sh.mainRows = mem.rows)
        (h3 : sh.mainDeg = 3)
    (hz : sh.maskRows = 0) (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hwid : 3 * (mem.rows + mem.rows) + fr.maskRows * 3 = Fmt.M2.widthOf S.P.mems 1)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (hL : LayAt [o0, o1] #[some 0, some f1] #[none, none]
        L)
    (seat : SeatP st book [o0, o1, id] n s.C.a [sh, sh, fr])
    (hcols : ∀ c ∈ cols, c.2.2 = colW d orc c.2.1) :
    ReadTie firstTree s (wordIn s (col1 S d orc)) (wordFr s (col1 S d orc)) (ioppFoldShape cu L) st
        book id
      cols poss := by
  intro i pos B left ys S' row eps claim gamma hB hS _ ho hold _ _ hpos hread x hx α
  have hlogN : pos.logN = s.C.a := by rw [hpos]; rfl
  obtain ⟨t, tree0, t1, _, t3, t4, t5, t6⟩ := seat.tree
  obtain ⟨tree, u1, u2, _, _⟩ := hB.tree t tree0 t1
  rw [← u2] at t3 t4 t5
  have hlay : i.old.layout = { L with k := cu.k, h := cu.h } := by rw [hold]; rfl
  have hm : i.old.masks = 2 := by rw [hold]; rfl
  have hfr : i.old.fresh = id := by rw [hold]; rfl
  have hgam : i.old.gamma = gamma := by rw [hold]; rfl
  have hmem : i.old.layout.members = #[o0, o1] := by rw [hlay]; exact hL.members
  have hids : singleRowsOracles i.old = #[o0, o1, id] := by
    unfold singleRowsOracles
    rw [hm, hmem, hfr]
    rfl
  obtain ⟨opened, cs, hcs, hsym, hwords, hparts⟩ := readPartsP i pos B left ys #[o0, o1, id] hids t
      tree
    (Nat.zero_lt_succ 2)
    (fun p hp => by
      have := hB.place _ _ (t6 p hp)
      match p, hp, this with
      | 0, _, this => exact this
      | 1, _, this => exact this
      | 2, _, this => exact this)
    u1 (t3.trans hlogN.symm) hread
  have hsz : i.old.layout.members.size = 2 := by
    rw [hmem]
    rfl
  have hwidT : tree.shape.mainWidth + tree.shape.maskWidth = Fmt.M2.widthOf S.P.mems 1 := by
    rw [← hwid]
    unfold TreeShape.mainWidth TreeShape.maskWidth
    rw [t4, t5]
    simp [hR, h3, hz, hfm]
    omega
  rw [foldWords_std, ← hgam]
  refine link_symS s hs0 i.old pos opened ys (col1 S d orc) hsym hm (fun w hw => ?_)
    (by rw [hlay]; exact hk) (by rw [hlay]; exact hh) hsz mem hE hm0 f1 hst hf1 hk1
    (by rw [hlay]; show L.mainFirst.getD 0 none = _; rw [hL.mainFirst]; rfl)
    (by rw [hlay]; show L.mainFirst.getD 1 none = _; rw [hL.mainFirst]; rfl)
    (by rw [hlay]; show L.maskFirst.getD 0 none = _; rw [hL.maskFirst]; rfl)
    (by rw [hlay]; show L.maskFirst.getD 1 none = _; rw [hL.maskFirst]; rfl)
    sh fr hR h3 hz hfm hfz tree cs t4 t5 (fun p hp => ?_) (fun k hk' => ?_) x hx α
  · rw [hsz] at hw
    rw [hlay]
    exact hL.kept w hw
  · obtain ⟨y0, e0, s0⟩ := seat.shape p hp
    obtain ⟨x0, f0, g0⟩ := hS _ _ e0
    refine ⟨x0, g0.trans s0, fun k hk' => ?_⟩
    match p, hp, f0 with
    | 0, hp, f0 => exact hparts 0 hp x0 f0 k hk'
    | 1, hp, f0 => exact hparts 1 hp x0 f0 k hk'
    | 2, hp, f0 => exact hparts 2 hp x0 f0 k hk'
  · obtain ⟨c, c1, c2, c3, c4⟩ := hwords k hk'
    have c5 := hcols c (ho ▸ c1)
    obtain ⟨kc, e⟩ := Option.isSome_iff_exists.1 (groupCol_isSome S.P.mems 1 c.2.2 (c3.trans hwidT))
    refine ⟨kc, by rw [c4, ← hmems]; exact e, ?_⟩
    rw [← c2]
    unfold col1
    rw [← c5, e]
    rfl

end Desc.K15

#print axioms Desc.K15.linkReads
