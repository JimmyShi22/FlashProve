-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeK5Debts.lean: code switching (K2): THE LAST PREMISE ON THE NUMBERS OF
"K5.readsThere" AT AN ATTENTION LINK's FIRST PLACE (hown, Johnson/P1K2R/MadeK5Reads.lean) PAID OUT
OF THE SHARE's OWN DEBTS: where the list of the link's own seats is the table's N.sent l 0 (so it
is at the composed meaning's own data: Johnson/Desc/Sound/MgAll.lean lays ownOf := fun m => N.sent
m 0), the seat of the link's first masked message is one of the seats that K2.LinkDebts.sent holds
to N.sent l 0. NO BLOCK IMPORTS THIS FILE.
  frame_at_yes     at an accept in a link's dress the front has a frame (K2.frameAt x = some W)
  sent_holds       LinkDebts.sent: every seat (trees in front + the lay's tree of notice i, its
                   part), i < 1 + K + own, stands in N.sent m 0
  r3_of_debts      r3B (N.sent l 0) sh l m.check.frame m.book = true FROM: hlk · hμ · hμ0 · the
                   share's premise «D» (LinkDebts at every front, frame and lay)
  made_k5_firstD   the two K5 items behind every accept of an attention link's first place, with
                   «D» in hown's place and hOwn : D.d5.ownOf l = N.sent l 0
LIMITS. hMade IS NOT PAID; the premises are shown at no value. No soundness is claimed.

-/
import Johnson.P1K2R.MadeK5Reads
import Johnson.Top.H0.Tw.K2C.HandsLink
import Johnson.Top.H0.Tw.K2C.HeldAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll sameMembers)
open VerifiableInference.Desc.First.K2 (P2 decideWith LinkDebts frameAt yes_whole rows_split
  frame_of_front frontAt_of yes_link_frame)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
open ProofFile (Cl)
open IM (XK Yes linksW placesW subW Joined)
open _root_.Tw.K2 (sendByL8 firstFront switchNotices)

theorem frame_at_yes {p : P2} {s m : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (hd : decideWith sendByL8 p s [r₁, r₂] gs = .ok m)
    {x : _root_.Tw.K2.Front} (hx : firstFront s.st s.check.frame = .ok x) :
    ∃ W, frameAt x = some W := by
  obtain ⟨x1, y, S3, Y, rows, G, c, A⟩ := yes_whole p s r₁ r₂ gs m hd
  obtain rfl : x = x1 :=
    Option.some.inj ((frontAt_of (Or.inl ⟨hp, hx⟩)).symm.trans A.front)
  obtain ⟨W, _, _, _, hW, _⟩ := rows_split A.made
  exact ⟨W, by rw [← frame_of_front A]; exact hW⟩

theorem sent_holds {N : Numbers} {m : Nat} {pIn pOut : Option Place} {s : S} {t : Nat}
    {x : _root_.Tw.K2.Front} {W : SwitchFrame} {lay : TreeLay}
    (Dd : LinkDebts N m pIn pOut s t x W lay) {i : Nat}
    (hi : i < 1 + x.T.kept.size + x.own.length) :
    (N.sent m 0).contains (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) = true := by
  have h := Dd.sent
  unfold sameMembers at h
  rw [Bool.and_eq_true] at h
  exact List.all_eq_true.1 h.1 _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem r3_of_debts {p : P2} {s m : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (hd : decideWith sendByL8 p s [r₁, r₂] gs = .ok m)
    {sh : Params.ReqShape} {l : Nat} (hlk : s.check.frame.link = l) {μ : Nat}
    (hμ : (((sh.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
      x.shape.maskRows != 0) = some μ)
    (hμ0 : μ < (s.check.frame.atMoment 0).length) {N : Numbers} {pIn pOut : Option Place}
    {t : Nat}
    (Dd : ∀ x W lay, firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l pIn pOut s t x W lay) :
    r3B (N.sent l 0) sh l m.check.frame m.book = true := by
  refine r3_left hp hd hlk hμ hμ0 fun x lay hx hlay => ?_
  obtain ⟨W, hW⟩ := frame_at_yes hp hd hx
  obtain ⟨x', _, hx', ho, _⟩ := yes_link_frame hp hd
  obtain rfl : x = x' := Except.ok.inj (hx.symm.trans hx')
  rw [← ho] at hμ0
  exact sent_holds (Dd x W lay hx hW hlay) (by omega)

variable {Q : Type}

theorem made_k5_firstD {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hsub : (ProofFile.subsOf Z)[l]? = some (subW l)) (hatt : subW l = .attention)
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (ha : D.d5.isAtt l = true)
    {q : Attention.Plan} (hW : D.d5.W.A[l / 2]? = some q)
    (c1 : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
      ((startFork (pubOf X) p.ns).trees[q.iU3]?).any (fun T => T.R == 1 && T.K == q.nW) = true)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} {s s' : S} (hy : Yes ft b s s')
    (hu : s.failed = none) (hu' : s'.failed = none)
    (hx : XK N linksW placesW E (14 * l + 2) s = true)
    (hsh : s.check.frame.shape = D.d5.shape)
    (hgr : s.check.frame.groups = reqGroups s.check.frame.shape) (hlk : s.check.frame.link = l)
    {lay₀ : Params.ReqLayout} (hlay : s.check.rows.layout = lay₀)
    (c2 : ∀ X, Z.p.built.links[l]? = some X →
      r2B lay₀ D.d5.shape l (pubOf X).arrayOf q.iU3 q.nW = true)
    {μ : Nat}
    (hμ : (((D.d5.shape.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
      x.shape.maskRows != 0) = some μ)
    (hμ0 : μ < (s.check.frame.atMoment 0).length) (hOwn : D.d5.ownOf l = N.sent l 0)
    {pIn pOut : Option Place} {t : Nat}
    (Dd : ∀ x W lay, firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      layTrees x.st.codes (switchNotices x.T x.others) = some lay →
      LinkDebts N l pIn pOut s t x W lay) :
    pubAll D base (.more (some l) "K5.liveReq") (z, s') = true ∧
      pubAll D base (.more (some l) "K5.readsThere") (z, s') = true :=
  made_k5_first h1 h24 hlot hpl hJ hsub hatt D base z ha hW c1 hy hu hu' hx hsh hgr hlk hlay c2
    fun _ _ _ _ _ hp hd => by
      rw [hOwn]
      exact r3_of_debts hp hd hlk hμ hμ0 Dd

end P1K2

#print axioms P1K2.frame_at_yes
#print axioms P1K2.sent_holds
#print axioms P1K2.r3_of_debts
#print axioms P1K2.made_k5_firstD
